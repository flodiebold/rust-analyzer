#[cfg(test)]
mod test_db;
#[cfg(test)]
mod tests;

use std::{
    cmp::Ordering,
    panic::{catch_unwind, AssertUnwindSafe},
    sync::Mutex,
};

use anyhow::{anyhow, Context};
use base_db::{impl_intern_key, salsa::InternKey, Upcast};
use cranelift::{
    codegen::{self, ir::StackSlot},
    frontend::Switch,
    prelude::{
        isa::{CallConv, TargetIsa},
        settings, types, AbiParam, Block, Configurable, EntityRef, FunctionBuilder,
        FunctionBuilderContext, Imm64, InstBuilder, IntCC, MemFlags, Signature, StackSlotData,
        TrapCode, Type, Value, Variable,
    },
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, FuncId, Module};
use either::Either;
use hir_def::{
    layout::{Abi, Scalar, TagEncoding},
    CallableDefId, FunctionId, LocalFieldId, Lookup, VariantId,
};
use hir_ty::{
    db::HirDatabase,
    layout::{Layout, RustcEnumVariantIdx, Variants},
    mir::{
        BasicBlockId, BinOp, CastKind, LocalId, MirBody, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind, UnOp,
    },
    AdtId, FnAbi, Interner, MemoryMap, Substitution, TraitEnvironment, Ty, TyExt, TyKind,
};
use la_arena::ArenaMap;
use rustc_hash::FxHashMap;
use salsa::InternValueTrivial;
use smallvec::SmallVec;
use triomphe::Arc;

#[derive(Clone)]
pub struct JitEngine<'a> {
    jit: Arc<Mutex<Jit>>,
    db: &'a dyn CodegenDatabase,
}

extern "C" fn ensure_function(engine: &JitEngine, func_id: u32) -> *const u8 {
    let jit = engine.jit.clone();
    let mut jit = jit.lock().unwrap();
    let func_id = MonoFunctionId::from_intern_id(func_id.into());
    let code = catch_unwind(AssertUnwindSafe(|| jit.compile(engine.db, func_id, engine).unwrap()))
        .unwrap_or_else(|err| {
            eprintln!("failed to compile function {}: {:?}", func_id.as_intern_id().as_u32(), err);
            std::process::abort();
        });
    code
}

impl<'a> JitEngine<'a> {
    pub fn new(db: &'a dyn CodegenDatabase) -> JitEngine {
        JitEngine { jit: Arc::new(Mutex::new(Jit::default())), db }
    }
}

pub struct Jit {
    /// The function builder context, which is reused across multiple
    /// FunctionBuilder instances.
    builder_context: FunctionBuilderContext,

    /// The main Cranelift context, which holds the state for codegen. Cranelift
    /// separates this from `Module` to allow for parallel compilation, with a
    /// context per thread, though this isn't used here.
    ctx: codegen::Context,

    /// The data description, which is to data objects what `ctx` is to functions.
    data_description: DataDescription,

    /// The module, with the jit backend, which manages the JIT'd
    /// functions.
    module: JITModule,

    compiled_functions: FxHashMap<MonoFunctionId, FuncId>,
    shims: FxHashMap<MonoFunctionId, FuncId>,
}

// FIXME: cleanup of Jit (needs to call free_memory())

impl Default for Jit {
    fn default() -> Self {
        let mut flag_builder = settings::builder();
        flag_builder.set("use_colocated_libcalls", "false").unwrap();
        flag_builder.set("is_pic", "true").unwrap(); // enable?
        let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
            panic!("host machine is not supported: {}", msg);
        });
        let isa = isa_builder.finish(settings::Flags::new(flag_builder)).unwrap();
        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        builder.hotswap(true);

        let module = JITModule::new(builder);
        Self {
            builder_context: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            data_description: DataDescription::new(),
            module,
            compiled_functions: FxHashMap::default(),
            shims: FxHashMap::default(),
        }
    }
}

impl Jit {
    fn compile(
        &mut self,
        db: &dyn CodegenDatabase,
        mono_func_id: MonoFunctionId,
        jit_engine: &JitEngine,
    ) -> Result<*const u8, anyhow::Error> {
        if let Some(f) = self.compiled_functions.get(&mono_func_id) {
            // FIXME check for changes to the function since the last compilation
            // FIXME also cache error?
            return Ok(self.module.get_finalized_function(*f));
        }

        let MonoFunction { func: func_id, subst } = db.lookup_intern_mono_function(mono_func_id);
        let data = db.function_data(func_id);
        eprintln!(
            "Compiling function {} ({})",
            func_id.as_intern_id().as_u32(),
            data.name.as_str()
        );
        let sig = db.callable_item_signature(func_id.into()).substitute(Interner, &subst);

        match sig.abi() {
            FnAbi::Rust => {}
            _ => panic!("unsupported abi for function: {:?}", sig.abi()),
        };

        let env = db.trait_environment(func_id.into());

        self.ctx.func.signature = translate_signature(&sig, self.module.isa(), db, &env);

        let builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        let body = db
            .monomorphized_mir_body(func_id.into(), subst, env.clone())
            .map_err(|e| anyhow!("failed to lower MIR: {:?}", e))?;

        let mut translator = FunctionTranslator {
            db,
            body: &body,
            variables: ArenaMap::new(),
            blocks: ArenaMap::new(),
            builder,
            module: &mut self.module,
            shims: &mut self.shims,
            env,
            engine: jit_engine,
        };

        translator.create_blocks();

        translator.compile_all_blocks();

        translator.builder.seal_all_blocks(); // FIXME do this better?
        translator.builder.finalize();

        let id = self
            .module
            // FIXME declare with name and linkage?
            .declare_anonymous_function(&self.ctx.func.signature)
            .context("failed to declare function")?;

        self.compiled_functions.insert(mono_func_id, id);

        // Define the function to jit. This finishes compilation, although
        // there may be outstanding relocations to perform. Currently, jit
        // cannot finish relocations until all functions to be called are
        // defined. For this toy demo for now, we'll just finalize the
        // function below.
        self.module.define_function(id, &mut self.ctx).context("failed to define function")?;

        // Now that compilation is finished, we can clear out the context state.
        self.module.clear_context(&mut self.ctx);

        // Finalize the functions which we just defined, which resolves any
        // outstanding relocations (patching in addresses, now that they're
        // available).
        self.module.finalize_definitions().unwrap();

        // We can now retrieve a pointer to the machine code.
        let code = self.module.get_finalized_function(id);

        Ok(code)
    }
}

struct FunctionTranslator<'a> {
    db: &'a dyn CodegenDatabase,
    body: &'a MirBody,
    variables: ArenaMap<LocalId, LocalKind>,
    blocks: ArenaMap<BasicBlockId, Block>,
    builder: FunctionBuilder<'a>,
    module: &'a mut JITModule,
    shims: &'a mut FxHashMap<MonoFunctionId, FuncId>,
    env: Arc<TraitEnvironment>,
    engine: &'a JitEngine<'a>,
}

#[derive(Clone, Copy, Debug)]
enum LocalKind {
    Variable(Variable),
    VariablePair(Variable, Variable),
    Stack(StackSlot),
}

#[derive(Clone, Copy, Debug)]
enum PlaceKind {
    Variable(Variable),
    VariablePair(Variable, Variable),
    Stack(StackSlot, i32),
    Mem(Value, i32),
}

#[derive(Clone, Copy, Debug)]
enum ValueKind {
    Primitive(Value, bool),
    ScalarPair(Value, Value),
    Aggregate { slot: MemSlot, offset: i32, size: i32 },
}

#[derive(Clone, Copy, Debug)]
enum MemSlot {
    Stack(StackSlot),
    MemAddr(Value),
}

impl<'a> FunctionTranslator<'a> {
    fn get_shim(&mut self, mono_func_id: MonoFunctionId) -> FuncId {
        if let Some(shim) = self.shims.get(&mono_func_id) {
            return *shim;
        }

        let MonoFunction { func, subst } = self.db.lookup_intern_mono_function(mono_func_id);
        let sig = self.db.callable_item_signature(func.into()).substitute(Interner, &subst);

        match sig.abi() {
            FnAbi::Rust => {}
            _ => panic!("unsupported abi for shim: {:?}", sig.abi()),
        };

        let mut ctx = self.module.make_context(); // FIXME share (extract ShimCompiler?)
        ctx.func.signature = translate_signature(&sig, self.module.isa(), self.db, &self.env);

        let sig = ctx.func.signature.clone();

        // FIXME can this legitimately fail?
        let id = self
            .module
            .declare_anonymous_function(&ctx.func.signature)
            .expect("failed to declare anonymous function for shim");

        let mut builder_context = FunctionBuilderContext::new(); // FIXME share
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);

        let mut signature = Signature::new(self.module.isa().default_call_conv());
        let ptr = self.module.isa().pointer_type();
        signature.params.push(AbiParam::new(ptr));
        signature.params.push(AbiParam::new(types::I32));
        signature.returns.push(AbiParam::new(ptr));
        let sig_ref = builder.import_signature(signature);

        let block = builder.create_block();
        builder.switch_to_block(block);
        builder.append_block_params_for_function_params(block);
        // FIXME can we pass engine and address of ensure_function as "global value" / "VM context pointer"?
        // FIXME also maybe just import the function? if that works? (need to declare it as exported though)
        let arg1 = builder.ins().iconst(ptr, self.engine as *const JitEngine as i64);
        let arg2 = builder.ins().iconst(types::I32, mono_func_id.as_intern_id().as_u32() as i64);
        let callee = builder.ins().iconst(ptr, ensure_function as usize as i64);
        let call = builder.ins().call_indirect(sig_ref, callee, &[arg1, arg2]);
        let result = builder.inst_results(call)[0];

        let sig_ref = builder.import_signature(sig);
        let args = builder.block_params(block).to_vec();
        let call = builder.ins().call_indirect(sig_ref, result, &args);
        let rvals = builder.inst_results(call).to_vec();
        builder.ins().return_(&rvals);
        // tail call doesn't work in SystemV callconv, but we might want another one anyway?
        // builder.ins().return_call_indirect(sig_ref, result, &[]);
        builder.seal_all_blocks();
        builder.finalize();
        // FIXME can this legitimately fail?
        self.module.define_function(id, &mut ctx).expect("failed to compile shim function");
        id
    }

    fn create_blocks(&mut self) {
        for (block_id, _) in self.body.basic_blocks.iter() {
            self.blocks.insert(block_id, self.builder.create_block());
        }
    }

    fn compile_all_blocks(&mut self) {
        let body = self.body.clone();
        for (block_id, _) in body.basic_blocks.iter() {
            self.compile_mir_block(block_id);
        }
    }

    fn compile_function_init(&mut self) {
        let block = self.blocks[self.body.start_block];
        self.builder.append_block_params_for_function_params(block);
        let mut param_values = self.builder.block_params(block).to_vec();
        param_values.reverse();
        for param in self.body.param_locals.iter().copied() {
            match self.get_variable(param) {
                LocalKind::Variable(var) => self.builder.def_var(var, param_values.pop().unwrap()),
                LocalKind::VariablePair(var1, var2) => {
                    self.builder.def_var(var1, param_values.pop().unwrap());
                    self.builder.def_var(var2, param_values.pop().unwrap());
                }
                LocalKind::Stack(ss) => {
                    let ty = self.body.locals[param].ty.clone();
                    let layout = self.ty_layout(ty);
                    let size = layout.size.bytes_usize() as i32;
                    self.translate_mem_copy(
                        MemSlot::Stack(ss),
                        0,
                        MemSlot::MemAddr(param_values.pop().unwrap()),
                        0,
                        size,
                    );
                }
            }
        }
    }

    fn compile_mir_block(&mut self, block_id: BasicBlockId) {
        self.builder.switch_to_block(self.blocks[block_id]);
        if self.body.start_block == block_id {
            self.compile_function_init();
        }
        let block = &self.body.basic_blocks[block_id];
        for stmt in &block.statements {
            self.translate_stmt(stmt);
        }
        let terminator = block.terminator.as_ref().unwrap();
        match &terminator.kind {
            TerminatorKind::Return => {
                self.emit_return();
            }
            TerminatorKind::Drop { place: _, target, unwind } => {
                // TODO actually drop place
                if unwind.is_some() {
                    panic!("unsupported unwind");
                }
                self.builder.ins().jump(self.blocks[*target], &[]);
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr = self.translate_operand(discr).assert_primitive().0;
                let mut switch = Switch::new();
                for (val, target) in targets.iter() {
                    switch.set_entry(val, self.blocks[target]);
                }
                switch.emit(&mut self.builder, discr, self.blocks[targets.otherwise()]);
            }
            TerminatorKind::Goto { target } => {
                self.builder.ins().jump(self.blocks[*target], &[]);
            }
            TerminatorKind::Call { func, args, destination, target, cleanup, from_hir_call: _ } => {
                if cleanup.is_some() {
                    panic!("unsupported unwind");
                }
                let static_func_id = match func {
                    Operand::Constant(konst) => match konst.data(Interner).ty.kind(Interner) {
                        TyKind::FnDef(func_id, subst) => {
                            let callable_def =
                                self.db.lookup_intern_callable_def((*func_id).into());
                            let subst = subst.clone();
                            let abi =
                                self.db.callable_item_signature(callable_def).skip_binders().abi();
                            Some((abi, callable_def, subst))
                        }
                        _ => None,
                    },
                    _ => None,
                };
                // FIXME order of operations? first args or first func?

                // handle tuple struct/enum constructor specially
                if let Some((
                    abi,
                    id @ (CallableDefId::StructId(_) | CallableDefId::EnumVariantId(_)),
                    subst,
                )) = static_func_id
                {
                    assert_eq!(abi, FnAbi::Rust);
                    match id {
                        CallableDefId::StructId(s) => {
                            let ty = TyKind::Adt(AdtId(s.into()), subst.clone()).intern(Interner);
                            let layout = self.ty_layout(ty.clone());
                            let tys: Vec<_> = self
                                .db
                                .field_types(VariantId::StructId(s))
                                .iter()
                                .map(|(_, t)| t.clone().substitute(Interner, &subst))
                                .collect();
                            self.store_tuple_layout(&layout, &tys, destination, &args);
                        }
                        CallableDefId::EnumVariantId(ev) => {
                            let ty = TyKind::Adt(
                                AdtId(ev.lookup(self.db.upcast()).parent.into()),
                                subst.clone(),
                            )
                            .intern(Interner);
                            let layout = self.ty_layout(ty.clone());
                            let variant_id = VariantId::EnumVariantId(ev);
                            let layout = self.store_tag_and_get_variant_layout(
                                variant_id,
                                &layout,
                                destination,
                            );
                            let tys: Vec<_> = self
                                .db
                                .field_types(variant_id)
                                .iter()
                                .map(|(_, t)| t.clone().substitute(Interner, &subst))
                                .collect();
                            self.store_tuple_layout(layout, &tys, destination, &args);
                        }
                        _ => unreachable!(),
                    };
                    if let Some(target) = target {
                        self.builder.ins().jump(self.blocks[*target], &[]);
                    }
                    return;
                }

                let args: Vec<_> = args
                    .iter()
                    .flat_map(|a| {
                        let v = self.translate_operand(a);
                        match v {
                            ValueKind::Primitive(val, _) => [val].to_vec(),
                            ValueKind::ScalarPair(val1, val2) => [val1, val2].to_vec(),
                            ValueKind::Aggregate { slot, offset, size: _ } => {
                                [self.translate_mem_slot_addr(slot, offset)].to_vec()
                            }
                        }
                    })
                    .collect();

                match static_func_id {
                    Some((FnAbi::RustIntrinsic, CallableDefId::FunctionId(func_id), subst)) => {
                        self.translate_rust_intrinsic_call(func_id, subst, &args, destination);
                    }
                    Some((_abi, CallableDefId::FunctionId(func_id), subst)) => {
                        let mono_func_id =
                            self.db.intern_mono_function(MonoFunction { func: func_id, subst });
                        let shim = self.get_shim(mono_func_id);
                        let func_ref =
                            self.module.declare_func_in_func(shim, &mut self.builder.func);
                        let call = self.builder.ins().call(func_ref, &args);
                        let results = self.builder.inst_results(call).to_vec();
                        self.store_func_call_return(&results, destination);
                    }
                    None => {
                        let _func = self.translate_operand(func);
                        panic!("unsupported indirect call");
                    }
                    _ => unreachable!(),
                }
                if let Some(target) = target {
                    self.builder.ins().jump(self.blocks[*target], &[]);
                }
            }
            TerminatorKind::Unreachable => {
                self.builder.ins().trap(TrapCode::UnreachableCodeReached);
            }
            TerminatorKind::UnwindResume => panic!("unsupported unwind"),
            TerminatorKind::Abort => panic!("unsupported abort"),
            TerminatorKind::Assert { .. } => panic!("unsupported assert"),
            TerminatorKind::Yield { .. } => panic!("unsupported yield"),
            TerminatorKind::CoroutineDrop => panic!("unsupported coroutine drop"),
            TerminatorKind::DropAndReplace { .. }
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. } => {
                panic!("encountered disallowed terminator: {:?}", terminator.kind)
            }
        }
    }

    fn store_func_call_return(&mut self, results: &[Value], destination: &Place) {
        let (dest, ret_ty) = self.translate_place_with_ty(destination);
        let ret_ty_layout = self.ty_layout(ret_ty.clone());
        if results.len() > 0 {
            let ret_val = match ret_ty_layout.abi {
                Abi::Uninhabited => panic!("uninhabited return"),
                Abi::Scalar(_) => {
                    assert_eq!(results.len(), 1);
                    ValueKind::Primitive(results[0], false)
                }
                Abi::ScalarPair(_, _) => {
                    assert_eq!(results.len(), 2);
                    ValueKind::ScalarPair(results[0], results[1])
                }
                Abi::Aggregate { sized } => {
                    if !sized {
                        panic!("unsupported unsized return")
                    }
                    assert_eq!(results.len(), 1);
                    let size = ret_ty_layout.size.bytes_usize() as i32;
                    ValueKind::Aggregate { slot: MemSlot::MemAddr(results[0]), offset: 0, size }
                }
                Abi::Vector { .. } => panic!("unsupported vector return"),
            };
            self.translate_place_kind_store(dest, ret_ty, ret_val);
        }
    }

    fn emit_return(&mut self) {
        let return_ty = self.body.locals[return_slot()].ty.clone();
        let layout = self.ty_layout(return_ty);
        let returns = match layout.abi {
            Abi::Aggregate { sized: true } if layout.size.bytes() == 0 => Vec::new(),
            _ => match self.translate_copy_local_with_projection(return_slot(), &[]).0 {
                ValueKind::Primitive(val, _) => [val].to_vec(),
                ValueKind::ScalarPair(val1, val2) => [val1, val2].to_vec(),
                ValueKind::Aggregate { slot, offset, size: _ } => {
                    let addr = self.translate_mem_slot_addr(slot, offset);
                    [addr].to_vec()
                }
            },
        };
        self.builder.ins().return_(&returns);
    }

    fn translate_stmt(&mut self, stmt: &hir_ty::mir::Statement) {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                self.translate_stmt_assign(place, rvalue);
            }
            StatementKind::Deinit(_place) => {
                panic!("unsupported deinit stmt")
            }
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::FakeRead(_)
            | StatementKind::Nop => {}
        }
    }

    fn translate_stmt_assign(&mut self, place: &Place, rvalue: &Rvalue) {
        let value = match rvalue {
            Rvalue::Use(operand) => self.translate_operand(operand),
            Rvalue::CheckedBinaryOp(binop, left, right) => {
                self.translate_checked_binop(binop, left, right)
            }
            Rvalue::UnaryOp(UnOp::Neg, op) => self.translate_neg(op),
            Rvalue::UnaryOp(UnOp::Not, op) => self.translate_not(op),
            Rvalue::Ref(_, place) => {
                let projection = place.projection.lookup(&self.body.projection_store);
                let typ = self.module.isa().pointer_type();
                match projection {
                    [] => {
                        // FIXME spilling on demand like this won't work properly, I think?
                        let stack_slot = self.spill_to_stack(place.local);
                        let addr = self.builder.ins().stack_addr(typ, stack_slot, 0);
                        ValueKind::Primitive(addr, false)
                    }
                    [rest @ .., ProjectionElem::Deref] => {
                        self.translate_copy_local_with_projection(place.local, rest).0
                    }
                    _ => {
                        let place_kind = self.translate_place(place);
                        let addr = match place_kind {
                            PlaceKind::Variable(_) => panic!("unsupported ref to variable"),
                            PlaceKind::VariablePair(_, _) => {
                                panic!("unsupported ref to variable pair")
                            }
                            PlaceKind::Stack(ss, off) => {
                                let addr = self.builder.ins().stack_addr(typ, ss, off);
                                addr
                            }
                            PlaceKind::Mem(addr, off) => {
                                self.builder.ins().iadd_imm(addr, off as i64)
                            }
                        };
                        ValueKind::Primitive(addr, false)
                    }
                }
            }
            Rvalue::Cast(kind, operand, to_ty) => {
                use hir_ty::PointerCast::*;
                let (value, from_ty) = self.translate_operand_with_ty(operand);
                let to_layout = self.ty_layout(to_ty.clone());
                match kind {
                    CastKind::IntToInt => {
                        let (from_sz, from_sign) =
                            get_int_ty(&from_ty, self.module.isa()).expect("int");
                        let (to_sz, to_sign) = get_int_ty(&to_ty, self.module.isa()).expect("int");
                        let to_typ = match &to_layout.abi {
                            Abi::Scalar(scalar) => {
                                translate_scalar_type(*scalar, self.module.isa())
                            }
                            _ => panic!("int with non-scalar abi"),
                        };
                        let value = value.assert_primitive().0;
                        let cast_value = match (from_sz.cmp(&to_sz), from_sign, to_sign) {
                            (Ordering::Greater, _, _) => {
                                // FIXME is this correct for signed reductions?
                                self.builder.ins().ireduce(to_typ, value)
                            }
                            (Ordering::Less, false, _) => self.builder.ins().uextend(to_typ, value),
                            (Ordering::Less, true, _) => self.builder.ins().sextend(to_typ, value),
                            (Ordering::Equal, _, _) => value,
                        };
                        ValueKind::Primitive(cast_value, to_sign)
                    }
                    CastKind::Pointer(UnsafeFnPointer | MutToConstPointer | ArrayToPointer) => {
                        // nothing to do here
                        value
                    }
                    CastKind::Pointer(Unsize) => {
                        let value = value.assert_primitive().0;
                        let from_pointee =
                            from_ty.as_reference_or_ptr().expect("pointer cast without pointer").0;
                        match from_pointee.kind(Interner) {
                            TyKind::Array(_, size) => {
                                assert!(matches!(to_layout.abi, Abi::ScalarPair(_, _)));
                                let size_val = self.translate_const(size).0.assert_primitive().0;
                                ValueKind::ScalarPair(value, size_val)
                            }
                            _ => panic!("unsupported unsize from {:?} to {:?}", from_ty, to_ty),
                        }
                    }

                    _ => panic!("unsupported cast: {:?} {:?} {:?}", kind, from_ty, to_ty),
                }
            }
            Rvalue::Aggregate(kind, operands) => {
                use hir_ty::mir::AggregateKind::*;
                match kind {
                    Array(elem_ty) => {
                        let layout = self.ty_layout(elem_ty.clone());
                        for (i, op) in operands.iter().enumerate() {
                            let val = self.translate_operand(op);
                            self.translate_place_store_with_offset(
                                place,
                                elem_ty.clone(),
                                i as i32 * layout.size.bytes_usize() as i32,
                                val,
                            );
                        }
                    }
                    Tuple(tuple_ty) => {
                        self.store_tuple(tuple_ty.clone(), place, operands);
                    }
                    Adt(variant_id, subst) => {
                        let adt = variant_id.adt_id(self.db.upcast());
                        let ty = TyKind::Adt(chalk_ir::AdtId(adt), subst.clone()).intern(Interner);
                        let layout = self.ty_layout(ty.clone());
                        let layout =
                            self.store_tag_and_get_variant_layout(*variant_id, &layout, place);
                        let field_types = self.db.field_types(*variant_id);
                        for (i, op) in operands.iter().enumerate() {
                            let val = self.translate_operand(op);
                            let field_offset = layout.fields.offset(i);
                            let field_ty = field_types[LocalFieldId::from_raw((i as u32).into())]
                                .clone()
                                .substitute(Interner, subst);
                            self.translate_place_store_with_offset(
                                place,
                                field_ty,
                                field_offset.bytes_usize() as i32,
                                val,
                            );
                        }
                    }
                    Union(_, _) => panic!("unsupported union aggregate"),
                    Closure(_) => panic!("unsupported closure aggregate"),
                }
                return;
            }
            Rvalue::Discriminant(place) => self.translate_load_discriminant(place),
            Rvalue::Repeat(_, _) => panic!("unsupported repeat rvalue"),
            Rvalue::Len(_) => panic!("unsupported len rvalue"),
            Rvalue::ShallowInitBox(_, _) => panic!("unsupported ShallowInitBox"),
            Rvalue::ShallowInitBoxWithAlloc(_) => panic!("unsupported ShallowInitBoxWithAlloc"),
            Rvalue::CopyForDeref(_) => panic!("unsupported CopyForDeref"),
        };
        self.translate_place_store(place, value)
    }

    fn translate_place(&mut self, place: &Place) -> PlaceKind {
        self.translate_place_with_ty(place).0
    }

    fn translate_place_with_ty(&mut self, place: &Place) -> (PlaceKind, Ty) {
        let projection = place.projection.lookup(&self.body.projection_store);
        let local = place.local;
        self.translate_local_with_projection(local, projection)
    }

    fn translate_local_with_projection(
        &mut self,
        local: LocalId,
        projection: &[ProjectionElem<LocalId, Ty>],
    ) -> (PlaceKind, Ty) {
        let mut ty = self.body.locals[local].ty.clone();
        let var = self.get_variable(local);
        let mut kind = match var {
            LocalKind::Variable(var) => PlaceKind::Variable(var),
            LocalKind::VariablePair(var1, var2) => PlaceKind::VariablePair(var1, var2),
            LocalKind::Stack(ss) => PlaceKind::Stack(ss, 0),
        };
        for elem in projection {
            match elem {
                ProjectionElem::Deref => {
                    ty = ty.as_reference_or_ptr().expect("non-ptr deref target").0.clone();
                    let addr =
                        self.translate_load_pointer_value(kind, self.module.isa().pointer_type());
                    kind = PlaceKind::Mem(addr, 0);
                }
                ProjectionElem::Index(idx) => {
                    let addr = self.translate_place_kind_addr(kind);
                    ty = match ty.kind(Interner) {
                        TyKind::Array(elem_ty, _size) => elem_ty.clone(),
                        TyKind::Slice(elem_ty) => elem_ty.clone(),
                        _ => panic!("can't index ty: {:?}", ty),
                    };
                    // FIXME bounds check?
                    let layout = self.ty_layout(ty.clone());
                    let ptr_typ = self.module.isa().pointer_type();
                    let elem_size =
                        self.builder.ins().iconst(ptr_typ, layout.size.bytes_usize() as i64);
                    let idx =
                        self.translate_copy_local_with_projection(*idx, &[]).0.assert_primitive().0;
                    let idx_offset = self.builder.ins().imul(idx, elem_size);
                    let addr = self.builder.ins().iadd(addr, idx_offset);
                    kind = PlaceKind::Mem(addr, 0);
                }
                ProjectionElem::Field(Either::Right(tuple_idx)) => {
                    let idx = tuple_idx.index as usize;
                    let layout = self.ty_layout(ty.clone());
                    ty = ty.as_tuple().unwrap().at(Interner, idx).assert_ty_ref(Interner).clone();
                    match kind {
                        PlaceKind::Variable(var) => {
                            assert_eq!(0, idx);
                            kind = PlaceKind::Variable(var);
                        }
                        PlaceKind::VariablePair(var1, var2) => {
                            assert!(idx < 2);
                            kind = PlaceKind::Variable(if idx == 0 { var1 } else { var2 });
                        }
                        PlaceKind::Stack(ss, off) => {
                            let offset = layout.fields.offset(idx).bytes_usize();
                            kind = PlaceKind::Stack(ss, off + offset as i32);
                        }
                        PlaceKind::Mem(addr, off) => {
                            let offset = layout.fields.offset(idx).bytes_usize();
                            kind = PlaceKind::Mem(addr, off + offset as i32);
                        }
                    }
                }
                ProjectionElem::Field(Either::Left(field_id)) => {
                    let layout = self.ty_layout(ty.clone());
                    let layout = match &layout.variants {
                        hir_ty::layout::Variants::Single { .. } => &layout,
                        hir_ty::layout::Variants::Multiple { variants, .. } => {
                            &variants[match field_id.parent {
                                hir_def::VariantId::EnumVariantId(it) => {
                                    RustcEnumVariantIdx(it.lookup(self.db.upcast()).index as usize)
                                }
                                _ => panic!("multiple variants in non-enum"),
                            }]
                        }
                    };
                    let idx = u32::from(field_id.local_id.into_raw()) as usize;
                    let (_, subst) = ty.as_adt().expect("non-adt field access");
                    ty = self.db.field_types(field_id.parent)[field_id.local_id]
                        .clone()
                        .substitute(Interner, subst);
                    let offset = layout.fields.offset(idx).bytes_usize();
                    match kind {
                        PlaceKind::Variable(var) => {
                            assert_eq!(0, offset);
                            kind = PlaceKind::Variable(var);
                        }
                        PlaceKind::VariablePair(var1, var2) => {
                            kind = PlaceKind::Variable(if offset == 0 { var1 } else { var2 });
                        }
                        PlaceKind::Stack(ss, off) => {
                            kind = PlaceKind::Stack(ss, off + offset as i32);
                        }
                        PlaceKind::Mem(addr, off) => {
                            kind = PlaceKind::Mem(addr, off + offset as i32);
                        }
                    }
                }
                ProjectionElem::ClosureField(_) => panic!("unsupported closure field"),
                ProjectionElem::ConstantIndex { .. } => panic!("unsupported constant index"),
                ProjectionElem::Subslice { .. } => panic!("unsupported subslice"),
                ProjectionElem::OpaqueCast(_) => panic!("unsupported opaque cast"),
            }
        }
        (kind, ty)
    }

    fn translate_place_kind_addr(&mut self, kind: PlaceKind) -> Value {
        match kind {
            PlaceKind::Variable(_) => panic!("trying to take addr of variable"),
            PlaceKind::VariablePair(_, _) => panic!("trying to take addr of variable pair"),
            PlaceKind::Stack(ss, off) => {
                self.builder.ins().stack_addr(self.module.isa().pointer_type(), ss, off)
            }
            PlaceKind::Mem(addr, off) => self.builder.ins().iadd_imm(addr, off as i64),
        }
    }

    fn translate_load_pointer_value(&mut self, kind: PlaceKind, typ: Type) -> Value {
        match kind {
            PlaceKind::Variable(var) => self.builder.use_var(var),
            PlaceKind::VariablePair(var1, _) => self.builder.use_var(var1),
            PlaceKind::Stack(ss, off) => self.builder.ins().stack_load(typ, ss, off),
            PlaceKind::Mem(addr, off) => {
                self.builder.ins().load(typ, MemFlags::trusted(), addr, off)
            }
        }
    }
    fn translate_place_store(&mut self, place: &Place, value: ValueKind) {
        let (kind, ty) = self.translate_place_with_ty(place);
        self.translate_place_kind_store_with_offset(kind, ty, 0, value)
    }

    fn translate_place_kind_store(&mut self, kind: PlaceKind, ty: Ty, value: ValueKind) {
        self.translate_place_kind_store_with_offset(kind, ty, 0, value)
    }

    fn translate_place_store_with_offset(
        &mut self,
        place: &Place,
        ty: Ty,
        offset: i32,
        value: ValueKind,
    ) {
        let kind = self.translate_place(place);
        self.translate_place_kind_store_with_offset(kind, ty, offset, value)
    }

    fn translate_place_kind_store_with_offset(
        &mut self,
        kind: PlaceKind,
        ty: Ty,
        offset: i32,
        value: ValueKind,
    ) {
        match kind {
            PlaceKind::Variable(var) => {
                if offset == 0 {
                    match value {
                        ValueKind::Primitive(val, _) => {
                            self.builder.def_var(var, val);
                        }
                        _ => panic!("unsupported value kind for variable store: {:?}", value),
                    }
                } else {
                    panic!("store with nonzero offset in variable");
                }
            }
            PlaceKind::VariablePair(var1, var2) => {
                if offset == 0 {
                    match value {
                        ValueKind::ScalarPair(val1, val2) => {
                            self.builder.def_var(var1, val1);
                            self.builder.def_var(var2, val2);
                        }
                        ValueKind::Primitive(val, _) => {
                            self.builder.def_var(var1, val);
                        }
                        _ => panic!("unsupported value kind for variable pair store: {:?}", value),
                    }
                } else {
                    self.builder.def_var(var2, value.assert_primitive().0);
                }
            }
            PlaceKind::Stack(dest, dest_offset) => match value {
                ValueKind::Primitive(value, _) => {
                    self.builder.ins().stack_store(value, dest, offset + dest_offset);
                }
                ValueKind::ScalarPair(val1, val2) => {
                    let layout = self.ty_layout(ty);
                    let off1 = layout.fields.offset(0).bytes_usize() as i32;
                    let off2 = layout.fields.offset(1).bytes_usize() as i32;
                    self.builder.ins().stack_store(val1, dest, offset + dest_offset + off1);
                    self.builder.ins().stack_store(val2, dest, offset + dest_offset + off2);
                }
                ValueKind::Aggregate { slot, offset: src_offset, size } => {
                    let dest = MemSlot::Stack(dest);
                    self.translate_mem_copy(dest, dest_offset + offset, slot, src_offset, size)
                }
            },
            PlaceKind::Mem(dest, dest_offset) => match value {
                ValueKind::Primitive(value, _) => {
                    self.builder.ins().store(
                        MemFlags::trusted(),
                        value,
                        dest,
                        offset + dest_offset,
                    );
                }
                ValueKind::ScalarPair(_val1, _val2) => {
                    panic!("unsupported mem store of scalar pair")
                }
                ValueKind::Aggregate { slot, offset: src_offset, size } => {
                    let dest = MemSlot::MemAddr(dest);
                    self.translate_mem_copy(dest, dest_offset + offset, slot, src_offset, size)
                }
            },
        }
    }

    fn translate_mem_slot_addr(&mut self, slot: MemSlot, offset: i32) -> Value {
        match slot {
            MemSlot::Stack(ss) => {
                self.builder.ins().stack_addr(self.module.isa().pointer_type(), ss, offset)
            }
            MemSlot::MemAddr(addr) if offset == 0 => addr,
            MemSlot::MemAddr(addr) => {
                let off =
                    self.builder.ins().iconst(self.module.isa().pointer_type(), offset as i64);
                self.builder.ins().iadd(addr, off)
            }
        }
    }

    fn get_variable(&mut self, local: LocalId) -> LocalKind {
        let typ = self.body.locals[local].ty.clone();
        let variable = *self.variables.entry(local).or_insert_with(|| {
            // FIXME error handling here!
            let layout = self
                .db
                .layout_of_ty(typ.clone(), self.env.clone())
                .expect("failed to lay out type");
            if let Abi::Scalar(scalar) = layout.abi {
                let var = Variable::new(local.into_raw().into_u32() as usize * 2);
                let typ = translate_scalar_type(scalar, self.module.isa());
                self.builder.declare_var(var, typ);
                LocalKind::Variable(var)
            } else if let Abi::ScalarPair(scalar1, scalar2) = layout.abi {
                let typ1 = translate_scalar_type(scalar1, self.module.isa());
                let typ2 = translate_scalar_type(scalar2, self.module.isa());
                let var1 = Variable::new(local.into_raw().into_u32() as usize * 2);
                let var2 = Variable::new(local.into_raw().into_u32() as usize * 2 + 1);
                self.builder.declare_var(var1, typ1);
                self.builder.declare_var(var2, typ2);
                LocalKind::VariablePair(var1, var2)
            } else {
                if !layout.is_sized() {
                    panic!("unsized type in local");
                }
                let size = layout.size.bytes_usize();
                let slot = self.builder.create_sized_stack_slot(StackSlotData {
                    kind: codegen::ir::StackSlotKind::ExplicitSlot,
                    size: size as u32,
                    align_shift: layout.align.pref.bytes().ilog2() as u8,
                });
                LocalKind::Stack(slot)
            }
        });
        variable
    }

    fn spill_to_stack(&mut self, local: LocalId) -> StackSlot {
        let current = self.get_variable(local);
        match current {
            LocalKind::Variable(var) => {
                let typ = self.body.locals[local].ty.clone();
                let layout = self
                    .db
                    .layout_of_ty(typ.clone(), self.env.clone())
                    .expect("failed to lay out type");
                let slot = self.builder.create_sized_stack_slot(StackSlotData {
                    kind: codegen::ir::StackSlotKind::ExplicitSlot,
                    size: layout.size.bytes_usize() as u32,
                    align_shift: layout.align.pref.bytes().ilog2() as u8,
                });
                let val = self.builder.use_var(var);
                self.builder.ins().stack_store(val, slot, 0);
                self.variables[local] = LocalKind::Stack(slot);
                slot
            }
            LocalKind::VariablePair(_var1, _var2) => {
                panic!("unsupported stack spill of variable pair")
            }
            LocalKind::Stack(slot) => slot,
        }
    }

    fn translate_operand(&mut self, operand: &Operand) -> ValueKind {
        self.translate_operand_with_ty(operand).0
    }

    fn translate_operand_with_ty(&mut self, operand: &Operand) -> (ValueKind, Ty) {
        match operand {
            Operand::Constant(konst) => self.translate_const(konst),
            Operand::Copy(place) | Operand::Move(place) => self.translate_place_copy(place),
            Operand::Static(_static_id) => panic!("unsupported static"),
        }
    }

    fn translate_const(&mut self, konst: &chalk_ir::Const<Interner>) -> (ValueKind, Ty) {
        let ty = konst.data(Interner).ty.clone();
        let chalk_ir::ConstValue::Concrete(c) = &konst.data(Interner).value else {
            panic!("evaluating non concrete constant");
        };
        let hir_ty::ConstScalar::Bytes(bytes, mm) = &c.interned else {
            panic!("bad const: {:?}", c.interned)
        };
        let layout = self.ty_layout(ty.clone());
        let memory_addr = match mm {
            MemoryMap::Empty => None,
            MemoryMap::Simple(bytes) => {
                let data = self
                    .module
                    .declare_anonymous_data(false, false)
                    .expect("failed to create data");
                let mut desc = DataDescription::new();
                desc.define(bytes.clone());
                self.module.define_data(data, &desc).expect("failed to define data");
                let global = self.module.declare_data_in_func(data, &mut self.builder.func);
                let ptr_type = self.module.isa().pointer_type();
                let addr = self.builder.ins().global_value(ptr_type, global);
                Some(addr)
            }
            _ => panic!("unsupported memory map in const: {:?}", mm),
        };
        let is_ref = ty.as_reference_or_ptr().is_some();
        let val = match layout.abi {
            Abi::Uninhabited => unreachable!(),
            Abi::Scalar(scalar) => {
                let typ = translate_scalar_type(scalar, self.module.isa());
                let signed = scalar_signedness(scalar);
                let val = bytes_to_imm64(bytes);
                let val = if is_ref {
                    let addr = memory_addr.expect("ref const without memory");
                    self.builder.ins().iadd_imm(addr, val)
                } else {
                    self.builder.ins().iconst(typ, val)
                };
                ValueKind::Primitive(val, signed)
            }
            Abi::ScalarPair(s1, s2) => {
                let typ1 = translate_scalar_type(s1, self.module.isa());
                let typ2 = translate_scalar_type(s2, self.module.isa());
                let val1 = bytes_to_imm64(&bytes[..typ1.bytes() as usize]);
                let val1 = if is_ref {
                    let addr = memory_addr.expect("ref const without memory");
                    self.builder.ins().iadd_imm(addr, val1)
                } else {
                    self.builder.ins().iconst(typ1, val1)
                };
                let val2 = self
                    .builder
                    .ins()
                    .iconst(typ2, bytes_to_imm64(&bytes[typ1.bytes() as usize..]));
                ValueKind::ScalarPair(val1, val2)
            }
            Abi::Aggregate { sized: true } => {
                let data = self
                    .module
                    .declare_anonymous_data(false, false)
                    .expect("failed to create data");
                let mut desc = DataDescription::new();
                desc.define(bytes.clone());
                self.module.define_data(data, &desc).expect("failed to define data");
                let global = self.module.declare_data_in_func(data, &mut self.builder.func);
                let ptr_type = self.module.isa().pointer_type();
                let addr = self.builder.ins().global_value(ptr_type, global);
                let size = layout.size.bytes_usize() as i32;
                ValueKind::Aggregate { slot: MemSlot::MemAddr(addr), offset: 0, size }
            }
            _ => panic!("unsupported abi for const: {:?}", layout.abi),
        };
        (val, ty)
    }

    fn translate_place_copy(&mut self, place: &Place) -> (ValueKind, Ty) {
        let projection = place.projection.lookup(&self.body.projection_store);
        let local = place.local;
        self.translate_copy_local_with_projection(local, projection)
    }

    fn translate_copy_local_with_projection(
        &mut self,
        local: LocalId,
        projection: &[ProjectionElem<LocalId, Ty>],
    ) -> (ValueKind, Ty) {
        let (place_kind, ty) = self.translate_local_with_projection(local, projection);
        let layout = self.ty_layout(ty.clone());
        let abi = layout.abi;
        let val = match place_kind {
            PlaceKind::Variable(var) => {
                let var_val = self.builder.use_var(var);
                match abi {
                    Abi::Scalar(scalar) => ValueKind::Primitive(var_val, scalar_signedness(scalar)),
                    _ => unreachable!("non-scalar in variable: {:?}", abi),
                }
            }
            PlaceKind::VariablePair(var1, var2) => {
                let var1_val = self.builder.use_var(var1);
                let var2_val = self.builder.use_var(var2);
                assert!(matches!(abi, Abi::ScalarPair(..)));
                ValueKind::ScalarPair(var1_val, var2_val)
            }
            PlaceKind::Stack(slot, off) => match abi {
                Abi::Scalar(scalar) => {
                    let loaded_val = self.builder.ins().stack_load(
                        translate_scalar_type(scalar, self.module.isa()),
                        slot,
                        off,
                    );
                    ValueKind::Primitive(loaded_val, scalar_signedness(scalar))
                }
                Abi::Aggregate { sized: true } => ValueKind::Aggregate {
                    slot: MemSlot::Stack(slot),
                    offset: off,
                    size: layout.size.bytes_usize() as i32,
                },
                _ => panic!("unsupported abi for var copy from stack: {:?}", abi),
            },
            PlaceKind::Mem(addr, off) => match abi {
                Abi::Scalar(scalar) => {
                    let loaded_val = self.builder.ins().load(
                        translate_scalar_type(scalar, self.module.isa()),
                        MemFlags::trusted(),
                        addr,
                        off,
                    );
                    ValueKind::Primitive(loaded_val, scalar_signedness(scalar))
                }
                Abi::Aggregate { sized: true } => ValueKind::Aggregate {
                    slot: MemSlot::MemAddr(addr),
                    offset: off,
                    size: layout.size.bytes_usize() as i32,
                },
                _ => panic!("unsupported abi for var copy from mem: {:?}", abi),
            },
        };
        (val, ty)
    }

    fn translate_checked_binop(
        &mut self,
        binop: &BinOp,
        left: &Operand,
        right: &Operand,
    ) -> ValueKind {
        let (left, signed1) = self.translate_operand(left).assert_primitive();
        let (right, signed2) = self.translate_operand(right).assert_primitive();
        assert_eq!(signed1, signed2);
        if !signed1 {
            panic!("unsupported unsigned operation");
        }
        let result = match binop {
            // FIXME checked?
            BinOp::Add => self.builder.ins().iadd(left, right),
            BinOp::Sub => self.builder.ins().isub(left, right),
            BinOp::Mul => self.builder.ins().imul(left, right),
            // FIXME handle unsigned
            BinOp::Div => self.builder.ins().sdiv(left, right),
            BinOp::Rem => self.builder.ins().srem(left, right),

            BinOp::Eq => self.builder.ins().icmp(IntCC::Equal, left, right),
            BinOp::Ne => self.builder.ins().icmp(IntCC::NotEqual, left, right),
            // FIXME handle unsigned
            BinOp::Lt => self.builder.ins().icmp(IntCC::SignedLessThan, left, right),
            BinOp::Le => self.builder.ins().icmp(IntCC::SignedLessThanOrEqual, left, right),
            BinOp::Gt => self.builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, left, right),
            BinOp::Ge => self.builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, left, right),
            _ => panic!("unsupported binop: {:?}", binop),
        };
        ValueKind::Primitive(result, signed1)
    }

    fn ty_layout(&self, ty: Ty) -> Arc<Layout> {
        // FIXME error handling?
        self.db.layout_of_ty(ty, self.env.clone()).expect("failed layout")
    }

    fn translate_mem_copy(
        &mut self,
        dest: MemSlot,
        dest_offset: i32,
        slot: MemSlot,
        offset: i32,
        size: i32,
    ) {
        let config = self.module.target_config();
        let dest = self.translate_mem_slot_addr(dest, dest_offset);
        let src = self.translate_mem_slot_addr(slot, offset);
        self.builder.emit_small_memory_copy(
            config,
            dest,
            src,
            size as u64,
            3, // FIXME align
            3,
            true,
            MemFlags::trusted(),
        )
    }

    fn translate_neg(&mut self, op: &Operand) -> ValueKind {
        let (value, ty) = self.translate_operand_with_ty(op);
        match ty.kind(Interner) {
            TyKind::Scalar(hir_ty::Scalar::Int(_)) => {
                let result = self.builder.ins().ineg(value.assert_primitive().0);
                ValueKind::Primitive(result, true)
            }
            TyKind::Scalar(hir_ty::Scalar::Float(_)) => {
                let result = self.builder.ins().fneg(value.assert_primitive().0);
                ValueKind::Primitive(result, true)
            }
            _ => unreachable!("bad type for negation: {:?}", ty),
        }
    }

    fn translate_not(&mut self, op: &Operand) -> ValueKind {
        let (value, ty) = self.translate_operand_with_ty(op);
        match ty.kind(Interner) {
            TyKind::Scalar(hir_ty::Scalar::Int(_) | hir_ty::Scalar::Uint(_)) => {
                let (value, signed) = value.assert_primitive();
                let result = self.builder.ins().bnot(value);
                ValueKind::Primitive(result, signed)
            }
            TyKind::Scalar(hir_ty::Scalar::Bool) => {
                let value = value.assert_primitive().0;
                let result = self.builder.ins().bxor_imm(value, 1);
                ValueKind::Primitive(result, false)
            }
            _ => unreachable!("bad type for not: {:?}", ty),
        }
    }

    fn translate_rust_intrinsic_call(
        &mut self,
        func_id: FunctionId,
        subst: Substitution,
        args: &[Value],
        destination: &Place,
    ) {
        // FIXME might want to share more/less code with the normal rust call code
        let function_data = self.db.function_data(func_id);
        let func_name = function_data.name.as_str();
        match func_name {
            "transmute" => self.translate_transmute(subst, args, destination),
            _ => panic!("unsupported intrinsic: {:?}", func_name),
        }
    }

    fn translate_transmute(&mut self, _subst: Substitution, args: &[Value], destination: &Place) {
        // FIXME check validity?
        self.store_func_call_return(args, destination);
    }

    fn store_tuple(&mut self, tuple_ty: Ty, place: &Place, operands: &[Operand]) {
        let layout = self.ty_layout(tuple_ty.clone());
        let tys: Vec<_> = tuple_ty
            .as_tuple()
            .expect("no tuple")
            .iter(Interner)
            .map(|g| g.assert_ty_ref(Interner).clone())
            .collect();
        self.store_tuple_layout(&layout, &tys, place, operands);
    }

    fn store_tuple_layout(
        &mut self,
        layout: &Layout,
        tys: &[Ty],
        place: &Place,
        operands: &[Operand],
    ) {
        for (i, op) in operands.iter().enumerate() {
            let val = self.translate_operand(op);
            let field_offset = layout.fields.offset(i);
            self.translate_place_store_with_offset(
                place,
                tys[i].clone(),
                field_offset.bytes_usize() as i32,
                val,
            );
        }
    }

    fn translate_load_discriminant(&mut self, place: &Place) -> ValueKind {
        let (kind, ty) = self.translate_place_with_ty(place);
        let &TyKind::Adt(chalk_ir::AdtId(hir_def::AdtId::EnumId(e)), _) = ty.kind(Interner) else {
            panic!("load discriminant of non-enum")
        };
        let layout = self.ty_layout(ty.clone());
        let Variants::Multiple { tag, tag_encoding, tag_field, .. } = &layout.variants else {
            panic!("load discriminant of non-multi variant")
        };
        let tag_typ = translate_scalar_type(*tag, self.module.isa());
        let tag_offset = layout.fields.offset(*tag_field).bytes_usize() as i32;
        let tag = match kind {
            PlaceKind::Variable(var) => {
                assert!(tag_offset == 0);
                self.builder.use_var(var)
            }
            PlaceKind::VariablePair(var1, _) => {
                assert!(tag_offset == 0);
                self.builder.use_var(var1)
            }
            PlaceKind::Stack(ss, off) => {
                self.builder.ins().stack_load(tag_typ, ss, off + tag_offset)
            }
            PlaceKind::Mem(mem, off) => {
                self.builder.ins().load(tag_typ, MemFlags::trusted(), mem, off + tag_offset)
            }
        };
        let mut tag = match tag_encoding {
            TagEncoding::Direct => tag,
            TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
                let min_tag = niche_start;
                let max_tag = niche_start
                    .wrapping_add((niche_variants.end().0 - niche_variants.start().0) as u128);
                let untagged_variant_discr = self
                    .db
                    .const_eval_discriminant(self.db.enum_data(e).variants[untagged_variant.0].0)
                    .expect("failed to eval discriminant");
                let untagged_variant_discr =
                    self.builder.ins().iconst(tag_typ, untagged_variant_discr as i64);
                let smaller =
                    self.builder.ins().icmp_imm(IntCC::UnsignedLessThan, tag, *min_tag as i64);
                let larger =
                    self.builder.ins().icmp_imm(IntCC::UnsignedGreaterThan, tag, max_tag as i64);
                let is_untagged = self.builder.ins().bor(smaller, larger);
                self.builder.ins().select(is_untagged, untagged_variant_discr, tag)
            }
        };
        tag = self.builder.ins().uextend(types::I128, tag);
        ValueKind::Primitive(tag, false)
    }

    fn store_tag_and_get_variant_layout<'b>(
        &mut self,
        variant_id: VariantId,
        layout: &'b Layout,
        place: &Place,
    ) -> &'b Layout {
        match &layout.variants {
            hir_def::layout::Variants::Single { .. } => &layout,
            hir_def::layout::Variants::Multiple { tag, tag_encoding, tag_field, variants } => {
                let hir_def::VariantId::EnumVariantId(enum_variant_id) = variant_id else {
                    panic!("multiple variants in non-enum")
                };
                let variant_idx = enum_variant_id.lookup(self.db.upcast()).index as usize;
                let rustc_enum_variant_idx = RustcEnumVariantIdx(variant_idx);
                let discr_typ = translate_scalar_type(*tag, self.module.isa());
                // FIXME error handling
                let mut discriminant = self
                    .db
                    .const_eval_discriminant(enum_variant_id)
                    .expect("failed to eval enum discriminant");
                let have_tag = match tag_encoding {
                    TagEncoding::Direct => true,
                    TagEncoding::Niche { untagged_variant, niche_variants: _, niche_start } => {
                        if *untagged_variant == rustc_enum_variant_idx {
                            false
                        } else {
                            discriminant = (variants
                                .iter_enumerated()
                                .filter(|(it, _)| it != untagged_variant)
                                .position(|(it, _)| it == rustc_enum_variant_idx)
                                .unwrap() as i128)
                                .wrapping_add(*niche_start as i128);
                            true
                        }
                    }
                };
                if have_tag {
                    let field_offset = layout.fields.offset(*tag_field);
                    let discriminant = ValueKind::Primitive(
                        self.builder.ins().iconst(discr_typ, discriminant as i64),
                        false,
                    );
                    self.translate_place_store_with_offset(
                        place,
                        // HACK the type doesn't really matter here
                        TyKind::Scalar(hir_ty::Scalar::Uint(chalk_ir::UintTy::U128))
                            .intern(Interner),
                        field_offset.bytes_usize() as i32,
                        discriminant,
                    );
                }
                &variants[rustc_enum_variant_idx]
            }
        }
    }
}

fn bytes_to_imm64(bytes: &[u8]) -> Imm64 {
    let mut data: [u8; 8] = [0; 8];
    data[0..bytes.len()].copy_from_slice(&bytes);
    Imm64::new(i64::from_le_bytes(data))
}

impl ValueKind {
    fn assert_primitive(&self) -> (Value, bool) {
        match *self {
            ValueKind::Primitive(val, signedness) => (val, signedness),
            _ => panic!("non-primitive value"),
        }
    }
}

#[salsa::query_group(CodegenDatabaseStorage)]
pub trait CodegenDatabase: HirDatabase + Upcast<dyn HirDatabase> {
    #[salsa::interned]
    fn intern_mono_function(&self, mf: MonoFunction) -> MonoFunctionId;
}

#[test]
fn codegen_database_is_object_safe() {
    fn _assert_object_safe(_: &dyn CodegenDatabase) {}
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct MonoFunction {
    func: FunctionId,
    subst: Substitution,
}
impl InternValueTrivial for MonoFunction {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct MonoFunctionId(salsa::InternId);
impl_intern_key!(MonoFunctionId);

fn translate_signature(
    sig: &hir_ty::CallableSig,
    isa: &dyn TargetIsa,
    db: &dyn CodegenDatabase,
    env: &Arc<TraitEnvironment>,
) -> Signature {
    let call_conv = match sig.abi() {
        hir_ty::FnAbi::Rust => CallConv::Fast,
        _ => panic!("unsupported ABI: {:?}", sig.abi()),
    };
    let mut signature = Signature::new(call_conv);
    signature.params.extend(
        sig.params()
            .iter()
            .flat_map(|ty| {
                let layout = db.layout_of_ty(ty.clone(), env.clone()).expect("failed layout");
                match layout.abi {
                    Abi::Uninhabited => SmallVec::new(),
                    Abi::Scalar(scalar) => SmallVec::from_buf([translate_scalar_type(scalar, isa)]),
                    Abi::ScalarPair(sc1, sc2) => SmallVec::from_vec(vec![
                        translate_scalar_type(sc1, isa),
                        translate_scalar_type(sc2, isa),
                    ]),
                    Abi::Aggregate { sized: true } if layout.size.bytes() == 0 => SmallVec::new(),
                    Abi::Aggregate { sized: true } => SmallVec::from_buf([isa.pointer_type()]),
                    _ => panic!("unsupported abi in function param: {:?}", layout.abi),
                }
            })
            .map(AbiParam::new),
    );
    let layout = db.layout_of_ty(sig.ret().clone(), env.clone()).expect("failed layout");
    signature.returns.extend(
        match layout.abi {
            Abi::Uninhabited => SmallVec::new(),
            Abi::Scalar(scalar) => SmallVec::from_buf([translate_scalar_type(scalar, isa)]),
            Abi::ScalarPair(sc1, sc2) => SmallVec::from_vec(vec![
                translate_scalar_type(sc1, isa),
                translate_scalar_type(sc2, isa),
            ]),
            Abi::Aggregate { sized: true } if layout.size.bytes() == 0 => SmallVec::new(),
            Abi::Aggregate { sized: true } => SmallVec::from_buf([isa.pointer_type()]),
            _ => panic!("unsupported abi in function return: {:?}", layout.abi),
        }
        .into_iter()
        .map(AbiParam::new),
    );
    signature
}

fn translate_scalar_type(scalar: Scalar, isa: &dyn TargetIsa) -> Type {
    use hir_def::layout::{AddressSpace, Float, Primitive};
    let (Scalar::Initialized { value, valid_range: _ } | Scalar::Union { value }) = scalar;
    match value {
        Primitive::Int(int, _) => {
            Type::int_with_byte_size(int.size().bytes_usize() as u16).unwrap()
        }
        Primitive::Float(Float::F16) => types::F16,
        Primitive::Float(Float::F32) => types::F32,
        Primitive::Float(Float::F64) => types::F64,
        Primitive::Float(Float::F128) => types::F128,
        Primitive::Pointer(AddressSpace::DATA) => isa.pointer_type(),
        Primitive::Pointer(_) => panic!("unsupported address space"),
    }
}

fn scalar_signedness(scalar: Scalar) -> bool {
    use hir_def::layout::Primitive;
    let (Scalar::Initialized { value, valid_range: _ } | Scalar::Union { value }) = scalar;
    match value {
        Primitive::Int(_, signedness) => signedness,
        Primitive::Float(_) | Primitive::Pointer(_) => false,
    }
}

fn return_slot() -> LocalId {
    LocalId::from_raw(la_arena::RawIdx::from(0))
}

fn get_int_ty(ty: &Ty, isa: &dyn TargetIsa) -> Option<(u8, bool)> {
    Some(match ty.kind(Interner) {
        TyKind::Scalar(hir_ty::Scalar::Int(int_ty)) => (
            match int_ty {
                chalk_ir::IntTy::Isize => isa.pointer_bytes(),
                chalk_ir::IntTy::I8 => 1,
                chalk_ir::IntTy::I16 => 2,
                chalk_ir::IntTy::I32 => 4,
                chalk_ir::IntTy::I64 => 8,
                chalk_ir::IntTy::I128 => 16,
            },
            true,
        ),
        TyKind::Scalar(hir_ty::Scalar::Uint(uint_ty)) => (
            match uint_ty {
                chalk_ir::UintTy::Usize => isa.pointer_bytes(),
                chalk_ir::UintTy::U8 => 1,
                chalk_ir::UintTy::U16 => 2,
                chalk_ir::UintTy::U32 => 4,
                chalk_ir::UintTy::U64 => 8,
                chalk_ir::UintTy::U128 => 16,
            },
            true,
        ),
        _ => return None,
    })
}
