#[cfg(test)]
mod test_db;
#[cfg(test)]
mod tests;

use std::{
    panic::{catch_unwind, AssertUnwindSafe},
    sync::Mutex,
};

use anyhow::{anyhow, Context};
use base_db::salsa::InternKey;
use cranelift::{
    codegen::{self, ir::StackSlot},
    frontend::Switch,
    prelude::{
        isa::{CallConv, TargetIsa},
        settings, types, AbiParam, Block, Configurable, EntityRef, FunctionBuilder,
        FunctionBuilderContext, InstBuilder, IntCC, MemFlags, Signature, StackSlotData, Type,
        Value, Variable,
    },
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, FuncId, Module};
use hir_def::{
    layout::{Abi, Scalar},
    FunctionId,
};
use hir_ty::{
    db::HirDatabase,
    layout::Layout,
    mir::{
        BasicBlockId, BinOp, CastKind, LocalId, MirBody, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind,
    },
    Interner, Substitution, TraitEnvironment, Ty, TyExt, TyKind,
};
use la_arena::ArenaMap;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use triomphe::Arc;

#[derive(Clone)]
pub struct JitEngine<'a> {
    jit: Arc<Mutex<Jit>>,
    db: &'a dyn HirDatabase,
}

extern "C" fn ensure_function(engine: &JitEngine, func_id: u32) -> *const u8 {
    let jit = engine.jit.clone();
    let mut jit = jit.lock().unwrap();
    let func_id = FunctionId::from_intern_id(func_id.into());
    let code = catch_unwind(AssertUnwindSafe(|| jit.compile(engine.db, func_id, engine).unwrap()))
        .unwrap_or_else(|err| {
            eprintln!("failed to compile function {}: {:?}", func_id.as_intern_id().as_u32(), err);
            std::process::abort();
        });
    code
}

impl<'a> JitEngine<'a> {
    pub fn new(db: &'a dyn HirDatabase) -> JitEngine {
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

    compiled_functions: FxHashMap<FunctionId, FuncId>,
    shims: FxHashMap<FunctionId, FuncId>,
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
        // let mut signature = Signature::new(module.isa().default_call_conv());
        // signature.params.push(AbiParam::new(module.isa().pointer_type()));
        // signature.params.push(AbiParam::new(types::I32));
        // signature.returns.push(AbiParam::new(module.isa().pointer_type()));
        // module.declare_function("ensure_function", Linkage::Import, &signature).unwrap();
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
        db: &dyn HirDatabase,
        func_id: FunctionId,
        jit_engine: &JitEngine,
    ) -> Result<*const u8, anyhow::Error> {
        if let Some(f) = self.compiled_functions.get(&func_id) {
            // FIXME check for changes to the function since the last compilation
            // FIXME also cache error?
            return Ok(self.module.get_finalized_function(*f));
        }

        let data = db.function_data(func_id);
        eprintln!(
            "Compiling function {} ({})",
            func_id.as_intern_id().as_u32(),
            data.name.as_str()
        );
        let (sig, binders) =
            db.callable_item_signature(func_id.into()).into_value_and_skipped_binders();
        if !binders.is_empty(Interner) {
            panic!("unsupported generic func");
        }

        self.ctx.func.signature = translate_signature(&sig, self.module.isa());

        let builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        let env = db.trait_environment(func_id.into());
        let body = db
            .monomorphized_mir_body(func_id.into(), Substitution::empty(Interner), env.clone())
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
        translator.compile_function_init();

        translator.compile_all_blocks();

        translator.builder.seal_all_blocks(); // FIXME do this better?
        translator.builder.finalize();

        let id = self
            .module
            // FIXME declare with name and linkage?
            .declare_anonymous_function(&self.ctx.func.signature)
            .context("failed to declare function")?;

        self.compiled_functions.insert(func_id, id);

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
    db: &'a dyn HirDatabase,
    body: &'a MirBody,
    variables: ArenaMap<LocalId, LocalKind>,
    blocks: ArenaMap<BasicBlockId, Block>,
    builder: FunctionBuilder<'a>,
    module: &'a mut JITModule,
    shims: &'a mut FxHashMap<FunctionId, FuncId>,
    env: Arc<TraitEnvironment>,
    engine: &'a JitEngine<'a>,
}

#[derive(Clone, Copy, Debug)]
enum LocalKind {
    Variable(Variable),
    Stack(StackSlot),
}

#[derive(Clone, Copy, Debug)]
enum PlaceKind {
    Variable(Variable),
    Stack(StackSlot, i32),
    Mem(Value, i32),
}

#[derive(Clone, Copy, Debug)]
enum ValueKind {
    Primitive(Value, bool),
    Aggregate { slot: MemSlot, offset: i32, size: i32 },
}

#[derive(Clone, Copy, Debug)]
enum MemSlot {
    Stack(StackSlot),
    MemAddr(Value),
}

impl<'a> FunctionTranslator<'a> {
    fn get_shim(&mut self, func: FunctionId) -> FuncId {
        if let Some(shim) = self.shims.get(&func) {
            return *shim;
        }

        let (sig, binders) =
            self.db.callable_item_signature(func.into()).into_value_and_skipped_binders();
        if !binders.is_empty(Interner) {
            panic!("unsupported generic func");
        }

        let mut ctx = self.module.make_context(); // FIXME share (extract ShimCompiler?)
        ctx.func.signature = translate_signature(&sig, self.module.isa());

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
        let arg2 = builder.ins().iconst(types::I32, func.as_intern_id().as_u32() as i64);
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
        self.builder.switch_to_block(block);
        let param_values = self.builder.block_params(block).to_vec();
        for (param, val) in self.body.param_locals.iter().copied().zip(param_values) {
            self.translate_local_store(param, val);
        }
    }

    fn compile_mir_block(&mut self, block_id: BasicBlockId) {
        self.builder.switch_to_block(self.blocks[block_id]);
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

                let args: Vec<_> = args
                    .iter()
                    .map(|a| self.translate_operand(a))
                    .map(|v| match v {
                        ValueKind::Primitive(val, _) => val,
                        _ => panic!("unsupported value in function call: {:?}", v),
                    })
                    .collect();
                let static_func_id = match func {
                    Operand::Constant(konst) => match konst.data(Interner).ty.kind(Interner) {
                        TyKind::FnDef(func_id, subst) => {
                            if !subst.is_empty(Interner) {
                                panic!("unsupported generic function call")
                            }
                            let callable_def =
                                self.db.lookup_intern_callable_def((*func_id).into());
                            match callable_def {
                                hir_def::CallableDefId::FunctionId(func_id) => Some(func_id),
                                _ => {
                                    panic!("unsupported struct/enum constructor");
                                }
                            }
                        }
                        _ => None,
                    },
                    _ => None,
                };
                // FIXME order of operations? first args or first func?

                if let Some(func_id) = static_func_id {
                    let shim = self.get_shim(func_id);
                    let func_ref = self.module.declare_func_in_func(shim, &mut self.builder.func);
                    let call = self.builder.ins().call(func_ref, &args);
                    match self.builder.inst_results(call).len() {
                        1 => {
                            let result =
                                ValueKind::Primitive(self.builder.inst_results(call)[0], false);
                            self.translate_place_store(destination, result);
                        }
                        0 => {}
                        _ => {
                            panic!("unsupported multiple returns");
                        }
                    }
                    if let Some(target) = target {
                        self.builder.ins().jump(self.blocks[*target], &[]);
                    }
                } else {
                    let _func = self.translate_operand(func);
                    panic!("unsupported indirect call");
                }
            }
            _ => panic!("unsupported terminator kind: {:?}", terminator.kind),
        }
    }

    fn emit_return(&mut self) {
        // FIXME use abi instead
        let types = translate_type_for_calls(
            self.body.locals[return_slot()].ty.clone(),
            self.module.isa(),
            "return",
        );
        let returns = match types.len() {
            0 => Vec::new(),
            1 => [self.translate_local_access(return_slot())].to_vec(),
            _ => panic!("unsupported multiple returns"),
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
            Rvalue::Ref(_, place) => {
                let projection = place.projection.lookup(&self.body.projection_store);
                match projection {
                    [] => {
                        // FIXME spilling on demand like this won't work properly, I think?
                        let stack_slot = self.spill_to_stack(place.local);
                        let typ = self.module.isa().pointer_type();
                        let addr = self.builder.ins().stack_addr(typ, stack_slot, 0);
                        ValueKind::Primitive(addr, false)
                    }
                    [rest @ .., ProjectionElem::Deref] => {
                        self.translate_copy_local_with_projection(place.local, rest)
                    }
                    _ => {
                        panic!("unsupported projection in rvalue: {:?}", projection);
                    }
                }
            }
            Rvalue::Cast(kind, operand, _ty) => {
                use hir_ty::PointerCast::*;
                let value = self.translate_operand(operand);
                match kind {
                    CastKind::Pointer(UnsafeFnPointer | MutToConstPointer | ArrayToPointer) => {
                        // nothing to do here
                        value
                    }
                    _ => panic!("unsupported cast: {:?}", kind),
                }
            }
            Rvalue::Aggregate(kind, operands) => {
                use hir_ty::mir::AggregateKind::*;
                match kind {
                    Array(elem_ty) => {
                        let typ = translate_type(elem_ty.clone(), self.module.isa(), "array elem");
                        for (i, op) in operands.iter().enumerate() {
                            let val = self.translate_operand(op);
                            self.translate_place_store_with_offset(
                                place,
                                i as i32 * typ.bytes() as i32,
                                val,
                            );
                        }
                        return;
                    }
                    _ => panic!("unsupported aggregate: {:?}", kind),
                }
            }
            _ => panic!("unsupported rvalue: {:?}", rvalue),
        };
        self.translate_place_store(place, value)
    }

    fn translate_place(&mut self, place: &Place) -> PlaceKind {
        let projection = place.projection.lookup(&self.body.projection_store);
        let local = place.local;
        self.translate_local_with_projection(local, projection).0
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
            LocalKind::Stack(ss) => PlaceKind::Stack(ss, 0),
        };
        for elem in projection {
            match elem {
                ProjectionElem::Deref => {
                    ty = ty.as_reference_or_ptr().expect("non-ptr deref target").0.clone();
                    let addr =
                        self.translate_place_kind_access(kind, self.module.isa().pointer_type());
                    kind = PlaceKind::Mem(addr, 0);
                }
                ProjectionElem::Index(idx) => {
                    let addr = self.translate_place_kind_addr(kind);
                    ty = match ty.kind(Interner) {
                        TyKind::Array(elem_ty, _size) => elem_ty.clone(),
                        _ => panic!("unsupported ty for indexing: {:?}", ty),
                    };
                    // FIXME bounds check?
                    let layout = self.ty_layout(ty.clone());
                    let ptr_typ = self.module.isa().pointer_type();
                    let elem_size =
                        self.builder.ins().iconst(ptr_typ, layout.size.bytes_usize() as i64);
                    let idx = self.translate_local_access(*idx);
                    let idx_offset = self.builder.ins().imul(idx, elem_size);
                    let addr = self.builder.ins().iadd(addr, idx_offset);
                    kind = PlaceKind::Mem(addr, 0);
                }
                _ => panic!("unsupported projection elem in place: {:?}", elem),
            }
        }
        (kind, ty)
    }

    fn translate_place_kind_addr(&mut self, kind: PlaceKind) -> Value {
        match kind {
            PlaceKind::Variable(_) => panic!("trying to take addr of variable"),
            PlaceKind::Stack(ss, off) => {
                let slot_addr =
                    self.builder.ins().stack_addr(self.module.isa().pointer_type(), ss, off);
                slot_addr
            }
            PlaceKind::Mem(addr, off) => {
                let off = self.builder.ins().iconst(self.module.isa().pointer_type(), off as i64);
                self.builder.ins().iadd(addr, off)
            }
        }
    }

    fn translate_place_kind_access(&mut self, kind: PlaceKind, typ: Type) -> Value {
        match kind {
            PlaceKind::Variable(var) => self.builder.use_var(var),
            PlaceKind::Stack(ss, off) => self.builder.ins().stack_load(typ, ss, off),
            PlaceKind::Mem(addr, off) => {
                self.builder.ins().load(typ, MemFlags::trusted(), addr, off)
            }
        }
    }

    fn translate_place_store(&mut self, place: &Place, value: ValueKind) {
        match self.translate_place(place) {
            PlaceKind::Variable(var) => match value {
                ValueKind::Primitive(val, _) => {
                    self.builder.def_var(var, val);
                }
                _ => panic!("unsupported value kind for variable store: {:?}", value),
            },
            PlaceKind::Stack(dest, dest_offset) => match value {
                ValueKind::Primitive(val, _) => {
                    self.builder.ins().stack_store(val, dest, dest_offset);
                }
                ValueKind::Aggregate { slot, offset, size } => {
                    let dest_slot = MemSlot::Stack(dest);
                    self.translate_mem_copy(dest_slot, dest_offset, slot, offset, size)
                }
            },
            PlaceKind::Mem(dest, dest_offset) => match value {
                ValueKind::Primitive(val, _) => {
                    self.builder.ins().store(MemFlags::trusted(), val, dest, dest_offset);
                }
                ValueKind::Aggregate { slot, offset: src_offset, size } => {
                    let dest = MemSlot::MemAddr(dest);
                    self.translate_mem_copy(dest, dest_offset, slot, src_offset, size)
                }
            },
        }
    }

    fn translate_place_store_with_offset(&mut self, place: &Place, offset: i32, value: ValueKind) {
        match self.translate_place(place) {
            PlaceKind::Variable(_var) => panic!("unsupported store with offset in variable"),
            PlaceKind::Stack(dest, dest_offset) => match value {
                ValueKind::Primitive(value, _) => {
                    self.builder.ins().stack_store(value, dest, offset + dest_offset);
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
                let var = Variable::new(local.into_raw().into_u32() as usize);
                let typ = translate_scalar_type(scalar, self.module.isa());
                self.builder.declare_var(var, typ);
                LocalKind::Variable(var)
            } else {
                if !layout.is_sized() {
                    panic!("unsupported unsized type in local");
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
            LocalKind::Stack(slot) => slot,
        }
    }

    fn translate_operand(&mut self, operand: &Operand) -> ValueKind {
        match operand {
            Operand::Constant(konst) => self.translate_const(konst),
            Operand::Copy(place) | Operand::Move(place) => self.translate_place_copy(place),
            _ => panic!("unsupported operand: {:?}", operand),
        }
    }

    fn translate_const(&mut self, konst: &chalk_ir::Const<Interner>) -> ValueKind {
        let ty = konst.data(Interner).ty.clone();
        let chalk_ir::ConstValue::Concrete(c) = &konst.data(Interner).value else {
            panic!("evaluating non concrete constant");
        };
        match &c.interned {
            hir_ty::ConstScalar::Bytes(bytes, _mm) => {
                let layout = self.ty_layout(ty);
                match layout.abi {
                    Abi::Uninhabited => unreachable!(),
                    Abi::Scalar(scalar) => {
                        let typ = translate_scalar_type(scalar, self.module.isa());
                        let signed = scalar_signedness(scalar);
                        let mut data: [u8; 8] = [0; 8];
                        data[0..bytes.len()].copy_from_slice(&bytes);
                        ValueKind::Primitive(
                            self.builder.ins().iconst(typ, i64::from_le_bytes(data)),
                            signed,
                        )
                    }
                    _ => panic!("unsupported abi for const: {:?}", layout.abi),
                }
            }
            hir_ty::ConstScalar::UnevaluatedConst(_, _) => panic!("unevaluated const"),
            hir_ty::ConstScalar::Unknown => panic!("unknown const scalar"),
        }
    }

    fn translate_place_copy(&mut self, place: &Place) -> ValueKind {
        let projection = place.projection.lookup(&self.body.projection_store);
        let local = place.local;
        self.translate_copy_local_with_projection(local, projection)
    }

    fn translate_copy_local_with_projection(
        &mut self,
        local: LocalId,
        projection: &[ProjectionElem<LocalId, Ty>],
    ) -> ValueKind {
        let (place_kind, ty) = self.translate_local_with_projection(local, projection);
        let layout = self.ty_layout(ty.clone());
        let abi = layout.abi;
        return match place_kind {
            PlaceKind::Variable(var) => {
                let var_val = self.builder.use_var(var);
                match abi {
                    Abi::Scalar(scalar) => ValueKind::Primitive(var_val, scalar_signedness(scalar)),
                    _ => panic!("unsupported for var load: {:?}", abi),
                }
            }
            PlaceKind::Stack(slot, off) => match abi {
                Abi::Scalar(scalar) => {
                    let loaded_val = self.builder.ins().stack_load(
                        translate_type(ty.clone(), self.module.isa(), "stack copy"),
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
                        translate_type(ty.clone(), self.module.isa(), "stack copy"),
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
    }

    fn translate_local_access(&mut self, local: LocalId) -> Value {
        let variable = self.get_variable(local);
        match variable {
            LocalKind::Variable(var) => self.builder.use_var(var),
            LocalKind::Stack(_) => panic!("unimplemented stack slot access"),
        }
    }

    fn translate_local_store(&mut self, local: LocalId, value: Value) {
        let variable = self.get_variable(local);
        match variable {
            LocalKind::Variable(var) => self.builder.def_var(var, value),
            LocalKind::Stack(_) => panic!("unimplemented stack slot store"),
        }
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
}

impl ValueKind {
    fn assert_primitive(&self) -> (Value, bool) {
        match *self {
            ValueKind::Primitive(val, signedness) => (val, signedness),
            _ => panic!("non-primitive value"),
        }
    }
}

fn translate_signature(sig: &hir_ty::CallableSig, isa: &dyn TargetIsa) -> Signature {
    let call_conv = match sig.abi() {
        hir_ty::FnAbi::Rust => CallConv::Fast,
        _ => panic!("unsupported ABI: {:?}", sig.abi()),
    };
    let mut signature = Signature::new(call_conv);
    signature.params.extend(
        sig.params().iter().map(|t| translate_type(t.clone(), isa, "sig")).map(AbiParam::new),
    );
    signature.returns.extend(
        translate_type_for_calls(sig.ret().clone(), isa, "sig return")
            .into_iter()
            .map(AbiParam::new),
    );
    signature
}

fn translate_type_for_calls(ty: Ty, isa: &dyn TargetIsa, ctx: &'static str) -> SmallVec<[Type; 1]> {
    use chalk_ir::{FloatTy, IntTy, TyKind, UintTy};
    use hir_ty::Scalar;
    let single_ty = match ty.kind(Interner) {
        TyKind::Scalar(scalar_ty) => match scalar_ty {
            Scalar::Bool => types::I8,
            Scalar::Char => types::I32,
            Scalar::Int(int_ty) => match int_ty {
                IntTy::Isize => types::I64, // FIXME
                IntTy::I8 => types::I8,
                IntTy::I16 => types::I16,
                IntTy::I32 => types::I32,
                IntTy::I64 => types::I64,
                IntTy::I128 => types::I128,
            },
            Scalar::Uint(uint_ty) => match uint_ty {
                UintTy::Usize => types::I64, // FIXME
                UintTy::U8 => types::I8,
                UintTy::U16 => types::I16,
                UintTy::U32 => types::I32,
                UintTy::U64 => types::I64,
                UintTy::U128 => types::I128,
            },
            Scalar::Float(float_ty) => match float_ty {
                FloatTy::F16 => types::F16,
                FloatTy::F32 => types::F32,
                FloatTy::F64 => types::F64,
                FloatTy::F128 => types::F128,
            },
        },
        // FIXME fat pointers
        TyKind::Ref(_, _, _) => isa.pointer_type(),
        TyKind::Raw(_, _) => isa.pointer_type(),
        TyKind::Tuple(0, _) => return SmallVec::new(),
        _ => panic!("unsupported ty for {}: {:?}", ctx, ty),
    };
    SmallVec::from_buf([single_ty])
}

fn translate_type(ty: Ty, isa: &dyn TargetIsa, ctx: &'static str) -> Type {
    let typ = translate_type_for_calls(ty.clone(), isa, ctx);
    if typ.len() == 1 {
        typ[0]
    } else {
        panic!("unsupported ty for {}: {:?}", ctx, ty)
    }
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
