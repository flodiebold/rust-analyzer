#![allow(unused)]

mod drop;
mod pointer;
#[cfg(test)]
mod test_db;
#[cfg(test)]
mod tests;

use std::{
    cmp::Ordering,
    io::Write,
    marker::PhantomData,
    panic::{AssertUnwindSafe, catch_unwind},
    process::abort,
    sync::Mutex,
};

use anyhow::{Context as _, anyhow};
use base_db::Crate;
use cranelift::{
    codegen::{
        self, Context,
        ir::{GlobalValue, StackSlot, immediates::Offset32},
    },
    frontend::Switch,
    prelude::{
        AbiParam, Block, Configurable, EntityRef, FloatCC, FunctionBuilder, FunctionBuilderContext,
        Imm64, InstBuilder, IntCC, MemFlags, Signature, StackSlotData, TrapCode, Type, Value,
        Variable,
        isa::{CallConv, TargetIsa},
        settings, types,
    },
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use either::Either;
use hir_def::{
    AdtId, CallableDefId, FunctionId, HasModule, LocalFieldId, Lookup, StaticId, VariantId,
    layout::{Scalar, TagEncoding, TargetDataLayout},
    signatures::StaticFlags,
};
use hir_ty::{
    FnAbi, MemoryMap, TraitEnvironment, attach_db,
    db::HirDatabase,
    layout::{Layout, RustcEnumVariantIdx, Variants},
    mir::{
        BasicBlockId, BinOp, CastKind, LocalId, MirBody, Operand, OperandKind, Place,
        ProjectionElem, Rvalue, StatementKind, TerminatorKind, UnOp,
    },
    next_solver::{Const, ConstKind, DbInterner, GenericArgs, PolyFnSig, Ty, TyKind},
};
use la_arena::ArenaMap;
use pointer::Pointer;
use ra_ap_rustc_abi::BackendRepr;
use ra_ap_rustc_ast_ir::{Mutability, UintTy};
use ra_ap_rustc_index::Idx;
use ra_ap_rustc_type_ir::inherent::{AdtDef, IntoKind, SliceLike};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use triomphe::Arc;

#[derive(Clone)]
pub struct JitEngine<'db> {
    jit: Arc<Mutex<Jit<'db>>>,
    db: &'db dyn HirDatabase,
}

// FIXME not pub, but extern linkage?
pub extern "C" fn ensure_function<'db>(engine: &JitEngine<'db>, func_id: u64) -> *const u8 {
    let jit = engine.jit.clone();
    let mut jit = jit.lock().unwrap_or_else(|err| {
        eprintln!("failed to lock jit");
        std::process::abort();
    });
    let func = MonoFunction(salsa::Id::from_bits(func_id), PhantomData);
    let code = catch_unwind(AssertUnwindSafe(|| {
        attach_db(engine.db, || jit.compile(engine.db, func, engine).unwrap())
    }))
    .unwrap_or_else(|err| {
        eprintln!("failed to compile function {}: {:?}", func.0.as_bits(), err);
        std::process::abort();
    });
    code
}

impl<'db> Drop for JitEngine<'db> {
    fn drop(&mut self) {
        // eprintln!("DROPPING JitEngine");
    }
}

impl<'a> JitEngine<'a> {
    pub fn new(db: &'a dyn HirDatabase) -> JitEngine<'a> {
        JitEngine { jit: Arc::new(Mutex::new(Jit::default())), db }
    }
}

pub struct Jit<'db> {
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

    compiled_functions: FxHashMap<MonoFunction<'db>, FuncId>,
    shims: FxHashMap<MonoFunction<'db>, FuncId>,
    statics: FxHashMap<StaticId, DataId>,
    drop_in_place_funcs: FxHashMap<Option<Ty<'db>>, FuncId>,
}

struct CompilationProcess<'a, 'db> {
    krate: Crate,
    interner: DbInterner<'db>,
    queue: &'a mut Vec<FuncToCompile<'db>>,
    module: &'a mut JITModule,
    shims: &'a mut FxHashMap<MonoFunction<'db>, FuncId>,
    statics: &'a mut FxHashMap<StaticId, DataId>,
    drop_in_place_funcs: &'a mut FxHashMap<Option<Ty<'db>>, FuncId>,
}

#[derive(Debug)]
struct FuncToCompile<'db> {
    func_id: FuncId,
    kind: FuncKind<'db>,
}

#[derive(Debug)]
enum FuncKind<'db> {
    CallShim(MonoFunction<'db>),
    Function(MonoFunction<'db>),
    DropShim(Ty<'db>),
}

macro_rules! reborrow_compilation {
    ($self:ident, $id:ident) => {
        let $id = CompilationProcess {
            krate: $self.krate,
            interner: $self.interner,
            queue: &mut *$self.queue,
            module: &mut *$self.module,
            shims: &mut *$self.shims,
            statics: &mut *$self.statics,
            drop_in_place_funcs: &mut *$self.drop_in_place_funcs,
        };
    };
}
use reborrow_compilation;

impl<'a, 'db> CompilationProcess<'a, 'db> {
    fn db(&self) -> &'db dyn HirDatabase {
        self.interner.db()
    }

    fn declare_call_shim(&mut self, mono_func_id: MonoFunction<'db>) -> FuncId {
        if let Some(shim) = self.shims.get(&mono_func_id) {
            return *shim;
        }

        let func = mono_func_id.func(self.db());
        let subst = mono_func_id.subst(self.db());
        let sig = self.db().callable_item_signature(func.into()).instantiate(self.interner, &subst);

        match sig.abi() {
            FnAbi::Rust => {}
            _ => panic!("unsupported abi for shim: {:?}", sig.abi()),
        };

        let signature = translate_signature(sig, self.module.isa(), self.db(), self.krate);

        // FIXME can this legitimately fail?
        let id = self
            .module
            .declare_anonymous_function(&signature)
            .expect("failed to declare anonymous function for shim");

        self.shims.insert(mono_func_id, id);
        self.queue.push(FuncToCompile { func_id: id, kind: FuncKind::CallShim(mono_func_id) });
        id
    }

    fn declare_function(&mut self, mono_func_id: MonoFunction<'db>) -> FuncId {
        let db = self.db();
        let func_id = mono_func_id.func(db);
        let subst = mono_func_id.subst(db);
        let data = db.function_signature(func_id);
        eprintln!("Declaring function {:?} ({})", func_id, data.name.as_str());
        let interner = DbInterner::new_with(db, Some(func_id.krate(db)), None);
        let sig = db.callable_item_signature(func_id.into()).instantiate(interner, subst);
        let krate = func_id.krate(db);

        match sig.abi() {
            FnAbi::Rust => {}
            _ => panic!("unsupported abi for function: {:?}", sig.abi()),
        };

        let env = db.trait_environment(func_id.into());

        let signature = translate_signature(sig, self.module.isa(), db, krate);

        // FIXME can this legitimately fail?
        let id = self
            .module
            // FIXME declare with name and linkage?
            .declare_anonymous_function(&signature)
            .expect("failed to declare function");

        self.queue.push(FuncToCompile { func_id: id, kind: FuncKind::Function(mono_func_id) });

        id
    }

    fn declare_drop_shim(&mut self, ty: Ty<'db>) -> FuncId {
        if let Some(func) = self.drop_in_place_funcs.get(&Some(ty.clone())) {
            return *func;
        }
        let mut signature = Signature::new(CallConv::Fast);
        signature.params.push(AbiParam::new(self.module.isa().pointer_type()));
        // FIXME can this legitimately fail?
        let id = self
            .module
            .declare_anonymous_function(&signature)
            .expect("failed to declare anonymous function for shim");
        self.drop_in_place_funcs.insert(Some(ty), id);
        self.queue.push(FuncToCompile { func_id: id, kind: FuncKind::DropShim(ty) });
        id
    }

    fn compile_function(
        &mut self,
        id: FuncId,
        mono_func_id: MonoFunction<'db>,
        ctx: &mut cranelift::codegen::Context,
        builder_context: &mut FunctionBuilderContext,
    ) -> anyhow::Result<()> {
        let db = self.db();
        let func_id = mono_func_id.func(db);
        let subst = mono_func_id.subst(db);
        let data = db.function_signature(func_id);
        eprintln!("Compiling function {:?} ({})", func_id, data.name.as_str());
        let interner = DbInterner::new_with(db, Some(func_id.krate(db)), None);
        let sig = db.callable_item_signature(func_id.into()).instantiate(interner, subst);
        let krate = func_id.krate(db);

        match sig.abi() {
            FnAbi::Rust => {}
            _ => panic!("unsupported abi for function: {:?}", sig.abi()),
        };

        let env = db.trait_environment(func_id.into());

        ctx.func.signature = translate_signature(sig, self.module.isa(), db, krate);

        let mut builder = FunctionBuilder::new(&mut ctx.func, builder_context);

        let body = db
            .monomorphized_mir_body(func_id.into(), subst, env.clone())
            .map_err(|e| anyhow!("failed to lower MIR: {:?}", e))?;

        let pointer_type = self.module.isa().pointer_type();
        reborrow_compilation!(self, compilation);
        let mut translator = FunctionTranslator {
            pointer_type,
            compilation,
            body: &body,
            variables: ArenaMap::new(),
            blocks: ArenaMap::new(),
            builder,
            env,
            referenced_locals: find_referenced_locals(&body),
        };

        translator.create_blocks();

        translator.compile_all_blocks();

        translator.builder.seal_all_blocks(); // FIXME do this better?
        translator.builder.finalize();

        // Define the function to jit. This finishes compilation, although
        // there may be outstanding relocations to perform. Currently, jit
        // cannot finish relocations until all functions to be called are
        // defined. For this toy demo for now, we'll just finalize the
        // function below.
        self.module.define_function(id, ctx).context("failed to define function")?;

        // Now that compilation is finished, we can clear out the context state.
        self.module.clear_context(ctx);

        Ok(())
    }

    fn compile_shim(
        &mut self,
        id: FuncId,
        mono_func_id: MonoFunction<'db>,
        engine: &JitEngine<'db>,
        ctx: &mut Context,
        builder_context: &mut FunctionBuilderContext,
    ) {
        let db = self.db();
        let func = mono_func_id.func(db);
        let subst = mono_func_id.subst(db);
        let sig = db.callable_item_signature(func.into()).instantiate(self.interner, &subst);

        match sig.abi() {
            FnAbi::Rust => {}
            _ => panic!("unsupported abi for shim: {:?}", sig.abi()),
        };

        ctx.func.signature = translate_signature(sig, self.module.isa(), db, self.krate);

        let sig = ctx.func.signature.clone();

        let mut builder = FunctionBuilder::new(&mut ctx.func, builder_context);

        let mut signature = Signature::new(self.module.isa().default_call_conv());
        let ptr = self.module.isa().pointer_type();
        signature.params.push(AbiParam::new(ptr));
        signature.params.push(AbiParam::new(types::I64));
        signature.returns.push(AbiParam::new(ptr));
        let sig_ref = builder.import_signature(signature);

        let block = builder.create_block();
        builder.switch_to_block(block);
        builder.append_block_params_for_function_params(block);
        // FIXME can we pass engine and address of ensure_function as "global value" / "VM context pointer"?
        // FIXME also maybe just import the function? if that works? (need to declare it as exported though)
        let arg1 = builder.ins().iconst(ptr, engine as *const JitEngine as i64);
        let arg2 = builder.ins().iconst(types::I64, mono_func_id.0.as_bits() as i64);
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
        builder.seal_all_blocks(); // FIXME do this better?
        builder.finalize();
        // FIXME can this legitimately fail?
        self.module.define_function(id, ctx).expect("failed to compile shim function");
        self.module.clear_context(ctx);
    }
}

// FIXME: cleanup of Jit (needs to call free_memory())

impl<'db> Default for Jit<'db> {
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
            statics: FxHashMap::default(),
            drop_in_place_funcs: FxHashMap::default(),
        }
    }
}

impl<'db> Jit<'db> {
    fn compile(
        &mut self,
        db: &'db dyn HirDatabase,
        mono_func_id: MonoFunction<'db>,
        jit_engine: &JitEngine<'db>,
    ) -> Result<*const u8, anyhow::Error> {
        if let Some(f) = self.compiled_functions.get(&mono_func_id) {
            // FIXME check for changes to the function since the last compilation
            // FIXME also cache error?
            return Ok(self.module.get_finalized_function(*f));
        }

        let mut queue = Vec::new();

        let func_id = mono_func_id.func(db);
        let krate = func_id.krate(db);
        let interner = DbInterner::new_with(db, Some(krate), None);

        let mut compilation = CompilationProcess {
            krate,
            interner,
            module: &mut self.module,
            shims: &mut self.shims,
            statics: &mut self.statics,
            drop_in_place_funcs: &mut self.drop_in_place_funcs,
            queue: &mut queue,
        };

        let id = compilation.declare_function(mono_func_id);

        self.compiled_functions.insert(mono_func_id, id);

        while let Some(task) = compilation.queue.pop() {
            eprintln!("task: {:?}", task);
            match task.kind {
                FuncKind::CallShim(mono_function) => compilation.compile_shim(
                    task.func_id,
                    mono_function,
                    jit_engine,
                    &mut self.ctx,
                    &mut self.builder_context,
                ),
                FuncKind::Function(mono_function) => compilation.compile_function(
                    task.func_id,
                    mono_function,
                    &mut self.ctx,
                    &mut self.builder_context,
                )?,
                FuncKind::DropShim(ty) => compilation.compile_drop_shim(
                    task.func_id,
                    ty,
                    &mut self.ctx,
                    &mut self.builder_context,
                ),
            }
        }

        // Finalize the functions which we just defined, which resolves any
        // outstanding relocations (patching in addresses, now that they're
        // available).
        self.module.finalize_definitions().unwrap();

        // We can now retrieve a pointer to the machine code.
        let code = self.module.get_finalized_function(id);

        // eprintln!("Done compiling function");

        Ok(code)
    }
}

struct FunctionTranslator<'a, 'db> {
    compilation: CompilationProcess<'a, 'db>,
    body: &'a MirBody<'db>,
    variables: ArenaMap<LocalId<'db>, PlaceKind>,
    blocks: ArenaMap<BasicBlockId<'db>, Block>,
    builder: FunctionBuilder<'a>,
    env: Arc<TraitEnvironment<'db>>,
    referenced_locals: FxHashSet<LocalId<'db>>,
    pointer_type: Type,
}

#[derive(Clone, Copy, Debug)]
enum PlaceKind {
    Variable(Variable),
    VariablePair(Variable, Variable),
    Addr(Pointer, Option<Value>),
}

#[derive(Clone, Copy, Debug)]
enum ValueKind {
    Primitive(Value),
    ScalarPair(Value, Value),
    Aggregate(Pointer, Option<Value>),
}

#[derive(Clone, Copy, Debug)]
enum MemSlot {
    Stack(StackSlot),
    MemAddr(Value),
}

impl<'a, 'db: 'a> FunctionTranslator<'a, 'db> {
    fn db(&self) -> &'db dyn HirDatabase {
        self.compilation.db()
    }

    fn get_shim(&mut self, mono_func_id: MonoFunction<'db>) -> FuncId {
        self.compilation.declare_call_shim(mono_func_id)
    }

    fn isa(&self) -> &dyn TargetIsa {
        self.compilation.module.isa()
    }

    fn module(&mut self) -> &mut JITModule {
        self.compilation.module
    }

    fn get_static(&mut self, static_id: StaticId) -> (GlobalValue, Ty<'db>) {
        // TODO move to compilation
        let static_data = self.db().static_signature(static_id);
        let data = self.db().const_eval_static(static_id).expect("failed to eval static");
        let ty = self
            .db()
            .value_ty(static_id.into())
            .unwrap()
            .instantiate(self.compilation.interner, GenericArgs::default());
        let data_id = self.compilation.statics.entry(static_id).or_insert_with(|| {
            let mut desc = DataDescription::new();
            let data_id = self
                .compilation
                .module
                .declare_anonymous_data(static_data.flags.contains(StaticFlags::MUTABLE), false)
                .expect("failed to declare static data");
            let ConstKind::Value(c) = &data.kind() else {
                panic!("evaluating gave non concrete constant for static");
            };
            let bytes = c.value.inner();
            match bytes.memory_map {
                MemoryMap::Empty => {}
                MemoryMap::Simple(_) | MemoryMap::Complex(_) => {
                    panic!("unsupported static with memory map");
                }
            };
            desc.define(bytes.memory.clone());
            self.compilation
                .module
                .define_data(data_id, &desc)
                .expect("failed to define static data");
            data_id
        });
        let global_value =
            self.compilation.module.declare_data_in_func(*data_id, &mut self.builder.func);
        (global_value, ty)
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
            let ty = self.body.locals[param].ty.clone();
            let layout = self.ty_layout(ty.clone());
            let value = match layout.backend_repr {
                BackendRepr::Scalar(_) => {
                    let val = param_values.pop().unwrap();
                    ValueKind::Primitive(val)
                }
                BackendRepr::ScalarPair(_, _) => {
                    let val1 = param_values.pop().unwrap();
                    let val2 = param_values.pop().unwrap();
                    ValueKind::ScalarPair(val1, val2)
                }
                BackendRepr::Memory { sized: true } if layout.size.bytes() == 0 => continue,
                BackendRepr::Memory { sized: true } => {
                    let addr = param_values.pop().unwrap();
                    ValueKind::Aggregate(Pointer::new(addr), None)
                }
                _ => panic!("unimplemented abi for param: {:?}", layout.backend_repr),
            };
            let place = self.get_variable(param);
            self.translate_place_kind_store(place, ty, value);
        }
    }

    fn compile_mir_block(&mut self, block_id: BasicBlockId<'db>) {
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
            TerminatorKind::Drop { place, target, unwind } => {
                if unwind.is_some() {
                    panic!("unsupported unwind");
                }
                self.translate_drop(*place);
                self.builder.ins().jump(self.blocks[*target], &[]);
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr = self.translate_operand(discr).assert_primitive();
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
                let static_func_id = match func.kind() {
                    OperandKind::Constant { konst: _, ty } => match ty.kind() {
                        TyKind::FnDef(func_id, subst) => {
                            let subst = subst.clone();
                            let abi =
                                self.db().callable_item_signature(func_id.0).skip_binder().abi();
                            Some((abi, func_id.0, subst))
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
                            let ty = Ty::new_adt(self.compilation.interner, s.into(), subst);
                            let layout = self.ty_layout(ty);
                            let tys: Vec<_> = self
                                .db()
                                .field_types(VariantId::StructId(s))
                                .iter()
                                .map(|(_, t)| t.instantiate(self.compilation.interner, &subst))
                                .collect();
                            self.store_tuple_layout(&layout, &tys, *destination, &args);
                        }
                        CallableDefId::EnumVariantId(ev) => {
                            let ty = Ty::new_adt(
                                self.compilation.interner,
                                ev.lookup(self.db()).parent.into(),
                                subst,
                            );
                            let layout = self.ty_layout(ty);
                            let variant_id = VariantId::EnumVariantId(ev);
                            let layout = self.store_tag_and_get_variant_layout(
                                variant_id,
                                &layout,
                                *destination,
                            );
                            let tys: Vec<_> = self
                                .db()
                                .field_types(variant_id)
                                .iter()
                                .map(|(_, t)| t.instantiate(self.compilation.interner, &subst))
                                .collect();
                            self.store_tuple_layout(layout, &tys, *destination, &args);
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
                        let (v, ty) = self.translate_operand_with_ty(a);
                        let layout = self.ty_layout(ty);
                        let size = layout.size.bytes_usize();
                        // FIXME is this correct?
                        match v {
                            ValueKind::Primitive(val) => [val].to_vec(),
                            ValueKind::ScalarPair(val1, val2) => [val1, val2].to_vec(),
                            ValueKind::Aggregate(pointer, None) => {
                                if size == 0 {
                                    Vec::new()
                                } else {
                                    [pointer.get_addr(self)].to_vec()
                                }
                            }
                            ValueKind::Aggregate(_pointer, Some(_meta)) => {
                                panic!("unsupported unsized param")
                            }
                        }
                    })
                    .collect();

                match static_func_id {
                    Some((FnAbi::RustIntrinsic, CallableDefId::FunctionId(func_id), subst)) => {
                        self.translate_rust_intrinsic_call(func_id, subst, &args, *destination);
                    }
                    Some((_abi, CallableDefId::FunctionId(func_id), subst))
                        if is_extern_func(self.db(), func_id) =>
                    {
                        let sig = self
                            .db()
                            .callable_item_signature(func_id.into())
                            .instantiate(self.compilation.interner, &subst);
                        let data = self.db().function_signature(func_id);
                        // TODO calling convention.....
                        let sig = translate_signature(sig, self.isa(), self.db(), self.env.krate);
                        let func = self
                            .compilation
                            .module
                            .declare_function(&data.name.as_str(), Linkage::Import, &sig)
                            .expect("failed to declare function");
                        let func_ref = self
                            .compilation
                            .module
                            .declare_func_in_func(func, &mut self.builder.func);
                        let call = self.builder.ins().call(func_ref, &args);
                        let results = self.builder.inst_results(call).to_vec();
                        self.store_func_call_return(&results, *destination);
                    }
                    Some((_abi, CallableDefId::FunctionId(func_id), subst)) => {
                        // FIXME handle drop_in_place calls by calling shim
                        let (func, subst) =
                            self.db().lookup_impl_method(self.env.clone(), func_id, subst.clone());
                        let mono_func_id = MonoFunction::new(self.db(), func, subst);
                        let shim = self.get_shim(mono_func_id);
                        let func_ref = self
                            .compilation
                            .module
                            .declare_func_in_func(shim, &mut self.builder.func);
                        let call = self.builder.ins().call(func_ref, &args);
                        let results = self.builder.inst_results(call).to_vec();
                        self.store_func_call_return(&results, *destination);
                    }
                    None => {
                        let (func, ty) = self.translate_operand_with_ty(func);
                        let sig = ty
                            .callable_sig(self.compilation.interner)
                            .expect("indirect call on non-callable");
                        let sig = translate_signature(sig, self.isa(), self.db(), self.env.krate);
                        let sig_ref = self.builder.import_signature(sig);
                        let call = self.builder.ins().call_indirect(
                            sig_ref,
                            func.assert_primitive(),
                            &args,
                        );
                        let results = self.builder.inst_results(call).to_vec();
                        self.store_func_call_return(&results, *destination);
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

    fn store_func_call_return(&mut self, results: &[Value], destination: Place<'db>) {
        let (dest, ret_ty) = self.translate_place_with_ty(destination);
        let ret_ty_layout = self.ty_layout(ret_ty.clone());
        if results.len() > 0 {
            let ret_val = match ret_ty_layout.backend_repr {
                BackendRepr::Scalar(_) => {
                    assert_eq!(results.len(), 1);
                    ValueKind::Primitive(results[0])
                }
                BackendRepr::ScalarPair(_, _) => {
                    assert_eq!(results.len(), 2);
                    ValueKind::ScalarPair(results[0], results[1])
                }
                BackendRepr::Memory { sized } => {
                    if !sized {
                        panic!("unsupported unsized return")
                    }
                    assert_eq!(results.len(), 1);
                    let pointer = Pointer::new(results[0]);
                    ValueKind::Aggregate(pointer, None)
                }
                BackendRepr::SimdVector { .. } => panic!("unsupported vector return"),
            };
            self.translate_place_kind_store(dest, ret_ty, ret_val);
        }
    }

    fn emit_return(&mut self) {
        let return_ty = self.body.locals[return_slot()].ty.clone();
        let layout = self.ty_layout(return_ty);
        let returns = match layout.backend_repr {
            BackendRepr::Memory { sized: true } if layout.size.bytes() == 0 => Vec::new(),
            _ => match self.translate_copy_local_with_projection(return_slot(), &[]).0 {
                ValueKind::Primitive(val) => [val].to_vec(),
                ValueKind::ScalarPair(val1, val2) => [val1, val2].to_vec(),
                ValueKind::Aggregate(pointer, None) => {
                    // FIXME: is this correct ABI-wise?
                    let addr = pointer.get_addr(self);
                    [addr].to_vec()
                }
                ValueKind::Aggregate(_pointer, Some(_meta)) => {
                    panic!("unsupported unsized return")
                }
            },
        };
        self.builder.ins().return_(&returns);
    }

    fn translate_stmt(&mut self, stmt: &hir_ty::mir::Statement<'db>) {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                self.translate_stmt_assign(*place, rvalue);
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

    fn translate_stmt_assign(&mut self, place: Place<'db>, rvalue: &Rvalue<'db>) {
        let value = match rvalue {
            Rvalue::Use(operand) => self.translate_operand(operand),
            Rvalue::CheckedBinaryOp(binop, left, right) => {
                self.translate_checked_binop(binop, left, right)
            }
            Rvalue::UnaryOp(UnOp::Neg, op) => self.translate_neg(op),
            Rvalue::UnaryOp(UnOp::Not, op) => self.translate_not(op),
            Rvalue::Ref(_, place) => {
                let projection = place.projection.lookup(&self.body.projection_store);
                match projection {
                    [rest @ .., ProjectionElem::Deref] => {
                        self.translate_copy_local_with_projection(place.local, rest).0
                    }
                    _ => {
                        let place_kind = self.translate_place(*place);
                        let addr = match place_kind {
                            PlaceKind::Variable(_) => panic!("unsupported ref to variable"),
                            PlaceKind::VariablePair(_, _) => {
                                panic!("unsupported ref to variable pair")
                            }
                            PlaceKind::Addr(pointer, _) => pointer.get_addr(self),
                        };
                        ValueKind::Primitive(addr)
                    }
                }
            }
            Rvalue::Cast(kind, operand, to_ty) => {
                use hir_ty::PointerCast::*;
                let (value, from_ty) = self.translate_operand_with_ty(operand);
                let to_layout = self.ty_layout(to_ty.clone());
                match kind {
                    CastKind::IntToInt => {
                        let (from_sz, from_sign) = get_int_ty(&from_ty, self.isa()).expect("int");
                        let (to_sz, to_sign) = get_int_ty(&to_ty, self.isa()).expect("int");
                        let to_typ = match &to_layout.backend_repr {
                            BackendRepr::Scalar(scalar) => {
                                translate_scalar_type(*scalar, self.isa())
                            }
                            _ => panic!("int with non-scalar abi"),
                        };
                        let value = value.assert_primitive();
                        let cast_value = match (from_sz.cmp(&to_sz), from_sign, to_sign) {
                            (Ordering::Greater, _, _) => self.builder.ins().ireduce(to_typ, value),
                            (Ordering::Less, false, _) => self.builder.ins().uextend(to_typ, value),
                            (Ordering::Less, true, _) => self.builder.ins().sextend(to_typ, value),
                            (Ordering::Equal, _, _) => value,
                        };
                        ValueKind::Primitive(cast_value)
                    }
                    CastKind::IntToFloat => {
                        let (_, from_sign) = get_int_ty(&from_ty, self.isa()).expect("int");
                        let to_typ = match &to_layout.backend_repr {
                            BackendRepr::Scalar(scalar) => {
                                translate_scalar_type(*scalar, self.isa())
                            }
                            _ => panic!("float with non-scalar abi"),
                        };
                        let value = value.assert_primitive();
                        let cast_value = if from_sign {
                            self.builder.ins().fcvt_from_sint(to_typ, value)
                        } else {
                            self.builder.ins().fcvt_from_uint(to_typ, value)
                        };
                        ValueKind::Primitive(cast_value)
                    }
                    CastKind::FloatToInt => {
                        let (_, to_sign) = get_int_ty(&to_ty, self.isa()).expect("int");
                        let to_typ = match &to_layout.backend_repr {
                            BackendRepr::Scalar(scalar) => {
                                translate_scalar_type(*scalar, self.isa())
                            }
                            _ => panic!("int with non-scalar abi"),
                        };
                        let value = value.assert_primitive();
                        let cast_value = if to_sign {
                            self.builder.ins().fcvt_to_sint(to_typ, value)
                        } else {
                            self.builder.ins().fcvt_to_uint(to_typ, value)
                        };
                        ValueKind::Primitive(cast_value)
                    }
                    CastKind::FloatToFloat => {
                        let from_sz = self.ty_layout(from_ty.clone()).size.bytes_usize();
                        let to_typ = match &to_layout.backend_repr {
                            BackendRepr::Scalar(scalar) => {
                                translate_scalar_type(*scalar, self.isa())
                            }
                            _ => panic!("float with non-scalar abi"),
                        };
                        let to_sz = to_typ.bytes() as usize;
                        let value = value.assert_primitive();
                        let cast_value = if from_sz > to_sz {
                            self.builder.ins().fdemote(to_typ, value)
                        } else {
                            self.builder.ins().fpromote(to_typ, value)
                        };
                        ValueKind::Primitive(cast_value)
                    }
                    CastKind::PtrToPtr => panic!("unimplemented PtrToPtr"),
                    CastKind::PointerCoercion(
                        UnsafeFnPointer | MutToConstPointer | ArrayToPointer,
                    ) => {
                        // nothing to do here
                        value
                    }
                    CastKind::PointerCoercion(Unsize) => {
                        let value = value.assert_primitive();
                        let from_pointee =
                            from_ty.as_reference_or_ptr().expect("pointer cast without pointer").0;
                        match from_pointee.kind() {
                            TyKind::Array(_, size) => {
                                assert!(matches!(
                                    to_layout.backend_repr,
                                    BackendRepr::ScalarPair(_, _)
                                ));
                                let size_val = self.translate_const(&size).0.assert_primitive();
                                ValueKind::ScalarPair(value, size_val)
                            }
                            _ => panic!("unsupported unsize from {:?} to {:?}", from_ty, to_ty),
                        }
                    }
                    CastKind::PointerCoercion(ReifyFnPointer) => {
                        let TyKind::FnDef(fn_id, subst) = from_ty.kind() else {
                            panic!("reify non-fn")
                        };
                        let func_ref = match fn_id.0 {
                            CallableDefId::FunctionId(func) if is_extern_func(self.db(), func) => {
                                panic!("unimplemented reify of extern func")
                            }
                            CallableDefId::FunctionId(func) => {
                                let (func, subst) = self.db().lookup_impl_method(
                                    self.env.clone(),
                                    func,
                                    subst.clone(),
                                );
                                let mono_func_id = MonoFunction::new(self.db(), func, subst);
                                let shim = self.get_shim(mono_func_id);
                                let func_ref = self
                                    .compilation
                                    .module
                                    .declare_func_in_func(shim, &mut self.builder.func);
                                func_ref
                            }
                            CallableDefId::StructId(_) => {
                                panic!("unsupported reify of struct constructor")
                            }
                            CallableDefId::EnumVariantId(_) => {
                                panic!("unsupported reify of enum variant constructor")
                            }
                        };
                        let ptr_typ = self.isa().pointer_type();
                        let addr = self.builder.ins().func_addr(ptr_typ, func_ref);
                        ValueKind::Primitive(addr)
                    }
                    CastKind::PointerExposeAddress | CastKind::PointerFromExposedAddress => {
                        let to_typ = match &to_layout.backend_repr {
                            BackendRepr::Scalar(scalar) => {
                                translate_scalar_type(*scalar, self.isa())
                            }
                            _ => panic!("int with non-scalar abi"),
                        };
                        // TODO what about fat pointers
                        let value = value.assert_primitive();
                        let cast_value = match self.pointer_type.bytes().cmp(&to_typ.bytes()) {
                            Ordering::Less => self.builder.ins().uextend(to_typ, value),
                            Ordering::Equal => value,
                            Ordering::Greater => self.builder.ins().ireduce(to_typ, value),
                        };
                        ValueKind::Primitive(cast_value)
                    }
                    CastKind::PointerCoercion(ClosureFnPointer(_)) => {
                        panic!("unimplemented closure cast")
                    }
                    CastKind::DynStar => panic!("unimplemented dyn*"),
                    CastKind::FnPtrToPtr => panic!("unimplemented fn ptr cast"),
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
                        self.store_tuple(*tuple_ty, place, operands);
                    }
                    Adt(variant_id, subst) => {
                        let adt = variant_id.adt_id(self.db());
                        let ty = Ty::new_adt(self.compilation.interner, adt, *subst);
                        let layout = self.ty_layout(ty.clone());
                        let layout =
                            self.store_tag_and_get_variant_layout(*variant_id, &layout, place);
                        let field_types = self.db().field_types(*variant_id);
                        for (i, op) in operands.iter().enumerate() {
                            let val = self.translate_operand(op);
                            let field_offset = layout.fields.offset(i);
                            let field_ty = field_types[LocalFieldId::from_raw((i as u32).into())]
                                .instantiate(self.compilation.interner, subst);
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
            Rvalue::Discriminant(place) => self.translate_load_discriminant(*place),
            Rvalue::Repeat(op, n) => {
                let num = const_to_int(n);
                let val = self.translate_operand(op);
                let (place_kind, ty) = self.translate_place_with_ty(place);
                // FIXME use memset for u8
                let loop_block = self.builder.create_block();
                let loop_block2 = self.builder.create_block();
                let done_block = self.builder.create_block();
                let pointer_type = self.isa().pointer_type();
                let index = self.builder.append_block_param(loop_block, pointer_type);
                let zero = self.builder.ins().iconst(pointer_type, 0);
                self.builder.ins().jump(loop_block, &[zero]);

                self.builder.switch_to_block(loop_block);
                let done = self.builder.ins().icmp_imm(IntCC::Equal, index, num as i64);
                self.builder.ins().brif(done, done_block, &[], loop_block2, &[]);

                self.builder.switch_to_block(loop_block2);
                let (place_kind, place_elem_ty) = self.place_index(place_kind, ty, index);
                self.translate_place_kind_store(place_kind, place_elem_ty, val);
                let index = self.builder.ins().iadd_imm(index, 1);
                self.builder.ins().jump(loop_block, &[index]);

                self.builder.switch_to_block(done_block);
                self.builder.ins().nop();
                return;
            }
            Rvalue::Len(place) => self.translate_array_len(*place),
            Rvalue::ShallowInitBox(_, _) => panic!("unsupported ShallowInitBox"),
            Rvalue::ShallowInitBoxWithAlloc(_) => panic!("unsupported ShallowInitBoxWithAlloc"),
            Rvalue::CopyForDeref(_) => panic!("unsupported CopyForDeref"),
            Rvalue::ThreadLocalRef(infallible)
            | Rvalue::AddressOf(infallible)
            | Rvalue::BinaryOp(infallible)
            | Rvalue::NullaryOp(infallible) => match *infallible {},
        };
        self.translate_place_store(place, value)
    }

    fn translate_place(&mut self, place: Place<'db>) -> PlaceKind {
        self.translate_place_with_ty(place).0
    }

    fn translate_place_with_ty(&mut self, place: Place<'db>) -> (PlaceKind, Ty<'db>) {
        let projection = place.projection.lookup(&self.body.projection_store);
        let local = place.local;
        self.translate_local_with_projection(local, projection)
    }

    fn place_index(&mut self, kind: PlaceKind, ty: Ty<'db>, idx: Value) -> (PlaceKind, Ty<'db>) {
        let addr = self.translate_place_kind_addr(kind);
        let ty = match ty.kind() {
            TyKind::Array(elem_ty, _size) => elem_ty.clone(),
            TyKind::Slice(elem_ty) => elem_ty.clone(),
            _ => panic!("can't index ty: {:?}", ty),
        };
        let layout = self.ty_layout(ty.clone());
        let ptr_typ = self.isa().pointer_type();
        let elem_size = self.builder.ins().iconst(ptr_typ, layout.size.bytes_usize() as i64);
        let idx_offset = self.builder.ins().imul(idx, elem_size);
        let addr = self.builder.ins().iadd(addr, idx_offset);
        (PlaceKind::Addr(Pointer::new(addr), None), ty)
    }

    fn translate_local_with_projection(
        &mut self,
        local: LocalId<'db>,
        projection: &[ProjectionElem<LocalId<'db>, Ty<'db>>],
    ) -> (PlaceKind, Ty<'db>) {
        let mut ty = self.body.locals[local].ty.clone();
        let mut kind = self.get_variable(local);
        for elem in projection {
            match elem {
                ProjectionElem::Deref => {
                    let derefed_ty =
                        ty.as_reference_or_ptr().expect("non-ptr deref target").0.clone();
                    if has_ptr_meta(self.db(), derefed_ty.clone()) {
                        let (addr, meta) = self.load_scalar_pair(kind, ty.clone());
                        kind = PlaceKind::Addr(Pointer::new(addr), Some(meta))
                    } else {
                        let addr = self.load_scalar(kind, ty.clone());
                        kind = PlaceKind::Addr(Pointer::new(addr), None);
                    }
                    ty = derefed_ty;
                }
                ProjectionElem::Index(idx) => {
                    let idx =
                        self.translate_copy_local_with_projection(*idx, &[]).0.assert_primitive();
                    (kind, ty) = self.place_index(kind, ty, idx);
                }
                ProjectionElem::Field(Either::Right(tuple_idx)) => {
                    let idx = tuple_idx.index as usize;
                    let layout = self.ty_layout(ty.clone());
                    ty = ty.as_tuple().unwrap().as_slice()[idx];
                    match kind {
                        PlaceKind::Variable(var) => {
                            assert_eq!(0, idx);
                            kind = PlaceKind::Variable(var);
                        }
                        PlaceKind::VariablePair(var1, var2) => {
                            assert!(idx < 2);
                            kind = PlaceKind::Variable(if idx == 0 { var1 } else { var2 });
                        }
                        PlaceKind::Addr(pointer, _) => {
                            let offset = layout.fields.offset(idx).bytes_usize();
                            kind = PlaceKind::Addr(pointer.offset_i64(self, offset as i64), None);
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
                                    RustcEnumVariantIdx(it.lookup(self.db()).index as usize)
                                }
                                _ => panic!("multiple variants in non-enum"),
                            }]
                        }
                        hir_ty::layout::Variants::Empty => unreachable!("empty variants field"),
                    };
                    let idx = u32::from(field_id.local_id.into_raw()) as usize;
                    let (_, subst) = ty.as_adt().expect("non-adt field access");
                    ty = self.db().field_types(field_id.parent)[field_id.local_id]
                        .instantiate(self.compilation.interner, subst);
                    let offset = layout.fields.offset(idx).bytes_usize();
                    match kind {
                        PlaceKind::Variable(var) => {
                            assert_eq!(0, offset);
                            kind = PlaceKind::Variable(var);
                        }
                        PlaceKind::VariablePair(var1, var2) => {
                            kind = PlaceKind::Variable(if offset == 0 { var1 } else { var2 });
                        }
                        PlaceKind::Addr(pointer, _) => {
                            kind = PlaceKind::Addr(pointer.offset_i64(self, offset as i64), None)
                        }
                    }
                }
                ProjectionElem::ConstantIndex { offset, from_end } => {
                    if *from_end {
                        panic!("unimplemented ConstantIndex from_end");
                    }
                    let ptr = self.place_kind_ptr(kind);
                    ty = match ty.kind() {
                        TyKind::Array(elem_ty, _size) => elem_ty.clone(),
                        TyKind::Slice(elem_ty) => elem_ty.clone(),
                        _ => panic!("can't index ty: {:?}", ty),
                    };
                    let layout = self.ty_layout(ty.clone());
                    let idx_offset = *offset * layout.size.bytes();
                    kind = PlaceKind::Addr(ptr.offset_i64(self, idx_offset as i64), None);
                }
                ProjectionElem::ClosureField(_) => panic!("unsupported closure field"),
                ProjectionElem::Subslice { .. } => panic!("unsupported subslice"),
                ProjectionElem::OpaqueCast(_) => panic!("unsupported opaque cast"),
            }
        }
        (kind, ty)
    }

    fn place_kind_ptr(&mut self, kind: PlaceKind) -> Pointer {
        match kind {
            PlaceKind::Variable(_) => panic!("trying to take ptr of variable"),
            PlaceKind::VariablePair(_, _) => panic!("trying to take ptr of variable pair"),
            PlaceKind::Addr(pointer, _) => pointer,
        }
    }

    fn translate_place_kind_addr(&mut self, kind: PlaceKind) -> Value {
        match kind {
            PlaceKind::Variable(_) => panic!("trying to take addr of variable"),
            PlaceKind::VariablePair(_, _) => panic!("trying to take addr of variable pair"),
            PlaceKind::Addr(pointer, _) => pointer.get_addr(self),
        }
    }

    fn load_scalar(&mut self, kind: PlaceKind, ty: Ty<'db>) -> Value {
        match kind {
            PlaceKind::Variable(var) => self.builder.use_var(var),
            PlaceKind::VariablePair(var1, _) => self.builder.use_var(var1),
            PlaceKind::Addr(pointer, None) => {
                let layout = self.ty_layout(ty.clone());
                let clif_ty = match layout.backend_repr {
                    BackendRepr::Scalar(scalar) => translate_scalar_type(scalar, self.isa()),
                    BackendRepr::SimdVector { element, count } => {
                        translate_scalar_type(element, self.isa())
                            .by(u32::try_from(count).unwrap())
                            .unwrap()
                    }
                    _ => unreachable!("{:?}", ty),
                };
                pointer.load(self, clif_ty, MemFlags::trusted())
            }
            PlaceKind::Addr(_pointer, Some(_)) => panic!("load_scalar on unsized place"),
        }
    }

    fn load_scalar_pair(&mut self, kind: PlaceKind, ty: Ty<'db>) -> (Value, Value) {
        match kind {
            PlaceKind::Variable(_) => panic!("load_scalar_pair on single variable"),
            PlaceKind::VariablePair(var1, var2) => {
                (self.builder.use_var(var1), self.builder.use_var(var2))
            }
            PlaceKind::Addr(pointer, None) => {
                let layout = self.ty_layout(ty);
                let (a_scalar, b_scalar) = match layout.backend_repr {
                    BackendRepr::ScalarPair(a, b) => (a, b),
                    _ => unreachable!("load_scalar_pair({:?})", layout.backend_repr),
                };
                let tdl = self.db().target_data_layout(self.env.krate).unwrap();
                let b_offset = scalar_pair_calculate_b_offset(&tdl, a_scalar, b_scalar);
                let clif_ty1 = translate_scalar_type(a_scalar, self.isa());
                let clif_ty2 = translate_scalar_type(b_scalar, self.isa());
                let flags = MemFlags::trusted();
                let val1 = pointer.load(self, clif_ty1, flags);
                let val2 = pointer.offset(self, b_offset).load(self, clif_ty2, flags);
                (val1, val2)
            }
            PlaceKind::Addr(_pointer, Some(_)) => panic!("load_scalar_pair on unsized place"),
        }
    }

    fn translate_place_store(&mut self, place: Place<'db>, value: ValueKind) {
        let (kind, ty) = self.translate_place_with_ty(place);
        self.translate_place_kind_store_with_offset(kind, ty, 0, value)
    }

    fn translate_place_kind_store(&mut self, kind: PlaceKind, ty: Ty<'db>, value: ValueKind) {
        self.translate_place_kind_store_with_offset(kind, ty, 0, value)
    }

    fn translate_place_store_with_offset(
        &mut self,
        place: Place<'db>,
        ty: Ty<'db>,
        offset: i32,
        value: ValueKind,
    ) {
        let kind = self.translate_place(place);
        self.translate_place_kind_store_with_offset(kind, ty, offset, value)
    }

    fn translate_place_kind_store_with_offset(
        &mut self,
        kind: PlaceKind,
        ty: Ty<'db>,
        offset: i32,
        value: ValueKind,
    ) {
        match kind {
            PlaceKind::Variable(var) => {
                if offset == 0 {
                    match value {
                        ValueKind::Primitive(val) => {
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
                        ValueKind::Primitive(val) => {
                            self.builder.def_var(var1, val);
                        }
                        _ => panic!("unsupported value kind for variable pair store: {:?}", value),
                    }
                } else {
                    self.builder.def_var(var2, value.assert_primitive());
                }
            }
            PlaceKind::Addr(pointer, _) => {
                let pointer = pointer.offset_i64(self, offset as i64);
                match value {
                    ValueKind::Primitive(value) => {
                        pointer.store(self, value, MemFlags::trusted());
                    }
                    ValueKind::ScalarPair(val1, val2) => {
                        let layout = self.ty_layout(ty.clone());
                        let BackendRepr::ScalarPair(s1, s2) = layout.backend_repr else {
                            panic!("wrong layout of scalar pair: {:?}", layout.backend_repr)
                        };
                        let tdl = self.db().target_data_layout(self.env.krate).unwrap();
                        let off2 = scalar_pair_calculate_b_offset(&tdl, s1, s2);
                        pointer.store(self, val1, MemFlags::trusted());
                        pointer.offset(self, off2).store(self, val2, MemFlags::trusted());
                    }
                    ValueKind::Aggregate(pointer_from, None) => {
                        let layout = self.ty_layout(ty);
                        let size = layout.size.bytes_usize() as i32;
                        self.translate_mem_copy(pointer, pointer_from, size)
                    }
                    ValueKind::Aggregate(_pointer_from, Some(_meta)) => {
                        panic!("unimplemented store from unsized value")
                    }
                }
            }
        }
    }

    fn get_variable(&mut self, local: LocalId<'db>) -> PlaceKind {
        let typ = self.body.locals[local].ty.clone();
        let db = self.compilation.db();
        let isa = self.compilation.module.isa();
        let variable = *self.variables.entry(local).or_insert_with(|| {
            // FIXME error handling here!
            let layout =
                db.layout_of_ty(typ.clone(), self.env.clone()).expect("failed to lay out type");
            let needs_stack = !layout.uninhabited
                && (self.referenced_locals.contains(&local)
                    || drop::needs_drop(db, &typ)
                    || matches!(layout.backend_repr, BackendRepr::Memory { .. }));
            if needs_stack {
                if !layout.is_sized() {
                    panic!("unsized type in local");
                }
                let size = layout.size.bytes_usize();
                let slot = self.builder.create_sized_stack_slot(StackSlotData {
                    kind: codegen::ir::StackSlotKind::ExplicitSlot,
                    size: size as u32,
                    align_shift: layout.align.abi.bytes().ilog2() as u8,
                });
                PlaceKind::Addr(Pointer::stack_slot(slot), None)
            } else if layout.uninhabited {
                PlaceKind::Addr(Pointer::dangling(layout.unadjusted_abi_align), None)
            } else if let BackendRepr::Scalar(scalar) = layout.backend_repr {
                let var = Variable::new(local.into_raw().into_u32() as usize * 2);
                let typ = translate_scalar_type(scalar, isa);
                self.builder.declare_var(var, typ);
                PlaceKind::Variable(var)
            } else if let BackendRepr::ScalarPair(scalar1, scalar2) = layout.backend_repr {
                let typ1 = translate_scalar_type(scalar1, isa);
                let typ2 = translate_scalar_type(scalar2, isa);
                let var1 = Variable::new(local.into_raw().into_u32() as usize * 2);
                let var2 = Variable::new(local.into_raw().into_u32() as usize * 2 + 1);
                self.builder.declare_var(var1, typ1);
                self.builder.declare_var(var2, typ2);
                PlaceKind::VariablePair(var1, var2)
            } else {
                panic!("unsupported layout for local: {:?}", layout.backend_repr);
            }
        });
        variable
    }

    fn translate_operand(&mut self, operand: &Operand<'db>) -> ValueKind {
        self.translate_operand_with_ty(operand).0
    }

    fn translate_operand_with_ty(&mut self, operand: &Operand<'db>) -> (ValueKind, Ty<'db>) {
        match operand.kind() {
            OperandKind::Constant { konst, ty: _ } => self.translate_const(konst),
            OperandKind::Copy(place) | OperandKind::Move(place) => {
                self.translate_place_copy(*place)
            }
            OperandKind::Static(static_id) => {
                let (global_value, ty) = self.get_static(*static_id);
                let addr = self.builder.ins().global_value(self.pointer_type, global_value);
                let ptr_ty =
                    Ty::new(self.compilation.interner, TyKind::RawPtr(ty, Mutability::Mut));
                (ValueKind::Primitive(addr), ptr_ty)
            }
        }
    }

    fn translate_const(&mut self, konst: &Const<'db>) -> (ValueKind, Ty<'db>) {
        let ConstKind::Value(c) = &**konst.inner() else {
            panic!("evaluating non concrete constant");
        };
        let ty = c.ty;
        let inner = c.value.inner();
        let bytes = &inner.memory;
        let mm = &inner.memory_map;
        let layout = self.ty_layout(ty.clone());
        let memory_addr = match mm {
            MemoryMap::Empty => None,
            MemoryMap::Simple(bytes) => {
                let data = self
                    .module()
                    .declare_anonymous_data(false, false)
                    .expect("failed to create data");
                let mut desc = DataDescription::new();
                desc.define(bytes.clone());
                self.module().define_data(data, &desc).expect("failed to define data");
                let global =
                    self.compilation.module.declare_data_in_func(data, &mut self.builder.func);
                let ptr_type = self.isa().pointer_type();
                let addr = self.builder.ins().global_value(ptr_type, global);
                Some(addr)
            }
            _ => panic!("unsupported memory map in const: {:?}", mm),
        };
        let is_ref = ty.as_reference_or_ptr().is_some();
        let val = match layout.backend_repr {
            BackendRepr::Scalar(scalar) => {
                let typ = translate_scalar_type(scalar, self.isa());
                if typ.is_float() {
                    let val = match typ.bytes() {
                        2 => panic!("unimplemented f16 constant"),
                        4 => {
                            let mut data: [u8; 4] = [0; 4];
                            data[0..bytes.len()].copy_from_slice(&bytes[0..bytes.len()]);
                            let val = f32::from_ne_bytes(data);
                            self.builder.ins().f32const(val)
                        }
                        8 => {
                            let mut data: [u8; 8] = [0; 8];
                            data[0..bytes.len()].copy_from_slice(&bytes[0..bytes.len()]);
                            let val = f64::from_ne_bytes(data);
                            self.builder.ins().f64const(val)
                        }
                        16 => {
                            panic!("unimplemented f128 constant");
                            // let mut data: [u8; 16] = [0; 16];
                            // data[0..bytes.len()].copy_from_slice(&bytes[0..bytes.len()]);
                            // let val = f128::from_ne_bytes(data);
                            // self.builder.ins().f128const(val)
                        }
                        _ => unreachable!("{:?}", typ),
                    };
                    ValueKind::Primitive(val)
                } else {
                    let val = bytes_to_imm64(bytes);
                    let val = if is_ref {
                        let addr = memory_addr.expect("ref const without memory");
                        self.builder.ins().iadd_imm(addr, val)
                    } else {
                        self.builder.ins().iconst(typ, val)
                    };
                    ValueKind::Primitive(val)
                }
            }
            BackendRepr::ScalarPair(s1, s2) => {
                let typ1 = translate_scalar_type(s1, self.isa());
                let typ2 = translate_scalar_type(s2, self.isa());
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
            BackendRepr::Memory { sized: true } => {
                let data = self
                    .module()
                    .declare_anonymous_data(false, false)
                    .expect("failed to create data");
                let mut desc = DataDescription::new();
                desc.define(bytes.clone());
                self.module().define_data(data, &desc).expect("failed to define data");
                let global =
                    self.compilation.module.declare_data_in_func(data, &mut self.builder.func);
                let ptr_type = self.isa().pointer_type();
                let addr = self.builder.ins().global_value(ptr_type, global);
                ValueKind::Aggregate(Pointer::new(addr), None)
            }
            BackendRepr::Memory { sized: false } => panic!("sized: false unsupported"),
            BackendRepr::SimdVector { .. } => panic!("SIMD unsupported"),
        };
        (val, ty)
    }

    fn translate_place_copy(&mut self, place: Place<'db>) -> (ValueKind, Ty<'db>) {
        let projection = place.projection.lookup(&self.body.projection_store);
        let local = place.local;
        self.translate_copy_local_with_projection(local, projection)
    }

    fn translate_copy_local_with_projection(
        &mut self,
        local: LocalId<'db>,
        projection: &[ProjectionElem<LocalId<'db>, Ty<'db>>],
    ) -> (ValueKind, Ty<'db>) {
        let (place_kind, ty) = self.translate_local_with_projection(local, projection);
        let layout = self.ty_layout(ty.clone());
        let abi = layout.backend_repr;
        let val = match place_kind {
            PlaceKind::Variable(var) => {
                let var_val = self.builder.use_var(var);
                match abi {
                    BackendRepr::Scalar(_) => ValueKind::Primitive(var_val),
                    _ => unreachable!("non-scalar in variable: {:?}", abi),
                }
            }
            PlaceKind::VariablePair(var1, var2) => {
                let var1_val = self.builder.use_var(var1);
                let var2_val = self.builder.use_var(var2);
                assert!(matches!(abi, BackendRepr::ScalarPair(..)));
                ValueKind::ScalarPair(var1_val, var2_val)
            }
            PlaceKind::Addr(ptr, _) => self.translate_mem_slot_load(ptr, ty.clone()),
        };
        (val, ty)
    }

    fn translate_mem_slot_load(&mut self, pointer: Pointer, ty: Ty) -> ValueKind {
        let layout = self.ty_layout(ty);
        let abi = layout.backend_repr;
        match abi {
            BackendRepr::Scalar(scalar) => {
                let typ = translate_scalar_type(scalar, self.isa());
                let loaded_val = pointer.load(self, typ, MemFlags::trusted());
                ValueKind::Primitive(loaded_val)
            }
            BackendRepr::ScalarPair(s1, s2) => {
                let typ1 = translate_scalar_type(s1, self.isa());
                let typ2 = translate_scalar_type(s2, self.isa());
                let tdl = self.db().target_data_layout(self.env.krate).unwrap();
                let off = scalar_pair_calculate_b_offset(&tdl, s1, s2);
                let v1 = pointer.load(self, typ1, MemFlags::trusted());
                let v2 = pointer.offset(self, off).load(self, typ2, MemFlags::trusted());
                ValueKind::ScalarPair(v1, v2)
            }
            BackendRepr::Memory { sized: true } => ValueKind::Aggregate(pointer, None),
            _ => panic!("unsupported abi for var copy: {:?}", abi),
        }
    }

    fn translate_checked_binop(
        &mut self,
        binop: &BinOp,
        left: &Operand<'db>,
        right: &Operand<'db>,
    ) -> ValueKind {
        let (left, ty1) = self.translate_operand_with_ty(left);
        let (right, _) = self.translate_operand_with_ty(right);
        let left = left.assert_primitive();
        let right = right.assert_primitive();
        let (float, signed) = match ty1.kind() {
            TyKind::Int(_) => (false, true),
            TyKind::Uint(_) => (false, false),
            TyKind::Float(_) => (true, true),
            _ => panic!("unsupported type for binop: {:?}", ty1),
        };
        let result = if !float {
            match binop {
                // FIXME checked?
                BinOp::Add => self.builder.ins().iadd(left, right),
                BinOp::Sub => self.builder.ins().isub(left, right),
                BinOp::Mul => self.builder.ins().imul(left, right),
                BinOp::Div if signed => self.builder.ins().sdiv(left, right),
                BinOp::Div => self.builder.ins().udiv(left, right),
                BinOp::Rem if signed => self.builder.ins().srem(left, right),
                BinOp::Rem => self.builder.ins().urem(left, right),

                BinOp::Eq => self.builder.ins().icmp(IntCC::Equal, left, right),
                BinOp::Ne => self.builder.ins().icmp(IntCC::NotEqual, left, right),
                BinOp::Lt if signed => self.builder.ins().icmp(IntCC::SignedLessThan, left, right),
                BinOp::Le if signed => {
                    self.builder.ins().icmp(IntCC::SignedLessThanOrEqual, left, right)
                }
                BinOp::Gt if signed => {
                    self.builder.ins().icmp(IntCC::SignedGreaterThan, left, right)
                }
                BinOp::Ge if signed => {
                    self.builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, left, right)
                }
                BinOp::Lt => self.builder.ins().icmp(IntCC::UnsignedLessThan, left, right),
                BinOp::Le => self.builder.ins().icmp(IntCC::UnsignedLessThanOrEqual, left, right),
                BinOp::Gt => self.builder.ins().icmp(IntCC::UnsignedGreaterThan, left, right),
                BinOp::Ge => {
                    self.builder.ins().icmp(IntCC::UnsignedGreaterThanOrEqual, left, right)
                }

                BinOp::BitXor => self.builder.ins().bxor(left, right),
                BinOp::BitAnd => self.builder.ins().band(left, right),
                BinOp::BitOr => self.builder.ins().bor(left, right),
                BinOp::Shl => self.builder.ins().ishl(left, right),
                BinOp::Shr if signed => self.builder.ins().sshr(left, right),
                BinOp::Shr => self.builder.ins().ushr(left, right),
                BinOp::Offset => panic!("unsupported binop: offset"),
            }
        } else {
            match binop {
                BinOp::Add => self.builder.ins().fadd(left, right),
                BinOp::Sub => self.builder.ins().fsub(left, right),
                BinOp::Mul => self.builder.ins().fmul(left, right),
                BinOp::Div => self.builder.ins().fdiv(left, right),

                BinOp::Eq => self.builder.ins().fcmp(FloatCC::Equal, left, right),
                BinOp::Ne => self.builder.ins().fcmp(FloatCC::NotEqual, left, right),
                BinOp::Lt => self.builder.ins().fcmp(FloatCC::LessThan, left, right),
                BinOp::Le => self.builder.ins().fcmp(FloatCC::LessThanOrEqual, left, right),
                BinOp::Gt => self.builder.ins().fcmp(FloatCC::GreaterThan, left, right),
                BinOp::Ge => self.builder.ins().fcmp(FloatCC::GreaterThanOrEqual, left, right),

                BinOp::BitXor
                | BinOp::BitAnd
                | BinOp::BitOr
                | BinOp::Shl
                | BinOp::Shr
                | BinOp::Rem
                | BinOp::Offset => panic!("bad float binop: {:?}", binop),
            }
        };
        ValueKind::Primitive(result)
    }

    fn ty_layout(&self, ty: Ty) -> Arc<Layout> {
        // FIXME error handling?
        self.db().layout_of_ty(ty, self.env.clone()).expect("failed layout")
    }

    fn translate_mem_copy(&mut self, dest: Pointer, src: Pointer, size: i32) {
        let config = self.module().target_config();
        let dest = dest.get_addr(self);
        let src = src.get_addr(self);
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

    fn translate_neg(&mut self, op: &Operand<'db>) -> ValueKind {
        let (value, ty) = self.translate_operand_with_ty(op);
        match ty.kind() {
            TyKind::Int(_) => {
                let result = self.builder.ins().ineg(value.assert_primitive());
                ValueKind::Primitive(result)
            }
            TyKind::Float(_) => {
                let result = self.builder.ins().fneg(value.assert_primitive());
                ValueKind::Primitive(result)
            }
            _ => unreachable!("bad type for negation: {:?}", ty),
        }
    }

    fn translate_not(&mut self, op: &Operand<'db>) -> ValueKind {
        let (value, ty) = self.translate_operand_with_ty(op);
        match ty.kind() {
            TyKind::Int(_) | TyKind::Uint(_) => {
                let value = value.assert_primitive();
                let result = self.builder.ins().bnot(value);
                ValueKind::Primitive(result)
            }
            TyKind::Bool => {
                let value = value.assert_primitive();
                let result = self.builder.ins().bxor_imm(value, 1);
                ValueKind::Primitive(result)
            }
            _ => unreachable!("bad type for not: {:?}", ty),
        }
    }

    fn translate_rust_intrinsic_call(
        &mut self,
        func_id: FunctionId,
        subst: GenericArgs<'db>,
        args: &[Value],
        destination: Place<'db>,
    ) {
        // FIXME might want to share more/less code with the normal rust call code
        let function_data = self.db().function_signature(func_id);
        let func_name = function_data.name.as_str();
        match func_name {
            "transmute" => self.translate_transmute(subst, args, destination),
            _ => panic!("unsupported intrinsic: {:?}", func_name),
        }
    }

    fn translate_transmute(
        &mut self,
        _subst: GenericArgs<'db>,
        args: &[Value],
        destination: Place<'db>,
    ) {
        // FIXME check validity?
        self.store_func_call_return(args, destination);
    }

    fn store_tuple(&mut self, tuple_ty: Ty<'db>, place: Place<'db>, operands: &[Operand<'db>]) {
        let layout = self.ty_layout(tuple_ty);
        let tys = tuple_ty.as_tuple().expect("no tuple");
        self.store_tuple_layout(&layout, tys.as_slice(), place, operands);
    }

    fn store_tuple_layout(
        &mut self,
        layout: &Layout,
        tys: &[Ty<'db>],
        place: Place<'db>,
        operands: &[Operand<'db>],
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

    fn translate_load_discriminant(&mut self, place: Place<'db>) -> ValueKind {
        let (kind, ty) = self.translate_place_with_ty(place);
        let TyKind::Adt(adt_def, _) = ty.kind() else { panic!("load discriminant of non-enum") };
        let AdtId::EnumId(e) = adt_def.def_id().0 else { panic!("load discriminant of non-enum") };
        let layout = self.ty_layout(ty.clone());
        let Variants::Multiple { tag, tag_encoding, tag_field, .. } = &layout.variants else {
            panic!("load discriminant of non-multi variant")
        };
        let tag_typ = translate_scalar_type(*tag, self.isa());
        let tag_offset = layout.fields.offset(tag_field.index()).bytes_usize() as i32;
        let tag = match kind {
            PlaceKind::Variable(var) => {
                assert!(tag_offset == 0);
                self.builder.use_var(var)
            }
            PlaceKind::VariablePair(var1, _) => {
                assert!(tag_offset == 0);
                self.builder.use_var(var1)
            }
            PlaceKind::Addr(pointer, _) => {
                pointer.offset_i64(self, tag_offset as i64).load(self, tag_typ, MemFlags::trusted())
            }
        };
        let mut tag = match tag_encoding {
            TagEncoding::Direct => tag,
            TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
                let min_tag = niche_start;
                let max_tag = niche_start
                    .wrapping_add((niche_variants.end().0 - niche_variants.start().0) as u128);
                let variants = e.enum_variants(self.db());
                let untagged_variant_discr = self
                    .db()
                    .const_eval_discriminant(variants.variants[untagged_variant.0].0)
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
        ValueKind::Primitive(tag)
    }

    fn store_tag_and_get_variant_layout<'b>(
        &mut self,
        variant_id: VariantId,
        layout: &'b Layout,
        place: Place<'db>,
    ) -> &'b Layout {
        match &layout.variants {
            hir_def::layout::Variants::Empty => unreachable!("empty variants"),
            hir_def::layout::Variants::Single { .. } => &layout,
            hir_def::layout::Variants::Multiple { tag, tag_encoding, tag_field, variants } => {
                let hir_def::VariantId::EnumVariantId(enum_variant_id) = variant_id else {
                    panic!("multiple variants in non-enum")
                };
                let variant_idx = enum_variant_id.lookup(self.db()).index as usize;
                let rustc_enum_variant_idx = RustcEnumVariantIdx(variant_idx);
                let discr_typ = translate_scalar_type(*tag, self.isa());
                // FIXME error handling
                let mut discriminant = self
                    .db()
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
                    let field_offset = layout.fields.offset(tag_field.index());
                    let discriminant = ValueKind::Primitive(
                        self.builder.ins().iconst(discr_typ, discriminant as i64),
                    );
                    self.translate_place_store_with_offset(
                        place,
                        // HACK the type doesn't really matter here
                        Ty::new_uint(self.compilation.interner, UintTy::U128),
                        field_offset.bytes_usize() as i32,
                        discriminant,
                    );
                }
                &variants[rustc_enum_variant_idx]
            }
        }
    }

    fn translate_array_len(&mut self, place: Place<'db>) -> ValueKind {
        let (place_kind, ty) = self.translate_place_with_ty(place);
        match ty.kind() {
            TyKind::Array(_, len) => self.translate_const(&len).0,
            TyKind::Slice(_) => {
                let meta = match place_kind {
                    PlaceKind::Addr(_, Some(meta)) => meta,
                    _ => panic!("slice is not unsized: {:?}", place_kind),
                };
                ValueKind::Primitive(meta)
            }
            _ => panic!("calling array len for non-array/slice {:?}", ty),
        }
    }
}

fn is_extern_func(db: &dyn HirDatabase, func_id: FunctionId) -> bool {
    let parent = func_id.lookup(db).container;
    matches!(parent, hir_def::ItemContainerId::ExternBlockId(_))
}

fn const_to_int(n: &Const) -> u64 {
    let ConstKind::Value(c) = &**n.inner() else { panic!("non-concrete const") };
    let inner = c.value.inner();
    let mm = &inner.memory_map;
    let bytes = &inner.memory;
    assert!(matches!(mm, MemoryMap::Empty));
    let mut data: [u8; 8] = [0; 8];
    data[0..bytes.len()].copy_from_slice(&bytes);
    u64::from_le_bytes(data)
}

/// Walks the full MIR body to find locals that are referenced, meaning that
/// they need to be stored on the stack.
fn find_referenced_locals<'db>(body: &MirBody<'db>) -> FxHashSet<LocalId<'db>> {
    let mut found = FxHashSet::default();
    for (_, block) in body.basic_blocks.iter() {
        for stmt in &block.statements {
            if let StatementKind::Assign(_, Rvalue::Ref(_, pl)) = &stmt.kind {
                let local = get_direct_local(pl, &body.projection_store);
                if let Some(local) = local {
                    found.insert(local);
                }
            }
        }
    }

    fn get_direct_local<'db>(
        pl: &hir_ty::mir::Place<'db>,
        projection_store: &hir_ty::mir::ProjectionStore<'db>,
    ) -> Option<LocalId<'db>> {
        let mut local = Some(pl.local);
        for elem in pl.projection.lookup(projection_store) {
            match elem {
                ProjectionElem::Deref => {
                    local = None;
                }
                ProjectionElem::Field(_)
                | ProjectionElem::ClosureField(_)
                | ProjectionElem::Index(_)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. }
                | ProjectionElem::OpaqueCast(_) => {}
            }
        }
        local
    }

    found
}
fn bytes_to_imm64(bytes: &[u8]) -> Imm64 {
    let mut data: [u8; 8] = [0; 8];
    data[0..bytes.len().min(8)].copy_from_slice(&bytes[0..bytes.len().min(8)]);
    Imm64::new(i64::from_le_bytes(data))
}

impl ValueKind {
    fn assert_primitive(&self) -> Value {
        match *self {
            ValueKind::Primitive(val) => val,
            _ => panic!("non-primitive value"),
        }
    }
}

#[salsa::interned(debug)]
pub struct MonoFunction {
    func: FunctionId,
    subst: GenericArgs<'db>,
}

fn translate_signature<'db>(
    sig: PolyFnSig<'db>,
    isa: &dyn TargetIsa,
    db: &'db dyn HirDatabase,
    krate: Crate,
) -> Signature {
    let call_conv = match sig.abi() {
        hir_ty::FnAbi::Rust => CallConv::Fast,
        hir_ty::FnAbi::C => isa.default_call_conv(),
        _ => panic!("unsupported ABI: {:?}", sig.abi()),
    };
    // TODO handle C abi better
    let mut signature = Signature::new(call_conv);
    let sig = sig.skip_binder(); // FIXME can we just skip?
    let env = TraitEnvironment::empty(krate);
    signature.params.extend(
        sig.inputs()
            .iter()
            .flat_map(|ty| {
                let layout = db.layout_of_ty(ty.clone(), env.clone()).expect("failed layout");
                match layout.backend_repr {
                    BackendRepr::Scalar(scalar) => {
                        SmallVec::from_buf([translate_scalar_type(scalar, isa)])
                    }
                    BackendRepr::ScalarPair(sc1, sc2) => SmallVec::from_vec(vec![
                        translate_scalar_type(sc1, isa),
                        translate_scalar_type(sc2, isa),
                    ]),
                    BackendRepr::Memory { sized: true } if layout.size.bytes() == 0 => {
                        SmallVec::new()
                    }
                    BackendRepr::Memory { sized: true } => SmallVec::from_buf([isa.pointer_type()]),
                    _ => panic!("unsupported abi in function param: {:?}", layout.backend_repr),
                }
            })
            .map(AbiParam::new),
    );
    let layout = db.layout_of_ty(sig.output().clone(), env.clone()).expect("failed layout");
    signature.returns.extend(
        match layout.backend_repr {
            BackendRepr::Scalar(scalar) => SmallVec::from_buf([translate_scalar_type(scalar, isa)]),
            BackendRepr::ScalarPair(sc1, sc2) => SmallVec::from_vec(vec![
                translate_scalar_type(sc1, isa),
                translate_scalar_type(sc2, isa),
            ]),
            BackendRepr::Memory { sized: true } if layout.size.bytes() == 0 => SmallVec::new(),
            BackendRepr::Memory { sized: true } => SmallVec::from_buf([isa.pointer_type()]),
            _ => panic!("unsupported abi in function return: {:?}", layout.backend_repr),
        }
        .into_iter()
        .map(AbiParam::new),
    );
    signature
}

fn translate_scalar_type(scalar: Scalar, isa: &dyn TargetIsa) -> Type {
    use hir_def::layout::{AddressSpace, Float, Primitive};
    let value = scalar.primitive();
    match value {
        Primitive::Int(int, _) => {
            Type::int_with_byte_size(int.size().bytes_usize() as u16).unwrap()
        }
        Primitive::Float(Float::F16) => types::F16,
        Primitive::Float(Float::F32) => types::F32,
        Primitive::Float(Float::F64) => types::F64,
        Primitive::Float(Float::F128) => types::F128,
        Primitive::Pointer(AddressSpace::ZERO) => isa.pointer_type(),
        Primitive::Pointer(_) => panic!("unsupported address space"),
    }
}

fn return_slot<'db>() -> LocalId<'db> {
    LocalId::from_raw(la_arena::RawIdx::from(0))
}

fn get_int_ty(ty: &Ty, isa: &dyn TargetIsa) -> Option<(u64, bool)> {
    Some(match ty.kind() {
        TyKind::Int(int_ty) => (int_ty.bit_width().unwrap_or(isa.pointer_bits() as u64) / 8, true),
        TyKind::Uint(uint_ty) => {
            (uint_ty.bit_width().unwrap_or(isa.pointer_bits() as u64) / 8, false)
        }
        _ => return None,
    })
}

fn scalar_pair_calculate_b_offset(
    tdl: &TargetDataLayout,
    a_scalar: Scalar,
    b_scalar: Scalar,
) -> Offset32 {
    let b_offset = a_scalar.size(tdl).align_to(b_scalar.align(tdl).abi);
    Offset32::new(b_offset.bytes().try_into().unwrap())
}

/// Is a pointer to this type a fat ptr?
pub(crate) fn has_ptr_meta(_db: &dyn HirDatabase, ty: Ty) -> bool {
    // if ty.is_sized(tcx, ParamEnv::reveal_all()) {
    //     return false;
    // }

    // let tail = tcx.struct_tail_for_codegen(ty, ParamEnv::reveal_all());
    let tail = ty; // FIXME handle this properly
    match tail.kind() {
        TyKind::Foreign(..) => false,
        TyKind::Str | TyKind::Slice(..) | TyKind::Dynamic(..) => true,
        _ => false,
        // _ => bug!("unexpected unsized tail: {:?}", tail),
    }
}
