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
    codegen,
    frontend::Switch,
    prelude::{
        settings, types, AbiParam, Block, Configurable, EntityRef, FunctionBuilder,
        FunctionBuilderContext, InstBuilder, IntCC, Signature, Type, Value, Variable,
    },
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use hir_def::FunctionId;
use hir_ty::{
    db::HirDatabase,
    mir::{
        BasicBlockId, BinOp, LocalId, MirBody, Operand, Place, Rvalue, StatementKind,
        TerminatorKind,
    },
    Interner, Substitution, Ty, TyKind,
};
use la_arena::ArenaMap;
use rustc_hash::FxHashMap;
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

        let mut module = JITModule::new(builder);
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

        // FIXME allow all signatures
        self.ctx.func.signature.returns.push(AbiParam::new(types::I32));

        let builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        let body = db
            .monomorphized_mir_body(
                func_id.into(),
                Substitution::empty(Interner),
                db.trait_environment(func_id.into()),
            )
            .map_err(|e| anyhow!("failed to lower MIR: {:?}", e))?;

        let mut translator = FunctionTranslator {
            db,
            body: &body,
            variables: ArenaMap::new(),
            blocks: ArenaMap::new(),
            builder,
            module: &mut self.module,
            shims: &mut self.shims,
            engine: jit_engine,
        };

        translator.create_blocks();
        translator
            .builder
            .append_block_params_for_function_params(translator.blocks[body.start_block]);

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
    variables: ArenaMap<LocalId, Variable>,
    blocks: ArenaMap<BasicBlockId, Block>,
    builder: FunctionBuilder<'a>,
    module: &'a mut JITModule,
    shims: &'a mut FxHashMap<FunctionId, FuncId>,
    engine: &'a JitEngine<'a>,
}

impl<'a> FunctionTranslator<'a> {
    fn get_shim(&mut self, func: FunctionId) -> FuncId {
        if let Some(shim) = self.shims.get(&func) {
            return *shim;
        }

        let mut ctx = self.module.make_context(); // FIXME share
                                                  // FIXME allow any signature
        ctx.func.signature.returns.push(AbiParam::new(types::I32));

        let sig = ctx.func.signature.clone();

        let id = self.module.declare_anonymous_function(&ctx.func.signature).unwrap(); // FIXME

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
        // FIXME can we pass engine and address of ensure_function as "global value" / "VM context pointer"?
        let arg1 = builder.ins().iconst(ptr, self.engine as *const JitEngine as i64);
        let arg2 = builder.ins().iconst(types::I32, func.as_intern_id().as_u32() as i64);
        let callee = builder.ins().iconst(ptr, ensure_function as usize as i64);
        let call = builder.ins().call_indirect(sig_ref, callee, &[arg1, arg2]);
        let result = builder.inst_results(call)[0];

        let sig_ref = builder.import_signature(sig);
        let call = builder.ins().call_indirect(sig_ref, result, &[]);
        let rvals = builder.inst_results(call).to_vec();
        builder.ins().return_(&rvals);
        // tail call doesn't work in SystemV callconv, but we might want another one anyway?
        // builder.ins().return_call_indirect(sig_ref, result, &[]);
        builder.seal_all_blocks();
        builder.finalize();
        self.module.define_function(id, &mut ctx).unwrap();
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
                let discr = self.translate_operand(discr);
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

                let args: Vec<_> = args.iter().map(|a| self.translate_operand(a)).collect();
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
                    let result = self.builder.inst_results(call)[0];
                    let projection = destination.projection.lookup(&self.body.projection_store);
                    if !projection.is_empty() {
                        panic!("unsupported projection");
                    }
                    let variable = self.get_variable(destination.local);
                    self.builder.def_var(variable, result);
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
        let return_var = self.builder.use_var(self.variables[return_slot()]);
        self.builder.ins().return_(&[return_var]);
    }

    fn translate_stmt(&mut self, stmt: &hir_ty::mir::Statement) {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                self.translate_stmt_assign(place, rvalue);
            }
            StatementKind::StorageLive(_local) => {
                // FIXME anything to do here?
            }
            StatementKind::StorageDead(_local) => {
                // FIXME anything to do here?
            }
            StatementKind::FakeRead(_place) => {
                // FIXME anything to do here?
            }
            _ => panic!("unsupported stmt kind: {:?}", stmt.kind),
        }
    }

    fn translate_stmt_assign(&mut self, place: &hir_ty::mir::Place, rvalue: &Rvalue) {
        let projection = place.projection.lookup(&self.body.projection_store);
        if !projection.is_empty() {
            panic!("unsupported projection");
        }
        let variable = self.get_variable(place.local);
        let value = self.translate_rvalue(rvalue);
        self.builder.def_var(variable, value);
    }

    fn get_type(&mut self, ty: Ty) -> Type {
        translate_type(ty)
    }

    fn get_variable(&mut self, local: LocalId) -> Variable {
        let typ = self.body.locals[local].ty.clone();
        let variable = *self.variables.entry(local).or_insert_with(|| {
            let var = Variable::new(local.into_raw().into_u32() as usize);
            let typ = translate_type(typ);
            self.builder.declare_var(var, typ);
            var
        });
        variable
    }

    fn translate_rvalue(&mut self, rvalue: &Rvalue) -> Value {
        let value = match rvalue {
            Rvalue::Use(operand) => self.translate_operand(operand),
            Rvalue::CheckedBinaryOp(binop, left, right) => {
                self.translate_checked_binop(binop, left, right)
            }
            _ => panic!("unsupported rvalue: {:?}", rvalue),
        };
        value
    }

    fn translate_operand(&mut self, operand: &Operand) -> Value {
        match operand {
            Operand::Constant(konst) => self.translate_const(konst),
            Operand::Copy(place) => self.translate_place_copy(place),
            _ => panic!("unsupported operand: {:?}", operand),
        }
    }

    fn translate_const(&mut self, konst: &chalk_ir::Const<Interner>) -> Value {
        let ty = konst.data(Interner).ty.clone();
        let chalk_ir::ConstValue::Concrete(c) = &konst.data(Interner).value else {
            panic!("evaluating non concrete constant");
        };
        match &c.interned {
            hir_ty::ConstScalar::Bytes(bytes, _mm) => {
                let typ = translate_type(ty);
                let mut data: [u8; 8] = [0; 8];
                data[0..bytes.len()].copy_from_slice(&bytes);
                self.builder.ins().iconst(typ, i64::from_le_bytes(data))
            }
            hir_ty::ConstScalar::UnevaluatedConst(_, _) => panic!("unevaluated const"),
            hir_ty::ConstScalar::Unknown => panic!("unknown const scalar"),
        }
    }

    fn translate_place_copy(&mut self, place: &Place) -> Value {
        let variable = self.get_variable(place.local);
        let projection = place.projection.lookup(&self.body.projection_store);
        if !projection.is_empty() {
            panic!("unsupported projection");
        }
        self.builder.use_var(variable)
    }

    fn translate_checked_binop(&mut self, binop: &BinOp, left: &Operand, right: &Operand) -> Value {
        let left = self.translate_operand(left);
        let right = self.translate_operand(right);
        match binop {
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
        }
    }
}

fn translate_type(ty: Ty) -> Type {
    use chalk_ir::{FloatTy, IntTy, TyKind, UintTy};
    use hir_ty::Scalar;
    match ty.kind(Interner) {
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
        _ => panic!("unsupported ty: {:?}", ty),
    }
}

fn return_slot() -> LocalId {
    LocalId::from_raw(la_arena::RawIdx::from(0))
}
