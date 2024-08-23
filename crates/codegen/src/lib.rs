#[cfg(test)]
mod test_db;
#[cfg(test)]
mod tests;

use anyhow::{anyhow, Context};
use cranelift::{
    codegen,
    prelude::{settings, AbiParam, Configurable, EntityRef, FunctionBuilder, FunctionBuilderContext, InstBuilder, Type, Variable},
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, Linkage, Module};
use hir_def::FunctionId;
use hir_ty::{db::HirDatabase, mir::{BasicBlockId, LocalId, MirBody, Operand, Rvalue, StatementKind, TerminatorKind}, Interner, Substitution};
use la_arena::ArenaMap;

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
}

impl Default for Jit {
    fn default() -> Self {
        let mut flag_builder = settings::builder();
        flag_builder.set("use_colocated_libcalls", "false").unwrap();
        flag_builder.set("is_pic", "false").unwrap();
        let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
            panic!("host machine is not supported: {}", msg);
        });
        let isa = isa_builder.finish(settings::Flags::new(flag_builder)).unwrap();
        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        // builder.hotswap(true); // TODO what's PIC code?

        let module = JITModule::new(builder);
        Self {
            builder_context: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            data_description: DataDescription::new(),
            module,
        }
    }
}

impl Jit {
    fn compile(
        &mut self,
        db: &dyn HirDatabase,
        func_id: FunctionId,
    ) -> Result<*const u8, anyhow::Error> {
        // 1. get MIR for func
        // 2. generate code, compiling dependent functions as necessary

        let t_i32 = Type::int(32).unwrap();
        self.ctx.func.signature.returns.push(AbiParam::new(t_i32));

        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

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
            builder,
            module: &mut self.module,
        };

        translator.compile_mir_block(body.start_block);

        // let val = builder.ins().iconst(t_i32, 4);
        // builder.ins().return_(&[val]);
        // builder.finalize();

        let id = self.module.declare_function("test", Linkage::Export, &self.ctx.func.signature)
            .context("failed to declare function")?;

        // Define the function to jit. This finishes compilation, although
        // there may be outstanding relocations to perform. Currently, jit
        // cannot finish relocations until all functions to be called are
        // defined. For this toy demo for now, we'll just finalize the
        // function below.
        self.module
            .define_function(id, &mut self.ctx)
            .context("failed to define function")?;

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
    builder: FunctionBuilder<'a>,
    module: &'a mut JITModule,
}

impl<'a> FunctionTranslator<'a> {
    fn compile_mir_block(&mut self, block_id: BasicBlockId) {
        eprintln!("locals: {:?}", self.body.locals);
        let block = &self.body.basic_blocks[block_id];
        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign(place, rvalue) => {
                    let projection = place.projection.lookup(&self.body.projection_store);
                    if !projection.is_empty() {
                        panic!("unsupported projection");
                    }
                    let variable = *self.variables.entry(place.local).or_insert_with(|| {
                        let var = Variable::new(place.local.into_raw().into_u32() as usize);
                        let t_i32 = Type::int(32).unwrap();
                        self.builder.declare_var(var, t_i32);
                        var
                    });
                    let value = match rvalue {
                        Rvalue::Use(operand) => {
                            match operand {
                                Operand::Constant(konst) => {
                                    let _ty = &konst.data(Interner).ty;
                                    let chalk_ir::ConstValue::Concrete(c) = &konst.data(Interner).value else {
                                        panic!("evaluating non concrete constant");
                                    };
                                    match &c.interned {
                                        hir_ty::ConstScalar::Bytes(bytes, _mm) => {
                                            let t_i32 = Type::int(32).unwrap();
                                            let bytes: &[u8; 4] = bytes.as_ref().try_into().unwrap();
                                            self.builder.ins().iconst(t_i32, i32::from_le_bytes(*bytes) as i64)
                                        },
                                        hir_ty::ConstScalar::UnevaluatedConst(_, _) => panic!("unevaluated const"),
                                        hir_ty::ConstScalar::Unknown => panic!("unknown const scalar"),
                                    }
                                },
                                _ => panic!("unsupported operand: {:?}", operand),
                            }
                        },
                        _ => panic!("unsupported rvalue: {:?}", rvalue),
                    };
                    self.builder.def_var(variable, value);
                }
                _ => panic!("unsupported stmt kind: {:?}", stmt.kind),
            }
        }
        let terminator = block.terminator.as_ref().unwrap();
        match terminator.kind {
            TerminatorKind::Return => {
                let return_var = self.builder.use_var(self.variables[return_slot()]);
                self.builder.ins().return_(&[return_var]);
            }
            _ => panic!("unsupported terminator kind: {:?}", terminator.kind),
        }
    }
}

fn return_slot() -> LocalId {
    LocalId::from_raw(la_arena::RawIdx::from(0))
}
