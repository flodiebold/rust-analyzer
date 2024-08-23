#[cfg(test)]
mod test_db;
#[cfg(test)]
mod tests;

use anyhow::{anyhow, Context};
use cranelift::{
    codegen,
    prelude::{settings, AbiParam, Configurable, FunctionBuilder, FunctionBuilderContext, InstBuilder, Type},
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, Linkage, Module};
use hir_def::FunctionId;
use hir_ty::db::HirDatabase;

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
        func: FunctionId,
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

        let val = builder.ins().iconst(t_i32, 4);
        builder.ins().return_(&[val]);
        builder.finalize();

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
