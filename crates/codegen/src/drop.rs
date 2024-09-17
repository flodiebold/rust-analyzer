use cranelift::{
    codegen::Context,
    prelude::{AbiParam, FunctionBuilder, FunctionBuilderContext, InstBuilder, Type},
};
use cranelift_jit::JITModule;
use cranelift_module::{FuncId, Module};
use hir_def::{
    AssocItemId, FunctionId,
    lang_item::{LangItem, lang_item},
};
use hir_expand::name::Name;
use hir_ty::{
    TraitEnvironment,
    db::HirDatabase,
    mir::Place,
    next_solver::{DbInterner, GenericArgs, Ty, TyKind},
};
use rustc_hash::FxHashMap;
use triomphe::Arc;

use crate::{CompilationProcess, FunctionTranslator, MonoFunction};

impl<'a, 'db: 'a> FunctionTranslator<'a, 'db> {
    pub(crate) fn translate_drop(&mut self, place: Place<'db>) {
        let (kind, ty) = self.translate_place_with_ty(place);

        if needs_drop(self.db(), &ty) {
            let drop_in_place = self.compilation.declare_drop_shim(ty);
            let addr = self.translate_place_kind_addr(kind);
            let func_ref =
                self.compilation.module.declare_func_in_func(drop_in_place, &mut self.builder.func);
            self.builder.ins().call(func_ref, &[addr]);
        }
    }
}

impl<'a, 'db> CompilationProcess<'a, 'db> {
    pub(super) fn compile_drop_shim(
        &mut self,
        id: FuncId,
        ty: Ty<'db>,
        ctx: &mut Context,
        builder_context: &mut FunctionBuilderContext,
    ) {
        ctx.func.signature.params.push(AbiParam::new(self.module.isa().pointer_type()));
        let mut builder = FunctionBuilder::new(&mut ctx.func, builder_context);
        let env = TraitEnvironment::empty(self.krate);
        let pointer_type = self.module.isa().pointer_type();
        super::reborrow_compilation!(self, compilation);
        let mut drop_shim_builder = DropShimBuilder { compilation, env, builder, pointer_type };

        drop_shim_builder.fill_drop_in_place(ty);

        drop_shim_builder.builder.seal_all_blocks(); // FIXME do this better?
        drop_shim_builder.builder.finalize();

        // FIXME can this legitimately fail?
        self.module.define_function(id, ctx).expect("failed to compile drop_in_place function");
        self.module.clear_context(ctx);
    }
}

struct DropShimBuilder<'a, 'db> {
    compilation: CompilationProcess<'a, 'db>,
    env: Arc<TraitEnvironment<'db>>,
    builder: FunctionBuilder<'a>,
    pointer_type: Type,
}

impl<'a, 'db> DropShimBuilder<'a, 'db> {
    fn db(&self) -> &'db dyn HirDatabase {
        self.compilation.db()
    }
    fn fill_drop_in_place(&mut self, ty: Ty<'db>) {
        let block = self.builder.create_block();
        self.builder.append_block_params_for_function_params(block);
        self.builder.switch_to_block(block);
        let param = self.builder.block_params(block)[0];

        // call drop if needed
        let drop_fn = get_drop_fn(self.db(), &self.env);
        if let Some(drop_fn) = drop_fn {
            let fn_subst = GenericArgs::new_from_iter(self.compilation.interner, [ty.into()]);
            let (drop_fn_impl, subst) =
                self.db().lookup_impl_method(self.env.clone(), drop_fn, fn_subst.clone());
            if drop_fn_impl != drop_fn {
                // drop is actually implemented
                let func = self.compilation.declare_call_shim(MonoFunction::new(
                    self.db(),
                    drop_fn_impl,
                    subst,
                ));
                let func_ref =
                    self.compilation.module.declare_func_in_func(func, &mut self.builder.func);
                self.builder.ins().call(func_ref, &[param]);
            }
        }

        // TODO: drop fields etc

        self.builder.ins().return_(&[]);
    }
}

pub(super) fn needs_drop(_db: &dyn HirDatabase, ty: &Ty) -> bool {
    // TODO more precise logic
    match ty.inner().internee {
        TyKind::Adt(_, _) => true,
        TyKind::Tuple(_) => true,
        TyKind::Array(_, _) => true,
        TyKind::Slice(_) => true,
        TyKind::Closure(_, _) => true,
        TyKind::Coroutine(_, _) => true,
        TyKind::Dynamic(_, _) => true,
        TyKind::Pat(_, _)
        | TyKind::Param(_)
        | TyKind::Error(_)
        | TyKind::UnsafeBinder(_)
        | TyKind::CoroutineClosure(_, _)
        | TyKind::CoroutineWitness(_, _)
        | TyKind::Placeholder(_)
        | TyKind::Alias(_, _)
        | TyKind::Bound(_, _)
        | TyKind::Infer(_) => unreachable!("{:?}", ty),
        TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Bool
        | TyKind::Never
        | TyKind::RawPtr(_, _)
        | TyKind::Ref(_, _, _)
        | TyKind::FnDef(_, _)
        | TyKind::Str
        | TyKind::Foreign(_)
        | TyKind::FnPtr(_, _) => false,
    }
}

fn get_drop_in_place_fn(db: &dyn HirDatabase, env: &TraitEnvironment) -> Option<FunctionId> {
    lang_item(db, env.krate, LangItem::DropInPlace).and_then(|l| l.as_function())
}

fn get_drop_fn(db: &dyn HirDatabase, env: &TraitEnvironment) -> Option<FunctionId> {
    let drop_trait = lang_item(db, env.krate, LangItem::Drop).and_then(|l| l.as_trait())?;
    match drop_trait.trait_items(db).assoc_item_by_name(&Name::new_root("drop")) {
        Some(AssocItemId::FunctionId(f)) => Some(f),
        _ => None,
    }
}
