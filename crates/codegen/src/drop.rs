use cranelift::prelude::{AbiParam, FunctionBuilder, FunctionBuilderContext, InstBuilder};
use cranelift_module::{FuncId, Module};
use hir_def::{
    AssocItemId, FunctionId, lang_item::{LangItem, lang_item},
};
use hir_expand::name::Name;
use hir_ty::{
    TraitEnvironment,
    db::HirDatabase,
    mir::Place,
    next_solver::{GenericArgs, Ty, TyKind},
};

use crate::{FunctionTranslator, MonoFunction};

impl<'a, 'db: 'a> FunctionTranslator<'a, 'db> {
    pub(crate) fn translate_drop(&mut self, place: Place<'db>) {
        let (kind, ty) = self.translate_place_with_ty(place);

        let drop_in_place = self.get_drop_in_place_func(ty);

        if let Some(func) = drop_in_place {
            let addr = self.translate_place_kind_addr(kind);
            let func_ref = self.module.declare_func_in_func(func, &mut self.builder.func);
            self.builder.ins().call(func_ref, &[addr]);
        }
    }

    fn get_drop_in_place_func(&mut self, ty: Ty<'db>) -> Option<FuncId> {
        if !needs_drop(self.db, &ty) {
            return None;
        }
        if let Some(func) = self.drop_in_place_funcs.get(&Some(ty.clone())) {
            return Some(*func);
        }
        let mut ctx = self.module.make_context(); // FIXME share (extract ShimCompiler?)
        ctx.func.signature.params.push(AbiParam::new(self.pointer_type));

        // FIXME can this legitimately fail?
        let id = self
            .module
            .declare_anonymous_function(&ctx.func.signature)
            .expect("failed to declare anonymous function for shim");

        self.drop_in_place_funcs.insert(Some(ty.clone()), id);

        let mut builder_context = FunctionBuilderContext::new(); // FIXME share
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);

        let block = builder.create_block();
        builder.append_block_params_for_function_params(block);
        builder.switch_to_block(block);
        let param = builder.block_params(block)[0];

        // call drop if needed
        let drop_fn = get_drop_fn(self.db, &self.env);
        if let Some(drop_fn) = drop_fn {
            let fn_subst = GenericArgs::new_from_iter(self.interner, [ty.into()]);
            let (drop_fn_impl, subst) =
                self.db.lookup_impl_method(self.env.clone(), drop_fn, fn_subst.clone());
            if drop_fn_impl != drop_fn {
                // drop is actually implemented
                let func = self.get_shim(MonoFunction::new(self.db, drop_fn_impl, subst));
                let func_ref = self.module.declare_func_in_func(func, &mut builder.func);
                builder.ins().call(func_ref, &[param]);
            }
        }

        // TODO: drop fields etc

        builder.ins().return_(&[]);

        builder.seal_all_blocks();
        builder.finalize();
        // FIXME can this legitimately fail?
        self.module
            .define_function(id, &mut ctx)
            .expect("failed to compile drop_in_place function");
        Some(id)
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
