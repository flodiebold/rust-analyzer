use chalk_ir::Substitution;
use cranelift::prelude::{AbiParam, FunctionBuilder, FunctionBuilderContext, InstBuilder};
use cranelift_module::{FuncId, Module};
use hir_def::{lang_item::LangItem, AssocItemId, FunctionId, TraitId};
use hir_expand::name::Name;
use hir_ty::{
    db::HirDatabase,
    mir::{BasicBlock, MirBody, MirSpan, Place, ProjectionStore, Terminator, TerminatorKind},
    Interner, TraitEnvironment, Ty,
};
use la_arena::{Arena, ArenaMap};

use crate::{CodegenDatabase, FunctionTranslator, MonoFunction, MonoFunctionId};

impl<'a> FunctionTranslator<'a> {
    pub(crate) fn translate_drop(&mut self, place: &Place) {
        let (kind, ty) = self.translate_place_with_ty(place);

        let drop_in_place = self.get_drop_in_place_func(ty);

        if let Some(func) = drop_in_place {
            let addr = self.translate_place_kind_addr(kind);
            let func_ref = self.module.declare_func_in_func(func, &mut self.builder.func);
            self.builder.ins().call(func_ref, &[addr]);
        }
    }

    fn get_drop_in_place_func(&mut self, ty: Ty) -> Option<FuncId> {
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
        let drop_fn = get_drop_fn(self.db.upcast(), &self.env);
        if let Some(drop_fn) = drop_fn {
            let fn_subst = Substitution::from1(Interner, ty.clone());
            let (drop_fn_impl, subst) =
                self.db.lookup_impl_method(self.env.clone(), drop_fn, fn_subst.clone());
            if drop_fn_impl != drop_fn {
                // drop is actually implemented
                let func = self.get_shim(
                    self.db.intern_mono_function(MonoFunction { func: drop_fn_impl, subst }),
                );
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

pub(super) fn needs_drop(_db: &dyn CodegenDatabase, ty: &Ty) -> bool {
    // TODO more precise logic
    match ty.kind(Interner) {
        chalk_ir::TyKind::Adt(_, _) => true,
        chalk_ir::TyKind::Tuple(_, _) => true,
        chalk_ir::TyKind::Array(_, _) => true,
        chalk_ir::TyKind::Slice(_) => true,
        chalk_ir::TyKind::Closure(_, _) => true,
        chalk_ir::TyKind::Coroutine(_, _) => true,
        chalk_ir::TyKind::Dyn(_) => true,
        chalk_ir::TyKind::AssociatedType(_, _)
        | chalk_ir::TyKind::CoroutineWitness(_, _)
        | chalk_ir::TyKind::Error
        | chalk_ir::TyKind::Placeholder(_)
        | chalk_ir::TyKind::Alias(_)
        | chalk_ir::TyKind::BoundVar(_)
        | chalk_ir::TyKind::InferenceVar(_, _)
        | chalk_ir::TyKind::OpaqueType(_, _) => unreachable!("{:?}", ty),
        chalk_ir::TyKind::Scalar(_)
        | chalk_ir::TyKind::Never
        | chalk_ir::TyKind::Raw(_, _)
        | chalk_ir::TyKind::Ref(_, _, _)
        | chalk_ir::TyKind::FnDef(_, _)
        | chalk_ir::TyKind::Str
        | chalk_ir::TyKind::Foreign(_)
        | chalk_ir::TyKind::Function(_) => false,
    }
}

fn get_drop_in_place_fn(db: &dyn HirDatabase, env: &TraitEnvironment) -> Option<FunctionId> {
    db.lang_item(env.krate, LangItem::DropInPlace).and_then(|l| l.as_function())
}

fn get_drop_fn(db: &dyn HirDatabase, env: &TraitEnvironment) -> Option<FunctionId> {
    let drop_trait = db.lang_item(env.krate, LangItem::Drop).and_then(|l| l.as_trait())?;
    match db.trait_data(drop_trait).items.get(0) {
        Some((_, AssocItemId::FunctionId(f))) => Some(*f),
        _ => None,
    }
}
