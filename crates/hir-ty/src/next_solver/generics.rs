use super::{DbInterner, DefId, GenericArg};

#[derive(Debug)]
pub struct Generics {
    pub parent: Option<DefId>,

    pub own_params: Vec<GenericParamDef>,
}

#[derive(Debug)]
pub struct GenericParamDef {
    pub def_id: DefId,
    pub index: u32,

    pub kind: GenericParamDefKind,
}

#[derive(Debug)]
pub enum GenericParamDefKind {
    Lifetime,
    Type,
    Const,
}

impl rustc_type_ir::inherent::GenericsOf<DbInterner> for Generics {
    fn count(&self) -> usize {
        todo!()
    }
}

impl GenericParamDef {
    pub fn to_error(&self, interner: DbInterner) -> GenericArg {
        todo!()
    }
}

impl DbInterner {
    pub fn mk_param_from_def(self, param: &GenericParamDef) -> GenericArg {
        todo!()
    }
}
