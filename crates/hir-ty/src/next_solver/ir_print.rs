use rustc_type_ir::{self as ty, ir_print::IrPrint};

use super::interner::DbInterner;

impl IrPrint<ty::AliasTy<Self>> for DbInterner {
    fn print(t: &ty::AliasTy<Self>, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }

    fn print_debug(t: &ty::AliasTy<Self>, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl IrPrint<ty::AliasTerm<Self>> for DbInterner {
    fn print(t: &ty::AliasTerm<Self>, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }

    fn print_debug(t: &ty::AliasTerm<Self>, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}
impl IrPrint<ty::TraitRef<Self>> for DbInterner {
    fn print(t: &ty::TraitRef<Self>, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }

    fn print_debug(t: &ty::TraitRef<Self>, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}
impl IrPrint<ty::TraitPredicate<Self>> for DbInterner {
    fn print(t: &ty::TraitPredicate<Self>, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }

    fn print_debug(
        t: &ty::TraitPredicate<Self>,
        fmt: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        todo!()
    }
}
impl IrPrint<ty::ExistentialTraitRef<Self>> for DbInterner {
    fn print(
        t: &ty::ExistentialTraitRef<Self>,
        fmt: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        todo!()
    }

    fn print_debug(
        t: &ty::ExistentialTraitRef<Self>,
        fmt: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        todo!()
    }
}
impl IrPrint<ty::ExistentialProjection<Self>> for DbInterner {
    fn print(
        t: &ty::ExistentialProjection<Self>,
        fmt: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        todo!()
    }

    fn print_debug(
        t: &ty::ExistentialProjection<Self>,
        fmt: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        todo!()
    }
}
impl IrPrint<ty::ProjectionPredicate<Self>> for DbInterner {
    fn print(
        t: &ty::ProjectionPredicate<Self>,
        fmt: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        todo!()
    }

    fn print_debug(
        t: &ty::ProjectionPredicate<Self>,
        fmt: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        todo!()
    }
}
impl IrPrint<ty::NormalizesTo<Self>> for DbInterner {
    fn print(t: &ty::NormalizesTo<Self>, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }

    fn print_debug(
        t: &ty::NormalizesTo<Self>,
        fmt: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        todo!()
    }
}
impl IrPrint<ty::SubtypePredicate<Self>> for DbInterner {
    fn print(
        t: &ty::SubtypePredicate<Self>,
        fmt: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        todo!()
    }

    fn print_debug(
        t: &ty::SubtypePredicate<Self>,
        fmt: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        todo!()
    }
}
impl IrPrint<ty::CoercePredicate<Self>> for DbInterner {
    fn print(t: &ty::CoercePredicate<Self>, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }

    fn print_debug(
        t: &ty::CoercePredicate<Self>,
        fmt: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        todo!()
    }
}
impl IrPrint<ty::FnSig<Self>> for DbInterner {
    fn print(t: &ty::FnSig<Self>, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }

    fn print_debug(t: &ty::FnSig<Self>, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}
