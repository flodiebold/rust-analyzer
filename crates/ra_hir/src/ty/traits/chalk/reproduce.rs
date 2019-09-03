use crate::{Crate, HasGenericParams, HirDatabase, HirDisplay, ImplBlock, Trait, TypeCtor};

pub(crate) fn chalk_reproduce_mode() -> bool {
    match std::env::var("RA_REPRODUCE_CHALK") {
        Ok(s) => s == "1",
        Err(_) => false,
    }
}

pub(super) fn reproduce_trait(db: &impl HirDatabase, _krate: Crate, trait_: Trait) {
    let name = trait_.name(db).expect("trait name missing for reproduce mode");
    let generic_params = trait_.generic_params(db);
    print!("trait {}", name);
    if generic_params.params.len() > 1 {
        print!("<");
        let mut first = true;
        for param in &generic_params.params[1..] {
            if !first {
                print!(", ");
            } else {
                first = false;
            }
            print!("{}", param.name);
        }
        print!(">");
    }
    print!(" {{");
    let mut first = true;
    for item in trait_.items(db) {
        match item {
            crate::traits::TraitItem::TypeAlias(t) => {
                if first {
                    println!();
                    first = false;
                }
                println!("  type {};", t.name(db));
            }
            _ => {}
        }
    }
    println!("}}");
    // TODO add bounds
}

pub(super) fn reproduce_struct(db: &impl HirDatabase, type_ctor: TypeCtor) {
    if let TypeCtor::Adt(adt) = type_ctor {
        let name = match adt {
            crate::AdtDef::Struct(s) => s.name(db),
            crate::AdtDef::Union(u) => u.name(db),
            crate::AdtDef::Enum(e) => e.name(db),
        }
        .expect("ADT without name for chalk reproduce mode");
        let generic_params = adt.generic_params(db);
        print!("struct {}", name);
        if !generic_params.params.is_empty() {
            print!("<");
            let mut first = true;
            for param in &generic_params.params {
                if !first {
                    print!(", ");
                } else {
                    first = false;
                }
                print!("{}", param.name);
            }
            println!(">;");
        } else {
            println!(";");
        }
        // TODO add bounds
    }
}

pub(super) fn reproduce_impl(db: &impl HirDatabase, impl_block: ImplBlock) {
    let trait_ref = impl_block
        .target_trait_ref(db)
        .expect("unresolved impl block trait ref in chalk reproduce mode");
    print!("impl");
    let generic_params = impl_block.generic_params(db);
    if !generic_params.params.is_empty() {
        print!("<");
        let mut first = true;
        for param in &generic_params.params {
            if !first {
                print!(", ");
            } else {
                first = false;
            }
            print!("{}", param.name);
        }
        print!(">");
    }
    let name = trait_ref.trait_.name(db).expect("no name for trait in chalk reproduce mode");
    print!(" {}", name);
    if trait_ref.substs.len() > 1 {
        print!("<");
        let mut first = true;
        for arg in &trait_ref.substs[1..] {
            if !first {
                print!(", ");
            } else {
                first = false;
            }
            print!("{}", arg.display(db));
        }
        print!(">");
    }
    print!(" for {}", trait_ref.substs[0].display(db));
    let mut first = true;
    let generic_predicates = db.generic_predicates(impl_block.into());
    for pred in generic_predicates.iter() {
        if first {
            print!(" where ");
            first = false;
        } else {
            print!(", ");
        }
        print!("{}", pred.display(db));
    }
    print!(" {{");
    let mut first = true;
    for item in impl_block.items(db) {
        match item {
            crate::ImplItem::TypeAlias(t) => {
                if first {
                    println!();
                    first = false;
                }
                println!("  type {} = {};", t.name(db), t.ty(db).display(db));
            }
            _ => {}
        }
    }
    println!("}}");
}
