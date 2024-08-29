use hir_def::db::DefDatabase;
use span::{Edition, EditionedFileId};
use test_fixture::WithFixture;

use crate::{test_db::TestDB, JitEngine};

fn eval_fn_i32(db: &TestDB, file_id: EditionedFileId) -> Result<i32, String> {
    let module_id = db.module_for_file(file_id);
    let def_map = module_id.def_map(db);
    let scope = &def_map[module_id.local_id].scope;
    let func_id = scope
        .declarations()
        .find_map(|x| match x {
            hir_def::ModuleDefId::FunctionId(x) => {
                if db.function_data(x).name.display(db, Edition::CURRENT).to_string() == "test" {
                    Some(x)
                } else {
                    None
                }
            }
            _ => None,
        })
        .expect("no test function found");

    let engine = JitEngine::new(db);
    let code = engine.jit.lock().unwrap().compile(db, func_id, &engine).unwrap();
    let func = unsafe { std::mem::transmute::<_, fn() -> i32>(code) };
    let result = func();
    Ok(result)
}

fn check_i32(ra_fixture: &str, expected: i32) {
    let (db, file_ids) = TestDB::with_many_files(ra_fixture);
    let file_id = *file_ids.last().unwrap();
    let x = eval_fn_i32(&db, file_id).unwrap();
    assert_eq!(x, expected);
}

#[test]
fn test_1() {
    check_i32(
        r#"
fn test() -> i32 { 4 }
"#,
        4,
    )
}

#[test]
fn test_2() {
    check_i32(
        r#"
fn test() -> i32 { 5 }
"#,
        5,
    )
}

#[test]
fn test_3() {
    check_i32(
        r#"
fn test() -> i32 {
    let x = 1;
    x
}
"#,
        1,
    )
}

#[test]
fn test_4() {
    check_i32(
        r#"
fn test() -> i32 { 1 + 4 }
"#,
        5,
    )
}

#[test]
fn test_function_call() {
    check_i32(
        r#"
fn foo() -> i32 { 4 }
fn test() -> i32 { 1 + foo() }
"#,
        5,
    )
}

#[test]
fn test_if_else() {
    check_i32(
        r#"
fn test() -> i32 { if true { 5 } else { 3 } }
"#,
        5,
    )
}

#[test]
fn test_match() {
    check_i32(
        r#"
fn test() -> i32 {
    match 3 {
        3 => 5,
        _ => 3,
    }
}
"#,
        5,
    )
}

#[test]
fn test_mut_assign() {
    check_i32(
        r#"
fn test() -> i32 {
    let mut x = 3;
    x = 5;
    x
}
"#,
        5,
    )
}

#[test]
fn test_while_loop() {
    check_i32(
        r#"
//- minicore: add
fn test() -> i32 {
    let mut x = 3;
    while x < 5 {
        x += 1;
    }
    x
}
"#,
        5,
    )
}

#[test]
fn test_function_param() {
    check_i32(
        r#"
fn foo(x: i32) -> i32 { x + 5 }
fn test() -> i32 { 1 + foo(7) }
"#,
        13,
    )
}

#[test]
fn test_ref() {
    check_i32(
        r#"
fn test() -> i32 {
    let x = 3;
    let r = &x;
    *r
}
"#,
        3,
    )
}

#[test]
fn test_mut_ref() {
    check_i32(
        r#"
fn test() -> i32 {
    let mut x = 3;
    let r = &mut x;
    *r = 5;
    x
}
"#,
        5,
    )
}

#[test]
fn test_mut_ref_through_func() {
    check_i32(
        r#"
fn mutate(r: &mut i32) { *r = 5; }
fn test() -> i32 {
    let mut x = 3;
    mutate(&mut x);
    x
}
"#,
        5,
    )
}
