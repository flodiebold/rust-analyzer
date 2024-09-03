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
#[ignore]
fn test_mut_ref_in_loop() {
    check_i32(
        r#"
fn test() -> i32 {
    let mut x = 3;
    let mut y = 0;
    while y < 2 {
        let r = &mut x;
        *r = *r + 1;
        y = y + 1;
    }
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

#[test]
fn test_raw_ptr() {
    check_i32(
        r#"
fn test() -> i32 {
    let mut x = 3;
    let r = &mut x as *mut i32;
    *r = 5;
    x
}
"#,
        5,
    )
}

#[test]
fn test_array_literal() {
    check_i32(
        r#"
//- minicore: index, slice
fn test() -> i32 {
    let a = [2i32, 3];
    a[0] + a[1]
}
"#,
        5,
    )
}

#[test]
fn test_slice() {
    check_i32(
        r#"
//- minicore: index, slice, coerce_unsized
fn test() -> i32 {
    let a: &[i32] = &[2, 3];
    a[0] + a[1]
}
"#,
        5,
    )
}

#[test]
fn test_array_assign() {
    check_i32(
        r#"
//- minicore: index, slice
fn test() -> i32 {
    let mut a = [2i32, 1];
    a[1] = 3;
    a[0] + a[1]
}
"#,
        5,
    )
}

#[test]
fn test_array_elem_ref() {
    check_i32(
        r#"
//- minicore: index, slice
fn test() -> i32 {
    let a = [1i32, 5];
    let b = &a[1];
    *b
}
"#,
        5,
    )
}

#[test]
#[ignore]
fn test_str_literal() {
    check_i32(
        r#"
//- minicore: index, slice, str
extern "rust-intrinsic" {
    #[rustc_nounwind]
    pub fn transmute<Src, Dst>(src: Src) -> Dst;
}
fn test() -> i32 {
    let s = "hello";
    let bytes: &[u8] = transmute::<&str, &[u8]>(s);
    let byte: u8 = bytes[0];
    byte as i32
}
"#,
        5,
    )
}

#[test]
fn test_tuple_1() {
    check_i32(
        r#"
fn test() -> i32 {
    let t = (2, 3);
    t.0 + t.1
}
"#,
        5,
    )
}

#[test]
fn test_tuple_2() {
    check_i32(
        r#"
fn test() -> i32 {
    let t = (2, 3);
    let (a, b) = t;
    a + b
}
"#,
        5,
    )
}

#[test]
fn test_tuple_3() {
    check_i32(
        r#"
fn test() -> i32 {
    let t = (2u8, 2i32, 1i64);
    let (a, b, c) = t;
    a as i32 + b + c as i32
}
"#,
        5,
    )
}

#[test]
#[ignore]
fn test_struct() {
    check_i32(
        r#"
struct S { a: i32, b: i32 }
fn test() -> i32 {
    let s = S { a: 3, b: 2 };
    s.a + s.b
}
"#,
        5,
    )
}

#[test]
#[ignore]
fn test_generic_call() {
    check_i32(
        r#"
fn id<T>(t: T) -> T { t }
fn test() -> i32 {
    let (a, b) = id((id(2), id(3)));
    a + b
}
"#,
        5,
    )
}

#[test]
fn test_int_cast_1() {
    check_i32(
        r#"
fn test() -> i32 {
    let i = -5i64;
    i as i32
}
"#,
        -5,
    )
}
