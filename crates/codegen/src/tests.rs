use hir_def::db::DefDatabase;
use span::{Edition, EditionedFileId};
use test_fixture::WithFixture;

use crate::{test_db::TestDB, Jit};



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

    let mut jit = Jit::default();
    let code = jit.compile(db, func_id).unwrap();
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
    check_i32(r#"
fn test() -> i32 { 4 }
"#, 4)
}

#[test]
fn test_2() {
    check_i32(r#"
fn test() -> i32 { 5 }
"#, 5)
}
