//! Runs `rustc --print target-spec-json` to get the target_data_layout.

use anyhow::Context;
use rustc_hash::FxHashMap;
use toolchain::Tool;

use crate::{toolchain_info::QueryConfig, utf8_stdout, Sysroot};

/// Uses `rustc --print target-spec-json`.
pub fn get(
    config: QueryConfig<'_>,
    target: Option<&str>,
    extra_env: &FxHashMap<String, String>,
) -> anyhow::Result<String> {
    const RUSTC_ARGS: [&str; 2] = ["--print", "target-spec-json"];
    let process = |output: String| {
        (|| Some(output.split_once(r#""data-layout": ""#)?.1.split_once('"')?.0.to_owned()))()
            .ok_or_else(|| {
                anyhow::format_err!("could not parse target-spec-json from command output")
            })
    };
    let sysroot = match config {
        QueryConfig::Cargo(sysroot, cargo_toml) => {
            let mut cmd = sysroot.tool(Tool::Cargo);
            cmd.envs(extra_env);
            cmd.current_dir(cargo_toml.parent()).env("RUSTC_BOOTSTRAP", "1");
            cmd.args(["rustc", "-Z", "unstable-options"]).args(RUSTC_ARGS).args([
                "--",
                "-Z",
                "unstable-options",
            ]);
            if let Some(target) = target {
                cmd.args(["--target", target]);
            }
            match utf8_stdout(&mut cmd) {
                Ok(output) => return process(output),
                Err(e) => {
                    tracing::warn!(%e, "failed to run `{cmd:?}`, falling back to invoking rustc directly");
                    sysroot
                }
            }
        }
        QueryConfig::Rustc(sysroot) => sysroot,
    };

    let mut cmd = Sysroot::tool(sysroot, Tool::Rustc);
    cmd.envs(extra_env)
        .env("RUSTC_BOOTSTRAP", "1")
        .args(["-Z", "unstable-options"])
        .args(RUSTC_ARGS);
    if let Some(target) = target {
        cmd.args(["--target", target]);
    }
    utf8_stdout(&mut cmd)
        .with_context(|| format!("unable to fetch target-data-layout via `{cmd:?}`"))
        .and_then(process)
}
