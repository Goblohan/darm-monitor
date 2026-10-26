/* build.rs — Rust build script
 *
 * This script:
 *   1. Finds the Lean toolchain path
 *   2. Compiles the C FFI wrapper (darm_shim.c)
 *   3. Links against the Lean runtime and the DARM AgentSandbox library
 *   4. Sets up the Rust FFI bindings
 */

use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    /* Step 1: Find Lean toolchain. */
    let lean_prefix = find_lean_prefix();
    println!("cargo:rustc-env=LEAN_PREFIX={}", lean_prefix.display());

    /* Step 2: Build the C wrapper. */
    let c_dir = PathBuf::from("../c");
    let c_src = c_dir.join("darm_shim.c");
    let c_header = c_dir.join("darm_shim.h");

    println!("cargo:rerun-if-changed={}", c_src.display());
    println!("cargo:rerun-if-changed={}", c_header.display());

    cc::Build::new()
        .file(c_src)
        .include(&c_dir)
        .include(format!("{}/include", lean_prefix.display()))
        .flag("-O3")
        .compile("darm_shim_c");

    /* Step 3: Link against Lean runtime. */
    println!("cargo:rustc-link-search=native={}/lib", lean_prefix.display());
    println!("cargo:rustc-link-lib=static=leanrt");
    println!("cargo:rustc-link-lib=dylib=AgentSandbox");  /* or static */

    /* Step 4: Platform-specific linking. */
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap();
    match target_os.as_str() {
        "linux" => {
            println!("cargo:rustc-link-lib=dylib=pthread");
            println!("cargo:rustc-link-lib=dylib=dl");
            println!("cargo:rustc-link-lib=dylib=m");
        }
        "macos" => {
            println!("cargo:rustc-link-lib=dylib=c++");
        }
        "windows" => {
            println!("cargo:rustc-link-lib=dylib=kernel32");
            println!("cargo:rustc-link-lib=dylib=msvcrt");
        }
        _ => {}
    }
}

fn find_lean_prefix() -> PathBuf {
    /* Try `lean --print-prefix` first. */
    if let Ok(output) = Command::new("lean").arg("--print-prefix").output() {
        if output.status.success() {
            let prefix = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !prefix.is_empty() {
                return PathBuf::from(prefix);
            }
        }
    }

    /* Fallback: check environment variable. */
    if let Ok(prefix) = env::var("LEAN_PREFIX") {
        return PathBuf::from(prefix);
    }

    /* Fallback: common paths. */
    for path in &["/usr/local/lean4", "/opt/lean4", "C:\lean4"] {
        if PathBuf::from(path).exists() {
            return PathBuf::from(path);
        }
    }

    panic!("Could not find Lean toolchain. Set LEAN_PREFIX or ensure `lean` is on PATH.");
}
