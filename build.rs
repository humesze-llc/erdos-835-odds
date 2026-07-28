//! Builds vendored CaDiCaL 2.1.3 plus the IPASIR-UP shim.
//!
//! Only runs under `--features cdcl`, so the default build keeps the
//! four-crate, no-C++-toolchain profile the odd835 spec asks for.

use std::path::{Path, PathBuf};

fn main() {
    if std::env::var_os("CARGO_FEATURE_CDCL").is_none() {
        println!("cargo:rerun-if-changed=build.rs");
        return;
    }

    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let cadical = root.join("vendor/cadical/src");
    let shim = root.join("vendor/shim");

    let mut sources: Vec<PathBuf> = std::fs::read_dir(&cadical)
        .expect("vendor/cadical/src missing")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().map_or(false, |x| x == "cpp"))
        .collect();
    sources.sort();
    assert!(!sources.is_empty(), "no CaDiCaL sources found");
    sources.push(shim.join("s45_shim.cpp"));

    let mut b = cc::Build::new();
    b.cpp(true)
        .include(&cadical)
        .include(&shim)
        .include(root.join("vendor/compat"))
        .files(&sources)
        // `NBUILD` skips the generated build.hpp (version/compiler banner);
        // `NUNLOCKED` avoids getc_unlocked, which MSVC's CRT lacks.
        .define("NBUILD", None)
        .define("NUNLOCKED", None)
        // CaDiCaL's Windows guards test `__WIN32`, which is a MinGW spelling
        // MSVC does not predefine. Everything else keys off `_WIN32`.
        .define("__WIN32", None)
        .define("_CRT_SECURE_NO_WARNINGS", None)
        .warnings(false);

    if b.get_compiler().is_like_msvc() {
        b.flag("/EHsc").flag("/std:c++17");
        // Dialect shims ahead of every TU; see vendor/compat/msvc_compat.h.
        b.flag("/FImsvc_compat.h");
        // resources.cpp -> GetProcessMemoryInfo
        println!("cargo:rustc-link-lib=psapi");
    } else {
        b.flag("-std=c++11");
    }

    b.compile("cadical_s45");

    rerun(&cadical);
    rerun(&shim);
    println!("cargo:rerun-if-changed=build.rs");
}

fn rerun(dir: &Path) {
    println!("cargo:rerun-if-changed={}", dir.display());
}
