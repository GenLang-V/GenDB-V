//! Export the compiler settings of this build to the crate as `GENDB_BUILD_{PROFILE,OPT_LEVEL,DEBUG,
//! CARGO_ENCODED_RUSTFLAGS,TARGET}`, so the runtime build identity can name them. Nothing is compiled or linked here
//! (the earlier version also compiled and linked an LLVM JITLink shim; the Verus path uses `dlopen` and needs no LLVM).
fn main() {
    for key in ["PROFILE", "OPT_LEVEL", "DEBUG", "CARGO_ENCODED_RUSTFLAGS", "TARGET"] {
        println!("cargo:rustc-env=GENDB_BUILD_{key}={}", std::env::var(key).unwrap_or_default());
    }
    println!("cargo:rerun-if-changed=build.rs");
}
