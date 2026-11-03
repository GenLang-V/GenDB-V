//! Scratch libraries for tests, always under a scratch `TMPDIR` (never `/tmp`).

use std::path::PathBuf;

/// A fresh, unique directory `$TMPDIR/gendb-artifacts-tests/<name>-<pid>-<nanos>`.
pub fn scratch_dir(name: &str) -> PathBuf {
    let lane = PathBuf::from(std::env::var_os("TMPDIR").expect("a scratch TMPDIR is required; /tmp is forbidden"));
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let root = lane.join("gendb-artifacts-tests").join(format!("{name}-{}-{nanos}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    root
}
