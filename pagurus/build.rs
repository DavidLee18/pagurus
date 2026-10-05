//! Build the Idris 2 `pagurus-core` executable next to this crate.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let core_dir = manifest_dir.join("..").join("core");
    println!("cargo:rerun-if-changed={}", core_dir.display());
    println!("cargo:rerun-if-env-changed=IDRIS2");
    println!("cargo:rerun-if-env-changed=PAGURUS_CORE");

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let dest = out_dir.join("pagurus-core");

    if let Ok(prebuilt) = env::var("PAGURUS_CORE") {
        let src = PathBuf::from(prebuilt);
        copy_core_bundle(&src, &dest);
        println!("cargo:rustc-env=PAGURUS_CORE_PATH={}", dest.display());
        return;
    }

    let idris2 = find_idris2().unwrap_or_else(|| {
        panic!(
            "Idris 2 0.8.0 not found. Install it with scripts/setup-idris2.sh \
             (or set IDRIS2 / PAGURUS_CORE). See README.md."
        );
    });

    let status = Command::new(&idris2)
        .args(["--build", "pagurus-core.ipkg"])
        .current_dir(&core_dir)
        .status()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", idris2.display()));
    if !status.success() {
        panic!("idris2 --build pagurus-core.ipkg failed");
    }

    let built = core_dir.join("build").join("exec").join("pagurus-core");
    if !built.exists() {
        panic!("pagurus-core was not produced at {}", built.display());
    }
    copy_core_bundle(&built, &dest);
    println!("cargo:rustc-env=PAGURUS_CORE_PATH={}", dest.display());
}

fn find_idris2() -> Option<PathBuf> {
    if let Ok(p) = env::var("IDRIS2") {
        let pb = PathBuf::from(p);
        if pb.exists() {
            return Some(pb);
        }
    }
    if let Some(p) = which("idris2") {
        return Some(p);
    }
    if let Ok(home) = env::var("HOME") {
        let p = PathBuf::from(home)
            .join(".idris2")
            .join("bin")
            .join("idris2");
        if p.exists() {
            return Some(p);
        }
    }
    None
}

fn which(name: &str) -> Option<PathBuf> {
    let path = env::var_os("PATH")?;
    for dir in env::split_paths(&path) {
        let candidate = dir.join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

fn copy_core_bundle(src_script: &Path, dest_script: &Path) {
    if let Some(parent) = dest_script.parent() {
        let _ = fs::create_dir_all(parent);
    }
    fs::copy(src_script, dest_script).unwrap_or_else(|e| {
        panic!(
            "failed to copy {} -> {}: {e}",
            src_script.display(),
            dest_script.display()
        );
    });
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perm = fs::metadata(dest_script).unwrap().permissions();
        perm.set_mode(0o755);
        fs::set_permissions(dest_script, perm).ok();
    }

    let src_app = src_script.parent().unwrap().join("pagurus-core_app");
    let dest_app = dest_script.parent().unwrap().join("pagurus-core_app");
    if src_app.exists() {
        copy_dir(&src_app, &dest_app);
    }
}

fn copy_dir(src: &Path, dest: &Path) {
    let _ = fs::remove_dir_all(dest);
    fs::create_dir_all(dest).unwrap();
    for entry in fs::read_dir(src).unwrap() {
        let entry = entry.unwrap();
        let to = dest.join(entry.file_name());
        let ty = entry.file_type().unwrap();
        if ty.is_dir() {
            copy_dir(&entry.path(), &to);
        } else {
            fs::copy(entry.path(), to).unwrap();
        }
    }
}
