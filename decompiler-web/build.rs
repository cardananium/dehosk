use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=frontend/src");
    println!("cargo:rerun-if-changed=frontend/index.html");
    println!("cargo:rerun-if-changed=frontend/package.json");

    let frontend_dir = std::path::Path::new("frontend");
    if !frontend_dir.exists() {
        println!("cargo:warning=frontend/ directory not found, skipping frontend build");
        // Create empty dist so rust-embed doesn't fail
        std::fs::create_dir_all("frontend/dist").ok();
        std::fs::write("frontend/dist/.gitkeep", "").ok();
        return;
    }

    let node_modules = frontend_dir.join("node_modules");
    if !node_modules.exists() {
        let status = Command::new("npm")
            .arg("install")
            .current_dir(frontend_dir)
            .status()
            .expect("Failed to run npm install");
        if !status.success() {
            panic!("npm install failed");
        }
    }

    let status = Command::new("npm")
        .args(["run", "build"])
        .current_dir(frontend_dir)
        .status()
        .expect("Failed to run npm run build");
    if !status.success() {
        panic!("npm run build failed");
    }
}
