use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Debug)]
pub struct Holmake {
    path: PathBuf,
}

impl Holmake {
    /// Create a new
    pub fn new(holmake_path: &Path) -> Self {
        Self {
            path: holmake_path.into(),
        }
    }

    /// Run Holmake in the given directory
    pub fn run(&self, build_dir: &Path) -> Result<(), String> {
        Command::new(&self.path)
            .current_dir(build_dir)
            .output()
            .map_err(|e| format!("Failed to execute Holmake: {}", e))
            .and_then(|output| {
                if output.status.success() {
                    Ok(())
                } else {
                    Err(format!(
                        "Error: Holmake failed with stderr:\n{}",
                        String::from_utf8_lossy(&output.stderr)
                    ))
                }
            })
    }
}
