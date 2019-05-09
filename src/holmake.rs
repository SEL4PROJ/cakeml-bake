use std::io;
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
    pub fn run(&self, build_dir: &Path) -> Result<(), io::Error> {
        let exit_status = Command::new(&self.path).current_dir(build_dir).status()?;
        if !exit_status.success() {
            panic!("Holmake failed");
        }
        Ok(())
    }
}
