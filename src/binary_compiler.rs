use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Instance of the CakeML binary compiler.
pub struct BinaryCompiler {
    /// Path to the compiler binary.
    path: PathBuf,
    /// Whether the input is in s-expression form (true) or concrete syntax (false).
    sexp: bool,
    /// Size of the heap in MiB for the compiled program.
    heap_size: usize,
    /// Size of the stack in MiB for the compiled program.
    stack_size: usize,
    /// Target to compile for.
    // FIXME: target enum
    target: String,
}

impl BinaryCompiler {
    pub fn new(path: &Path) -> Self {
        Self {
            path: path.into(),
            sexp: false,
            heap_size: 100,
            stack_size: 50,
            target: "x64".to_string(),
        }
    }

    /// Set the s-expression flag.
    pub fn sexp(&mut self, sexp: bool) -> &mut Self {
        self.sexp = sexp;
        self
    }

    /// Pipe the contents of `input` into the compiler
    pub fn compile(&self, input: &Path, build_dir: &Path, output_name: &str) -> Result<(), String> {
        let input_file = File::open(input)
            .map_err(|e| format!("Failed to read {:?} for compilation: {}", input, e))?;

        let output = Command::new(&self.path)
            .arg(format!("--sexp={}", self.sexp))
            .arg(format!("--exclude_prelude={}", true))
            .arg(format!("--heap_size={}", self.heap_size))
            .arg(format!("--stack_size={}", self.stack_size))
            .arg(format!("--target={}", self.target))
            .stdin(input_file)
            .output()
            .map_err(|e| format!("Failed to execute CakeML binary compiler: {}", e))?;

        if output.stdout.is_empty() {
            return Err(format!(
                "Error: CakeML binary compiler failed with stderr:\n{}",
                String::from_utf8_lossy(&output.stderr)
            ));
        }

        let output_filename = build_dir.join(output_name);
        File::create(&output_filename)
            .and_then(|mut f| f.write_all(&output.stdout))
            .map_err(|e| format!("Error writing output file {:?}: {}", output_filename, e))
    }
}
