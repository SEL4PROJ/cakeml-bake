use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, Clone, StructOpt)]
#[structopt(rename_all = "kebab-case")]
pub struct Opts {
    /// Names of the modules to build
    #[structopt(long)]
    pub module_names: Vec<String>,
    /// Directories to search for module source code
    #[structopt(long)]
    pub search_dirs: Vec<PathBuf>,
    /// Directory to build in
    #[structopt(long)]
    pub build_dir: PathBuf,
    /// Top-level CakeML function to run when the program executes
    // FIXME: this might depend on which module is last in the chain...
    #[structopt(long, default_value = "main")]
    pub entry_point: String,
    /// Path to a checkout of the CakeML compiler repository
    #[structopt(long)]
    pub cakeml_dir: PathBuf,
    /// HOL4 dependency directories required by the build
    ///
    /// Will be built using Holmake
    #[structopt(long)]
    pub hol_includes: Vec<PathBuf>,
}
