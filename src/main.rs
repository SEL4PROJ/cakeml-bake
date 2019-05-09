use self::binary_compiler::BinaryCompiler;
use self::cli::Opts;
use self::holmake::Holmake;
use petgraph::algo::toposort;
use petgraph::Graph;
use std::collections::{HashMap, VecDeque};
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use structopt::StructOpt;
use tera::{Context, Tera};

mod binary_compiler;
mod cli;
mod holmake;

const BASIS: &str = "basisProg";
const REQUIRE_KEYWORD: &str = "require ";
const SEXPR_FILENAME: &str = "program.sexp";
const ASM_FILENAME: &str = "program.S";

/// Directed dependency graph, with edges from modules to their dependencies.
type DepGraph = Graph<String, ()>;

struct ModuleTemplate {
    /// Name of this module.
    name: String,
    /// Path to the source file of this module template.
    file_location: PathBuf,
    /// Contents of the template file.
    file_contents: String,
    /// List of modules upon which this module depends.
    dependencies: Vec<String>,
}

struct Module {
    name: String,
    file_contents: String,
}

fn module_path(module_name: &str, dir_path: &Path) -> PathBuf {
    dir_path.join(format!("{}Script.sml", module_name))
}

fn file_path<P: AsRef<Path>>(path: P) -> Result<P, ()> {
    if path.as_ref().is_file() {
        Ok(path)
    } else {
        Err(())
    }
}

impl ModuleTemplate {
    fn load_file(module_name: &str, module_path: &Path) -> Result<Self, io::Error> {
        let mut module_template = ModuleTemplate {
            name: module_name.into(),
            file_location: module_path.into(),
            file_contents: String::new(),
            dependencies: vec![],
        };

        println!("filename is: {:?}", module_path);
        let mut f = File::open(module_path)?;
        f.read_to_string(&mut module_template.file_contents)?;

        module_template.dependencies =
            Self::parse_require_directives(&module_template.file_contents);

        Ok(module_template)
    }

    fn parse_require_directives(file_contents: &str) -> Vec<String> {
        // TODO: multi-line requires?
        let mut requirements = vec![];
        for line in file_contents.lines() {
            if Self::is_require_line(line) {
                requirements.extend(
                    line.trim_start_matches(REQUIRE_KEYWORD)
                        .trim_end_matches(';')
                        .split_whitespace()
                        .map(|s| s.to_string()),
                );
            }
        }
        requirements
    }

    fn is_require_line(line: &str) -> bool {
        line.starts_with(REQUIRE_KEYWORD)
    }

    /// Replace all the require statements with a single `translation_extends` call to the
    /// given parent module.
    fn instantiate_parent(&self, parent_module: &str) -> Module {
        // TODO: this is probably a rather inefficient way to do this
        let mut new_contents = String::with_capacity(self.file_contents.len());
        let mut parent_added = false;

        for line in self.file_contents.lines() {
            new_contents.push_str("\n");

            if Self::is_require_line(line) {
                if !parent_added {
                    let trans_ext = format!("val _ = translation_extends \"{}\";", parent_module);
                    new_contents.push_str(&trans_ext);
                    parent_added = true;
                }
            } else {
                new_contents.push_str(line);
            }
        }

        Module {
            name: self.name.clone(),
            file_contents: new_contents,
        }
    }
}

/// Given a list of entry-point modules (usually just one), and a list of directories to search,
/// gather the collection of modules required (entry points and their dependencies)
fn collect_modules(
    entry_points: &[String],
    search_paths: &[PathBuf],
) -> Result<HashMap<String, ModuleTemplate>, Vec<String>> {
    let mut modules = HashMap::new();
    let mut modules_to_find = VecDeque::from(entry_points.to_vec());
    let mut missing_modules = vec![];

    while let Some(module_name) = modules_to_find.pop_front() {
        for dep_directory in search_paths {
            if let Ok(module_template) = file_path(module_path(&module_name, dep_directory))
                .and_then(|mod_path| {
                    ModuleTemplate::load_file(&module_name, &mod_path).map_err(|_| ())
                })
            {
                // Add module dependencies to the search list if they haven't already
                // been resolved
                modules_to_find.extend(
                    module_template
                        .dependencies
                        .iter()
                        .filter(|dep_name| {
                            dep_name.as_str() != BASIS && !modules.contains_key(dep_name.as_str())
                        })
                        .cloned(),
                );
                // Add the resolved module to the modules collection
                modules.insert(module_name.clone(), module_template);
                break;
            }
        }

        if !modules.contains_key(&module_name) {
            println!("couldn't find {} module", module_name);
            missing_modules.push(module_name.to_string());
        }
    }

    if missing_modules.is_empty() {
        Ok(modules)
    } else {
        Err(missing_modules)
    }
}

/// Build a dependency graph from a set of modules.
fn build_dep_graph(modules: &[&ModuleTemplate]) -> DepGraph {
    let mut graph = Graph::new();

    let mut indices = HashMap::new();

    let basis_idx = graph.add_node(BASIS.to_string());
    indices.insert(BASIS, basis_idx);

    // Add nodes for all the modules
    for module in modules {
        let idx = graph.add_node(module.name.to_string());
        indices.insert(module.name.as_str(), idx);
    }

    // Add dependencies as edges
    for module in modules {
        let mod_idx = *indices
            .get(module.name.as_str())
            .expect("module index not found");
        for dep in &module.dependencies {
            let dep_idx = *indices.get(dep.as_str()).expect("dep index not found");

            graph.add_edge(mod_idx, dep_idx, ());
        }
    }

    graph
}

/// Compute a dependency-compatible linearisation of the dependency DAG.
///
/// Returns dependencies in bottom-up order, beginning with basis and proceeding
/// to modules later in the chain.
fn linearise_deps(deps: &DepGraph) -> Result<Vec<String>, ()> {
    // Do a topological sort, which will give us the dependencies in top-down order,
    // beginning from the last in the chain and ending in basis. Reverse to get the
    // bottom-up ordering.
    let mut linear_dep_idx = toposort(deps, None).map_err(|_| ())?;
    linear_dep_idx.reverse();
    Ok(linear_dep_idx
        .into_iter()
        .map(|node_idx| deps[node_idx].clone())
        .collect())
}

/// Instantiate a collection of module templates according to a linearisation.
///
/// Return a list of modules with their parent links filled in according to the linearisation,
/// ready for writing out to a file.
fn instantiate_module_templates(
    mut module_templates: HashMap<String, ModuleTemplate>,
    linearisation: &[String],
) -> Vec<Module> {
    linearisation
        .windows(2)
        .map(|w| {
            let parent_module = &w[0];
            let module_name = &w[1];
            let template = module_templates
                .remove(module_name)
                .expect("module missing");
            template.instantiate_parent(parent_module)
        })
        .collect()
}

impl Module {
    /// Write the instantiated module to a file in the given directory.
    fn write_out(&self, build_directory: &Path) -> Result<(), io::Error> {
        let mut file = File::create(module_path(&self.name, build_directory))?;
        file.write_all(self.file_contents.as_bytes())
    }
}

/// Load meta-templates required to generate the build module.
fn load_build_templates() -> Result<Tera, tera::Error> {
    let mut tera = Tera::default();
    tera.add_raw_template("buildScript.sml", include_str!("templates/buildScript.sml"))?;
    tera.add_raw_template("Holmakefile", include_str!("templates/Holmakefile"))?;
    Ok(tera)
}

fn get_sexpr_path(build_dir: &Path) -> Result<PathBuf, io::Error> {
    Ok(build_dir.canonicalize()?.join(SEXPR_FILENAME))
}

fn create_build_script(
    build_dir: &Path,
    terminal_module: &str,
    entry_function: &str,
    sexpr_path: &Path,
    tera: &Tera,
) -> Result<(), io::Error> {
    let mut file = File::create(module_path("build", build_dir))?;

    let mut context = Context::default();
    context.insert("terminal_module", terminal_module);
    context.insert("entry_function", entry_function);
    context.insert("sexpr_file", &sexpr_path.to_string_lossy());

    // FIXME: error handling
    let file_contents = tera.render("buildScript.sml", &context).unwrap();
    file.write_all(file_contents.as_bytes())
}

fn create_holmakefile(
    build_dir: &Path,
    cakeml_dir: &Path,
    include_dirs: &[PathBuf],
    tera: &Tera,
) -> Result<(), io::Error> {
    let mut file = File::create(build_dir.join("Holmakefile"))?;

    let string_include_dirs = include_dirs
        .iter()
        .map(|p| p.to_string_lossy())
        .collect::<Vec<_>>();

    let mut context = Context::default();
    context.insert("cakeml_dir", &cakeml_dir.to_string_lossy());
    context.insert("include_dirs", &string_include_dirs);

    // FIXME: error handling
    let file_contents = tera.render("Holmakefile", &context).unwrap();
    file.write_all(file_contents.as_bytes())
}

fn main() {
    let opts = Opts::from_args();

    println!("{:?}", opts);

    let module_templates = collect_modules(&opts.module_names, &opts.search_dirs).unwrap();

    for (_, mt) in &module_templates {
        println!(
            "{}, depends: {:?}, from: {:?}",
            mt.name, mt.dependencies, mt.file_location
        );
    }

    let flat_modules: Vec<_> = module_templates.values().collect();
    let dep_graph = build_dep_graph(&flat_modules);

    println!("{:#?}", dep_graph);

    let linear_deps = linearise_deps(&dep_graph).expect("dependency graph contains cycles!");

    println!("{:?}", linear_deps);

    let instantiated_modules = instantiate_module_templates(module_templates, &linear_deps);

    for module in instantiated_modules {
        module.write_out(&opts.build_dir).unwrap();
    }

    let tera = load_build_templates().unwrap();
    let terminal_module = linear_deps.last().unwrap();
    let sexpr_path = get_sexpr_path(&opts.build_dir).unwrap();
    create_build_script(
        &opts.build_dir,
        terminal_module,
        &opts.entry_point,
        &sexpr_path,
        &tera,
    )
    .unwrap();
    create_holmakefile(&opts.build_dir, &opts.cakeml_dir, &opts.hol_includes, &tera).unwrap();

    let holmake = Holmake::new(&opts.holmake);
    holmake.run(&opts.build_dir).unwrap();

    BinaryCompiler::new(&opts.cakeml_bin)
        .sexp(true)
        .compile(&sexpr_path, &opts.build_dir, ASM_FILENAME)
        .expect("binary compiler failed");
}
