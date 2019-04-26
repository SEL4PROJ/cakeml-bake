use std::collections::{HashMap, VecDeque};
use std::path::{Path, PathBuf};
use std::{
    env,
    fs::File,
    io::{self, Read},
};

const REQUIRE_KEYWORD: &str = "require ";

struct ModuleTemplate {
    name: String,
    file_contents: String,
    dependencies: Vec<String>,
}

struct Module {
    name: String,
    file_contents: String,
}

fn module_path(module_name: &str, dir_path: &str) -> Result<PathBuf, ()> {
    let filename = format!("{}/{}Script.sml", dir_path, module_name);
    let path = PathBuf::from(filename);

    if path.is_file() {
        Ok(path)
    } else {
        Err(())
    }
}

impl ModuleTemplate {
    fn load_file(module_name: &str, module_path: &Path) -> Result<Self, io::Error> {
        let mut module_template = ModuleTemplate {
            name: module_name.into(),
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
            if line.starts_with(REQUIRE_KEYWORD) {
                if line.ends_with(';') {
                    requirements.extend(
                        line.trim_start_matches(REQUIRE_KEYWORD)
                            .trim_end_matches(';')
                            .split_whitespace()
                            .map(|s| s.to_string()),
                    );
                } else {
                    eprintln!(
                        "WARN: ignored line starting with `require` without terminating semi-colon"
                    );
                }
            }
        }
        requirements
    }
}

/// Given a list of entry-point modules (usually just one), and a list of directories to search,
/// gather the collection of modules required (entry points and their dependencies)
// TODO: use Path/PathBuf for the search directories
fn collect_modules(
    entry_points: Vec<String>,
    search_paths: &[String],
) -> Result<HashMap<String, ModuleTemplate>, Vec<String>> {
    let mut modules = HashMap::new();
    let mut modules_to_find = VecDeque::from(entry_points);
    let mut missing_modules = vec![];

    while let Some(module_name) = modules_to_find.pop_front() {
        for dep_directory in search_paths {
            if let Ok(module_template) =
                module_path(&module_name, dep_directory).and_then(|mod_path| {
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
                            dep_name.as_str() != "basis" && !modules.contains_key(dep_name.as_str())
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

impl Module {
    fn write_out(_filename: &str) -> Result<(), ()> {
        Ok(())
    }
}

fn resolve_dependency_order(_module_templates: Vec<ModuleTemplate>) -> Vec<Module> {
    vec![]
}

fn main() {
    let mut args: Vec<_> = env::args().collect();

    let name = args.pop().unwrap();
    let search_dirs = args;

    let module_templates = collect_modules(vec![name], &search_dirs).unwrap();

    for (_, mt) in module_templates {
        println!("{}, depends: {:?}", mt.name, mt.dependencies);
    }
}
