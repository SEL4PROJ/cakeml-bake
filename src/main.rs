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

impl ModuleTemplate {
    fn load_file(name: &str, path: &str) -> Result<Self, io::Error> {
        let mut module_template = ModuleTemplate {
            name: name.into(),
            file_contents: String::new(),
            dependencies: vec![],
        };

        let filename = format!("{}/{}Script.sml", path, name);
        println!("filename is: {}", filename);
        let mut f = File::open(filename)?;
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

impl Module {
    fn write_out(_filename: &str) -> Result<(), ()> {
        Ok(())
    }
}

fn resolve_dependency_order(_module_templates: Vec<ModuleTemplate>) -> Vec<Module> {
    vec![]
}

fn main() {
    let args: Vec<_> = env::args().collect();

    let name = &args[1];
    let directory = &args[2];
    let module_template = ModuleTemplate::load_file(&name, &directory).unwrap();

    println!("{}", module_template.name);
    println!("{:?}", module_template.dependencies);
}
