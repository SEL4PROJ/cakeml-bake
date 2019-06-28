use lexpr::{self, Parser, Value};
use std::fs::File;
use std::path::Path;

pub fn splice_in_sexpr_file(
    output_file: &Path,
    file_to_insert: &Path,
    after_module: Option<&str>,
) -> Result<(), String> {
    let output_sexpr = read_sexpr(output_file)?;
    let splice_sexpr = read_sexpr(file_to_insert)?;

    let result_sexpr = splice_in_sexpr(output_sexpr, splice_sexpr, after_module)?;

    // TODO: Write out.
    Ok(())
}

pub fn splice_in_sexpr(
    main_sexpr: lexpr::Value,
    splice_sexpr: lexpr::Value,
    after_module: Option<&str>,
) -> Result<lexpr::Value, String> {
    // println!("here's the main sexp: {:#?}", main_sexpr);
    if let Value::List(ref topdecs) = main_sexpr {
        for topdec in topdecs {
            if let Value::List(ref topdec_contents) = topdec {
                if topdec_contents.len() >= 2 && topdec_contents[0].as_symbol() == Some("Tmod") {
                    println!("Module: {}", topdec_contents[1].as_str().unwrap());
                }
            }
        }
    }
    Ok(main_sexpr)
}

pub fn read_sexpr(filename: &Path) -> Result<lexpr::Value, String> {
    let f = File::open(filename)
        .map_err(|e| format!("Unable to open s-expression from {:?}: {}", filename, e))?;
    Parser::from_reader(f)
        .parse_value()
        .map_err(|e| format!("Error parsing s-expression from {:?}: {}", filename, e))
}
