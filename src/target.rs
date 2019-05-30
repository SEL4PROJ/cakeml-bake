/// Word size in bits for a given target.
pub fn target_word_size_bits(target: &str) -> Result<u8, String> {
    // Targets from cakeml/compiler/compilerScript.sml
    match target {
        "ag32" => Ok(32),
        "arm6" => Ok(32),
        "arm8" => Ok(64),
        "x64" => Ok(64),
        "mips" => Ok(64),
        "riscv" => Ok(64),
        _ => Err(format!("Unsupported target: {}", target)),
    }
}
