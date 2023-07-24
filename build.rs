fn main() {
    // HACK(eddyb) disable the default of re-running the build script on *any*
    // change to *the entire source tree* (i.e. the default is roughly `./`).
    println!("cargo:rerun-if-changed=build.rs");

    let khr_spv_include_dir =
        std::env::current_dir().unwrap().join("khronos-spec/SPIRV-Headers/include/spirv/unified1");
    println!("cargo:rerun-if-changed={}", khr_spv_include_dir.display());

    if !std::fs::metadata(&khr_spv_include_dir).map_or(false, |m| m.is_dir()) {
        eprintln!(" error: {} is not a directory", khr_spv_include_dir.display());
        eprintln!("  help: git submodules are required to build from a git checkout");
        eprintln!("  help: run `git submodule update --init`");
        eprintln!("  note: if the error persists, please open an issue");
        std::process::exit(1);
    }

    let core_grammar = "spirv.core.grammar.json";
    let mut extinsts_names_and_grammars: Vec<_> = std::fs::read_dir(&khr_spv_include_dir)
        .unwrap()
        .filter_map(|e| {
            let file_name = e.unwrap().file_name();
            Some((
                file_name
                    .to_str()?
                    .strip_prefix("extinst.")?
                    .strip_suffix(".grammar.json")?
                    .to_string(),
                file_name,
            ))
        })
        .collect();
    extinsts_names_and_grammars.sort();

    let all_jsons = format!(
        "pub(super) const SPIRV_CORE_GRAMMAR: &str = include_str!({:?});\n\
         pub(super) const EXTINST_NAMES_AND_GRAMMARS: &[(&str, &str)] = &[\n{}];",
        khr_spv_include_dir.join(core_grammar),
        extinsts_names_and_grammars
            .into_iter()
            .map(|(name, grammar)| {
                format!("({:?}, include_str!({:?})),\n", name, khr_spv_include_dir.join(grammar),)
            })
            .collect::<String>()
    );
    std::fs::write(
        std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap())
            .join("khr_spv_grammar_jsons.rs"),
        all_jsons,
    )
    .unwrap();
}
