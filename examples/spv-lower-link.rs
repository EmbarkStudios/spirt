use std::fs;
use std::path::Path;
use std::rc::Rc;

fn main() -> std::io::Result<()> {
    match &std::env::args().collect::<Vec<_>>()[..] {
        [_, in_file] => {
            let in_file_path = Path::new(in_file);

            // FIXME(eddyb) adapt the other examples to this style.

            fn eprint_duration<R>(f: impl FnOnce() -> R) -> R {
                let start = std::time::Instant::now();
                let r = f();
                eprint!("[{:8.3}ms] ", start.elapsed().as_secs_f64() * 1000.0);
                r
            }

            eprint_duration(|| spirt::spv::spec::Spec::get());
            eprintln!("spv::spec::Spec::get");

            let cx = Rc::new(spirt::Context::new());

            let mut module =
                eprint_duration(|| spirt::Module::lower_from_spv_file(cx.clone(), in_file_path))?;
            eprintln!("Module::lower_from_spv_file({})", in_file_path.display());

            let original_export_count = module.exports.len();
            eprint_duration(|| {
                spirt::passes::link::minimize_exports(&mut module, |export_key| {
                    matches!(export_key, spirt::ExportKey::SpvEntryPoint { .. })
                })
            });
            eprintln!(
                "link::minimize_exports: {} -> {} exports",
                original_export_count,
                module.exports.len()
            );
            fs::write(
                in_file_path.with_extension("after.minimize_exports.spirt"),
                spirt::print::Plan::for_module(&module).to_string(),
            )?;

            eprint_duration(|| spirt::passes::link::resolve_imports(&mut module));
            eprintln!("link::resolve_imports");
            fs::write(
                in_file_path.with_extension("after.resolve_imports.spirt"),
                spirt::print::Plan::for_module(&module).to_string(),
            )?;

            Ok(())
        }
        args => {
            eprintln!("Usage: {} IN", args[0]);
            std::process::exit(1);
        }
    }
}
