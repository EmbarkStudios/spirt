use std::fs;
use std::path::Path;
use std::rc::Rc;

fn main() -> std::io::Result<()> {
    match &std::env::args().collect::<Vec<_>>()[..] {
        [_, in_file, merge_file] => {
            let in_file_path = Path::new(in_file);
            let in_merge_file_path = Path::new(merge_file);

            let save_print_plan = |suffix: &str, plan: spirt::print::Plan| {
                let pretty = plan.pretty_print();
                let ext = format!("{suffix}.spirt");

                // FIXME(eddyb) don't allocate whole `String`s here.
                fs::write(in_file_path.with_extension(&ext), pretty.to_string())?;
                fs::write(
                    in_file_path.with_extension(ext + ".html"),
                    pretty
                        .render_to_html()
                        .with_dark_mode_support()
                        .to_html_doc(),
                )
            };

            // FIXME(eddyb) adapt the other examples to this style.

            fn eprint_duration<R>(f: impl FnOnce() -> R) -> R {
                let start = std::time::Instant::now();
                let r = f();
                eprint!("[{:8.3}ms] ", start.elapsed().as_secs_f64() * 1000.0);
                r
            }

            eprint_duration(|| {
                let _ = spirt::spv::spec::Spec::get();
            });
            eprintln!("spv::spec::Spec::get");

            let cx = Rc::new(spirt::Context::new());

            let multi_version_printing = true;
            let mut per_pass_module = vec![];
            let mut after_pass = |pass, module: &spirt::Module| {
                if multi_version_printing {
                    per_pass_module.push((pass, module.clone()));
                    Ok(())
                } else {
                    save_print_plan(
                        &format!("after.{pass}"),
                        spirt::print::Plan::for_module(module),
                    )
                }
            };

            let mut module =
                eprint_duration(|| spirt::Module::lower_from_spv_file(cx.clone(), in_file_path))?;
            eprintln!(
                "[Mergee] Module::lower_from_spv_file({})",
                in_file_path.display()
            );

            after_pass("lower_from_spv_file module", &module)?;

            let merged = eprint_duration(|| {
                spirt::Module::lower_from_spv_file(cx.clone(), in_merge_file_path)
            })?;
            eprintln!(
                "[Merged] Module::lower_from_spv_file({})",
                in_merge_file_path.display()
            );
            after_pass("merge file", &merged)?;

            eprint_duration(|| spirt::passes::merge::merge(&mut module, merged)).unwrap();
            eprintln!("merge");
            after_pass("merged", &module)?;

            /* NOTE: If you add that, it'll probably delete the just merged exports
             * to prevent that, use an module that declares an `import` for one of the merged
             * `export`s.
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

            after_pass("minimize_exports", &module)?;
            */
            eprint_duration(|| spirt::passes::legalize::structurize_func_cfgs(&mut module));
            eprintln!("legalize::structurize_func_cfgs");
            after_pass("structurize_func_cfgs", &module)?;

            eprint_duration(|| spirt::passes::link::resolve_imports(&mut module));
            eprintln!("link::resolve_imports");
            after_pass("resolve_imports", &module)?;

            if multi_version_printing {
                // FIXME(eddyb) use a better suffix than `link` (or none).
                save_print_plan(
                    "link",
                    spirt::print::Plan::for_versions(
                        &cx,
                        per_pass_module
                            .iter()
                            .map(|(pass, module)| (format!("after {pass}"), module)),
                    ),
                )?;
            }

            let out_file_path = in_file_path.with_extension("link.spv");
            eprint_duration(|| module.lift_to_spv_file(&out_file_path))?;
            eprintln!("Module::lift_to_spv_file({})", out_file_path.display());

            Ok(())
        }
        args => {
            eprintln!("Usage: {} IN", args[0]);
            std::process::exit(1);
        }
    }
}
