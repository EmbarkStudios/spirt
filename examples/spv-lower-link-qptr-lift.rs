use std::fs;
use std::path::Path;
use std::rc::Rc;

fn main() -> std::io::Result<()> {
    match &std::env::args().collect::<Vec<_>>()[..] {
        [_, in_file] => {
            let in_file_path = Path::new(in_file);

            let save_print_plan = |suffix: &str, plan: spirt::print::Plan| {
                let pretty = plan.pretty_print();
                let ext = format!("{suffix}.spirt");

                // FIXME(eddyb) don't allocate whole `String`s here.
                fs::write(in_file_path.with_extension(&ext), pretty.to_string())?;
                fs::write(
                    in_file_path.with_extension(ext + ".html"),
                    pretty.render_to_html().with_dark_mode_support().to_html_doc(),
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
            eprintln!("Module::lower_from_spv_file({})", in_file_path.display());

            // FIXME(eddyb) DO NOT KEEP THIS
            if true {
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
                //after_pass("minimize_exports", &module)?;
            }

            // HACK(eddyb) do this late enough to avoid spending time on unused
            // functions, which `link::minimize_exports` makes unreachable.
            eprint_duration(|| spirt::passes::legalize::structurize_func_cfgs(&mut module));
            eprintln!("legalize::structurize_func_cfgs");
            //after_pass("structurize_func_cfgs", &module)?;

            eprint_duration(|| spirt::passes::link::resolve_imports(&mut module));
            eprintln!("link::resolve_imports");
            //after_pass("resolve_imports", &module)?;

            // HACK(eddyb)
            after_pass("", &module)?;

            // HACK(eddyb) this is roughly what Rust-GPU would need.
            let layout_config = &spirt::qptr::LayoutConfig {
                abstract_bool_size_align: (1, 1),
                logical_ptr_size_align: (4, 4),
                ..spirt::qptr::LayoutConfig::VULKAN_SCALAR_LAYOUT
            };

            eprint_duration(|| {
                spirt::passes::qptr::lower_from_spv_ptrs(&mut module, layout_config)
            });
            eprintln!("qptr::lower_from_spv_ptrs");
            after_pass("qptr::lower_from_spv_ptrs", &module)?;

            if true {
                eprint_duration(|| spirt::passes::qptr::analyze_uses(&mut module, layout_config));
                eprintln!("qptr::analyze_uses");
                after_pass("qptr::analyze_uses", &module)?;

                eprint_duration(|| {
                    spirt::passes::qptr::lift_to_spv_ptrs(&mut module, layout_config)
                });
                eprintln!("qptr::lift_to_spv_ptrs");
                after_pass("qptr::lift_to_spv_ptrs", &module)?;
            }

            if multi_version_printing {
                // FIXME(eddyb) use a better suffix than `qptr` (or none).
                save_print_plan(
                    "qptr",
                    spirt::print::Plan::for_versions(
                        &cx,
                        per_pass_module.iter().map(|(pass, module)| {
                            (
                                // HACK(eddyb)
                                if pass.is_empty() {
                                    "initial".into()
                                } else {
                                    format!("after {pass}")
                                },
                                module,
                            )
                        }),
                    ),
                )?;
            }

            //let out_file_path = in_file_path.with_extension("qptr.spv");
            //eprint_duration(|| module.lift_to_spv_file(&out_file_path))?;
            //eprintln!("Module::lift_to_spv_file({})", out_file_path.display());

            Ok(())
        }
        args => {
            eprintln!("Usage: {} IN", args[0]);
            std::process::exit(1);
        }
    }
}
