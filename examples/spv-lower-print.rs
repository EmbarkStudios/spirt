use std::fs;
use std::path::Path;
use std::rc::Rc;

fn main() -> std::io::Result<()> {
    match &std::env::args().collect::<Vec<_>>()[..] {
        [_, in_files @ ..] => {
            for in_file in in_files {
                let in_file_path = Path::new(in_file);

                let save_print_plan = |suffix: &str, plan: spirt::print::Plan| {
                    let pretty = plan.pretty_print();
                    let ext =
                        if suffix.is_empty() { "spirt".into() } else { format!("{suffix}.spirt") };

                    // FIXME(eddyb) don't allocate whole `String`s here.
                    fs::write(in_file_path.with_extension(&ext), pretty.to_string())?;
                    fs::write(
                        in_file_path.with_extension(ext + ".html"),
                        pretty.render_to_html().with_dark_mode_support().to_html_doc(),
                    )
                };

                let mut module = spirt::Module::lower_from_spv_file(
                    Rc::new(spirt::Context::new()),
                    in_file_path,
                )?;
                save_print_plan("", spirt::print::Plan::for_module(&module))?;

                spirt::passes::legalize::structurize_func_cfgs(&mut module);
                save_print_plan("structured", spirt::print::Plan::for_module(&module))?;
            }

            Ok(())
        }
        args => {
            eprintln!("Usage: {} FILES", args[0]);
            std::process::exit(1);
        }
    }
}
