use std::rc::Rc;

fn main() -> std::io::Result<()> {
    match &std::env::args().collect::<Vec<_>>()[..] {
        [_, in_file] => {
            let cx = Rc::new(spirt::Context::new());
            let module = spirt::Module::lower_from_spv_file(cx.clone(), in_file)?;
            eprintln!("{}", spirt::print::Plan::for_module(&module));
            Ok(())
        }
        args => {
            eprintln!("Usage: {} IN", args[0]);
            std::process::exit(1);
        }
    }
}
