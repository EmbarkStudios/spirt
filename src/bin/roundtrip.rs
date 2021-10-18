fn main() -> std::io::Result<()> {
    match &std::env::args().collect::<Vec<_>>()[..] {
        [_, in_file, out_file] => {
            let module = spirt::compat::Module::read_from_spv_file(in_file)?;

            let spv_spec = spirt::compat::spv::spec::Spec::get();
            let (mut known, mut unknown) = (0, 0);
            for top_level in &module.top_level {
                match top_level {
                    spirt::compat::TopLevel::SpvInst { opcode, operands } => {
                        eprint!(
                            "    {}",
                            spv_spec.instructions.get_named(*opcode).unwrap().0
                        );
                        spirt::compat::spv::OperandPrinter {
                            operands: operands.iter(),
                            out: std::io::stderr().lock(),
                        }
                        .all_operands()
                        .unwrap();
                        eprintln!();
                        known += 1;
                    }
                    spirt::compat::TopLevel::SpvUnknownInst { opcode, .. } => {
                        eprintln!(
                            "    {} ???",
                            spv_spec.instructions.get_named(*opcode).unwrap().0
                        );
                        unknown += 1;
                    }
                }
            }
            eprintln!("known/unknown instructions: {}/{}", known, unknown);

            module.write_to_spv_file(out_file)
        }
        args => {
            eprintln!("Usage: {} IN OUT", args[0]);
            std::process::exit(1);
        }
    }
}
