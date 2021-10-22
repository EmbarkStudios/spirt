fn main() -> std::io::Result<()> {
    match &std::env::args().collect::<Vec<_>>()[..] {
        [_, in_file, out_file] => {
            let module = spirt::Module::read_from_spv_file(in_file)?;

            let spv_spec = spirt::spv::spec::Spec::get();
            let (mut known, mut unknown) = (0, 0);
            for top_level in &module.top_level {
                match top_level {
                    spirt::TopLevel::SpvInst(inst) => {
                        eprint!("    ");

                        if let Some(id) = inst.result_id {
                            eprint!("%{}", id);
                            if let Some(type_id) = inst.result_type_id {
                                eprint!(": %{}", type_id);
                            }
                            eprint!(" = ");
                        }

                        eprint!(
                            "{}",
                            spv_spec.instructions.get_named(inst.opcode).unwrap().0
                        );
                        spirt::spv::OperandPrinter {
                            operands: inst.operands.iter(),
                            out: std::io::stderr().lock(),
                        }
                        .all_operands()
                        .unwrap();
                        eprintln!();
                        known += 1;
                    }
                    spirt::TopLevel::SpvUnknownInst { opcode, .. } => {
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
