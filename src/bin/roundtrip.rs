fn main() -> std::io::Result<()> {
    match &std::env::args().collect::<Vec<_>>()[..] {
        [_, in_file, out_file] => {
            let module = spirt::Module::read_from_spv_file(in_file)?;

            let print_operands = |operands: &[_]| {
                spirt::spv::OperandPrinter {
                    operands: operands.iter(),
                    out: std::io::stderr().lock(),
                }
                .all_operands()
                .unwrap();
            };

            let spv_spec = spirt::spv::spec::Spec::get();

            match &module.layout {
                spirt::ModuleLayout::Spv(layout) => {
                    let v = layout.header_version;
                    eprintln!("SPIR-V {}.{} module:", v >> 16, (v >> 8) & 0xff);

                    if !layout.capabilities.is_empty() {
                        eprintln!("  Capabilities:");
                        for &cap in &layout.capabilities {
                            eprint!("    ");
                            print_operands(&[spirt::SpvOperand::ShortImm(
                                spv_spec.well_known.capability,
                                cap,
                            )]);
                            eprintln!();
                        }
                    }
                }
            }

            eprintln!("  All other instructions:");
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
                        print_operands(&inst.operands);
                        eprintln!();
                    }
                }
            }

            module.write_to_spv_file(out_file)
        }
        args => {
            eprintln!("Usage: {} IN OUT", args[0]);
            std::process::exit(1);
        }
    }
}
