fn main() -> std::io::Result<()> {
    match &std::env::args().collect::<Vec<_>>()[..] {
        [_, in_file] => {
            let module = spirt::Module::lower_from_spv_file(in_file)?;

            let print_operands = |operands: &[_]| {
                spirt::spv::print::OperandPrinter {
                    operands: operands.iter(),
                    out: std::io::stderr().lock(),
                }
                .all_operands()
                .unwrap();
            };

            let spv_spec = spirt::spv::spec::Spec::get();

            match &module.dialect {
                spirt::ModuleDialect::Spv(dialect) => {
                    eprintln!(
                        "SPIR-V {}.{} module:",
                        dialect.version_major, dialect.version_minor
                    );

                    if !dialect.capabilities.is_empty() {
                        eprintln!("  Capabilities:");
                        for &cap in &dialect.capabilities {
                            // HACK(eddyb) this is one shorter because
                            // `print_operands` always prints a space first.
                            eprint!("   ");
                            print_operands(&[spirt::spv::Operand::Imm(spirt::spv::Imm::Short(
                                spv_spec.well_known.capability,
                                cap,
                            ))]);
                            eprintln!();
                        }
                    }

                    if !dialect.extensions.is_empty() {
                        eprintln!("  Extensions:");
                        for ext in &dialect.extensions {
                            eprintln!("    {}", ext);
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

            Ok(())
        }
        args => {
            eprintln!("Usage: {} IN", args[0]);
            std::process::exit(1);
        }
    }
}
