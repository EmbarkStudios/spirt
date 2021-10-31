fn main() -> std::io::Result<()> {
    match &std::env::args().collect::<Vec<_>>()[..] {
        [_, in_file, out_file] => {
            let module = spirt::Module::lower_from_spv_file(in_file)?;
            module.lift_to_spv_file(out_file)?;

            // FIXME(eddyb) dump the module without reading the just-written file.
            let parser = spirt::spv::read::ModuleParser::read_from_spv_file(out_file)?;

            // FIXME(eddyb) deduplicate the rest of this function between this
            // example and `spv-read-write-roundtrip`.
            let print_operands = |operands: &[_]| {
                spirt::spv::print::OperandPrinter {
                    operands: operands.iter(),
                    out: std::io::stderr().lock(),
                }
                .all_operands()
                .unwrap();
            };

            {
                // FIXME(eddyb) show more of the header.
                let [_, v, ..] = parser.header;
                eprintln!("SPIR-V {}.{} module:", v >> 16, (v >> 8) & 0xff);
            }

            let spv_spec = spirt::spv::spec::Spec::get();
            for inst in parser {
                let inst = inst.unwrap();

                eprint!("  ");

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

            Ok(())
        }
        args => {
            eprintln!("Usage: {} IN OUT", args[0]);
            std::process::exit(1);
        }
    }
}
