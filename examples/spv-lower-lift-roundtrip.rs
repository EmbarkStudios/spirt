use std::rc::Rc;

fn main() -> std::io::Result<()> {
    match &std::env::args().collect::<Vec<_>>()[..] {
        [_, in_file, out_file] => {
            let module =
                spirt::Module::lower_from_spv_file(Rc::new(spirt::Context::new()), in_file)?;
            module.lift_to_spv_file(out_file)?;

            // FIXME(eddyb) dump the module without reading the just-written file.
            let parser = spirt::spv::read::ModuleParser::read_from_spv_file(out_file)?;

            // FIXME(eddyb) deduplicate the rest of this function between this
            // example and `spv-read-write-roundtrip`.

            {
                // FIXME(eddyb) show more of the header.
                let [_, v, ..] = parser.header;
                eprintln!("SPIR-V {}.{} module:", v >> 16, (v >> 8) & 0xff);
            }

            for inst in parser {
                let inst = inst.unwrap();

                eprint!("  ");

                if let Some(id) = inst.result_id {
                    eprint!("%{id}");
                    if let Some(type_id) = inst.result_type_id {
                        eprint!(": %{type_id}");
                    }
                    eprint!(" = ");
                }

                eprint!("{}", inst.opcode.name());
                spirt::spv::print::inst_operands(
                    inst.opcode,
                    inst.imms.iter().copied(),
                    inst.ids.iter().map(|id| format!("%{id}")),
                )
                .for_each(|operand_parts| eprint!(" {}", operand_parts.concat_to_plain_text()));

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
