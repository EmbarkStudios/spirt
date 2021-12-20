fn main() -> std::io::Result<()> {
    match &std::env::args().collect::<Vec<_>>()[..] {
        [_, in_file, out_file] => {
            let parser = spirt::spv::read::ModuleParser::read_from_spv_file(in_file)?;
            let mut emitter = spirt::spv::write::ModuleEmitter::with_header(parser.header);

            {
                // FIXME(eddyb) show more of the header.
                let [_, v, ..] = parser.header;
                eprintln!("SPIR-V {}.{} module:", v >> 16, (v >> 8) & 0xff);
            }

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

                eprint!("{}", inst.opcode.name());
                spirt::spv::print::inst_operands(
                    inst.opcode,
                    inst.imm_operands.iter().copied(),
                    inst.id_operands.iter().map(|id| format!("%{}", id)),
                )
                .for_each(|operand_parts| eprint!(" {}", operand_parts.concat()));

                eprintln!();

                emitter.push_inst(&inst).unwrap();
            }

            emitter.write_to_spv_file(out_file)
        }
        args => {
            eprintln!("Usage: {} IN OUT", args[0]);
            std::process::exit(1);
        }
    }
}
