const BASE_DIR_IN: &str = "tests/snapshots/in";
const BASE_DIR_OUT: &str = "tests/snapshots/out-spirt";
const BASE_DIR_IN_SPVASM: &str = "tests/snapshots/in-spvasm";
const BASE_DIR_OUT_SPVASM: &str = "tests/snapshots/out-spvasm";

#[test]
fn snapshots() {
    let paths = std::fs::read_dir(BASE_DIR_IN).unwrap();

    for path in paths {
        let path = path.unwrap().path();
        let file_name = path.file_name().unwrap().to_str().unwrap();
        let extension = path.extension().unwrap().to_str().unwrap();
        let spvasm_in_file = format!("{BASE_DIR_IN_SPVASM}/{file_name}.spvasm");
        let spvasm_out_file = format!("{BASE_DIR_OUT_SPVASM}/{file_name}.spvasm");
        let spirt_file = format!("{BASE_DIR_OUT}/{file_name}.spirt");

        let spirv_words = match extension {
            "wgsl" => {
                let file_contents = std::fs::read_to_string(&path).unwrap();
                let naga_module = naga::front::wgsl::parse_str(&file_contents).unwrap();
                let ir_capabilities = naga::valid::Capabilities::all();
                let module_info = naga::valid::Validator::new(
                    naga::valid::ValidationFlags::all(),
                    ir_capabilities,
                )
                .validate(&naga_module)
                .unwrap();
                let flags = naga::back::spv::WriterFlags::DEBUG;
                let spirv_out_options =
                    naga::back::spv::Options { lang_version: (1, 5), flags, ..Default::default() };
                let pipeline_options = None;
                naga::back::spv::write_vec(
                    &naga_module,
                    &module_info,
                    &spirv_out_options,
                    pipeline_options,
                )
                .unwrap()
            }
            "glsl" => {
                let spv_in_file_tmp = format!("{BASE_DIR_IN_SPVASM}/{file_name}.spv.tmp");
                let glslang_status = std::process::Command::new("glslangValidator")
                    .args([
                        "-V",
                        "-g",
                        "--target-env",
                        "spirv1.3",
                        "-g",
                        &path.to_str().unwrap(),
                        "-o",
                        &spv_in_file_tmp,
                    ])
                    .status()
                    .expect("Couldn't launch glslangValidator");
                assert!(glslang_status.success(), "Failed running glslangValidator");
                let spv_in_bytes = std::fs::read(&spv_in_file_tmp).unwrap();
                std::fs::remove_file(&spv_in_file_tmp).unwrap();
                bytemuck::cast_slice::<u8, u32>(&spv_in_bytes).to_vec()
            }
            "spvasm" => {
                let spv_in_file_tmp = format!("{BASE_DIR_IN_SPVASM}/{file_name}.spv.tmp");
                let glslang_status = std::process::Command::new("spirv-as")
                    .args([
                        "--target-env",
                        "spv1.3",
                        &path.to_str().unwrap(),
                        "-o",
                        &spv_in_file_tmp,
                    ])
                    .status()
                    .expect("Couldn't launch spirv-as");
                assert!(glslang_status.success(), "Failed running spirv-as");
                let spv_in_bytes = std::fs::read(&spv_in_file_tmp).unwrap();
                std::fs::remove_file(&spv_in_file_tmp).unwrap();
                bytemuck::cast_slice::<u8, u32>(&spv_in_bytes).to_vec()
            }
            _ => {
                panic!("Unsupported file extension: {extension}");
            }
        };
        let spirv_bytes = spirv_words.iter().flat_map(|val| val.to_le_bytes()).collect::<Vec<u8>>();
        spv_to_spvasm(&spirv_bytes, &spvasm_in_file);

        let mut spirt_module = spirt::Module::lower_from_spv_bytes(
            std::rc::Rc::new(spirt::Context::new()),
            spirv_bytes,
        )
        .unwrap();
        spirt::passes::legalize::structurize_func_cfgs(&mut spirt_module);
        let spirt_plan = spirt::print::Plan::for_module(&spirt_module);
        let spirt_pretty = spirt_plan.pretty_print();
        std::fs::write(spirt_file, spirt_pretty.to_string()).unwrap();

        let spirv_out_words = &spirt_module.lift_to_spv_module_emitter().unwrap().words;
        let spirv_out_bytes =
            spirv_out_words.iter().flat_map(|val| val.to_le_bytes()).collect::<Vec<u8>>();
        spv_to_spvasm(&spirv_out_bytes, &spvasm_out_file);
    }
}

#[cfg(test)]
fn spv_to_spvasm(spirv_bytes: &[u8], output_path: &str) {
    use std::io::Write;
    let output_file = std::fs::File::create(output_path).unwrap();
    let mut cmd = std::process::Command::new("spirv-dis")
        .args(["-"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::from(output_file))
        .spawn()
        .expect("Couldn't launch spirv-dis");

    let cmd_stdin = cmd.stdin.as_mut().unwrap();
    cmd_stdin.write_all(spirv_bytes).unwrap();
    cmd.wait().expect("Error running spirv-dis");
}
