//! Vulkan layer that can rewrite SPIR-V shaders passed to Vulkan commands.

use ash::{self, prelude::*, vk};
use lazy_static::lazy_static;
use std::rc::Rc;
use std::sync::Arc;
use vulkan_layer::auto_deviceinfo_impl;
use vulkan_layer::DeviceHooks;
use vulkan_layer::LayerResult;
use vulkan_layer::{
    declare_introspection_queries, Global, Layer, LayerManifest, StubGlobalHooks, StubInstanceInfo,
};

#[derive(Default)]
struct Config {
    verbose: bool,
    spv_copy: bool,
    spirt_passes: Option<Vec<String>>,
}

lazy_static! {
    static ref CONFIG: Config = {
        let var_name = "VK_LAYER_SPIRT_CONFIG";
        let var_contents = std::env::var(var_name)
            .unwrap_or_else(|e| panic!("env var `{var_name}` is required: {e:?}"));

        let mut config = Config::default();
        for part in var_contents.split('+') {
            if part == "verbose" {
                config.verbose = true;
            } else if part == "spv-copy" {
                config.spv_copy = true;
            } else if let Some(passes) = part.strip_prefix("spirt-passes=") {
                config.spirt_passes = Some(
                    passes.split(',').filter(|s| !s.is_empty()).map(|s| s.to_string()).collect(),
                );
            } else {
                panic!(
                    "`{var_name}` should contain `+`-separated `verbose`/`spv-copy`/`spirt-passes=...`"
                );
            }
        }
        if config.spv_copy == config.spirt_passes.is_some() {
            panic!("`{var_name}` should have exactly one of `spv-copy` or `spirt-passes=...`");
        }
        config
    };
}

#[derive(Default)]
struct ShadersLayer(StubGlobalHooks);

struct ShadersDeviceHooks {
    config: &'static Config,
    spv_spec: &'static spirt::spv::spec::Spec,
    device_as_next: Arc<ash::Device>,
}

impl Layer for ShadersLayer {
    type GlobalHooksInfo = StubGlobalHooks;
    type InstanceInfo = StubInstanceInfo;
    type DeviceInfo = ShadersDeviceHooks;
    type InstanceInfoContainer = Self::InstanceInfo;
    type DeviceInfoContainer = Self::DeviceInfo;

    fn global_instance() -> &'static Global<Self> {
        lazy_static! {
            static ref GLOBAL: Global<ShadersLayer> = Default::default();
        }
        &GLOBAL
    }

    fn manifest() -> LayerManifest {
        let mut manifest = LayerManifest::default();
        manifest.name = "VK_LAYER_SPIRT_shaders";
        manifest.spec_version = vk::API_VERSION_1_1;
        manifest.description = "SPIR-T-based shader rewriter layer";
        manifest
    }

    fn global_hooks_info(&self) -> &Self::GlobalHooksInfo {
        &self.0
    }

    fn create_instance_info(
        &self,
        _: &vk::InstanceCreateInfo,
        _: Option<&vk::AllocationCallbacks>,
        _: Arc<ash::Instance>,
        _next_get_instance_proc_addr: vk::PFN_vkGetInstanceProcAddr,
    ) -> Self::InstanceInfoContainer {
        Default::default()
    }

    fn create_device_info(
        &self,
        _: vk::PhysicalDevice,
        _: &vk::DeviceCreateInfo,
        _: Option<&vk::AllocationCallbacks>,
        device_as_next: Arc<ash::Device>,
        _next_get_device_proc_addr: vk::PFN_vkGetDeviceProcAddr,
    ) -> ShadersDeviceHooks {
        ShadersDeviceHooks {
            config: &CONFIG,
            spv_spec: spirt::spv::spec::Spec::get(),
            device_as_next,
        }
    }
}

declare_introspection_queries!(Global::<ShadersLayer>);

// FIXME(eddyb) stop abusing `io::Error` for error reporting.
fn invalid(reason: &str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, format!("malformed SPIR-V ({reason})"))
}

impl ShadersDeviceHooks {
    fn timed_pass<R>(&self, name: &str, f: impl FnOnce() -> R) -> R {
        if !self.config.verbose {
            return f();
        }

        let start = std::time::Instant::now();
        let r = f();
        eprintln!("[{:8.3}ms] {name}", start.elapsed().as_secs_f64() * 1000.0);
        r
    }

    fn process_shader(&self, in_spv_bytes: &[u8]) -> std::io::Result<Vec<u32>> {
        let in_spv_words = bytemuck::cast_slice::<u8, u32>(in_spv_bytes);

        if self.config.spv_copy {
            if !in_spv_words.starts_with(&[self.spv_spec.magic]) {
                return Err(invalid("does not start with SPIR-V magic number"));
            }
            return Ok(in_spv_words.to_vec());
        }
        let spirt_passes = self.config.spirt_passes.as_ref().unwrap();

        if self.config.verbose {
            eprintln!();
        }

        // FIXME(eddyb) there should be no conversion necessary to use `&[u32]`.
        let mut module = self.timed_pass("Module::lower_from_spv_bytes", || {
            spirt::Module::lower_from_spv_bytes(
                Rc::new(spirt::Context::new()),
                bytemuck::cast_slice(in_spv_words).to_vec(),
            )
        })?;

        // FIXME(eddyb) this should be its own
        if self.config.verbose {
            let (printed_deps, printed_exports) =
                spirt::print::Plan::for_module(&module).pretty_print_deps_and_root_separately();
            let printed_deps = printed_deps.to_string();
            let printed_deps_lines = printed_deps.lines().collect::<Vec<_>>();
            const CONTEXT: usize = 100;
            eprintln!("```spirt");
            if printed_deps_lines.len() <= CONTEXT * 2 {
                eprintln!("{}", printed_deps_lines.join("\n"));
            } else {
                eprintln!("{}", printed_deps_lines[..CONTEXT].join("\n"));
                eprintln!("··· {} lines skipped ···", printed_deps_lines.len() - CONTEXT * 2);
                eprintln!(
                    "{}",
                    printed_deps_lines[printed_deps_lines.len() - CONTEXT..].join("\n")
                );
            }
            eprintln!("{printed_exports}");
            eprintln!("```");
        }

        self.timed_pass("legalize::structurize_func_cfgs", || {
            spirt::passes::legalize::structurize_func_cfgs(&mut module)
        });

        for pass in spirt_passes {
            match &pass[..] {
                "qptr" => {
                    let layout_config = &spirt::qptr::LayoutConfig {
                        abstract_bool_size_align: (1, 1),
                        logical_ptr_size_align: (8, 8),
                        ..spirt::qptr::LayoutConfig::VULKAN_SCALAR_LAYOUT
                    };

                    self.timed_pass("qptr::lower_from_spv_ptrs", || {
                        spirt::passes::qptr::lower_from_spv_ptrs(&mut module, layout_config)
                    });
                    self.timed_pass("qptr::analyze_uses", || {
                        spirt::passes::qptr::analyze_uses(&mut module, layout_config)
                    });
                    self.timed_pass("qptr::lift_to_spv_ptrs", || {
                        spirt::passes::qptr::lift_to_spv_ptrs(&mut module, layout_config)
                    });
                }
                _ => unimplemented!("unknown pass {pass}"),
            }
        }

        let out_spv_module_emitter = self.timed_pass("Module::lift_to_spv_module_emitter", || {
            module.lift_to_spv_module_emitter()
        });
        Ok(out_spv_module_emitter.unwrap().words)
    }
}

#[auto_deviceinfo_impl]
impl DeviceHooks for ShadersDeviceHooks {
    fn create_shader_module(
        &self,
        create_info: &vk::ShaderModuleCreateInfo,
        allocation_callbacks: Option<&vk::AllocationCallbacks>,
    ) -> LayerResult<VkResult<vk::ShaderModule>> {
        let mut create_info = *create_info;
        let in_spv_bytes = unsafe {
            std::slice::from_raw_parts(create_info.p_code as *const u8, create_info.code_size)
        };

        let out_spv_words = match self.process_shader(in_spv_bytes) {
            Ok(spv_words) => spv_words,
            Err(e) => {
                eprintln!("[VK_LAYER_SPIRT_shaders] ERROR in vkCreateShaderModule: {e}");
                return LayerResult::Handled(Err(vk::Result::ERROR_INITIALIZATION_FAILED));
            }
        };

        // FIXME(eddyb) can we use the builder here somehow?
        create_info.p_code = out_spv_words.as_ptr();
        create_info.code_size = out_spv_words.len() * 4;

        let result =
            unsafe { self.device_as_next.create_shader_module(&create_info, allocation_callbacks) };

        LayerResult::Handled(result)
    }
}
