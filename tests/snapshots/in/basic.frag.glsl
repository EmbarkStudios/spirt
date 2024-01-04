// Minimal fragment shader, for use with `glslangValidator`, e.g. full command
// for a debuginfo build (the `--target-env` is to get `OpModuleProcessed`):
// `glslangValidator -V --target-env spirv1.3 -g basic.frag.glsl -o basic.frag.glsl.dbg.spv`

#version 450

// NOTE(eddyb) some arbitrary extension for `OpSourceExtension`.
#extension GL_EXT_scalar_block_layout : enable

layout(location = 0) out vec4 output_color;

void main() {
    output_color = vec4(1.0);
}
