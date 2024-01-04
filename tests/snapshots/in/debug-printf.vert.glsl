// `debugPrintfEXT`-using vertex shader, for use with `glslangValidator`, e.g.:
// `glslangValidator -V --target-env spirv1.3 debug-printf.vert.glsl -o debug-printf.vert.glsl.spv`

#version 450

#extension GL_EXT_debug_printf : enable

void main() {
    debugPrintfEXT("int=%u float=%f", 123, 123.456);
}
