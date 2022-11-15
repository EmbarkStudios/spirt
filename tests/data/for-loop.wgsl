// Simple control-flow example (for `README.md`).
// NOTE(eddyb) should be equivalent to `for-loop.vert.glsl`.

@vertex
fn main() -> @location(0) i32 {
    var o: i32 = 1;
    for(var i: i32 = 1; i < 10; i++) {
        o *= i;
    }
    return o;
}
