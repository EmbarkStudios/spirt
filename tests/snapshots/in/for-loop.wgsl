@vertex
fn main() -> @builtin(position) vec4<f32> {
    var o: i32 = 1;
    for(var i: i32 = 1; i < 10; i++) {
    	o *= i;
    }
    return vec4(f32(o), 1, 1, 1);
}
