#version 450

layout(location = 0) out int output0;

void main() {
    int o = 1;
    for (int i = 1; i < 10; i++)
    	  o *= i;
    output0 = o;
}
