nglsl is a nim-ified version of glsl to write shaders inside nim without having to switch between syntaxes.
I know there is [shady](https://github.com/treeform/shady) but it had a bug that prevented me from using it and it doesnt have full type-inference.
So I made this as a little side project for my own game project. Maybe its useful for someone ales aswell so Im sharing it here (but you probably want to use shady instead since it has the added benefit if debugging code on cpu).

You can find examples in `tests/test.nim`. The first shader is just nonsense to test out the syntax.
