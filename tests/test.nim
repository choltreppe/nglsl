import nglsl


let testShader = shader:
  let
    a, b, x: Vec3
    texMap: uniform Sampler2D
    finalColor: out Vec4

  proc test(a, b: Vec2): Vec4 =
    let v = a * b
    let w = vec3(a, 0).cross vec3(b, 1)
    let x: bool = 0.8 + 1

    if not (a.x > 0.8) and b.y < 1.0:
      return vec4(0, a*b, 1).normalize()
    else:
      return if a.y == 0.0: vec4(1) else: vec4(0)

  proc main =
    finalColor += test(vec2(1, 0), vec2(0.8, 0.5))

debugEcho "\n", testShader, "\n"