import nimsl


let testShader = shader:
  let
    a, b: Vec3
    texMap: uniform Sampler2D
    finalColor: out Vec4

  proc test(a, b: Vec2): Vec4 =
    let
      x: Vec2 = vec2(1)
      y, z: int = 1
    return if true: vec4((a + vec2(1, 2)) * 0.4, b.yx) else: vec4(1)

  proc main =
    finalColor = vec4(a.cross b, 1)
    finalColor += vec4(Vec3(0.1), 0)

debugEcho "\n", testShader