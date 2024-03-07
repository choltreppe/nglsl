import nglsl


let testShader = shader:
  var
    a, b, x: Vec3
    texMap: uniform Sampler2D
    finalColor: out Vec4

  proc test(a, b: Vec2): Vec4 =
    var v = a * b
    var w = vec3(a, 0).cross vec3(b, 1)
    var x = 0.8 + 1
    if not (a.x > 0.8) and b.y < 1.0:
      for i in 2 ..< a.x:
        x += i
      var j = 6
      while j > 3:
        --j
        x += j
      return vec4(0, a*b, 1).normalize()
    else:
      return if a.y == 0.0: vec4(1) else: vec4(0)

  proc main =
    finalColor += test(vec2(1, 0), vec2(0.8, 0.5))

debugEcho "\n", testShader, "\n"


let exampleShader = shader:
  var 
    fragPosition, fragNormal: Vec3
    viewPos, lightDir, baseColor, shadowColor, highlightColor: uniform Vec3
    finalColor: out Vec4

  proc main =

    finalColor = vec4(baseColor, 1)

    let viewDir = normalize(viewPos - fragPosition)
    let reflected = normalize(lightDir - 2*dot(lightDir, fragNormal)*fragNormal)
    if dot(viewDir, reflected) > 0.9:
      finalColor = vec4(highlightColor, 1)

    let shadow = clamp(dot(-lightDir, fragNormal), 0.0, 1.0)
    finalColor = mix(vec4(shadowColor, 1), finalColor, shadow)

debugEcho "\n", exampleShader, "\n"