import nglsl


let testShader = glsl:
  var
    a, b, x: Vec3
    texture0: uniform SamplerCube
    finalColor: out Vec4

  proc test(a, b: Vec2, tex: SamplerCube): Vec4 =
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
    finalColor = texture(texture0, a)
    finalColor += test(vec2(1, 0), vec2(0.8, 0.5), texture0)

debugEcho "\n", testShader, "\n"


let exampleVertShader = glsl:
  var
    vertexPosition, vertexNormal: Vec3
    mvp, matModel, matNormal: uniform Mat4
    fragPosition, fragNormal: out Vec3

  proc main =
    fragPosition = vec3(matModel * vec4(vertexPosition, 1.0))
    fragNormal = normalize(vec3(matNormal * vec4(vertexNormal, 1.0)))
    gl_Position = mvp * vec4(vertexPosition, 1.0)

let exampleFragShader = glsl:
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

    let shadow = clamp(dot(-lightDir, fragNormal), 0, 1)
    finalColor = mix(vec4(shadowColor, 1), finalColor, shadow)

debugEcho "\n", exampleVertShader, "\n"
debugEcho "\n", exampleFragShader, "\n"