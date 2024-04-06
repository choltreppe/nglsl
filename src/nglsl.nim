#
#    nglsl - a glsl dsl for nim
#        (c) Copyright 2024 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#

import std/[macros, tables]
import jsony
import ./nglsl/private/[ast, parsing]


when not declared(buildOS):
  const buildOS {.magic: "BuildOS".}: string = ""

const cmdPrefix =
  when buildOS == "windows": "cmd /C "
  else: ""

macro glsl*(body: untyped): string =
  let data = parse(body).toJson
  let (output, code) = gorgeEx(cmdPrefix & "nglslc", input=data, cache=data)
  if code == 0: newLit(output)
  else:
    echo output
    quit code