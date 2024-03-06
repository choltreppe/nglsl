#
#    nglsl - a glsl dsl for nim
#        (c) Copyright 2024 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#

import std/macros
import ./nglsl/private/[ast, parsing, semantics]


macro shader*(body: untyped): string =
  var prog = parse(body)
  let symCount = bindSyms(prog)
  inferTyps(prog, symCount)
  newLit(genCode(prog))