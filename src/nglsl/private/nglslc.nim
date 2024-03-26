#
#    nglslc - prebuild compiler for nglsl
#        (c) Copyright 2024 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#

{.define: nglslc.}

import jsony
import ./ast, ./semantics

var prog = readAll(stdin).fromJson(Prog)
let symCount = bindSyms(prog)
inferTyps(prog, symCount)
echo genCode(prog)