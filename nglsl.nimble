# Package

version       = "0.1.1"
author        = "Joel Lienhard"
description   = "glsl dsl for nim"
license       = "MIT"
srcDir        = "src"
installExt    = @["nim"]
bin           = @["nglsl/private/nglslc"]


# Dependencies

requires "nim >= 2.0.2"
requires "fusion"
requires "jsony"