#
#    nimsl - a glsl dsl for nim
#        (c) Copyright 2024 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#

template glslErr*(msg: string, node: NimNode) =
  error "[GLSL] "&msg, node
  return