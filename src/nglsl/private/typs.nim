#
#    nglsl - a glsl dsl for nim
#        (c) Copyright 2024 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#

import std/[macros, strutils, strformat, options]
import fusion/matching
import ./utils


type
  BasicTyp* = enum typBool="bool", typInt="int", typUint="uint", typFloat="float", typDouble="double"
  TypKind* = enum typVoid="void", typBasic, typImage="image", typSampler, typSamplerCube="samplerCube", typVec="vec", typMat="mat", typArray
  Typ* = ref object
    case kind*: TypKind
    of typBasic:
      typ*: BasicTyp
    of typSampler:
      samplerDim: int # 1..3
    of typVec:
      dim: int # 2..4
      vecTyp*: BasicTyp
    of typMat:
      cols*, rows*: int # 2..4
    of typArray:
      len*: Natural
      arrayTyp*: Typ
    else: discard

converter asTyp*(kind: TypKind): Typ = Typ(kind: kind)

converter asTyp*(typ: BasicTyp): Typ = Typ(kind: typBasic, typ: typ)

func newSamplerTyp*(dim: range[1..3]): Typ {.inline.} =
  Typ(kind: typSampler, samplerDim: dim)

func newVecTyp*(dim: range[1..4], typ: BasicTyp): Typ {.inline.} =
  if dim == 1: typ.asTyp
  else: Typ(kind: typVec, dim: dim, vecTyp: typ)

func newMatTyp*(cols, rows: range[2..4]): Typ {.inline.} =
  Typ(kind: typMat, cols: cols, rows: rows)

func newMatTyp*(dim: range[2..4]): Typ {.inline.} = newMatTyp(dim, dim)

func newArrayTyp*(len: Natural, typ: Typ): Typ {.inline.} =
  Typ(kind: typArray, len: len, arrayTyp: typ)


func dim*(typ: Typ): int =
  case typ.kind
  of typBasic: 1
  of typVec: typ.dim
  of typSampler: typ.samplerDim
  else:
    assert false, &"typ of kind `{typ.kind}` has no dim"
    0

func elemTyp*(typ: Typ): BasicTyp =
  case typ.kind
  of typBasic: typ.typ
  of typVec: typ.vecTyp
  else:
    assert false, &"typ of kind `{typ.kind}` has no elem typ"
    return

func isFloatOrVecf*(typ: Typ): bool {.inline.} =
  typ.kind in {typBasic, typVec} and typ.elemTyp == typFloat


proc `==`*(a, b: Typ): bool =
  if system.`==`(a, b): return true
  if system.`==`(a, nil) or system.`==`(b, nil): return false
  if a.kind != b.kind: return false
  case a.kind
  of typBasic: a.typ == b.typ
  of typSampler: a.samplerDim == b.samplerDim
  of typVec: a.dim == b.dim and a.vecTyp == b.vecTyp
  of typMat: a.rows == b.rows and a.cols == b.cols
  of typArray: a.len == b.len and a.arrayTyp == b.arrayTyp
  else: true


func `$`*(typ: Typ): string =
  func short(typ: BasicTyp): string {.inline.} =
    if typ == typFloat: ""
    else: ($typ)[0..0]
  case typ.kind
  of typBasic: $typ.typ
  of typSampler: &"sampler{typ.samplerDim}D"
  of typVec: &"{typ.vecTyp.short}vec{typ.dim}"
  of typMat:
    if typ.cols == typ.rows: &"mat{typ.cols}"
    else: &"mat{typ.cols}x{typ.rows}"
  of typArray: assert false; ""
  else: $typ.kind

template defGenericTyps(body) =
  when defined(nglslc):
    let genericTyps {.inject.} = block: body
  else:
    let genericTyps {.inject, compiletime.} = block: body
defGenericTyps:
    var typs: seq[(string, Typ)]
    proc addTyp(typ: Typ) = typs.add ($typ, typ)
    addTyp typImage
    addTyp typSamplerCube
    for dim in 1..3:
      addTyp newSamplerTyp(dim)
    for vecTyp in BasicTyp:
      for dim in 2..4:
        addTyp newVecTyp(dim, vecTyp)
    for vecTyp in BasicTyp:
      for cols in 2..4:
        for rows in 2..4:
          addTyp newMatTyp(cols, rows)
    typs

proc parseTyp*(name: string): Option[Typ] =
  for (n, typ) in genericTyps:
    if cmpIgnoreCase(name, n) == 0:
      return some(typ)
  try:
    some(parseEnum[BasicTyp](
      case name
      of "float32": "float"
      of "float64": "double"
      of "int32": "int"
      of "uint32": "uint"
      else: name
    ).asTyp)
  except: none(Typ)

proc parseTyp*(node: NimNode): Typ =
  case node.kind
  of nnkIdent:
    let name = node.repr
    if Some(@typ) ?= parseTyp(name): typ
    else: glslErr &"unknown type `{name}`", node
  
  of nnkBracketExpr:
    let baseName = node[0].repr
    if baseName == "array":
      if len(node) != 3:
        glslErr &"`array` expects exactly 2 generic parameters", node
      newArrayTyp(
        (if node[1].kind == nnkIntLit: node[1].intVal
        else: glslErr "expected int literal", node),
        parseTyp(node[2])
      )
    else:
      glslErr &"unknown type `{baseName}`", node
  
  of nnkEmpty: typVoid

  else:
    glslErr &"malformed type defenition: `{node.repr}`", node