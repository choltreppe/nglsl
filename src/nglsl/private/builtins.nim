#
#    nglsl - a glsl dsl for nim
#        (c) Copyright 2024 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#

import std/[macros, options, tables]
import fusion/matching
import ./typs, ./ast


type
  PolyParamTypKind = enum specificTyp, polyDimVec, fullPoly, polyDimSampler
  PolyParamTyp = object
    case kind: PolyParamTypKind
    of specificTyp: typ: Typ
    of polyDimVec: elemTyp: BasicTyp 
    of fullPoly, polyDimSampler: discard

  PolyFuncTyp = object
    allowedDims: Slice[int]
    params: seq[PolyParamTyp]
    ret: PolyParamTyp

func polyVec: PolyParamTyp {.inline.} =
  PolyParamTyp(kind: fullPoly)

func polyVec(typ: BasicTyp): PolyParamTyp {.inline.} =
  PolyParamTyp(kind: polyDimVec, elemTyp: typ)

let polySampler {.compiletime.} = PolyParamTyp(kind: polyDimSampler)

converter asPolyTyp(typ: Typ): PolyParamTyp =
  PolyParamTyp(kind: specificTyp, typ: typ)

converter asPolyTyp(typ: BasicTyp): PolyParamTyp = typ.asTyp.asPolyTyp

template asPolyTyp(typ: PolyParamTyp): PolyParamTyp = typ

func pvFuncTyp(
  dims: Slice[int],
  params: seq[PolyParamTyp],
  ret: PolyParamTyp
): PolyFuncTyp {.inline.} =
  PolyFuncTyp(allowedDims: dims, params: params, ret: ret)

macro `->`(lhs: untyped, retTyp: PolyParamTyp): PolyFuncTyp =
  lhs.expectKind nnkCall
  lhs[0].expectKind nnkBracket
  let dims = lhs[0][0]
  var params = nnkBracket.newTree()
  for param in lhs[1..^1]:
    params.add newCall(bindSym"asPolyTyp", param)
  quote do:
    pvFuncTyp(`dims`, @`params`, `retTyp`)

func match(args: var seq[Expr], funcTyp: PolyFuncTyp): Option[Typ] =   #TODO: handle conversion of args  (`tyUnify`)
  if len(args) != len(funcTyp.params): return

  var dim = -1
  var vecTyp: Option[BasicTyp]
  var conversions: seq[tuple[argId: int, typ: Typ]]  # to defer conversions after func id completely checked

  for i, arg in args.mpairs:
    let paramTyp = funcTyp.params[i]

    template checkDim =
      if dim == -1:
        dim = arg.typ.dim
        if dim notin funcTyp.allowedDims: return
      elif arg.typ.dim != dim: return

    case paramTyp.kind
    of specificTyp:
      if arg.typ == paramTyp.typ: discard
      elif arg.typ.isConvertableTo(paramTyp.typ):
        conversions &= (i, paramTyp.typ)
      else: return

    of polyDimVec:
      if arg.typ.kind in {typBasic, typVec} and
         arg.typ.elemTyp.isConvertableTo(paramTyp.elemTyp):
          checkDim()
          conversions &= (i, newVecTyp(dim, paramTyp.elemTyp))
      else: return

    of fullPoly:
      if arg.typ.kind in {typBasic, typVec}:
        checkDim()
        if Some(@vecTyp) ?= vecTyp:
          if arg.typ.elemTyp != vecTyp: return
        else:
          vecTyp = some(arg.typ.elemTyp)
      else: return

    of polyDimSampler:
      if arg.typ.kind == typSampler: checkDim()
      else: return

  for (i, typ) in conversions:
    args[i].convertTo(typ)

  some:
    case funcTyp.ret.kind
    of specificTyp: funcTyp.ret.typ
    of polyDimVec: newVecTyp(dim, funcTyp.ret.elemTyp)
    of fullPoly: newVecTyp(dim, vecTyp.get)
    of polyDimSampler: newSamplerTyp(dim)


let polyFloatVec {.compiletime.} = polyVec(typFloat)
let compwiseFloatFuncTyp {.compiletime.} = [1..4](polyFloatVec) -> polyFloatVec

let builtinFuncs {.compiletime.} = toTable {
  "radians": @[compwiseFloatFuncTyp],
  "degrees": @[compwiseFloatFuncTyp],
  "sin": @[compwiseFloatFuncTyp],
  "cos": @[compwiseFloatFuncTyp],
  "tan": @[compwiseFloatFuncTyp],
  "asin": @[compwiseFloatFuncTyp],
  "acos": @[compwiseFloatFuncTyp],
  "atan": @[
    [1..4](polyFloatVec, polyFloatVec) -> polyFloatVec,
    compwiseFloatFuncTyp,
  ],

  "pow": @[ [1..4](polyFloatVec, polyFloatVec) -> polyFloatVec ],
  "exp": @[compwiseFloatFuncTyp],
  "log": @[compwiseFloatFuncTyp],
  "exp2": @[compwiseFloatFuncTyp],
  "log2": @[compwiseFloatFuncTyp],
  "sqrt": @[compwiseFloatFuncTyp],
  "inversesqrt": @[compwiseFloatFuncTyp],

  "abs": @[compwiseFloatFuncTyp],
  "sign": @[compwiseFloatFuncTyp],
  "floor": @[compwiseFloatFuncTyp],
  "ceil": @[compwiseFloatFuncTyp],
  "fract": @[compwiseFloatFuncTyp],
  "mod": @[
    [1..4](polyFloatVec, polyFloatVec) -> polyFloatVec,
    [1..4](polyFloatVec, typFloat) -> polyFloatVec
  ],
  "min": @[
    [1..4](polyFloatVec, polyFloatVec) -> polyFloatVec,
    [1..4](polyFloatVec, typFloat) -> polyFloatVec
  ],
  "max": @[
    [1..4](polyFloatVec, polyFloatVec) -> polyFloatVec,
    [1..4](polyFloatVec, typFloat) -> polyFloatVec
  ],
  "clamp": @[
    [1..4](polyFloatVec, polyFloatVec, polyFloatVec) -> polyFloatVec,
    [1..4](polyFloatVec, typFloat, typFloat) -> polyFloatVec,
  ],
  "mix": @[
    [1..4](polyFloatVec, polyFloatVec, polyFloatVec) -> polyFloatVec,
    [1..4](polyFloatVec, polyFloatVec, typFloat) -> polyFloatVec,
  ],
  "step": @[
    [1..4](polyFloatVec, polyFloatVec) -> polyFloatVec,
    [1..4](typFloat, polyFloatVec) -> polyFloatVec
  ],
  "smoothstep": @[
    [1..4](polyFloatVec, polyFloatVec, polyFloatVec) -> polyFloatVec,
    [1..4](typFloat, typFloat, polyFloatVec) -> polyFloatVec
  ],

  "length": @[ [2..4](polyFloatVec) -> typFloat ],
  "distance": @[ [2..4](polyFloatVec, polyFloatVec) -> typFloat ],
  "dot": @[ [2..4](polyFloatVec, polyFloatVec) -> typFloat ],
  "cross": @[ [2..4](newVecTyp(3, typFloat), newVecTyp(3, typFloat)) -> newVecTyp(3, typFloat) ],
  "normalize": @[ [2..4](polyFloatVec) -> polyFloatVec ],
  "faceforward": @[ [2..4](polyFloatVec, polyFloatVec, polyFloatVec) -> polyFloatVec ],
  "reflect": @[ [2..4](polyFloatVec, polyFloatVec) -> polyFloatVec ],
  "refract": @[ [2..4](polyFloatVec, polyFloatVec, typFloat) -> polyFloatVec ],

  "lessThan": @[ [2..4](polyVec(), polyVec()) -> polyVec(typBool) ],
  "lessThanEqual": @[ [2..4](polyVec(), polyVec()) -> polyVec(typBool) ],
  "greaterThan": @[ [2..4](polyVec(), polyVec()) -> polyVec(typBool) ],
  "greaterThanEqual": @[ [2..4](polyVec(), polyVec()) -> polyVec(typBool) ],
  "equal": @[ [2..4](polyVec(), polyVec()) -> polyVec(typBool) ],
  "notEqual": @[ [2..4](polyVec(), polyVec()) -> polyVec(typBool) ],
  "any": @[ [2..4](polyVec(typBool)) -> typBool ],
  "all": @[ [2..4](polyVec(typBool)) -> typBool ],
  # TODO not func (is not that simple because `not` is an operator in nimified version)

  "texture": @[
    [1..1](newSamplerTyp(1), typFloat) -> newVecTyp(4, typFloat),
    [2..3](polySampler, polyVec(typFloat)) -> newVecTyp(4, typFloat),
    [3..3](Typ(kind: typSamplerCube), newVecTyp(3, typFloat)) -> newVecTyp(4, typFloat)
  ],
  "textureLod": @[
    [1..1](newSamplerTyp(1), typFloat, typFloat) -> newVecTyp(4, typFloat),
    [2..3](polySampler, polyVec(typFloat), typFloat) -> newVecTyp(4, typFloat)
  ]
}

proc tryCallBuiltin*(funcName: string, args: var seq[Expr]): Option[Typ] =
  if funcName in builtinFuncs:
    for funcTyp in builtinFuncs[funcName]:
      result = match(args, funcTyp)
      if result.isSome: break



let builtinVars* {.compiletime.}: seq[tuple[name: string, typ: Typ]] = @{
  "gl_Position": newVecTyp(4, typFloat),
  "gl_PointSize": typFloat.asTyp,

  "gl_FragCoord": newVecTyp(4, typFloat),
  "gl_FrontFacing": typBool.asTyp,
  "gl_PointCoord": newVecTyp(2, typFloat),
  
  "gl_FragColor": newVecTyp(4, typFloat)
  #TODO: gl_FragCoordData  (needs dyn array type)
}