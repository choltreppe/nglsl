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
  PolyVecParamTypKind = enum specificTyp, polyDimVec, fullPolyVec
  PolyVecParamTyp = object
    case kind: PolyVecParamTypKind
    of specificTyp: typ: Typ
    of polyDimVec: elemTyp: BasicTyp 
    of fullPolyVec: discard

  PolyVecFuncTyp = object
    allowedDims: Slice[int]
    params: seq[PolyVecParamTyp]
    ret: PolyVecParamTyp

func polyVec: PolyVecParamTyp {.inline.} =
  PolyVecParamTyp(kind: fullPolyVec)

func polyVec(typ: BasicTyp): PolyVecParamTyp {.inline.} =
  PolyVecParamTyp(kind: polyDimVec, elemTyp: typ)

converter asPolyTyp(typ: Typ): PolyVecParamTyp =
  PolyVecParamTyp(kind: specificTyp, typ: typ)

converter asPolyTyp(typ: BasicTyp): PolyVecParamTyp = typ.asTyp.asPolyTyp

template asPolyTyp(typ: PolyVecParamTyp): PolyVecParamTyp = typ

func pvFuncTyp(
  dims: Slice[int],
  params: seq[PolyVecParamTyp],
  ret: PolyVecParamTyp
): PolyVecFuncTyp {.inline.} =
  PolyVecFuncTyp(allowedDims: dims, params: params, ret: ret)

macro `->`(lhs: untyped, retTyp: PolyVecParamTyp): PolyVecFuncTyp =
  lhs.expectKind nnkCall
  lhs[0].expectKind nnkBracket
  let dims = lhs[0][0]
  var params = nnkBracket.newTree()
  for param in lhs[1..^1]:
    params.add newCall(bindSym"asPolyTyp", param)
  quote do:
    pvFuncTyp(`dims`, @`params`, `retTyp`)

func match(args: var seq[Expr], funcTyp: PolyVecFuncTyp): Option[Typ] =   #TODO: handle conversion of args  (`tyUnify`)
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
      if arg.typ.isConvertableTo(paramTyp.typ):
        conversions &= (i, paramTyp.typ)
      else: return

    of polyDimVec:
      if arg.typ.kind in {typBasic, typVec} and
         arg.typ.elemTyp.isConvertableTo(paramTyp.elemTyp):
          checkDim()
          conversions &= (i, newVecTyp(dim, paramTyp.elemTyp))
      else: return

    of fullPolyVec:
      if arg.typ.kind in {typBasic, typVec}:
        checkDim()
        if Some(@vecTyp) ?= vecTyp:
          if arg.typ.elemTyp != vecTyp: return
        else:
          vecTyp = some(arg.typ.elemTyp)
      else: return

  for (i, typ) in conversions:
    args[i].convertTo(typ)

  some:
    case funcTyp.ret.kind
    of specificTyp: funcTyp.ret.typ
    of polyDimVec: newVecTyp(dim, funcTyp.ret.elemTyp)
    of fullPolyVec: newVecTyp(dim, vecTyp.get)


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

  "texture2DLod": @[
    [2..2](newSamplerTyp(2), newVecTyp(2, typFloat)) -> newVecTyp(4, typFloat),
    [2..2](newSamplerTyp(2), newVecTyp(2, typFloat), typFloat) -> newVecTyp(4, typFloat)
  ],
  "texture2DLodProj": @[
    [3..4](newSamplerTyp(2), polyVec(typFloat)) -> newVecTyp(4, typFloat),
    [3..4](newSamplerTyp(2), polyVec(typFloat), typFloat) -> newVecTyp(4, typFloat)
  ],
}

proc tryCallBuiltin*(funcName: string, args: var seq[Expr]): Option[Typ] =
  if funcName in builtinFuncs:
    for funcTyp in builtinFuncs[funcName]:
      result = match(args, funcTyp)
      if result.isSome: break