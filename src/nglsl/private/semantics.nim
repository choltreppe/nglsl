#
#    nglsl - a glsl dsl for nim
#        (c) Copyright 2024 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#

import std/[macros, sequtils, strutils, strformat, tables, options]
import fusion/matching
import ./utils, ./ast, ./typs, ./builtins


proc bindSyms*(prog: var Prog): int =  # returns sym count
  var nextSymId = 0
  proc addVar(symIds: var Table[string, int], v: var Var) =
    v.id = nextSymId
    symIds[v.name] = nextSymId
    inc nextSymId

  proc bindSyms(expr: var Expr, symIds: Table[string, int]) =
    case expr.kind
    of exprLit: discard

    of exprVar:
      if expr.v.name in symIds:
        expr.v.id = symIds[expr.v.name]
      else:
        glslErr &"`{expr.v.name}` not defined", expr.nimNode

    of exprArrayAcc:
      bindSyms(expr.arr, symIds)
      bindSyms(expr.index, symIds)

    of exprFieldAcc:
      bindSyms(expr.vec, symIds)

    of exprCall:
      for arg in expr.args.mitems:
        bindSyms(arg, symIds)

    of exprUnOp:
      bindSyms(expr.operand, symIds)

    of exprTernaryOp:
      bindSyms(expr.tcond, symIds)
      bindSyms(expr.tif, symIds)
      bindSyms(expr.telse, symIds)

    of exprBinOp:
      bindSyms(expr.lop, symIds)
      bindSyms(expr.rop, symIds)

    of exprPar:
      bindSyms(expr.expr, symIds)

  proc bindSyms(stmts: var StmtList, symIds: Table[string, int]) =
    var symIds = symIds
    for stmt in stmts.mitems:
      case stmt.kind
      of stmtExpr:
        bindSyms(stmt.expr, symIds)

      of stmtVarDef:
        symIds.addVar stmt.defVar
        if stmt.initVal != nil:
          bindSyms(stmt.initVal, symIds)

      of stmtAsgn:
        bindSyms(stmt.lval, symIds)
        bindSyms(stmt.rval, symIds)

      of stmtReturn:
        bindSyms(stmt.ret, symIds)

      of stmtIf:
        for (cond, body) in stmt.elifBranches.mitems:
          bindSyms(cond, symIds)
          bindSyms(body, symIds)
        bindSyms(stmt.elseBranch, symIds)

      of stmtWhile:
        bindSyms(stmt.whileCond, symIds)
        bindSyms(stmt.whileBody, symIds)

      of stmtFor:
        var symIds = symIds
        symIds.addVar stmt.forVar
        bindSyms(stmt.forBody, symIds)

  var symIds: Table[string, int]
  for def in prog.toplevelDefs.mitems:
    symIds.addVar def.v

  for funcs in prog.funcs.mvalues:
    for def in funcs.mitems:
      var symIds = symIds
      for param in def.params.mitems:
        symIds.addVar param.v
      bindSyms(def.body, symIds)

  nextSymId



proc assertLVal(expr: Expr) =
  case expr.kind
  of exprPar: assertLVal expr.expr
  of exprArrayAcc: assertLVal expr.arr
  of exprFieldAcc: assertLVal expr.vec
  of exprLit, exprCall, exprTernaryOp, exprUnOp, exprBinOp:
    glslErr &"`{expr}` is not a l-value", expr.nimNode
  else: discard


proc inferTyps*(prog: var Prog, symCount: int) =
  let funcs = prog.funcs
  var varTyps = newSeq[Typ](symCount)

  proc getTyp(expr: Expr): Typ =
    case expr.kind
    of exprVar: varTyps[expr.v.id]
    of exprLit: expr.typ
    of exprPar: getTyp(expr.expr)

    of exprArrayAcc:
      let indexTyp = getTyp(expr.index)
      assertEq indexTyp, typInt, expr.nimNode  #TODO: check actual typing rules
      let arrTyp = getTyp(expr.arr)
      case arrTyp.kind
      of typArray: arrTyp.arrayTyp
      of typVec: arrTyp.vecTyp
      of typMat: newVecTyp(arrTyp.cols, typFloat)
      else:
        glslErr &"expected a vec, mat or array type but got `{arrTyp}`", expr.nimNode

    of exprFieldAcc:
      const swizzelFields = ["xyzw", "stpq", "rgba"]
      let vecTyp = getTyp(expr.vec)
      if vecTyp.kind == typVec:
        for fieldSet in swizzelFields:
          if expr.fields[0] in fieldSet:
            for field in expr.fields:
              let i = fieldSet.find(field)
              if i < 0:
                glslErr &"unexpected `{field}` in swizzle", expr.nimNode
              if i >= vecTyp.dim:
                glslErr &"field `{field}` is out of range", expr.nimNode
            return
              if len(expr.fields) == 1: vecTyp.vecTyp.asTyp
              else: newVecTyp(len(expr.fields), vecTyp.vecTyp)
        glslErr &"unexpected `{expr.fields[0]}` in swizzle", expr.nimNode
      glslErr &"expected a vec type but got `{vecTyp}`", expr.nimNode

    of exprUnOp:
      let typ = getTyp(expr.operand)
      if expr.unop == opNot:
        assertEq typ, typBool, expr.nimNode
      else:
        assertNumberTyp typ, expr.nimNode
      typ

    of exprBinOp:
      let ltyp = getTyp(expr.lop)
      let rtyp = getTyp(expr.rop)
      case expr.binop
      of opAdd..opDiv:
        if expr.withAsgn: assertLVal expr.lop
        assertNumberTyp ltyp, rtyp, expr.nimNode
        for (atyp, btyp) in [(ltyp, rtyp), (rtyp, ltyp)]:
          if atyp.kind == typVec and btyp.kind == typBasic and atyp.vecTyp == btyp.typ:
            return atyp
        if expr.binop == opMul:
          template checkMatVecMul(m, v, vecAxis, otherAxis) =
            if m.kind == typMat and v.kind == typVec and
               v.vecTyp == typFloat and v.dim == m.otherAxis:
                  return newVecTyp(m.vecAxis, typFloat)
          checkMatVecMul(ltyp, rtyp, cols, rows)
          checkMatVecMul(rtyp, ltyp, rows, cols)
        tryUnify(expr.lop, ltyp, expr.rop, rtyp)
      of opEq..opGe:
        for typ in [ltyp, rtyp]:
          if typ.kind != typBasic or typ.typ == typBool:
            glslErr "expected a number type", expr.nimNode
        discard tryUnify(expr.lop, ltyp, expr.rop, rtyp)
        typBool
      of opAnd..opXor:
        assertEq ltyp, typBool, expr.nimNode
        assertEq rtyp, typBool, expr.nimNode
        typBool

    of exprTernaryOp:
      let condTyp = getTyp(expr.tcond)
      let ifTyp = getTyp(expr.tif)
      let elseTyp = getTyp(expr.telse)
      if condTyp != typBool:
        typErr expr.tcond.typ, typBool, expr.nimNode
      if ifTyp != elseTyp:
        glslErr &"types of ternary branches dont match `{ifTyp}` != `{elseTyp}`", expr.nimNode
      ifTyp

    of exprCall:
      let argTyps = expr.args.map(getTyp)

      # user defined
      if expr.funcName in funcs:
        for def in funcs[expr.funcName]:
          if len(def.params) == len(expr.args) and
             toSeq(0..<len(def.params)).allIt(def.params[it].typ == argTyps[it]):
                return def.retTyp

      # constructors
      let justOneBasicTyp = len(argTyps) == 1 and argTyps[0].kind == typBasic
      var combVecDim = 0  # -1 if not just vecs and basics
      for argTyp in argTyps:
        if argTyp.kind in {typBasic, typVec}:
          combVecDim += argTyp.dim
        else:
          combVecDim = -1
          break
      if Some(@typ) ?= parseTyp(expr.funcName):
        if (
          case typ.kind
          of typBasic: justOneBasicTyp
          of typVec: justOneBasicTyp or combVecDim >= typ.dim
          of typMat: justOneBasicTyp or combVecDim >= typ.cols * typ.rows  #TODO: support diagonal construction
          else: false
        ):
          return typ

      # builtin
      if Some(@typ) ?= tryCallBuiltin(expr.funcName, argTyps):
        return typ

      glslErr &"there is no `{expr.funcName}` with matching parameter types", expr.nimNode

  proc inferTyps(stmts: var StmtList, retTyp: Typ) =
    for stmt in stmts.mitems:
      case stmt.kind
      of stmtExpr:
        discard getTyp(stmt.expr)

      of stmtVarDef:
        if stmt.initVal != nil:
          let valTyp = getTyp(stmt.initVal)
          if stmt.varTyp == nil:
            stmt.varTyp = valTyp
            varTyps[stmt.defVar.id] = valTyp
          else:
            varTyps[stmt.defVar.id] = stmt.varTyp
            if valTyp == stmt.varTyp: discard
            elif valTyp.kind == stmt.varTyp.kind and valTyp.kind in {typBasic, typVec}:
              stmt.initVal.convertTo(stmt.varTyp)
            else:
              typErr valTyp, stmt.varTyp, stmt.nimNode

      of stmtAsgn:
        assertLVal stmt.lval
        assertEq getTyp(stmt.rval), getTyp(stmt.lval), stmt.nimNode

      of stmtReturn:
        assertEq getTyp(stmt.ret), retTyp, stmt.nimNode

      of stmtIf:
        for branch in stmt.elifBranches.mitems:
          let condTyp = getTyp(branch.cond)
          if condTyp != typBool:
            typErr condTyp, typBool, stmt.nimNode
          inferTyps branch.body, retTyp
        inferTyps stmt.elseBranch, retTyp

      of stmtWhile:
        let condTyp = getTyp(stmt.whileCond)
        if condTyp != typBool:
          typErr condTyp, typBool, stmt.nimNode
        inferTyps stmt.whileBody, retTyp

      of stmtFor:
        assert stmt.forVarTyp == nil
        stmt.forVarTyp = tryUnify(
          stmt.forRange.a, getTyp(stmt.forRange.a),
          stmt.forRange.b, getTyp(stmt.forRange.b)
        )
        varTyps[stmt.forVar.id] = stmt.forVarTyp
        if stmt.forVarTyp.kind != typBasic or stmt.forVarTyp.typ == typBool:
          glslErr &"expected a number type for a for-loop range, but got `{stmt.forVarTyp}`", stmt.nimNode
        inferTyps stmt.forBody, retTyp

  for def in prog.toplevelDefs:
    varTyps[def.v.id] = def.typ

  for funcs in prog.funcs.mvalues:
    for def in funcs.mitems:
      for param in def.params:
        varTyps[param.v.id] = param.typ
      inferTyps def.body, def.retTyp