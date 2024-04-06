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


let builtinVarIds = block:
  var res: Table[string, int]
  for i, (name, _) in builtinVars:
    res[name] = i
  res

proc bindSyms*(prog: var Prog): int =  # returns sym count
  var nextSymId = len(builtinVars)
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
        glslErr &"`{expr.v.name}` not defined", expr.lineInfo

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
        bindSyms(stmt.forRange.a, symIds)
        bindSyms(stmt.forRange.b, symIds)
        bindSyms(stmt.forBody, symIds)

  var symIds = builtinVarIds
  for def in prog.toplevelDefs.mitems:
    symIds.addVar def.v
  for c in prog.consts.mitems:
    symIds.addVar c.v

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
    glslErr &"`{expr}` is not a l-value", expr.lineInfo
  else: discard


let builtinVarTyps = builtinVars.mapIt(it.typ)

proc inferTyps*(prog: var Prog, symCount: int) =
  let funcs = prog.funcs
  var varTyps = builtinVarTyps
  varTyps.setLen symCount

  proc inferTyps(expr: var Expr) =
    case expr.kind
    of exprVar: expr.typ = varTyps[expr.v.id]
    of exprLit: discard
    of exprPar:
      inferTyps expr.expr
      expr.typ = expr.expr.typ

    of exprArrayAcc:
      inferTyps expr.index
      assertEq expr.index.typ, typInt, expr.lineInfo  #TODO: check actual typing rules
      inferTyps expr.arr
      expr.typ =
        case expr.arr.typ.kind
        of typArray: expr.arr.typ.arrayTyp
        of typVec: expr.arr.typ.elemTyp
        of typMat: newVecTyp(expr.arr.typ.cols, typFloat)
        else:
          glslErr &"expected a vec, mat or array type but got `{expr.arr.typ}`", expr.lineInfo

    of exprFieldAcc:
      const swizzelFields = ["xyzw", "stpq", "rgba"]
      inferTyps expr.vec
      let typ = expr.vec.typ
      if typ.kind == typVec:
        for fieldSet in swizzelFields:
          if expr.fields[0] in fieldSet:
            for field in expr.fields:
              let i = fieldSet.find(field)
              if i < 0:
                glslErr &"unexpected `{field}` in swizzle", expr.lineInfo
              if i >= typ.dim:
                glslErr &"field `{field}` is out of range", expr.lineInfo
            expr.typ =
              if len(expr.fields) == 1: typ.elemTyp.asTyp
              else: newVecTyp(len(expr.fields), typ.elemTyp)
            return
        glslErr &"unexpected `{expr.fields[0]}` in swizzle", expr.lineInfo
      glslErr &"expected a vec type but got `{typ}`", expr.lineInfo

    of exprUnOp:
      inferTyps expr.operand
      expr.typ = expr.operand.typ
      if expr.unop == opNot:
        assertEq expr.typ, typBool, expr.lineInfo
      else:
        assertNumberTyp expr.typ, expr.lineInfo

    of exprBinOp:
      inferTyps expr.lop
      inferTyps expr.rop
      let ltyp = expr.lop.typ
      let rtyp = expr.rop.typ
      case expr.binop
      of opAdd..opDiv:
        if expr.withAsgn: assertLVal expr.lop
        assertNumberTyp ltyp, rtyp, expr.lineInfo
        for (atyp, btyp) in [(ltyp, rtyp), (rtyp, ltyp)]:
          if atyp.kind == typVec and btyp.kind == typBasic and atyp.vecTyp == btyp.typ:
            expr.typ = atyp
            return
        if expr.binop == opMul:
          template checkMatVecMul(m, v, vecAxis, otherAxis) =
            if m.kind == typMat and v.kind == typVec and
               v.vecTyp == typFloat and v.dim == m.otherAxis:
                  expr.typ = newVecTyp(m.vecAxis, typFloat)
                  return
          checkMatVecMul(ltyp, rtyp, cols, rows)
          checkMatVecMul(rtyp, ltyp, rows, cols)
        expr.typ = tryUnify(expr.lop, expr.rop)
      of opEq..opGe:
        var dims: array[2, int]
        for i, typ in [ltyp, rtyp]:
          if typ.kind in {typBasic, typVec} and typ.elemTyp != typBool:
            dims[i] = typ.dim
          else:
            glslErr "expected a number type", expr.lineInfo
        if dims[0] != dims[1]:
          glslErr "vec dimensions don't matching", expr.lineInfo
        discard tryUnify(expr.lop, expr.rop)
        expr.typ = typBool
      of opAnd..opXor:
        assertEq ltyp, typBool, expr.lineInfo
        assertEq rtyp, typBool, expr.lineInfo
        expr.typ = typBool

    of exprTernaryOp:
      inferTyps expr.tcond
      inferTyps expr.tif
      inferTyps expr.telse
      if expr.tcond.typ != typBool:
        typErr expr.tcond.typ, typBool, expr.lineInfo
      if expr.tif.typ != expr.telse.typ:
        glslErr &"types of ternary branches dont match `{expr.tif.typ}` != `{expr.telse.typ}`", expr.lineInfo
      expr.typ = expr.tif.typ

    of exprCall:
      for arg in expr.args.mitems:
        inferTyps arg

      # user defined
      if expr.funcName in funcs:
        for def in funcs[expr.funcName]:
          if len(def.params) == len(expr.args) and
             toSeq(0..<len(def.params)).allIt(def.params[it].typ == expr.args[it].typ):
                expr.typ = def.retTyp
                return

      # constructors
      let justOneBasicTyp = len(expr.args) == 1 and expr.args[0].typ.kind == typBasic
      var combVecDim = 0  # -1 if not just vecs and basics
      for arg in expr.args:
        if arg.typ.kind in {typBasic, typVec}:
          combVecDim += arg.typ.dim
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
          expr.typ = typ
          return

      # builtin
      if Some(@typ) ?= tryCallBuiltin(expr.funcName, expr.args):
        expr.typ = typ

      else: glslErr &"there is no `{expr.funcName}` with matching parameter types", expr.lineInfo

  proc inferTyps(stmts: var StmtList, retTyp: Typ) =
    for stmt in stmts.mitems:
      case stmt.kind
      of stmtExpr:
        inferTyps stmt.expr

      of stmtVarDef:
        if stmt.initVal != nil:
          inferTyps stmt.initVal
          let valTyp = stmt.initVal.typ
          if stmt.varTyp == nil:
            stmt.varTyp = valTyp
            varTyps[stmt.defVar.id] = valTyp
          else:
            varTyps[stmt.defVar.id] = stmt.varTyp
            if valTyp == stmt.varTyp: discard
            elif valTyp.isConvertableTo(stmt.varTyp):
              stmt.initVal.convertTo(stmt.varTyp)
            else:
              typErr valTyp, stmt.varTyp, stmt.lineInfo

      of stmtAsgn:
        assertLVal stmt.lval
        inferTyps stmt.lval
        inferTyps stmt.rval
        if stmt.rval.typ.isConvertableTo stmt.lval.typ:
          stmt.rval.convertTo(stmt.lval.typ)
        else:
          typErr stmt.lval.typ, stmt.rval.typ, stmt.lineInfo

      of stmtReturn:
        inferTyps stmt.ret
        assertEq stmt.ret.typ, retTyp, stmt.lineInfo

      of stmtIf:
        for branch in stmt.elifBranches.mitems:
          inferTyps branch.cond
          if branch.cond.typ != typBool:
            typErr branch.cond.typ, typBool, stmt.lineInfo
          inferTyps branch.body, retTyp
        inferTyps stmt.elseBranch, retTyp

      of stmtWhile:
        inferTyps stmt.whileCond
        if stmt.whileCond.typ != typBool:
          typErr stmt.whileCond.typ, typBool, stmt.lineInfo
        inferTyps stmt.whileBody, retTyp

      of stmtFor:
        assert stmt.forVarTyp == nil
        inferTyps stmt.forRange.a
        inferTyps stmt.forRange.b
        stmt.forVarTyp = tryUnify(stmt.forRange.a, stmt.forRange.b)
        varTyps[stmt.forVar.id] = stmt.forVarTyp
        if stmt.forVarTyp.kind != typBasic or stmt.forVarTyp.typ == typBool:
          glslErr &"expected a number type for a for-loop range, but got `{stmt.forVarTyp}`", stmt.lineInfo
        inferTyps stmt.forBody, retTyp

  for def in prog.toplevelDefs:
    varTyps[def.v.id] = def.typ

  for c in prog.consts.mitems:
    inferTyps c.val
    if c.typ == nil:
      c.typ = c.val.typ
    elif c.val.typ.isConvertableTo c.typ:
      c.val.convertTo(c.typ)
    else:
      typErr c.val.typ, c.typ, c.lineInfo

  for funcs in prog.funcs.mvalues:
    for def in funcs.mitems:
      for param in def.params:
        varTyps[param.v.id] = param.typ
      inferTyps def.body, def.retTyp