#
#    nglsl - a glsl dsl for nim
#        (c) Copyright 2024 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#

import std/[macros, sugar, sequtils, strutils, strformat, tables, options]
import fusion/matching
import ./utils, ./ast, ./typs


func newVar(name: string): Var {.inline.} = Var(name: name)

proc parseExpr(node: NimNode): Expr =
  let lineInfo = node.lineInfo

  result =
    case node.kind
    of nnkIntLit: Expr(kind: exprLit, typ: typInt, val: node.repr)
    of nnkFloatLit: Expr(kind: exprLit, typ: typFloat, val: node.repr)
    of nnkIdent:
      let name = node.strVal
      if name in ["true", "false"]:  Expr(kind: exprLit, typ: typBool, val: name)
      
      else: Expr(kind: exprVar, v: newVar(name))
    
    of nnkCall, nnkCommand:
      let (nameNode, args) =
        if node[0].kind == nnkDotExpr:
          (node[0][1], node[0][0] & node[1..^1])
        else:
          (node[0], node[1..^1])
      nameNode.expectKind {nnkIdent, nnkSym}
      let name = nameNode.strVal
      Expr(
        kind: exprCall,
        funcName: name,
        args: args.map(parseExpr)
      )

    of nnkDotExpr:
      Expr(
        kind: exprFieldAcc,
        vec: parseExpr(node[0]),
        fields: node[1].strVal
      )

    of nnkPrefix:
      let opStr = node[0].strVal
      let op =
        if opStr == "not": opNot
        else:
          try: parseEnum[UnaryOp](opStr)
          except: glslErr &"unknown operator `{opStr}`", node
      Expr(
        kind: exprUnOp,
        unop: op,
        operand: parseExpr(node[1])
      )

    of nnkInfix:
      proc buildExpr(op: BinaryOp): Expr =
        Expr(
          kind: exprBinOp,
          binop: op,
          lop: parseExpr(node[1]),
          rop: parseExpr(node[2]),
          lineInfo: lineInfo
        )
      let opStr = node[0].strVal
      let op =
        case opStr
        of "and": opAnd
        of "or": opOr
        of "xor": opXor
        else:
          try: parseEnum[BinaryOp](opStr)
          except:
            if len(opStr) > 1 and opStr[^1] == '=':
              try:
                let op = parseEnum[BinaryOp](opStr[0 ..< ^1])
                if op in opAdd..opDiv:
                  var expr = buildExpr(op)
                  expr.withAsgn = true
                  return expr
              except: discard
            glslErr &"unknown operator `{opStr}`", node
      buildExpr(op)

    of nnkIfExpr, nnkIfStmt:
      if len(node) != 2 or node[1].kind notin {nnkElse, nnkElseExpr}:
        glslErr "if expressions only support a single if/else pair", node
      Expr(
        kind: exprTernaryOp,
        tcond: parseExpr(node[0][0]),
        tif: parseExpr(node[0][1]),
        telse: parseExpr(node[1][0])
      )

    of nnkPar:
      Expr(kind: exprPar, expr: parseExpr(node[0]))

    of nnkStmtList, nnkStmtListExpr:
      if len(node) == 1:
        Expr(kind: exprPar, expr: parseExpr(node[0]))
      else:
        glslErr "statement-list expressions are not supported", node
    
    else:
      glslErr "unsupported syntax", node

  result.lineInfo = lineInfo

proc parseStmts(
  stmts: var StmtList,
  node: NimNode
) =
  let lineInfo = node.lineInfo
  var newStmt =
    case node.kind
    of nnkStmtList:
      for node in node: parseStmts(stmts, node)
      return

    of nnkAsgn:
      Stmt(
        kind: stmtAsgn,
        lval: parseExpr(node[0]),
        rval: parseExpr(node[1])
      )

    of nnkVarSection, nnkLetSection:
      for node in node:
        if node.kind == nnkVarTuple:
          glslErr "no tuple unpacking supported", node
        node.expectKind nnkIdentDefs
        var val: Expr
        if node.kind != nnkEmpty:
          val = parseExpr(node[^1])
        var typ: Typ
        if node[^2].kind != nnkEmpty:
          typ = parseTyp(node[^2])
        for v in node[0 ..< ^2]:
          stmts &= Stmt(
            kind: stmtVarDef,
            defVar: newVar(v.strVal),
            varTyp: typ,
            initVal: val,
            lineInfo: lineInfo
          )
      return

    of nnkReturnStmt:
      Stmt(
        kind: stmtReturn,
        ret: parseExpr(node[0])
      )

    of nnkIfStmt:
      var stmt = Stmt(kind: stmtIf)
      for node in node:
        case node.kind
        of nnkElifBranch:
          stmt.elifBranches &= (parseExpr(node[0]), @[])
          parseStmts(stmt.elifBranches[^1].body, node[1])
        of nnkElse:
          parseStmts(stmt.elseBranch, node[0])
        else: assert false
      stmt

    of nnkWhileStmt:
      var stmt = Stmt(
        kind: stmtWhile,
        whileCond: parseExpr(node[0])
      )
      parseStmts(stmt.whileBody, node[1])
      stmt

    of nnkForStmt:
      proc getForRange(node: NimNode): Option[ForRange] =
        if node.kind == nnkInfix:
          return some(ForRange(
            inclusive: (
              case node[0].strVal
              of "..": true
              of "..<": false
              else: return
            ),
            a: parseExpr(node[1]),
            b: parseExpr(node[2])
          ))
      if Some(@r) ?= getForRange(node[^2]):
        if len(node) > 3:
          glslErr "wrong amount of variables. expect 1 for a range loop", node
        var stmt = Stmt(
          kind: stmtFor,
          forVar: newVar(node[0].strVal),
          forRange: r
        )
        parseStmts(stmt.forBody, node[^1])
        stmt
      else:
        glslErr "only for loops over ranges (`..` or `..<`) are supported", node

    else: Stmt(kind: stmtExpr, expr: parseExpr(node))

  newStmt.lineInfo = lineInfo
  stmts.add newStmt

proc parse*(node: NimNode): Prog =
  for i, node in node:
    case node.kind
    of nnkLetSection, nnkVarSection:
      for defs in node:
        assert defs[^1].kind == nnkEmpty
        let (quali, td) = block:
          let td = defs[^2]
          if td.kind == nnkOutTy:
            (qualiOut, td[0])
          elif td.kind == nnkCommand and td[0].repr == "uniform":
            (qualiUniform, td[1])
          else:
            (qualiIn, td)
        let typ = parseTyp(td)
        for name in defs[0 ..< ^2]:
          result.toplevelDefs.add QualifiedVarDef(
            quali: quali,
            v: newVar(name.strVal),
            typ: typ
          )

    of nnkConstSection:
      for defs in node:
        assert defs[^1].kind != nnkEmpty
        let val = parseExpr(defs[^1])
        let typ =
          if defs[^2].kind == nnkEmpty: Typ nil
          else: parseTyp(defs[^2])
        for name in defs[0 ..< ^2]:
          result.consts &= ConstDef(
            v: newVar(name.strVal),
            typ: typ,
            val: val,
            lineInfo: name.lineInfo
          )

    of nnkProcDef, nnkFuncDef:
      node[4].expectKind nnkEmpty
      let name = node.name.strVal
      let params = node[3]
      var funcDef = FuncDef(
        retTyp: parseTyp(params[0]),
        params:
          if len(params) <= 1: @[]
          else: collect(
            for defs in params[1..^1]:
              defs[^1].expectKind nnkEmpty
              let typ = parseTyp(defs[^2])
              for v in defs[0 ..< ^2]:
                QualifiedVarDef(
                  quali: qualiIn, #TODO
                  v: newVar(v.strVal),
                  typ: typ
                )
          )
      )
      parseStmts(funcDef.body, node[6])  #TODO refactor to just allow toplevel func defs
      result.funcs.mgetOrPut(name, @[]) &= funcDef

    else: parseStmts(result.stmts, node)