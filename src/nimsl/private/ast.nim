#
#    nimsl - a glsl dsl for nim
#        (c) Copyright 2024 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#

import std/[sequtils, strutils, strformat, tables]
import ./typs


type
  Var* = object
    name*: string
    id*: int

  Qualifier* = enum qualiIn="in", qualiOut="out", qualiInOut="inout", qualiUniform="uniform"
  QualifiedVarDef* = object
    quali*: Qualifier
    v*: Var
    typ*: Typ

  FuncDef* = object
    params*: seq[QualifiedVarDef]
    retTyp*: Typ
    body*: StmtList

  FuncTable* = OrderedTable[string, seq[FuncDef]]

  UnaryOp* = enum opPos="+", opNeg="-", opInc="++", opDec="--"

  BinaryOp* = enum
    opAdd="+", opSub="-", opMul="*", opDiv="/",
    opEq="==", opNe="!=", opLt="<", opGt=">", opLe="<=", opGe=">=",
    opAnd="&&", opOr="||", opXor="^^"

  ExprKind* = enum
    exprLit, exprVar,
    exprArrayAcc, exprSwizzle, exprCall,
    exprUnOp, exprBinOp, exprTernaryOp
    exprPar
  
  Expr* = ref object
    case kind*: ExprKind
    of exprLit:
      val*: string
      typ*: BasicTyp

    of exprVar: v*: Var

    of exprArrayAcc:
      arr*: Expr
      index*: Expr

    of exprSwizzle:
      vec*: Expr
      fields*: string

    of exprCall:
      funcName*: string
      args*: seq[Expr]

    of exprUnOp:
      unop*: UnaryOp
      operand*: Expr

    of exprTernaryOp:
      tcond*, tif*, telse*: Expr

    of exprBinOp:
      case binop*: BinaryOp
      of opAdd..opDiv: withAsgn*: bool
      else: discard
      lop*, rop*: Expr

    of exprPar: expr*: Expr

    nimNode*: NimNode

  StmtKind* = enum stmtExpr, stmtVarDef, stmtAsgn, stmtReturn, stmtIf
  Stmt* = ref object
    case kind*: StmtKind
    of stmtExpr: expr*: Expr

    of stmtVarDef:
      defVar*: Var
      varTyp*: Typ
      initVal*: Expr  # nil if none

    of stmtAsgn:
      lval*, rval*: Expr

    of stmtReturn:
      ret*: Expr

    of stmtIf:
      elifBranches*: seq[tuple[
        cond: Expr,
        body: StmtList
      ]]
      elseBranch*: StmtList  # empty if none
    
    nimNode*: NimNode

  StmtList* = seq[Stmt]

  Prog* = object
    toplevelDefs*: seq[QualifiedVarDef]
    funcs*: FuncTable
    stmts*: StmtList


func `$`(v: Var): string {.inline.} =
  v.name
  #&"{v.name}<{v.id}>"

proc `$`(expr: Expr): string =
  case expr.kind
  of exprLit: expr.val
  of exprVar: $expr.v
  of exprArrayAcc: &"{expr.arr}[{expr.index}]"
  of exprSwizzle: &"{expr.vec}.{expr.fields}"
  of exprUnOp: &"{expr.unop}{expr.operand}"
  of exprBinOp:
    if expr.binop in opAdd..opDiv and expr.withAsgn:
      &"{expr.lop} {expr.binop}= {expr.rop}"
    else: &"{expr.lop} {expr.binop} {expr.rop}"
  of exprTernaryOp: &"({expr.tcond} ? {expr.tif} : {expr.telse})"
  of exprPar: &"({expr.expr})"
  of exprCall:
    let args = expr.args.mapIt($it).join(", ")
    &"{expr.funcName}({args})"

proc genCode*(prog: Prog): string =
  var code: string

  proc genVarDef(v: Var, typ: Typ): string =
    var arrDims: string
    var typ = typ
    while typ.kind == typArray:
      arrDims &= &"[{typ.len}]"
      typ = typ.arrayTyp
    &"{typ} {v}{arrDims}"

  proc gen(def: QualifiedVarDef): string =
    $def.quali & " " & genVarDef(def.v, def.typ)

  proc gen(stmts: StmtList, indent: int) =
    let indentSpaces = "  ".repeat(indent)
    proc addLine(s: string) =
      code &= "\n"&indentSpaces&s

    for stmt in stmts:
      case stmt.kind
      of stmtExpr:
        addLine $stmt.expr & ";"

      of stmtVarDef:
        addLine genVarDef(stmt.defVar, stmt.varTyp)
        if stmt.initVal != nil:
          code &= &" = {stmt.initVal}"
        code &= ";"

      of stmtAsgn:
        addLine &"{stmt.lval} = {stmt.rval};"

      of stmtReturn:
        addLine &"return {stmt.ret};"

      of stmtIf:
        for i, (cond, body) in stmt.elifBranches:
          addLine if i == 0: "" else: "else "
          code &= &"if({cond}) {{"
          gen(body, indent+1)
          addLine "}"
        if len(stmt.elseBranch) > 0:
          addLine "else {"
          gen(stmt.elseBranch, indent+1)
          addLine "}"

  code &= "#version 410\n"

  for def in prog.toplevelDefs:
    code &= "\n"&gen(def)&";"

  for name, defs in prog.funcs:
    for def in defs:
      let params = def.params.mapIt(gen(it)).join(", ")
      code &= &"\n\n{def.retTyp} {name}({params}) {{"
      gen(def.body, 1)
      code &= "\n}"

  gen(prog.stmts, 0)
  code