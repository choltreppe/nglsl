#
#    nglsl - a glsl dsl for nim
#        (c) Copyright 2024 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#

import std/[macros, sequtils, strutils, strformat, tables]
import ./utils, ./typs


type
  Var* = object
    name*: string
    id*: int

  Qualifier* = enum qualiIn="in", qualiOut="out", qualiInOut="inout", qualiUniform="uniform"
  QualifiedVarDef* = object
    quali*: Qualifier
    v*: Var
    typ*: Typ

  ConstDef* = object
    v*: Var
    typ*: Typ
    val*: Expr
    lineInfo*: string

  FuncDef* = object
    params*: seq[QualifiedVarDef]
    retTyp*: Typ
    body*: StmtList

  FuncTable* = OrderedTable[string, seq[FuncDef]]

  UnaryOp* = enum opPos="+", opNeg="-", opInc="++", opDec="--", opNot="!"

  BinaryOp* = enum
    opAdd="+", opSub="-", opMul="*", opDiv="/",
    opEq="==", opNe="!=", opLt="<", opGt=">", opLe="<=", opGe=">=",
    opAnd="&&", opOr="||", opXor="^^"

  ExprKind* = enum
    exprLit, exprVar,
    exprArrayAcc, exprFieldAcc, exprCall,
    exprUnOp, exprBinOp, exprTernaryOp
    exprPar
  
  Expr* = ref object
    case kind*: ExprKind
    of exprLit: val*: string

    of exprVar: v*: Var

    of exprArrayAcc:
      arr*: Expr
      index*: Expr

    of exprFieldAcc:  # includes swizzle
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
      binop*: BinaryOp
      withAsgn*: bool   # only for binop in opAdd..opDiv
      lop*, rop*: Expr

    of exprPar: expr*: Expr

    typ*: Typ
    lineInfo*: string

  ForRange* = object
    a*, b*: Expr
    inclusive*: bool

  StmtKind* = enum stmtExpr, stmtVarDef, stmtAsgn, stmtReturn, stmtIf, stmtWhile, stmtFor
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

    of stmtWhile:
      whileCond*: Expr
      whileBody*: StmtList

    of stmtFor:
      forVar*: Var
      forVarTyp*: Typ
      forRange*: ForRange
      forBody*: StmtList
    
    lineInfo*: string

  StmtList* = seq[Stmt]

  Prog* = object
    toplevelDefs*: seq[QualifiedVarDef]
    consts*: seq[ConstDef]
    funcs*: FuncTable
    stmts*: StmtList


template typErr*(a, b: Typ, lineInfo: string) =
  glslErr "types dont match: `" & $a & "` and `" & $b & "`", lineInfo

template assertEq*(a, b: Typ, lineInfo: string) =
  if a != b: typErr a, b, lineInfo

# is a number or some container of one ?
proc assertNumberTyp*(typs: varargs[Typ], lineInfo: string) =
  const msg = "expected a number type or a vec/mat/array of one"
  for typ in typs:
    case typ.kind
    of typBasic:
      if typ.typ == typBool:
        glslErr msg, lineInfo
    of typVec:
      assertNumberTyp typ.vecTyp, lineInfo
    of typMat: discard
    of typArray:
      assertNumberTyp typ.arrayTyp, lineInfo
    else:
      glslErr msg, lineInfo

func isConvertableTo*(a, b: Typ): bool =
  a.kind == b.kind and a.kind in {typBasic, typVec} and a.elemTyp != typBool

proc convertTo*(expr: var Expr, typ: Typ) = 
  if typ.kind == typBasic and expr.kind == exprLit:
    macro genConversions: string =
      result = nnkIfStmt.newTree()
      for fromTyp in typBool..typFloat:
        let parseProc = ident("parse" & $fromTyp)
        for toTyp in typBool..typFloat:
          let castProc = ident($toTyp)
          let cond = quote do: expr.typ == `fromTyp` and typ == `toTyp`
          let body = quote do: $`castProc`(`parseProc`(expr.val))
          result.add nnkElifBranch.newTree(cond, body)
      result.add nnkElse.newTree(newLit(""))  # should not happen
    expr = Expr(
      kind: exprLit,
      typ: typ.typ,
      val: genConversions()
    )
  else:
    expr = Expr(kind: exprCall, funcName: $typ, args: @[expr])

proc tryUnify*(a: var Expr, b: var Expr): Typ =
  if a.typ == b.typ: a.typ
  elif a.typ.isConvertableTo(b.typ):
    if a.typ.elemTyp > b.typ.elemTyp:
       b.convertTo(a.typ); a.typ
    else:
       a.convertTo(b.typ); b.typ
  else:
    typErr a.typ, b.typ, a.lineInfo


func `$`(v: Var): string {.inline.} =
  v.name
  #&"{v.name}<{v.id}>"

proc `$`(expr: Expr): string =
  case expr.kind
  of exprLit: expr.val
  of exprVar: $expr.v
  of exprArrayAcc: &"{expr.arr}[{expr.index}]"
  of exprFieldAcc: &"{expr.vec}.{expr.fields}"
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

      of stmtWhile:
        addLine &"while({stmt.whileCond}) {{"
        gen(stmt.whileBody, indent+1)
        addLine "}"

      of stmtFor:
        let v = stmt.forVar
        let cmpOp = if stmt.forRange.inclusive: "<=" else: "<"
        addLine &"for({genVarDef(v, stmt.forVarTyp)} = {stmt.forRange.a}; {v} {cmpOp} {stmt.forRange.b}; ++{v}) {{"
        gen(stmt.forBody, indent+1)
        addLine "}"

  code &= "#version 410\nprecision highp float;\n"

  for def in prog.toplevelDefs:
    code &= "\n"&gen(def)&";"

  code &= "\n"
  for c in prog.consts:
    code &= &"\nconst {genVarDef(c.v, c.typ)} = {c.val};"

  for name, defs in prog.funcs:
    for def in defs:
      let params = def.params.mapIt(gen(it)).join(", ")
      code &= &"\n\n{def.retTyp} {name}({params}) {{"
      gen(def.body, 1)
      code &= "\n}"

  gen(prog.stmts, 0)
  code