#
#    nimsl - a glsl dsl for nim
#        (c) Copyright 2024 Joel Lienhard
#
#    See the file "LICENSE.txt", included in this
#    distribution, for details about the copyright.
#


import std/[macros, sugar, sequtils, strutils, strformat, tables, options]
import fusion/matching


template glslErr(msg: string, node: NimNode) =
  error "[GLSL] "&msg, node
  return


type
  BasicTyp = enum typBool="bool", typInt="int", typUint="uint", typFloat="float", typDouble="double"
  TypKind = enum typVoid="void", typBasic, typImage="image", typSampler, typVec="vec", typMat="mat", typArray
  Typ = ref object
    case kind: TypKind
    of typBasic:
      typ: BasicTyp
    of typSampler:
      samplerDim: range[1..3]
    of typVec, typMat:
      dim: range[2..4]
      ofTyp: BasicTyp
    of typArray:
      len: Natural
      arrayTyp: Typ
    else: discard

  Var = object
    name: string
    id: int

  Qualifier = enum qualiIn="in", qualiOut="out", qualiInOut="inout", qualiUniform="uniform"
  QualifiedVarDef = object
    quali: Qualifier
    v: Var
    typ: Typ

  FuncDef = object
    params: seq[QualifiedVarDef]
    retTyp: Typ
    body: StmtList

  FuncTable = OrderedTable[string, seq[FuncDef]]

  UnaryOp = enum opPos="+", opNeg="-", opInc="++", opDec="--"

  BinaryOp = enum
    opAdd="+", opSub="-", opMul="*", opDiv="/",
    opEq="==", opNe="!=", opLt="<", opGt=">", opLe="<=", opGe=">=",
    opAnd="&&", opOr="||", opXor="^^"

  ExprKind = enum
    exprLit, exprVar,
    exprArrayAcc, exprSwizzel, exprCall,
    exprUnOp, exprBinOp, exprTernaryOp
    exprPar
  
  Expr = ref object
    case kind: ExprKind
    of exprLit: val: string

    of exprVar: v: Var

    of exprArrayAcc:
      arr: Expr
      index: Expr

    of exprSwizzel:
      vec: Expr
      fields: string

    of exprCall:
      funcName: string
      args: seq[Expr]

    of exprUnOp:
      unop: UnaryOp
      operand: Expr

    of exprTernaryOp:
      tcond, tif, telse: Expr

    of exprBinOp:
      case binop: BinaryOp
      of opAdd..opDiv: withAsgn: bool
      else: discard
      lop, rop: Expr

    of exprPar: expr: Expr

    typ: Typ

  StmtKind = enum stmtExpr, stmtVarDef, stmtAsgn, stmtReturn, stmtIf
  Stmt = ref object
    case kind: StmtKind
    of stmtExpr: expr: Expr

    of stmtVarDef:
      defVar: Var
      varTyp: Typ
      initVal: Option[Expr]

    of stmtAsgn:
      lval, rval: Expr
      case withOp: bool
      of true: op: range[opAdd..opDiv]
      of false: discard

    of stmtReturn:
      ret: Expr

    of stmtIf:
      elifBranches: seq[tuple[
        cond: Expr,
        body: StmtList
      ]]
      elseBranch: StmtList

  StmtList = seq[Stmt]

  Prog = object
    toplevelDefs: seq[QualifiedVarDef]
    funcs: FuncTable
    stmts: StmtList


converter asTyp(typ: BasicTyp): Typ = Typ(kind: typBasic, typ: typ)


func `$`(typ: Typ): string =
  func short(typ: BasicTyp): string {.inline.} =
    if typ == typFloat: ""
    else: ($typ)[0..0]
  case typ.kind
  of typBasic: $typ.typ
  of typSampler: &"sampler{typ.samplerDim}d"
  of typVec, typMat: &"{typ.ofTyp.short}{typ.kind}{typ.dim}"
  of typArray: assert false; ""
  else: $typ.kind

func `$`(v: Var): string {.inline.} = v.name

proc `$`(expr: Expr): string =
  case expr.kind
  of exprLit: expr.val
  of exprVar: $expr.v
  of exprArrayAcc: &"{expr.arr}[{expr.index}]"
  of exprSwizzel: &"{expr.vec}.{expr.fields}"
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

proc genCode(prog: Prog): string =
  var code: string

  proc genVarDef(v: Var, typ: Typ): string =
    var name = v.name
    var typ = typ
    while typ.kind == typArray:
      name &= &"[{typ.len}]"
      typ = typ.arrayTyp
    &"{typ} {name}"

  proc gen(def: QualifiedVarDef): string =
    $def.quali & " " & genVarDef(def.v, def.typ)

  proc gen(stmts: StmtList, indent: int) =
    let indentSpaces = "  ".repeat(indent)
    for stmt in stmts:
      code &= indentSpaces
      case stmt.kind
      of stmtExpr:
        code &= $stmt.expr & ";"

      of stmtVarDef:
        code &= genVarDef(stmt.defVar, stmt.varTyp)
        if Some(@v) ?= stmt.initVal:
          code &= &" = {v}"
        code &= ";"

      of stmtAsgn:
        code &= &"{stmt.lval} = {stmt.rval};"

      of stmtReturn:
        code &= &"return {stmt.ret};"

      of stmtIf:
        for i, (cond, body) in stmt.elifBranches:
          if i > 0: code &= indentSpaces&"else "
          code &= &"if({cond}) {{\n"
          gen(body, indent+1)
          code &= "} "
        if len(stmt.elseBranch) > 0:
          code &= "else {\n"
          gen(stmt.elseBranch, indent+1)
          code &= "}"
        
      code &= "\n"

  code &= "#version 410\n\n"

  for def in prog.toplevelDefs:
    code &= gen(def)&";\n"
  code &= "\n"

  for name, defs in prog.funcs:
    for def in defs:
      let params = def.params.mapIt(gen(it)).join(", ")
      code &= &"{def.retTyp} {name}({params}) {{\n"
      gen(def.body, 1)
      code &= "}\n\n"

  gen(prog.stmts, 0)
  code



func identStr(n: NimNode): string {.inline.} =
  assert n.kind == nnkIdent
  n.strVal.nimIdentNormalize

let genericTyps {.compiletime.} = block:
  var typs: seq[(string, Typ)]
  proc addTyp(typ: Typ) = typs.add (capitalizeAscii($typ), typ)
  for dim in 1..3:
    addTyp Typ(kind: typSampler, samplerDim: dim)
  template typVecMat(k: TypKind) =
    for ofTyp in BasicTyp:
      for dim in 2..4:
        addTyp Typ(kind: k, dim: dim, ofTyp: ofTyp)
  typVecMat(typVec)
  typVecMat(typMat)
  typs

proc parseTyp(node: NimNode): Typ =
  case node.kind
  of nnkEmpty: Typ(kind: typVoid)

  of nnkIdent:
    let name = node.repr.nimIdentNormalize
    for (n, typ) in genericTyps:
      if name == n: return typ
    try:
      parseEnum[BasicTyp](
        case name
        of "float32": "float"
        of "float64": "double"
        of "int32": "int"
        of "uint32": "uint"
        else: name
      )
    except:
      glslErr &"unknown type `{name}`", node
  
  of nnkBracketExpr:
    let baseName = node[0].repr.nimIdentNormalize
    if baseName == "array":
      if len(node) != 3:
        glslErr &"`array` expects exactly 2 generic parameters", node
      Typ(kind: typArray,
        arrayTyp: parseTyp(node[2]),
        len: if node[1].kind == nnkIntLit: node[1].intVal
             else: glslErr "expected int literal", node
      )
    else:
      glslErr &"unknown type `{baseName}`", node

  else:
    glslErr "malformed type defenition: `{node.repr}`", node

func newVar(name: string): Var {.inline.} = Var(name: name)

proc parseExpr(node: NimNode): Expr =
  case node.kind
  of nnkIntLit: Expr(kind: exprLit, typ: typInt, val: node.repr)
  of nnkFloatLit: Expr(kind: exprLit, typ: typFloat, val: node.repr)
  of nnkIdent:
    let name = node.identStr
    if name in ["true", "false"]:  Expr(kind: exprLit, typ: typBool, val: name)
    
    else: Expr(kind: exprVar, v: newVar(name))
  
  of nnkCall, nnkCommand:
    let (nameNode, args) =
      if node[0].kind == nnkDotExpr:
        (node[0][1], node[0][0] & node[1..^1])
      else:
        (node[0], node[1..^1])
    nameNode.expectKind {nnkIdent, nnkSym}
    let name = nameNode.identStr
    Expr(
      kind: exprCall,
      funcName: name,
      args: args.map(parseExpr)
    )

  of nnkDotExpr:
    Expr(
      kind: exprSwizzel,
      vec: parseExpr(node[0]),
      fields: node[1].strVal
    )

  of nnkPrefix:
    let opStr = node[0].strVal
    let op = 
      try: parseEnum[UnaryOp](opStr)
      except: glslErr &"unknown operator `{opStr}`", node
    Expr(
      kind: exprUnOp,
      unop: op,
      operand: parseExpr(node[1])
    )

  of nnkInfix:
    template buildExpr(o, a): Expr =
      var e = Expr(
        kind: exprBinOp,
        binop: o,
        lop: parseExpr(node[1]),
        rop: parseExpr(node[2])
      )
      e.withAsgn = a
      e
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
                return buildExpr(op, true)
            except: discard
          glslErr &"unknown operator `{opStr}`", node
    buildExpr(op, false)

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
    glslErr "TODO: " & $node.kind, node

proc parseStmts(
  stmts: var StmtList,
  node: NimNode
) =
  stmts.add:
    case node.kind
    of nnkStmtList:
      for node in node: parseStmts(stmts, node)
      return

    of nnkAsgn:
      Stmt(
        kind: stmtAsgn,
        withOp: false,
        lval: parseExpr(node[0]),
        rval: parseExpr(node[1])
      )

    of nnkVarSection, nnkLetSection:
      for node in node:
        if node.kind == nnkVarTuple:
          glslErr "no tuple unpacking supported", node
        node.expectKind nnkIdentDefs
        let val =
          if node.kind == nnkEmpty: none(Expr)
          else: some(parseExpr(node[^1]))
        var typ: Typ
        if node[^2].kind != nnkEmpty:
          typ = parseTyp(node[^2])
        for v in node[0 ..< ^2]:
          stmts &= Stmt(
            kind: stmtVarDef,
            defVar: newVar(v.identStr),
            varTyp: typ,
            initVal: val
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

    else: Stmt(kind: stmtExpr, expr: parseExpr(node))

proc parse(node: NimNode): Prog =
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
            v: newVar(name.identStr),
            typ: typ
          )

    of nnkProcDef, nnkFuncDef:
      node[4].expectKind nnkEmpty
      let name = node.name.identStr
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
                  v: newVar(v.identStr),
                  typ: typ
                )
          )
      )
      parseStmts(funcDef.body, node[6])  #TODO refactor to just allow toplevel func defs
      result.funcs.mgetOrPut(name, @[]) &= funcDef

    else: parseStmts(result.stmts, node)



macro shader*(body: untyped): string =
  var prog = parse(body)
  newLit(genCode(prog))