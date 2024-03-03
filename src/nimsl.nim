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
    nimNode: NimNode

  StmtKind = enum stmtExpr, stmtVarDef, stmtAsgn, stmtReturn, stmtIf
  Stmt = ref object
    case kind: StmtKind
    of stmtExpr: expr: Expr

    of stmtVarDef:
      defVar: Var
      varTyp: Typ
      initVal: Expr  # nil if none

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
      elseBranch: StmtList  # empty if none
    
    nimNode: NimNode

  StmtList = seq[Stmt]

  Prog = object
    toplevelDefs: seq[QualifiedVarDef]
    funcs: FuncTable
    stmts: StmtList


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

func `$`(v: Var): string {.inline.} =
  #v.name
  &"{v.name}<{v.id}>"

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



func identStr(n: NimNode): string {.inline.} =
  assert n.kind == nnkIdent
  n.strVal.nimIdentNormalize

converter asTyp(typ: BasicTyp): Typ = Typ(kind: typBasic, typ: typ)

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
  result =
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
      proc buildExpr(op: BinaryOp): Expr =
        Expr(
          kind: exprBinOp,
          binop: op,
          lop: parseExpr(node[1]),
          rop: parseExpr(node[2]),
          nimNode: node
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
      glslErr "TODO: " & $node.kind, node

  result.nimNode = node

proc parseStmts(
  stmts: var StmtList,
  node: NimNode
) =
  var newStmt =
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
        var val: Expr
        if node.kind != nnkEmpty:
          val = parseExpr(node[^1])
        var typ: Typ
        if node[^2].kind != nnkEmpty:
          typ = parseTyp(node[^2])
        for v in node[0 ..< ^2]:
          stmts &= Stmt(
            kind: stmtVarDef,
            defVar: newVar(v.identStr),
            varTyp: typ,
            initVal: val,
            nimNode: node
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

  newStmt.nimNode = node
  stmts.add newStmt

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



proc bindSyms(prog: var Prog) =
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

    of exprSwizzel:
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

  var symIds: Table[string, int]
  for def in prog.toplevelDefs.mitems:
    symIds.addVar def.v

  for funcs in prog.funcs.mvalues:
    for def in funcs.mitems:
      var symIds = symIds
      for param in def.params.mitems:
        symIds.addVar param.v
      bindSyms(def.body, symIds)



macro shader*(body: untyped): string =
  var prog = parse(body)
  bindSyms(prog)
  newLit(genCode(prog))