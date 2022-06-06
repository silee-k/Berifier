module Verifier

open B2R2
open B2R2.BinIR
open B2R2.FrontEnd.BinLifter.Intel
open B2R2.MiddleEnd.BinEssence
open B2R2.MiddleEnd.BinGraph
open B2R2.MiddleEnd.ControlFlowAnalysis
open B2R2.MiddleEnd.ControlFlowGraph
open B2R2.MiddleEnd.DataFlow
open B2R2.BinIR.SSA

open System.Collections.Generic
open Microsoft

open B2R2Utils

type BBInfo =
  {
    Relation: Z3.FuncDecl
    FreeVars: Variable list
  }

let z3 =
  let settings = new Dictionary<string, string>();
  settings.Add("model", "true");
  settings.Add("proof", "true");
  settings.Add("unsat_core", "true");
  new Z3.Context(settings)

let solver =
  let s = z3.MkFixedpoint()
  let param = z3.MkParams()
  param.Add("engine", "spacer") |> ignore
  param.Add("datalog.generate_explanations", true) |> ignore
  param.Add("spacer.elim_aux", false) |> ignore
  param.Add("xform.slice", false) |> ignore
  param.Add("xform.inline_linear", false) |> ignore
  param.Add("xform.inline_eager", false) |> ignore
  s.Parameters <- param
  s


let z3exprOfVar var =
  z3.MkBVConst(Variable.toString var, uint32(varSizeOf var))

let z3sizeFromRegType rt = RegType.toBitWidth rt |> uint32

let z3zero size = z3.MkBV(0, size)
let z3one size = z3.MkBV(1, size)

let rec z3exprOf expr =
  match expr with
  | Num bv ->
    z3.MkBV(BitVector.toUInt64(bv), z3sizeFromRegType bv.Length)
    :> Z3.BitVecExpr
  | Var v -> z3exprOfVar v
  | Load (v, _, _) -> failwith "LOAD"
    // z3exprOfVar v
  | Store _ -> failwith "Store"
  | FuncName _ -> failwith "FunctionName"
  | UnOp (op, rt, e) -> 
    let e = z3exprOf e
    match op with
    | UnOpType.NEG -> z3.MkBVNeg(e)
    | UnOpType.NOT -> z3.MkBVNot(e)
    | UnOpType.FSQRT | UnOpType.FCOS
    | UnOpType.FSIN | UnOpType.FTAN
    | UnOpType.FATAN -> failwith "FSQR FCOS FSIN FTAN FATAN"
    | _ -> failwith "Unknown UnOpType"
  | BinOp (op, rt, e1, e2) ->
    let e1, e2 = z3exprOf e1, z3exprOf e2
    let e =
      match op with
      | BinOpType.ADD -> z3.MkBVAdd(e1, e2)
      | BinOpType.SUB -> z3.MkBVSub(e1, e2)
      | BinOpType.MUL -> z3.MkBVMul(e1, e2)
      | BinOpType.DIV -> z3.MkBVUDiv(e1, e2)
      | BinOpType.SDIV -> z3.MkBVSDiv(e1, e2)
      | BinOpType.MOD -> failwith "UMOD not supported"
      | BinOpType.SMOD -> z3.MkBVSMod (e1, e2)
      | BinOpType.SHL -> z3.MkBVSHL(e1, e2)
      | BinOpType.SHR -> z3.MkBVLSHR(e1, e2)
      | BinOpType.SAR -> z3.MkBVASHR(e1, e2)
      | BinOpType.AND -> z3.MkBVAND(e1, e2)
      | BinOpType.OR -> z3.MkBVOR(e1, e2)
      | BinOpType.XOR -> z3.MkBVXOR(e1, e2)
      | BinOpType.CONCAT -> z3.MkConcat(e1, e2)
      | BinOpType.APP -> failwith "APP"
      | BinOpType.CONS -> failwith "CONS"
      | BinOpType.FADD | BinOpType.FSUB 
      | BinOpType.FMUL | BinOpType.FDIV 
      | BinOpType.FPOW | BinOpType.FLOG -> failwith "FP"
      | _ -> failwith "Unkown BinOpType"
  
    let size = z3sizeFromRegType rt
    z3.MkExtract(size - 1u, 0u, e)
  | RelOp (op, rt, e1, e2) ->
    let e1, e2 = z3exprOf e1, z3exprOf e2
    let e =
      match op with
      | RelOpType.EQ -> z3.MkEq(e1, e2)
      | RelOpType.NEQ ->z3.MkEq(e1, e2) |> z3.MkNot
      | RelOpType.GT -> z3.MkBVUGT(e1, e2)
      | RelOpType.GE -> z3.MkBVUGE(e1, e2)
      | RelOpType.SGT -> z3.MkBVSGT(e1, e2)
      | RelOpType.SGE -> z3.MkBVSGE(e1, e2)
      | RelOpType.LT -> z3.MkBVULT(e1, e2)
      | RelOpType.LE -> z3.MkBVULE(e1, e2)
      | RelOpType.SLT -> z3.MkBVSLT(e1, e2)
      | RelOpType.SLE -> z3.MkBVSLE(e1, e2)
      | RelOpType.FGT | RelOpType.FGE
      | RelOpType.FLT | RelOpType.FLE -> failwith "FRelType not supported"
      | _ -> failwith "Unknown RelOpType"
    let size = z3sizeFromRegType rt
    z3.MkITE(e, z3.MkBV(1, size) :> Z3.Expr,
                z3.MkBV(0, size) :> Z3.Expr) :?> Z3.BitVecExpr
  | Ite (b, rt, e1, e2) ->
    let b, e1, e2 = z3exprOf b, z3exprOf e1, z3exprOf e2
    let size = z3sizeFromRegType rt
    z3.MkITE(z3.MkEq(b, z3zero size) |> z3.MkNot, e1, e2) :?> Z3.BitVecExpr
  | Cast (op, rt, e1) ->
    let size = z3sizeFromRegType rt
    let e1 = z3exprOf e1
    let extSize = size - e1.SortSize
    let e = 
      match op with
      | CastKind.SignExt -> z3.MkSignExt(extSize, e1)
      | CastKind.ZeroExt -> z3.MkZeroExt(extSize, e1)
      | CastKind.IntToFloat | CastKind.FtoIRound
      | CastKind.FtoICeil | CastKind.FtoIFloor
      | CastKind.FtoITrunc | CastKind.FloatCast -> failwith "Float not supported"
      | _ -> failwith "Unknown CastKind"
    e
  | Extract (e1, rt, pos) -> 
    let e1 = z3exprOf e1
    let size = z3sizeFromRegType rt
    z3.MkExtract(uint32 pos + size - 1u, uint32 pos, e1)
  | Undefined (rt, _) -> z3.MkBV(1, z3sizeFromRegType rt)
  | ReturnVal _ -> z3.MkBV(0, 1u)
  | _ -> failwith "Unsupported expr"


let defsOfBb (bb: Vertex<SSABasicBlock>) =
  bb.VData.SSAStmtInfos
  |> Array.choose (snd >> B2R2Utils.getDefVar)
  |> HashSet

let boundVarsOf (bb: Vertex<SSABasicBlock>) =
  bb.VData.SSAStmtInfos
  |> Array.map snd
  |> Array.filter (fun stmt ->
    B2R2Utils.getDefVar stmt |> Option.isSome && B2R2Utils.getPhiVar stmt = None)
  |> Array.choose B2R2Utils.getDefVar
  |> HashSet

let phiVarsOf (bb: Vertex<SSABasicBlock>) =
  bb.VData.SSAStmtInfos
  |> Array.choose (snd >> B2R2Utils.getPhiVar)
  |> HashSet
 
let toTransitiveClosure g =
  Traversal.foldPreorder g (DiGraph.getUnreachables g) (fun g v ->
    DiGraph.getSuccs g v |> List.fold (fun g sv ->
      DiGraph.getPreds g v |> List.fold (fun g pv ->
        DiGraph.addEdge g pv sv IntraJmpEdge
      ) g
    ) g
  ) g

let envOfFunction (cfg: DiGraph<SSABasicBlock, CFGEdgeKind>) bbenv f =
  Traversal.foldPreorder cfg (DiGraph.getUnreachables(cfg)) (fun bbmap bb ->
    let boundVars = boundVarsOf bb
    let phiVars = phiVarsOf bb
    let cfg = toTransitiveClosure cfg
    let reachableVars = new HashSet<Variable>()
    DiGraph.getPreds cfg bb
      |> List.iter (fun tp -> 
        defsOfBb tp |> reachableVars.UnionWith)
    let freeVars = new HashSet<Variable>(reachableVars)
    freeVars.ExceptWith (boundVars)
    freeVars.UnionWith (phiVars)
    let sortVec, freeVars =
      Set.fold (fun (sortVec, freeVars) var ->
        let varSize = varSizeOf var
        let sort = z3.MkBitVecSort(uint32(varSize)) :> Z3.Sort
        (sort :: sortVec, var :: freeVars)
        ) ([], []) (Set.ofSeq freeVars)
      |> (fun (sortVec, freeVars) ->
        List.rev sortVec |> Array.ofList, List.rev freeVars)
    let returnSort = z3.MkBoolSort()
    let relation =
      z3.MkFuncDecl (bb.VData.ToString(), sortVec, returnSort)
    solver.RegisterRelation relation
    Map.add bb { Relation = relation; FreeVars = freeVars} bbmap
  ) bbenv

let makeRule (vars: Z3.Expr list) (cons: Z3.Expr) =
  if vars = [] then cons :?> Z3.BoolExpr // TODO
  else
    let vars = Array.ofList vars
    z3.MkForall(vars, cons)

let initializeFunction cfg bbenv f =
  let entry = DiGraph.getUnreachables cfg |> List.head
  let bbenv = envOfFunction cfg bbenv f
  let bbinfo = Map.find entry bbenv
  let entryFreeVars = bbinfo.FreeVars
  let freeVars = List.map (fun e -> z3exprOfVar e :> Z3.Expr) entryFreeVars
                 |> Array.ofList

  let cons = bbinfo.Relation.Apply(freeVars)
  let r0 = makeRule [] cons
  solver.AddRule(r0, z3.MkSymbol("entry"))
  bbenv

let initialize (ess: BinEssence) (func: RegularFunction) =
  let bbenv = Map.empty
  let cfg, _ = getInitSSACFG ess func
  initializeFunction cfg bbenv func
