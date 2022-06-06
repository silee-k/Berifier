module Extractor

open B2R2.BinIR.SSA
open B2R2.MiddleEnd.BinEssence
open B2R2.MiddleEnd.ControlFlowAnalysis
open B2R2.MiddleEnd.ControlFlowGraph
open B2R2.MiddleEnd.BinGraph

open Microsoft

open B2R2Utils
open Verifier

let extractStmts (ess: BinEssence) (func: RegularFunction)  
                 (bb: Vertex<SSABasicBlock>) = 
  let g, root = func.GetSSACFG(ess.BinHandle)
  bb.VData.SSAStmtInfos
  |> Array.fold (fun (conss, succs) (_, stmt) ->
    let conss, succs = 
      if bb.VData.IsFakeBlock() then
         let callees = func.CallTargets bb.VData.FakeBlockInfo.CallSite
         let callee = Set.minElement callees 
                      |> ess.CodeManager.FunctionMaintainer.FindRegular
         if callee.FunctionName = "assume" then
           let arg1 = getArg1 ess.BinHandle bb |> Option.get
           let con = z3.MkNot(z3.MkEq(z3exprOfVar arg1, Verifier.z3zero (uint32(varSizeOf arg1))))
           List.map (fun cons -> con :: cons) conss, succs
         else conss, succs
       else conss, succs
    match stmt with
    | LMark _ -> (conss, succs)
    | Def (var, expr) when B2R2Utils.isPCVar var |> not -> 
      let expr = 
        match expr with
        | ReturnVal (addr, _, prevVar) -> z3exprOf (Var (prevVar))
        | _ -> z3exprOf expr
      let con = z3.MkEq(z3exprOfVar var, expr)
      List.map (fun cons -> con :: cons) conss, succs
    | Phi (var, inVars) -> (conss, succs)
    | Jmp (InterCJmp (cond, _, _) as jt) | Jmp (IntraCJmp (cond, _, _) as jt) ->
      let condExpr = z3.MkNot(z3.MkEq(Verifier.z3exprOf cond, z3zero 1u))
      let cons = List.head conss
      let getVertexWithEdge edgeKind =
        DiGraph.getSuccs g bb
        |> List.pick (fun succBb->
          let e = DiGraph.findEdgeData g bb succBb
          match e with
          | v when v = edgeKind -> Some succBb
          | _ -> None)
      let tb, fb = 
        match jt with
        | IntraCJmp _ -> getVertexWithEdge IntraCJmpTrueEdge,
                         getVertexWithEdge IntraCJmpFalseEdge
        | _ -> getVertexWithEdge InterCJmpTrueEdge,
               getVertexWithEdge InterCJmpFalseEdge


      [tb; fb]
      |> List.fold (fun (conss, succs) succBb ->
        if succBb = tb then
          List.map (fun cons -> condExpr :: cons) conss, succBb :: succs
        else (z3.MkNot(condExpr) :: cons) :: conss, succBb :: succs
      ) (conss, succs)
    | Jmp _ ->
      let succBbs = DiGraph.getSuccs g bb
      if succBbs = [] then (conss, succs)
      else (conss, (succBbs |> List.head) :: succs)
    | SideEffect _ -> (conss, succs)
    | _ -> (conss, succs)
  ) ([[]], [])
  |> (fun (conss, succs) ->
    let succs = 
      if succs.Length = 0 then
        DiGraph.getSuccs g bb 
      else succs |> List.rev
    List.map List.rev conss |> List.rev |> Array.ofList, 
    succs |> Array.ofList
  )
  
let getPhis (bb: Vertex<SSABasicBlock>) =
  bb.VData.SSAStmtInfos
  |> Array.fold (fun (accVars, accInVars) (_, stmt) ->
    match stmt with
    | Phi (var, nums) -> 
      let inVars = Array.map (fun varNum -> 
                    { var with Identifier = varNum } ) nums 
                   |> Array.toList
      (var :: accVars, inVars @ accInVars)
    | _ -> accVars, accInVars
  ) ([], []) 
  |> (fun (vars, inVars) -> List.rev vars, List.rev inVars)

let extractBb ess (func: RegularFunction) bbenv bb =
  let g, root = func.GetSSACFG(ess.BinHandle)
  let toExprs exprs = List.map (fun e -> e :> Z3.Expr) exprs
  let apply (relation: Z3.FuncDecl) exprList = 
    relation.Apply(exprList |> toExprs |> Array.ofList )
  let bbInfo = Map.find bb bbenv
  let freeVars = List.map Verifier.z3exprOfVar bbInfo.FreeVars 
  let relationCons = apply bbInfo.Relation freeVars
  let conss, succs = extractStmts ess func bb
  let varToBbMap = 
    Traversal.foldPreorder g [root] (fun acc v -> 
      v.VData.SSAStmtInfos 
      |> Array.fold (fun acc (_, stmt) -> 
        match stmt with
        | Def (var, _) | Phi (var, _) -> Map.add var v acc
        | _ -> acc ) acc ) Map.empty
  succs
  |> Array.iteri (fun i succBb -> 
    let bbInfo = Map.find succBb bbenv
    let phiVars, phiInVars = getPhis succBb
    let succFreeVars =
      phiInVars
      |> List.fold (fun acc var ->
        if List.contains var acc then acc
        else var :: acc) bbInfo.FreeVars
      |> List.rev
      |> List.map Verifier.z3exprOfVar
    let freeVars =
      succFreeVars
      |> List.fold (fun acc var ->
        if List.contains var acc then acc
        else var :: acc) freeVars
      |> List.rev
    let freeVarExprs = 
      bbInfo.FreeVars
      |> List.map (fun freeVar ->
        match List.tryFind ((=) freeVar) phiVars with
        | None -> freeVar
        | Some _ ->
          phiInVars
          |> List.pick (fun phiInVar ->
            let v = varToBbMap[phiInVar]
            if v = bb && phiInVar.Kind = freeVar.Kind then 
              Some phiInVar
            else Some freeVar
          )
      )
      |> List. map Verifier.z3exprOfVar

    let succRelationCons = apply bbInfo.Relation freeVarExprs
    let instrCons = conss[i] |> z3.MkAnd
    let head = z3.MkAnd [|relationCons :?> Z3.BoolExpr; instrCons|]
    let cons = z3.MkImplies (head, succRelationCons :?> Z3.BoolExpr)
    let r = Verifier.makeRule (toExprs freeVars) cons
    let name = bb.ToString() |> z3.MkSymbol
    solver.AddRule(r, name)
  )

let extract bbenv (ess: BinEssence) (func: RegularFunction) =
  let g, root = func.GetSSACFG(ess.BinHandle)
  Traversal.iterPreorder g [root] (extractBb ess func bbenv) 

let isAssertFail = function
                  | SideEffect (UndefinedInstr) -> true
                  | _ -> false

let extractQueries (func: RegularFunction)
  (bbenv: Map<Vertex<SSABasicBlock>, BBInfo>) (ess: BinEssence) =
  let g, root = func.GetSSACFG(ess.BinHandle)
  Traversal.foldPreorder g [root] (fun queries bb ->
    bb.VData.SSAStmtInfos
    |> Array.fold (fun queries (_, stmt) ->
      if isAssertFail stmt then
        let bbinfo = Map.find bb bbenv
        bbinfo.Relation :: queries
      else queries
    ) queries
  ) []
  |> List.rev