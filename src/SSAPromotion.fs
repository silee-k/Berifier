[<RequireQualifiedAccess>]
module FixedSSAPromotion

open System.Collections.Generic
open B2R2
open B2R2.FrontEnd.BinInterface
open B2R2.BinIR.SSA
open B2R2.MiddleEnd.BinGraph
open B2R2.MiddleEnd.ControlFlowGraph
open B2R2.MiddleEnd.DataFlow


let [<Literal>] InitialStackPointer = 0x80000000UL

let private extractStackVar stmt =
  match stmt with
  | Def (v, _) -> v
  | _ -> Utils.impossible ()

let private findLastStackDef v targetVarKind =
  SSACFG.findReachingDef v targetVarKind
  |> Option.map extractStackVar

let private updateIfStackValueIsConstant (v: Vertex<SSABasicBlock>) spState sp =
  match CPState.findReg spState sp with
  | SPValue.Const bv ->
    let spValue = BitVector.toUInt64 bv
    let offset = InitialStackPointer - spValue |> int |> Some
    v.VData.FakeBlockInfo <-
      { v.VData.FakeBlockInfo with FrameDistance = offset }
  | _ -> ()

let private updateStackFrameDistance hdl g (v: Vertex<SSABasicBlock>) spState =
  match hdl.RegisterBay.StackPointer with
  | Some rid ->
    let spName = hdl.RegisterBay.RegIDToString rid
    let spRegKind = RegVar (hdl.ISA.WordSize |> WordSize.toRegType, rid, spName)
    match findLastStackDef v spRegKind with
    | Some sp -> updateIfStackValueIsConstant v spState sp
    | None -> ()
  | None -> ()

let private memStore ((pp, _) as stmtInfo) rt addr src =
  match addr with
  | SPValue.Const addr ->
    let addr = BitVector.toUInt64 addr
    let offset = int (int64 InitialStackPointer - int64 addr)
    let v = { Kind = StackVar (rt, offset); Identifier = 0 }
    Some (pp, Def (v, src))
  | _ -> Some stmtInfo

let private loadToVar rt addr =
  match addr with
  | SPValue.Const addr ->
    let addr = BitVector.toUInt64 addr
    let offset = int (int64 InitialStackPointer - int64 addr)
    let v = { Kind = StackVar (rt, offset); Identifier = 0 }
    Some (Var v)
  | _ -> None

let rec private replaceLoad spState v e =
  match e with
  | Load (_, rt, addr) ->
    let addr = SPTransfer.evalExpr spState v addr
    loadToVar rt addr
  | Cast (ck, rt, e) ->
    replaceLoad spState v e
    |> Option.map (fun e -> Cast (ck, rt, e))
  | Extract (e, rt, sPos) ->
    replaceLoad spState v e
    |> Option.map (fun e -> Extract (e, rt, sPos))
  | BinOp (op, rt, e1, e2) ->
    let re1 = replaceLoad spState v e1
    let re2 = replaceLoad spState v e2
    match re1, re2 with
    | Some e1, Some e2 -> BinOp (op, rt, e1, e2) |> Some
    | Some e1, None -> BinOp (op, rt, e1, e2) |> Some
    | None, Some e2 -> BinOp (op, rt, e1, e2) |> Some
    | None, None -> BinOp (op, rt, e1, e2) |> Some
  | _ -> None

let private stmtChooser spState v ((pp, stmt) as stmtInfo) =
  match stmt with
  | Phi (_, _) -> None
  | Def ({ Kind = MemVar }, Store (_, rt, addr, src)) ->
    let addr = SPTransfer.evalExpr spState v addr
    memStore stmtInfo rt addr src
  | Def (dstVar, e) ->
    match replaceLoad spState v e with
    | Some e -> Some (pp, Def (dstVar, e))
    | None -> Some stmtInfo
  | _ -> Some stmtInfo

let prepare hdl ssaCFG spState vertices (v: Vertex<SSABasicBlock>) =
  (vertices: List<SSAVertex>).Add v
  if v.VData.IsFakeBlock () then updateStackFrameDistance hdl ssaCFG v spState
  else ()
  v.VData.SSAStmtInfos
  |> Array.choose (stmtChooser spState v)
  |> fun stmts -> v.VData.SSAStmtInfos <- stmts

let promote hdl (ssaCFG: DiGraph<SSABasicBlock, CFGEdgeKind>) ssaRoot =
  let spp = StackPointerPropagation (hdl, ssaCFG)
  let spState = spp.Compute ssaRoot
  let vertices = List<SSAVertex> ()
  DiGraph.iterVertex ssaCFG (prepare hdl ssaCFG spState vertices)
  SSACFG.installPhis vertices ssaCFG ssaRoot
  struct (ssaCFG, ssaRoot)
