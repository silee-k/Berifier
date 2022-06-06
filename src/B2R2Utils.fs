module B2R2Utils

open System.Text

open B2R2
open B2R2.BinIR.SSA
open B2R2.BinIR
open B2R2.FrontEnd.BinInterface
open B2R2.MiddleEnd.BinEssence
open B2R2.MiddleEnd.ControlFlowAnalysis
open B2R2.MiddleEnd.ControlFlowGraph

let isPCVar var =
  match var.Kind with
  | PCVar _ -> false
  | _ -> false

let getDefVar stmt =
  match stmt with
  | Def (var, _) | Phi (var, _) -> Some var
  | _ -> None

let getPhiVar stmt =
  match stmt with
  | Phi (var, _) -> Some var
  | _ -> None

let initVarMapOfFunction cfg =
  let ssaEdges = SSAEdges.compute cfg
  ssaEdges.Uses 
  |> Map.fold (fun acc var locs -> 
    match var.Kind with
    | StackVar _ | TempVar _ | RegVar _ | MemVar _ when var.Identifier = 0 ->
      locs |> Set.fold (fun acc (vid, _) -> 
      match Map.tryFind vid acc with
      | Some vars -> Map.add vid (var :: vars) acc
      | None -> Map.add vid [var] acc ) acc
    | _ -> acc ) Map.empty
    
let varSizeOf var =
  match var.Kind with
  | RegVar (rt, _, _) | PCVar (rt) | TempVar (rt, _) | StackVar(rt, _)
  | GlobalVar (rt, _ ) -> RegType.toBitWidth(rt)
  | MemVar -> 
    // failwith "MemVar Unsupported"
    int ISA.DefaultISA.WordSize // Unsupported

let getInitSSACFG (ess: BinEssence) (func: RegularFunction) = 
  let g, root = func.GetSSACFG(ess.BinHandle)
  let struct (g, root) = FixedSSAPromotion.promote ess.BinHandle g root
  let initVarMaps = initVarMapOfFunction g 
  let initStmtInfos = 
    initVarMaps.Values 
    |> Seq.concat
    |> Seq.distinct
    |> Seq.map (fun var -> Def (var, Var (var)))
    |> Seq.map (fun stmt -> ProgramPoint (0UL, 0), stmt)
    |> Array.ofSeq
  
  root.VData.SSAStmtInfos <- Array.append initStmtInfos root.VData.SSAStmtInfos
  g, root

let getArg1 hdl fakeBlk = 
  let rid = CallingConvention.functionArgRegister hdl 1
  let name = hdl.RegisterBay.RegIDToString rid
  let varKind = match hdl.ISA.Arch with
                | Arch.IntelX86 -> RegVar (32<rt>, rid, name)
                | _ -> RegVar (64<rt>, rid, name)
  match SSACFG.findReachingDef fakeBlk varKind with
  | Some (Def (var, _)) -> Some var
  | _ -> None
