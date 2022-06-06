open Printf
open System.IO

open B2R2
open B2R2.FrontEnd.BinInterface
open B2R2.MiddleEnd.BinEssence
open Microsoft

open Verifier

let report (solver: Z3.Fixedpoint) (status: Z3.Status) =
  match status with
  | Z3.Status.SATISFIABLE ->
    printfn "Not verified"
    let answer = solver.GetAnswer()
    printfn "Counterexample:"
    printfn "%s" (answer.ToString())
  | Z3.Status.UNSATISFIABLE -> printfn "Verified"
  | _ -> printfn "Unknown error in Z3"


let print (solver: Z3.Fixedpoint) (queries: Z3.FuncDecl array) =
  let file = File.CreateText("formula.smt2")
  solver.ToString() |> fprintf file "%s\n"
  Array.iter (fun (q: Z3.FuncDecl) ->
    fprintf file "(query %s)" (q.Name.ToString())
  ) queries
  file.Close()
  let file = File.CreateText("debug.smt2")
  solver.Rules
  |> Array.iter (fun r -> r.ToString() |> fprintf file "%s\n")
  solver.Assertions
  |> Array.iter (fun r -> r.ToString() |> fprintf file "%s\n")
  file.Close()

[<EntryPoint>]
let main args =
  if Array.length args <> 1 then (
    printfn "verifier: You must specify one Binary";
    printfn "verifier: verifier [Binary]";
    exit 1)
  let hdl = BinHandle.Init (ISA.DefaultISA, args.[0])
  let ess = BinEssence.init hdl [] [] []
  let func =
    ess.CodeManager.FunctionMaintainer.RegularFunctions
    |> Array.filter (fun func -> func.FunctionName = "main")
    |> Array.item 0

  let bbenv = Verifier.initialize ess func
  Extractor.extract bbenv ess func
  let queries = Extractor.extractQueries func bbenv ess |> Array.ofList
  print Verifier.solver queries
  solver.Query(queries) |> report Verifier.solver
  0
