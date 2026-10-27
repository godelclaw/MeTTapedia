import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedOperationControls
import Lean.Data.Json.Printer

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution
open RetainedOperationControls

private def checkTerm (operation : Operation) : Term :=
  .application "==" [operation.callTerm,.application "quote" [operation.expectedTerm]]

def casesJson : Lean.Json := Lean.Json.mkObj
  [("scope", .str "Retained returns, child requests, commit and readout; complete encoded values and continuations; no full producer qualification"),
   ("cases", .arr (controls.map (fun (name,operation) => Lean.Json.mkObj
      [("name", .str name),("call", .str (checkTerm operation).render),("expected", .str "true")])).toArray)]

def main (arguments : List String) : IO Unit := do
  if arguments == ["--json"] then
    IO.println casesJson.pretty
  else if arguments.isEmpty then
    for (name,operation) in controls do
      IO.println ("!(println! (RetainedOperationControl " ++ reprStr name ++ " " ++
        (checkTerm operation).render ++ "))")
  else
    throw (IO.userError "expected no arguments or --json")
