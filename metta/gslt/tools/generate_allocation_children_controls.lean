import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.AllocationChildrenControls
import Lean.Data.Json.Printer

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution
open AllocationChildrenControls

private def checkTerm (operation : Operation) : Term :=
  .application "==" [operation.callTerm,
    .application "quote" [encodeList RetainedWire.taskTerm operation.tasks]]

def main (arguments : List String) : IO Unit := do
  if arguments == ["--json"] then
    IO.println (Lean.Json.mkObj
      [("scope", .str "Allocation child construction from caller-ordered residuals; normalization remains separate"),
       ("cases", .arr (controls.map (fun (name,operation) => Lean.Json.mkObj
         [("name", .str name),("call", .str (checkTerm operation).render),
          ("expected", .str "true")])).toArray)]).pretty
  else if arguments.isEmpty then
    for (name,operation) in controls do
      IO.println ("!(println! (AllocationChildrenControl " ++ reprStr name ++ " " ++
        (checkTerm operation).render ++ "))")
  else
    throw (IO.userError "expected no arguments or --json")
