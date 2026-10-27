import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorScanControls
import Lean.Data.Json.Printer

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution
open RetainedConstructors.Controls RetainedWire

private def call (head : String) (arguments : List String) : String :=
  "(" ++ String.intercalate " " (head :: arguments) ++ ")"

private def selected (code pattern body : String) : String :=
  call "case" [code,"((" ++ pattern ++ " " ++ body ++ "))"]

def controlSource (control : Control) : IO String := do
  unless control.change.1.length == control.children && control.change.2.isEmpty do
    throw (IO.userError s!"Constructor scan {control.name} has the wrong child/publication account")
  let expected := call "quote" [(expansionTerm control.change).render]
  let body := call "println!" [call "ConstructorScanControl"
    [reprStr control.name,call "==" ["$changed",expected],
      call "==" [call "gslt:automata:length" ["$tasks"],toString control.children],
      call "==" ["$published","LNil"]]]
  let measurement := Lean.Json.mkObj
    [("label", .str ("constructor-scan-" ++ control.name)),
      ("source_constructor_rows", Lean.toJson control.remaining.length),
      ("source_ordinal", Lean.toJson control.ordinal),
      ("target_binder_depth", Lean.toJson control.focus.bound.length),
      ("schema_binder_depth", Lean.toJson control.schemaBound.length),
      ("child_tasks", Lean.toJson control.children),
      ("constructor_frames", Lean.toJson (if control.children == 2 then 1 else (0 : Nat))),
      ("publications", Lean.toJson control.change.2.length),
      ("input_wire_bytes", Lean.toJson (taskTerm control.task).render.utf8ByteSize)]
  pure ("; GSLT-MEASUREMENT " ++ measurement.compress ++ "\n!" ++
    call "let" ["$changed",control.callTerm.render,
      selected "$changed" "(ViewExpansion $tasks $published)" body])

def casesJson : Lean.Json := Lean.Json.mkObj
  [("scope", .str "Exact retained constructor scan; full queued tasks, ordinals, contexts and continuations; no general admission"),
   ("cases", .arr (controls.map (fun control => Lean.Json.mkObj
     [("name", .str control.name),
      ("call", .str (call "==" [control.callTerm.render,
        call "quote" [(expansionTerm control.change).render]])),
      ("expected", .str "true")])).toArray)]

def main (arguments : List String) : IO Unit := do
  if arguments == ["--json"] then
    IO.println casesJson.pretty
  else if arguments.isEmpty then
    for control in controls do IO.println (← controlSource control)
  else
    throw (IO.userError "expected no arguments or --json")
