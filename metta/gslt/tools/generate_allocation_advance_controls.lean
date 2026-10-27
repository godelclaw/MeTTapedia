import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.AllocationAdvance
import Lean.Data.Json.Printer

set_option autoImplicit false
set_option Elab.async false

namespace RetainedAllocationAdvanceControls

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts
open Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus
open RecursiveView Retained
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution
open AllocationAdvance
open InferenceCettaWire.AuthoredRule (typeTerm)

private def p : TypeExpr := .base "Proc"
private def source (width : Nat) : Pattern :=
  .collection .hashBag [.apply "unit" [], .collection .hashBag
    ((List.range width).map fun index => .apply (if index % 2 == 0 then "A" else "B") []) none] none

private def focus (source : Pattern) : Focus :=
  .original [p, .arrow p p] p source (.lambda (some "outer") .hole)

private def next (focus : Focus) : Continuation .spelling :=
  .lambda ⟨[3, 1], [p], focus, some 19, none⟩ (some "display-kept") .done

private inductive PublicationCursor where
  | zero | current | oneBehind

private def control (count width fuel : Nat) (mode : PublicationCursor) : IO Lean.Json := do
  let source := source width
  let focus := focus source
  let next := next focus
  let records := normalizedOccurrences "unit" source
  unless records.length == width &&
      records.all (fun record => record.context.fill record.original == source) &&
      (records.map SourceOccurrence.address).eraseDups.length == width do
    throw (IO.userError "Allocation cursor fixture lost its actual complete source occurrences")
  let initial := GroupedCursor.start count records
  let cursor := GroupedCursor.run fuel initial
  let published := match mode with
    | .zero => 0
    | .current => cursor.answers.length
    | .oneBehind => cursor.answers.length - 1
  have within : published ≤ cursor.answers.length := by cases mode <;> simp_all [published]
  let schemaBound := [p, .arrow p p]
  let path := [7, 2]
  let schemas := List.replicate count (.fvar "kept-schema")
  let rest : Option String := some "kept-residual"
  let advanced := GroupedCursor.tick cursor
  let pending := pendingTasks schemaBound path focus schemas rest advanced next
  let expected := progressTerm schemaBound path focus schemas rest cursor published next
  let modeLabel := match mode with
    | .zero => "zero"
    | .current => "current"
    | .oneBehind => "one-behind"
  let label := s!"groups-{count}-components-{width}-fuel-{fuel}-{modeLabel}-published-{published}"
  let call (head : String) (args : List String) := "(" ++ String.intercalate " " (head :: args) ++ ")"
  let quote (term : Term) := "(quote " ++ term.render ++ ")"
  let bind (name value : String) := "(" ++ name ++ " " ++ value ++ ")"
  let initialBindings :=
    [bind "$records" (quote (encodeList RetainedWire.occurrenceTerm records)),
     bind "$begun" (call "gslt:collection-presentation:group-begin" [toString count, "$records"]),
     bind "$cursor" (call "gslt:collection-presentation:group-run" [toString fuel, "$begun"]),
     bind "$schema-bound" (quote (encodeList typeTerm schemaBound)),
     bind "$path" (quote (encodeList Term.natural path)),
     bind "$focus" (quote (RetainedWire.focusTerm focus)),
     bind "$schemas" (quote (encodeList InferenceCettaWire.encodePattern schemas)),
     bind "$rest-wire" (quote (InferenceCettaWire.encodeRest rest)),
     bind "$continuation" (quote (RetainedWire.continuationTerm next)),
     bind "$task" (call "ViewAllocations" ["$schema-bound", "$path", "$focus", "$schemas", "$rest-wire",
       "$cursor", toString published, "$continuation"]),
     bind "$actual" (call "gslt:collection-presentation:view-allocation-advance" ["$task"]),
     bind "$fresh" (call "gslt:allocation-advance-control:fresh" ["$actual"]),
     bind "$index" (call "gslt:allocation-advance-control:index" ["$actual"]),
     bind "$pending" (call "gslt:allocation-advance-control:pending" ["$actual"])]
  let checks :=
    [call "==" ["$cursor", quote (RetainedWire.cursorTerm cursor)],
     call "==" ["$task", quote (RetainedWire.taskTerm
       (.allocations schemaBound path focus schemas rest cursor published within next))],
     call "==" ["$actual", quote expected],
     call "==" [call "gslt:automata:length" ["$fresh"], toString (advanced.answers.drop published).length],
     call "==" ["$index", toString advanced.answers.length],
     call "==" [call "gslt:automata:length" ["$pending"], toString pending.length]]
  let tail := match pending with
    | [] =>
        let idleTask := .allocations schemaBound path focus schemas rest advanced
          advanced.answers.length (Nat.le_refl _) next
        let idle := progressTerm schemaBound path focus schemas rest advanced advanced.answers.length next
        let idleCall := "(let $idle-data " ++ quote (RetainedWire.taskTerm idleTask) ++ " " ++
          call "gslt:collection-presentation:view-allocation-advance" ["$idle-data"] ++ ")"
        let checkedIdle := call "=="
          [idleCall, quote idle]
        call "println!" [call "AllocationAdvanceControl" (reprStr label :: checks ++ [checkedIdle])]
    | _ :: _ =>
        let later := progressTerm schemaBound path focus schemas rest advanced advanced.answers.length next
        "(let* (" ++ bind "$next-task" (call "gslt:allocation-advance-control:head" ["$pending"]) ++
          bind "$again" (call "gslt:collection-presentation:view-allocation-advance" ["$next-task"]) ++ ") " ++
          call "println!" [call "AllocationAdvanceControl" (reprStr label :: checks ++
            [call "==" ["$again", quote later]])] ++ ")"
  let invocation := "!(let* (" ++ String.intercalate "\n" initialBindings ++ ")\n" ++ tail ++ ")"
  let expression := "(let* (" ++ String.intercalate "\n" (initialBindings.take (initialBindings.length - 3)) ++ ") " ++
    call "==" ["$actual", quote expected] ++ ")"
  pure (Lean.Json.mkObj [("label", .str label), ("name", .str label),
    ("call", .str expression), ("expected", .str "true"), ("control", .str invocation),
    ("assertions", Lean.toJson (checks.length + 1)),
    ("old_published", Lean.toJson published), ("old_answer_count", Lean.toJson cursor.answers.length),
    ("advanced_answer_count", Lean.toJson advanced.answers.length),
    ("fresh_answer_count", Lean.toJson (advanced.answers.drop published).length),
    ("pending_count", Lean.toJson pending.length),
    ("component_count", Lean.toJson width), ("group_count", Lean.toJson count),
    ("cursor_budget", Lean.toJson fuel), ("resume_budget", Lean.toJson (1 : Nat)),
    ("source_nesting_depth", Lean.toJson (2 : Nat)), ("premise_branching", Lean.toJson (0 : Nat))])

def main (arguments : List String) : IO Unit := do
  unless arguments.isEmpty || arguments == ["--json"] do
    throw (IO.userError "expected no arguments or --json")
  let mut cases : Array Lean.Json := #[]
  if arguments.isEmpty then
    IO.println "(= (gslt:allocation-advance-control:fresh $progress) (case $progress (((ViewAllocationProgress $cursor $fresh $published $pending) $fresh))))"
    IO.println "(= (gslt:allocation-advance-control:index $progress) (case $progress (((ViewAllocationProgress $cursor $fresh $published $pending) $published))))"
    IO.println "(= (gslt:allocation-advance-control:pending $progress) (case $progress (((ViewAllocationProgress $cursor $fresh $published $pending) $pending))))"
    IO.println "(= (gslt:allocation-advance-control:head $pending) (case $pending (((LCons $task $later) $task))))"
  for (count, width, fuel, mode) in
      [(0, 0, 1, PublicationCursor.zero), (0, 2, 0, .zero), (0, 2, 100, .zero),
       (0, 2, 100, .current), (0, 2, 100, .oneBehind),
       (1, 2, 0, .zero), (1, 2, 8, .zero), (1, 2, 8, .current),
       (1, 2, 100, .oneBehind), (2, 3, 15, .zero)] do
    let row ← control count width fuel mode
    cases := cases.push row
    if arguments.isEmpty then
      IO.println (← IO.ofExcept (row.getObjValAs? String "control"))
      let fields := ["label", "old_published", "old_answer_count", "advanced_answer_count",
        "fresh_answer_count", "pending_count", "component_count", "group_count", "cursor_budget",
        "resume_budget", "source_nesting_depth", "premise_branching"]
      let measured ← fields.mapM fun name => do
        pure (name, ← IO.ofExcept (row.getObjVal? name))
      IO.println ("; GSLT-MEASUREMENT " ++ (Lean.Json.mkObj
        (("family", .str "retained-allocation-advance") :: measured)).compress)
  if arguments == ["--json"] then
    IO.println (Lean.Json.mkObj [("cases", .arr cases)]).pretty

end RetainedAllocationAdvanceControls

def main (arguments : List String) : IO Unit :=
  RetainedAllocationAdvanceControls.main arguments
