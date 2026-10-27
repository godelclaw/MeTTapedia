import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedTransitionControls
import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender
import Lean.Data.Json.Printer

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution
open RetainedTransitionControls RetainedWire
open Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.Retained

private def call (head : String) (arguments : List String) : String :=
  "(" ++ String.intercalate " " (head :: arguments) ++ ")"

private def jobCheck (name : String) (job : Job) : IO String := do
  let some source := Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender.render? job.code
    | throw (IO.userError s!"Retained transition {name} cannot be read back exactly")
  pure (call "==" [source,call "quote" [(stateTerm job.after).render]])

/-- The fixture consumes the actual previous output. Its queue contains only
completed spelling returns; other producer cases are qualified separately. -/
private def returnedQueueStep (input suffix : String) : String := Id.run do
  let account := "$queueAccount" ++ suffix
  let value := "$queueValue" ++ suffix
  let next := "$queueNext" ++ suffix
  let pending := "$queuePending" ++ suffix
  let change := "$queueChange" ++ suffix
  return call "case" [input,
    "(((ViewState LNil " ++ account ++ ") (ViewState LNil " ++ account ++ ")) " ++
    "((ViewState (LCons (ViewReturned ViewSpellingKind " ++ value ++ " " ++ next ++ ") " ++ pending ++ ") " ++ account ++ ") " ++
      call "let" [change,call "gslt:collection-presentation:view-return" [value,next],
        call "gslt:collection-presentation:view-commit" [pending,account,change]] ++ "))"]

def returnedQueueControl : String := Id.run do
  let initial : State :=
    ⟨[.returned RetainedOperationControls.value .done,.returned RetainedOperationControls.otherValue .done],account⟩
  let middle := tick RetainedOperationControls.parameters initial
  let whole := run RetainedOperationControls.parameters 2 initial
  let finalAccount := encodeList spellingTerm whole.answers
  return "!" ++ call "let*"
    ["(($initial " ++ call "quote" [(stateTerm initial).render] ++ ") " ++
      "($middle " ++ returnedQueueStep "$initial" "First" ++ ") " ++
      "($whole " ++ returnedQueueStep "$middle" "Second" ++ ") " ++
      "($resumed " ++ returnedQueueStep "$middle" "Resumed" ++ ") " ++
      "($later " ++ returnedQueueStep "$whole" "Later" ++ "))",
     call "println!" [call "RetainedResumeControl"
       [reprStr "completed-candidate-queue",
        call "==" ["$middle",call "quote" [(stateTerm middle).render]],
        call "==" ["$whole",call "quote" [(stateTerm whole).render]],
        call "==" ["$resumed","$whole"],call "==" ["$later","$whole"],
        call "==" [call "gslt:collection-presentation:view-answers" ["$whole"],call "quote" [finalAccount.render]],
        call "==" [call "gslt:collection-presentation:view-complete" ["$whole"],"True"]]]]

def main (arguments : List String) : IO Unit := do
  let rows ← jobs.mapM fun (name,job) => do
    pure (name,← jobCheck name job)
  if arguments == ["--json"] then
    IO.println (Lean.Json.mkObj
      [("scope",.str "Joined retained return/child transitions with exact old agenda and ordered candidate prefix"),
       ("cases",.arr (rows.map (fun (name,code) => Lean.Json.mkObj
          [("name",.str name),("call",.str code),("expected",.str "true")])).toArray)]).pretty
  else if arguments.isEmpty then
    for (name,code) in rows do
      IO.println ("!" ++ call "println!" [call "RetainedTransitionControl" [reprStr name,code]])
    IO.println returnedQueueControl
  else
    throw (IO.userError "expected no arguments or --json")
