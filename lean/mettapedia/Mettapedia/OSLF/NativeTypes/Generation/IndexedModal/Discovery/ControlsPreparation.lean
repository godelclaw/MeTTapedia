import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ControlsParameters

/-! # Independent generated-question preparation controls -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ControlsPreparation

open Mettapedia.OSLF.MeTTaIL Syntax
open FocusMeaning FiniteFocusChecking ControlsParameters

def expect {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

def install (language : LanguageDef) : IO Joined.Installed :=
  match Consumers.generate language with
  | .ok installed => pure installed
  | .error reason => throw (IO.userError ("Authored language refused: " ++ reprStr reason))

@[noinline] def run : IO Unit := do
  let lambda ← install BindingPipeline.Controls.originalLambda
  let question ← expect (lambdaQuestion lambda)
  if (requests question.parameters).length != 2 then
    throw (IO.userError "Independent lambda domain did not retain both arguments")
  if !(lambda.indexed.headers[question.index].indices.isEmpty) then
    throw (IO.userError "Lambda identity fixture gained a fixed shared index")
  if !checkFocus lambda question.index [] question.focus then
    throw (IO.userError "Independently authored identity focus was ill-typed")
  for values in requests question.parameters do
    let some argument := relyBody? values "A"
      | throw (IO.userError "Authored lambda argument slot was lost")
    if !question.parameters.target values [] argument then
      throw (IO.userError "Dependent lambda target rejected its supplied argument")
    let other := if argument == identity then constant else identity
    if question.parameters.target values [] other then
      throw (IO.userError "Dependent lambda target ignored its supplied argument")
  let binder ← expect (binderQuestion lambda)
  if !(lambda.indexed.schema binder.index).focusBound == [.base "Term"] then
    throw (IO.userError "Binder-local fixture lost its independently declared local context")
  if (requests binder.parameters).length != 1 then
    throw (IO.userError "Zero rely slots did not retain their mandatory empty-tuple request")
  let root ← expect (rootQuestion lambda)
  if (requests root.parameters).length != 1 then
    throw (IO.userError "Closed beta fixture has no empty-tuple request")
  let letCase ← install BindingPipeline.Controls.originalLetCase
  let case ← expect (caseQuestion letCase)
  if (requests case.parameters).length != 4 then
    throw (IO.userError "Two independent rely domains did not produce their full Cartesian product")
  if !checkFocus letCase case.index [] case.focus then
    throw (IO.userError "Two-binder case focus was ill-typed")
  for values in requests case.parameters do
    let some first := relyBody? values "L"
      | throw (IO.userError "CasePair left input was lost")
    let expected := Pattern.apply "Return" [first]
    if !case.parameters.target values [] expected then
      throw (IO.userError "CasePair target did not depend on its left input")
  let shared ← install Consumers.sharedLanguage
  let left ← expect (sharedQuestion shared 0)
  let right ← expect (sharedQuestion shared 1)
  if (shared.indexed.schema left.index).ordinal == (shared.indexed.schema right.index).ordinal then
    throw (IO.userError "Distinct authored origins collapsed before execution")
  if (shared.indexed.headers[left.index].indices.isEmpty) ||
      (shared.indexed.headers[right.index].indices.isEmpty) then
    throw (IO.userError "Independent shared-index parameters were not generated")
  let invalid := parameters? lambda question.index [] [] [("A", [.apply "Unit" []])]
    lambdaTarget
  if invalid.isSome then
    throw (IO.userError "Ill-sorted rely input was accepted before execution")
  IO.println "Independent contextual questions: lambda=2, pair-case=4, binder-local=1, root=1, distinct shared origins"

#eval run

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ControlsPreparation
