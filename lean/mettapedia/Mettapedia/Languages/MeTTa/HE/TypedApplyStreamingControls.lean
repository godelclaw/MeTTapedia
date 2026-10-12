import Mettapedia.Languages.MeTTa.HE.TypedApplyStreaming
import Mettapedia.Languages.MeTTa.HE.Eval

/-!
# Typed application execution and profile-boundary controls

The examples distinguish retained choices from independent requests, retain
binding environments and pending siblings, and exercise raw/error and failed
merge/binder paths. The final controls check the recursive HE model's tagged
argument success protocol on raw `Error` data. This example does not assert
unrestricted correspondence between the two evaluator profiles.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypedApplyStreaming.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open TypedApplyDerivation (Services Derivation)

def a : Atom := .symbol "a"
def b : Atom := .symbol "b"
def pick : Atom := .symbol "pick"
def boundPick : Atom := .symbol "bound-pick"
def valueType : Atom := .symbol "Value"
def rejectedType : Atom := .symbol "Reject"
def failure : Atom := Atom.error (.symbol "failed") (.symbol "BadType")
def environmentA : Bindings := Bindings.empty.assign "selected" a
def environmentB : Bindings := Bindings.empty.assign "selected" b

def evaluate : Atom → Atom → Bindings → ResultList
  | .symbol "pick", _, environment => [(a, environment), (b, environment)]
  | .symbol "bound-pick", _, environment =>
      [(a, environment.assign "selected" a), (b, environment.assign "selected" b)]
  | .symbol "duplicates", _, environment => [(a, environment), (a, environment), (b, environment)]
  | .symbol "fail", _, environment => [(failure, environment)]
  | .symbol "bad-then-good", _, environment =>
      [(a, environment.assign "reject" a), (b, environment)]
  | argument, _, environment => [(argument, environment)]

def services : Services where
  evaluate := evaluate
  apply := Bindings.applyDefault
  merge := fun _ result => if result.lookup "reject" = some a then none else some result
  extend := fun environment type _ => if type = rejectedType then none else some environment
  raw := fun type => type == Atom.atomType

private theorem empty_binding_application (fuel : Nat) (argument : Atom) :
    Bindings.apply Bindings.empty argument fuel = argument := by
  induction fuel generalizing argument with
  | zero => rfl
  | succ fuel ih =>
      cases argument with
      | expression atoms =>
          simp only [Bindings.apply]
          apply congrArg Atom.expression
          have identity : (fun atom => Bindings.apply Bindings.empty atom fuel) = id := funext ih
          rw [identity]
          exact List.map_id atoms
      | symbol name => rfl
      | grounded value => rfl
      | var name => rfl

private theorem empty_default_application (argument : Atom) :
    Bindings.applyDefault Bindings.empty argument = argument :=
  empty_binding_application 100 argument

def shared : TypedApplyState :=
  .initial (.symbol "Same") [boundPick, .var "selected"]
    [valueType, valueType] Bindings.empty

def independent : TypedApplyState :=
  .initial (.symbol "Same") [pick, pick] [valueType, valueType] Bindings.empty

def firstResult : ResultPair := (.expression [.symbol "Same", a, a], environmentA)
def secondResult : ResultPair := (.expression [.symbol "Same", b, b], environmentB)

def saved : Configuration :=
  ⟨[.argConsumer [(b, environmentB)] boundPick valueType shared], [firstResult]⟩

/-- These finite controls observe a budgeted run of the actual common driver. -/
def results (state : TypedApplyState) : ResultList :=
  ((machine services).run 20 (.initial state)).1

theorem choose_once_retains_correlation :
    results shared = [firstResult, secondResult] := by decide

theorem independent_choices_remain_independent :
    (results independent).map Prod.fst =
      [.expression [.symbol "Same", a, a], .expression [.symbol "Same", a, b],
        .expression [.symbol "Same", b, a], .expression [.symbol "Same", b, b]] := by decide

theorem mixed_shared_answer_rejected :
    (.expression [.symbol "Same", a, b], environmentA) ∉ results shared := by
  rw [choose_once_retains_correlation]
  decide

theorem administrative_budget_derived : rank services (.initial shared) = 8 := by
  have account := spent_plus_remaining services (fun _ _ _ => 0) 20 (.initial shared)
  have spent : (machine services).spent (price services (fun _ _ _ => 0))
      20 (.initial shared) = 8 := by decide
  have remaining : (machineRun services.evaluate services.apply services.merge services.extend
      services.raw (.initial shared) 20).work services.evaluate services.apply services.merge
        services.extend services.raw (fun _ _ _ => 0) = 0 := rfl
  simpa [rank, spent, remaining] using account.symm


theorem pause_after_first_occurrence :
    (machine services).run 4 (.initial shared) = ([firstResult], .exhausted saved) := rfl

theorem saved_sibling_is_the_remaining_occurrence :
    ((machine services).run 5 saved).1 = [secondResult] := by decide

theorem prefix_and_resumption_agree :
    (machine services).run 9 (.initial shared) =
      ([firstResult] ++ ((machine services).run 5 saved).1,
        ((machine services).run 5 saved).2) :=
  resume_after_prefix services 4 5 (.initial shared) saved [firstResult]
    pause_after_first_occurrence

theorem saved_history_is_not_emitted_again : firstResult ∉ ((machine services).run 5 saved).1 := by
  decide

theorem restart_repeats_the_prefix :
    ((machine services).run 4 (.initial shared)).1 ++
        ((machine services).run 5 (.initial shared)).1 ≠ results shared := by
  rw [choose_once_retains_correlation]
  decide

theorem omitted_sibling_loses_an_answer :
    ((machine services).run 5 (⟨[], [firstResult]⟩ : Configuration)).1 ≠
      ((machine services).run 5 saved).1 := by decide

def splicedBindings : Configuration :=
  ⟨[.apply (shared.advance b Bindings.empty)], [firstResult]⟩

theorem discarded_binding_changes_the_answer :
    ((machine services).run 5 splicedBindings).1 =
      [(.expression [.symbol "Same", b, .var "selected"], Bindings.empty)] := by decide

theorem spliced_state_is_not_the_residual :
    ((machine services).run 5 splicedBindings).1 ≠ ((machine services).run 5 saved).1 := by decide

theorem service_charge_is_separate :
    (machine services).spent (price services (fun _ _ _ => 7)) 20 (.initial shared) = 15 := by
  decide

theorem resumed_service_is_not_recharged :
    (machine services).spent (price services (fun _ _ _ => 7)) 5 saved = 4 := by decide

theorem exhausted_history_finishes_at_zero_charge :
    (machine services).spent (price services (fun _ _ _ => 7)) 5
      (⟨[], [firstResult, secondResult]⟩ : Configuration) = 0 := by decide

theorem duplicate_occurrences_are_retained :
    results (.initial (.symbol "f") [.symbol "duplicates"] [valueType] Bindings.empty) =
      [(.expression [.symbol "f", a], Bindings.empty),
        (.expression [.symbol "f", a], Bindings.empty),
        (.expression [.symbol "f", b], Bindings.empty)] := by decide

theorem argument_error_short_circuits :
    results (.initial (.symbol "f") [.symbol "fail", pick]
      [valueType, valueType] Bindings.empty) = [(failure, Bindings.empty)] := by decide

theorem unchanged_error_is_data :
    results (.initial (.symbol "f") [failure, .symbol "tail"]
      [valueType, valueType] Bindings.empty) =
      [(.expression [.symbol "f", failure, .symbol "tail"], Bindings.empty)] := by decide

theorem raw_choice_is_not_requested :
    results (.initial (.symbol "f") [pick] [Atom.atomType] Bindings.empty) =
      [(.expression [.symbol "f", pick], Bindings.empty)] := by decide

/-- The raw policy retains arbitrary syntax trees, including binder and
quotation syntax; this is a data-holding law, not a binder evaluator theorem. -/
theorem arbitrary_raw_tree_retained (argument : Atom) :
    results (.initial (.symbol "f") [argument] [Atom.atomType] Bindings.empty) =
      [(.expression [.symbol "f", argument], Bindings.empty)] := by
  unfold results
  simp [Machine.run, machine, events, next, stepConfig, processFrame, processApplyFrame,
    TypedApplyConfig.initial, TypedApplyConfig.isDone, TypedApplyState.initial,
    empty_default_application, services, getArgType, TypedApplyState.advance,
    rejectedType, Atom.atomType]

theorem failed_merge_skips_only_its_own_candidate :
    results (.initial (.symbol "f") [.symbol "bad-then-good"] [valueType] Bindings.empty) =
      [(.expression [.symbol "f", b], Bindings.empty)] := by decide

theorem failed_binder_contributes_no_answer :
    results (.initial (.symbol "f") [pick] [rejectedType] Bindings.empty) = [] := by decide

def failingRawBinder : Services :=
  { services with extend := fun _ _ _ => none }

theorem raw_binder_failure_also_rejects :
    typedApplyDirect failingRawBinder.evaluate failingRawBinder.apply failingRawBinder.merge
      failingRawBinder.extend failingRawBinder.raw
      (.initial (.symbol "f") [pick] [Atom.atomType] Bindings.empty) = []  := by
  unfold typedApplyDirect
  simp [failingRawBinder, services, TypedApplyState.initial, Atom.atomType]

theorem rejected_branch_has_no_derivation :
    ¬Derivation services
      (.initial (.symbol "f") [.symbol "bad-then-good"] [valueType] Bindings.empty)
      (.expression [.symbol "f", a], Bindings.empty) := by
  let state := TypedApplyState.initial (.symbol "f") [.symbol "bad-then-good"]
    [valueType] Bindings.empty
  let emitted : ResultList := [(.expression [.symbol "f", b], Bindings.empty)]
  let final : Configuration := ⟨[], emitted⟩
  have finished : (machine services).run 20 (.initial state) = (emitted, .finished final) := rfl
  have exactResults := (completed_initial services state 20 emitted final finished).1
  rw [← TypedApplyDerivation.direct_iff, ← exactResults]
  decide


def rawErrorArguments : List Atom := [.symbol "x", .symbol "Error", .symbol "y"]
def rawErrorTypes : List Atom := [Atom.atomType, Atom.atomType, Atom.atomType]

theorem recursive_HE_argument_packet_retains_raw_error :
    interpretArgs Space.empty GroundedDispatch.none rawErrorArguments rawErrorTypes
      Bindings.empty 16 = [(argumentPacket rawErrorArguments, Bindings.empty)] := by
  decide

theorem typed_prefix_retains_raw_error_symbol :
    results (.initial (.symbol "f") rawErrorArguments rawErrorTypes Bindings.empty) =
      [(.expression [.symbol "f", .symbol "x", .symbol "Error", .symbol "y"], Bindings.empty)] := by decide

/-- The function path unpacks success data before constructing the call. -/
def assemble (head : Atom) (result : ResultPair) : ResultPair :=
  if argumentsSucceeded result.1 = false then result
  else (.expression (head :: argumentValues result.1), result.2)

theorem tagged_recursive_HE_example_agrees :
    results (.initial (.symbol "f") rawErrorArguments rawErrorTypes Bindings.empty) =
      (interpretArgs Space.empty GroundedDispatch.none rawErrorArguments rawErrorTypes
        Bindings.empty 16).map (assemble (.symbol "f")) := by
  rw [typed_prefix_retains_raw_error_symbol, recursive_HE_argument_packet_retains_raw_error]
  decide

end Mettapedia.Languages.MeTTa.HE.TypedApplyStreaming.Controls
