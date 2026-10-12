import Mettapedia.Languages.MeTTa.HE.RecursiveMachine
import Mettapedia.Languages.MeTTa.HE.NativeSelectedTypeScan
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Conformance

/-!
# First-success strategy for retained recursive HE requests

This strategy reuses the existing recursive request and continuation vocabulary.
Only expression dispatch and function-candidate scanning change. Every nested
recursive request is expanded by the same strategy, so a selected overload
does not acquire the old all-candidate policy inside its arguments or body.

The classification parser is connected to the independent arrow grammar. The
applicability callback is the existing fuel-indexed source function; its exact
outputs are retained, including binding alternatives. Full correspondence of
that callback with the independent type service remains separate from the
constructed dispatch strategy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveStrategy

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks Spec.Eval Spec.Type

/-- Parse one complete arrow, retaining its original argument domains and return
projection together. A bare arrow has no result type and is rejected. -/
def readPolicy : Atom → Option SelectedTypePolicy
  | .expression (.symbol "->" :: first :: remaining) =>
      some ⟨.expression (.symbol "->" :: first :: remaining),
        (first :: remaining).dropLast,
        (first :: remaining).getLast (by simp), by
          change Atom.expression (.symbol "->" :: first :: remaining) =
            Atom.expression (.symbol "->" ::
              ((first :: remaining).dropLast ++
                [(first :: remaining).getLast (by simp)]))
          rw [List.dropLast_append_getLast]⟩
  | _ => none

theorem readPolicy_sound {candidate : Atom} {policy : SelectedTypePolicy}
    (parsed : readPolicy candidate = some policy) : policy.functionType = candidate := by
  unfold readPolicy at parsed
  split at parsed
  · cases Option.some.inj parsed
    rfl
  · cases parsed

theorem readPolicy_complete {candidate : Atom} {arguments : List Atom} {returned : Atom}
    (arrow : FunctionTypeRel candidate arguments returned) :
    ∃ policy, readPolicy candidate = some policy ∧ policy.functionType = candidate ∧
      policy.argumentTypes = arguments ∧ policy.returnType = returned := by
  change candidate = .expression (.symbol "->" :: (arguments ++ [returned])) at arrow
  subst candidate
  cases arguments with
  | nil => exact ⟨_, rfl, rfl, rfl, rfl⟩
  | cons first remaining =>
      refine ⟨_, rfl, rfl, ?_, ?_⟩
      · change ((first :: remaining) ++ [returned]).dropLast = first :: remaining
        exact List.dropLast_concat
      · change ((first :: remaining) ++ [returned]).getLast _ = returned
        exact List.getLast_concat

theorem readPolicy_none_iff (candidate : Atom) :
    readPolicy candidate = none ↔ ¬∃ arguments returned,
      FunctionTypeRel candidate arguments returned := by
  constructor
  · rintro missing ⟨arguments, returned, arrow⟩
    obtain ⟨policy, parsed, _⟩ := readPolicy_complete arrow
    rw [missing] at parsed
    cases parsed
  · intro nonFunction
    cases parsed : readPolicy candidate with
    | none => rfl
    | some policy =>
        have exactType := readPolicy_sound parsed
        exact (nonFunction ⟨policy.argumentTypes, policy.returnType,
          exactType ▸ policy.isFunction⟩).elim

inductive Selection where
  | selected (policy : SelectedTypePolicy) (alternatives : List Bindings)
  | exhausted (errors : List Atom) (tupleEligible : Bool)

def noteNonFunction : Selection → Selection
  | .selected policy alternatives => .selected policy alternatives
  | .exhausted errors _ => .exhausted errors true

def noteErrors (earlier : List Atom) : Selection → Selection
  | .selected policy alternatives => .selected policy alternatives
  | .exhausted errors eligible => .exhausted (earlier ++ errors) eligible

/-- The first successful source callback selects one arrow. Its ordered binding
alternatives all use that arrow; no later candidate is visited. -/
def select (space : Space) (expression expected : Atom) (incoming : Bindings)
    (fuel : Nat) : List Atom → Selection
  | [] => .exhausted [] false
  | candidate :: remaining =>
      match readPolicy candidate with
      | none => noteNonFunction (select space expression expected incoming fuel remaining)
      | some policy =>
          match checkIfFunctionTypeIsApplicable expression candidate expected space incoming fuel with
          | .inl errors => noteErrors errors (select space expression expected incoming fuel remaining)
          | .inr alternatives => .selected policy alternatives

/-- Source control judgment. Arrow shape is independent syntax evidence; the
existing applicability source function remains an explicitly named leaf. -/
inductive SelectionRel (space : Space) (expression expected : Atom)
    (incoming : Bindings) (fuel : Nat) : List Atom → Selection → Prop where
  | nil : SelectionRel space expression expected incoming fuel [] (.exhausted [] false)
  | nonFunction {candidate remaining result} :
      (¬∃ arguments returned, FunctionTypeRel candidate arguments returned) →
      SelectionRel space expression expected incoming fuel remaining result →
      SelectionRel space expression expected incoming fuel (candidate :: remaining)
        (noteNonFunction result)
  | failed {candidate remaining policy errors result} :
      readPolicy candidate = some policy →
      checkIfFunctionTypeIsApplicable expression candidate expected space incoming fuel = .inl errors →
      SelectionRel space expression expected incoming fuel remaining result →
      SelectionRel space expression expected incoming fuel (candidate :: remaining)
        (noteErrors errors result)
  | selected {candidate remaining policy alternatives} :
      readPolicy candidate = some policy →
      checkIfFunctionTypeIsApplicable expression candidate expected space incoming fuel = .inr alternatives →
      SelectionRel space expression expected incoming fuel (candidate :: remaining)
        (.selected policy alternatives)

theorem select_sound (space : Space) (expression expected : Atom)
    (incoming : Bindings) (fuel : Nat) (candidates : List Atom) :
    SelectionRel space expression expected incoming fuel candidates
      (select space expression expected incoming fuel candidates) := by
  induction candidates with
  | nil => exact .nil
  | cons candidate remaining ih =>
      cases parsed : readPolicy candidate with
      | none =>
          simpa only [select, parsed] using
            SelectionRel.nonFunction ((readPolicy_none_iff candidate).mp parsed) ih
      | some policy =>
          cases checked : checkIfFunctionTypeIsApplicable expression candidate expected space incoming fuel with
          | inl errors => simpa only [select, parsed, checked] using .failed parsed checked ih
          | inr alternatives => simpa only [select, parsed, checked] using
              (SelectionRel.selected (remaining := remaining) parsed checked)

theorem select_complete {space : Space} {expression expected : Atom}
    {incoming : Bindings} {fuel : Nat} {candidates : List Atom} {result : Selection}
    (derivation : SelectionRel space expression expected incoming fuel candidates result) :
    select space expression expected incoming fuel candidates = result := by
  induction derivation with
  | nil => rfl
  | nonFunction missing _ ih => simp [select, (readPolicy_none_iff _).mpr missing, ih]
  | failed parsed checked _ ih => simp [select, parsed, checked, ih]
  | selected parsed checked => simp [select, parsed, checked]

theorem select_iff (space : Space) (expression expected : Atom) (incoming : Bindings)
    (fuel : Nat) (candidates : List Atom) (result : Selection) :
    select space expression expected incoming fuel candidates = result ↔
      SelectionRel space expression expected incoming fuel candidates result := by
  constructor
  · rintro rfl
    exact select_sound space expression expected incoming fuel candidates
  · exact select_complete

theorem selected_suffix_irrelevant (space : Space) (expression expected candidate : Atom)
    (incoming : Bindings) (fuel : Nat) (policy : SelectedTypePolicy)
    (alternatives : List Bindings) (first second : List Atom)
    (parsed : readPolicy candidate = some policy)
    (checked : checkIfFunctionTypeIsApplicable expression candidate expected space incoming fuel =
      .inr alternatives) :
    select space expression expected incoming fuel (candidate :: first) =
      select space expression expected incoming fuel (candidate :: second) := by
  simp [select, parsed, checked]

/-- All recursive requests reuse the old control expansion except these two
strategy sites. The old all-candidate profile is unchanged. -/
def enter (space : Space) (dispatch : HE.GroundedDispatch) : Task → Control × List Frame
  | .expression value expected bindings (fuel + 1) =>
      match value with
      | .expression (operator :: _) =>
          (.work (.functions value expected bindings fuel (getAtomTypes space operator)), [])
      | _ => (.returning [], [])
  | .functions value expected bindings fuel candidates =>
      match select space value expected bindings fuel candidates with
      | .selected policy alternatives =>
          (.work (.bindingAlternatives value policy.functionType
            (if policy.returnType = Atom.expressionType then Atom.undefinedType else policy.returnType)
            fuel alternatives), [])
      | .exhausted errors eligible =>
          if eligible then
            (.work (.tupleCalls value expected bindings fuel),
              [.prepend (errors.map fun error => (error, bindings))])
          else (.returning (errors.map fun error => (error, bindings)), [])
  | task => RecursiveMachine.enter space dispatch task

theorem selected_enter (space : Space) (dispatch : HE.GroundedDispatch)
    (expression expected : Atom) (incoming : Bindings) (fuel : Nat)
    (candidates : List Atom) (policy : SelectedTypePolicy) (alternatives : List Bindings)
    (selected : select space expression expected incoming fuel candidates =
      .selected policy alternatives) :
    enter space dispatch (.functions expression expected incoming fuel candidates) =
      (.work (.bindingAlternatives expression policy.functionType
        (if policy.returnType = Atom.expressionType then Atom.undefinedType else policy.returnType)
        fuel alternatives), []) := by
  simp only [enter, selected]

end Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveStrategy
