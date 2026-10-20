import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.Frontier

/-!
# Finite response families over certified equation profiles

The input is a finite family of source requests, already reconstructed from
the proposed focus and rely values. Each input has its own dependent target
classifier. A successful verification returns a complete occurrence receipt
for every input. Refutation needs a checked exhaustive source frontier;
missing evidence or exhausted fuel alone yields `unknown`.

This operational companion does not infer source reconstruction, focus
admission, or the vocabulary of a generated former. Those obligations remain
with its caller, including the existing `FocusQuery` interface.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles

open Mettapedia.OSLF.MeTTaIL Syntax GeneralOccurrenceFrontier Complete
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe u

structure FamilyParameters (Input : Type u) where
  inputs : List Input
  request : Input → Request
  target : (input : Input) → Test (request input)

namespace FamilyParameters

variable {Input : Type u} (parameters : FamilyParameters Input)

/-- Native universal-input may membership in the independently presented
one-step relation. The target can depend on the selected input. -/
def Meaning : Prop :=
  ∀ input ∈ parameters.inputs,
    gsltDiamond (Presented.gslt (parameters.request input).plan (parameters.request input).bound
      (parameters.request input).expected) (parameters.target input).predicate (parameters.request input).root

abbrev States := (input : Input) → State (parameters.request input)

structure Response (states : parameters.States) (input : Input) where
  answer : Answer (parameters.request input)
  retained : answer ∈ (states input).answers
  target : (parameters.target input).accepts answer.val.target = true

def response? (states : parameters.States) (input : Input) : Option (parameters.Response states input) :=
  match found : (states input).answers.find? (fun answer : Answer (parameters.request input) => (parameters.target input).accepts answer.val.target) with
  | none => none
  | some answer => some ⟨answer, List.mem_of_find?_eq_some found, List.find?_some (p := fun answer : Answer (parameters.request input) =>
      (parameters.target input).accepts answer.val.target) found⟩

theorem response?_exact (states : parameters.States) (input : Input) :
    (parameters.response? states input).isSome = true ↔
      (targets (parameters.request input) (states input)).any (parameters.target input).accepts = true := by
  unfold response?
  split
  · rename_i absent
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    intro found
    obtain ⟨target, member, accepts⟩ := List.any_eq_true.mp found
    change target ∈ (states input).answers.map (fun answer => answer.val.target) at member
    obtain ⟨answer, retained, same⟩ := List.mem_map.mp member
    subst target
    exact (List.find?_eq_none.mp absent answer retained) accepts
  · rename_i answer found
    simp only [Option.isSome_some, true_iff]
    exact List.any_eq_true.mpr ⟨answer.val.target,
      List.mem_map.mpr ⟨answer, List.mem_of_find?_eq_some found, rfl⟩, List.find?_some (p := fun answer : Answer (parameters.request input) =>
      (parameters.target input).accepts answer.val.target) found⟩

def check (states : parameters.States) : Bool :=
  parameters.inputs.all fun input => (parameters.response? states input).isSome

structure Family (states : parameters.States) where
  respond : ∀ input ∈ parameters.inputs, parameters.Response states input

/-- Accepted verification yields executable responses, selected from the
retained source frontiers without discarding any payload field. -/
def membership? (states : parameters.States) : Option (parameters.Family states) :=
  if checked : parameters.check states = true then
    some ⟨fun input member => (parameters.response? states input).get
      (List.all_eq_true.mp checked input member)⟩
  else none

theorem Response.source {states : parameters.States} {input : Input}
    (response : parameters.Response states input) :
    gsltDiamond (Presented.gslt (parameters.request input).plan (parameters.request input).bound
      (parameters.request input).expected) (parameters.target input).predicate (parameters.request input).root := by
  apply (gsltDiamond_spec _ _ _).mpr
  exact ⟨response.answer.val.target,
    Presented.step_of_gslt _ _ _ (emitted_step (parameters.request input) response.answer), response.target⟩

theorem check_sound (states : parameters.States) (checked : parameters.check states = true) :
    parameters.Meaning := by
  intro input member
  obtain ⟨response, present⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp checked input member)
  exact response.source parameters

theorem membership?_exact (states : parameters.States) :
    (parameters.membership? states).isSome = true ↔ parameters.check states = true := by
  unfold membership?
  split <;> simp_all

/-- Checked physical coverage and the two local semantic obligations are
enough to reflect universal-input membership into a finite receipt family. -/
theorem check_complete (states : parameters.States)
    (certificates : ∀ input ∈ parameters.inputs, LocalCertificate (parameters.request input))
    (admitted : ∀ input ∈ parameters.inputs, Admitted (parameters.request input))
    (covered : ∀ input ∈ parameters.inputs, checkCertificate (parameters.request input) (states input) = true) :
    parameters.check states = true ↔ parameters.Meaning := by
  constructor
  · exact parameters.check_sound states
  · intro meaning
    apply List.all_eq_true.mpr
    intro input member
    exact (parameters.response?_exact states input).mpr
      ((certified_possibility (certificates input member) (admitted input member) (covered input member)
        (parameters.target input)).mpr (meaning input member))

/-- A semantic refutation is earned by an exhaustive negative readout on a
particular admitted input. Partial source frontiers cannot refute a family. -/
def counterexample (states : parameters.States) : Bool :=
  parameters.inputs.any fun input =>
    readout .possibility (parameters.request input) (states input) (parameters.target input) == .decided false

def verdict (states : parameters.States) : CheckResult :=
  if parameters.check states then .decided true
  else if parameters.counterexample states then .decided false else .unknown

theorem counterexample_sound (states : parameters.States)
    (certificates : ∀ input ∈ parameters.inputs, LocalCertificate (parameters.request input))
    (compiled : ∀ input ∈ parameters.inputs,
      (parameters.request input).plan = GeneralExecutionAdmission.compile
        (parameters.request input).plan.snapshot (parameters.request input).plan.permissions)
    (negative : parameters.counterexample states = true) : ¬ parameters.Meaning := by
  intro meaning
  obtain ⟨input, member, negative⟩ := List.any_eq_true.mp negative
  exact possibility_refuted (certificates input member) (compiled input member) (parameters.target input)
    (beq_iff_eq.mp negative) (meaning input member)

theorem verdict_proved (states : parameters.States)
    (positive : parameters.verdict states = .decided true) : parameters.Meaning := by
  unfold verdict at positive
  split at positive
  · exact parameters.check_sound states (by assumption)
  · split at positive <;> cases positive

theorem verdict_refuted (states : parameters.States)
    (certificates : ∀ input ∈ parameters.inputs, LocalCertificate (parameters.request input))
    (compiled : ∀ input ∈ parameters.inputs,
      (parameters.request input).plan = GeneralExecutionAdmission.compile
        (parameters.request input).plan.snapshot (parameters.request input).plan.permissions)
    (negative : parameters.verdict states = .decided false) : ¬ parameters.Meaning := by
  unfold verdict at negative
  split at negative
  · cases negative
  · split at negative
    · exact parameters.counterexample_sound states certificates compiled (by assumption)
    · cases negative

def begin : parameters.States := fun input => start (parameters.request input)

def resume (states : parameters.States) (fuel : Nat) : parameters.States :=
  fun input => run (parameters.request input) fuel (states input)

theorem resume_add (states : parameters.States) (first extra : Nat) :
    parameters.resume states (first + extra) = parameters.resume (parameters.resume states first) extra := by
  funext input
  exact run_add _ _ _ _

/-- This statement is about unfinished frontiers, not a timeout interpreted
as a mathematical counterexample. -/
theorem unfinished_unknown (states : parameters.States) (input : Input)
    (member : input ∈ parameters.inputs)
    (none : (states input).answers = [])
    (unfinished : ∀ candidate ∈ parameters.inputs, complete (parameters.request candidate) (states candidate) = false)
    (empty : ∀ candidate ∈ parameters.inputs, (states candidate).answers = []) :
    parameters.verdict states = .unknown := by
  have noCheck : parameters.check states = false := by
    cases checked : parameters.check states with
    | false => rfl
    | true =>
      have response := (parameters.response?_exact states input).mp (List.all_eq_true.mp checked input member)
      simp [targets, none] at response
  have noCounterexample : parameters.counterexample states = false := by
    apply Bool.eq_false_iff.mpr
    intro found
    obtain ⟨candidate, present, negative⟩ := List.any_eq_true.mp found
    have unknown := unfinished_is_unknown (empty candidate present) (unfinished candidate present)
      (parameters.target candidate)
    rw [unknown] at negative
    exact Bool.noConfusion negative
  simp [verdict, noCheck, noCounterexample]

end FamilyParameters

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles
