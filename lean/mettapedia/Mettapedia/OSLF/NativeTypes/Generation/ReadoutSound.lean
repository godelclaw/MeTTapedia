import Mettapedia.OSLF.NativeTypes.Generation.Checking

open Mettapedia.OSLF.Framework

/-!
# Semantic contracts of the public generated modal checker

Both conclusive polarities are checked against the independently generated
operational relation. A positive existential answer or a negative universal
answer needs an actual witness. The other polarities require a complete
coverage certificate and equation invariance of the supplied predicate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralOccurrenceFrontier

def ModalHolds (kind : ModalQuery) (request : Request) (test : Pattern → Bool) : Prop :=
  match kind with
  | .possibility => ∃ target,
      (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).Step request.root target ∧
        test target = true
  | .outgoingUniversal => ∀ target,
      (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).Step request.root target →
        test target = true

theorem universal_counterexample_sound {request : Request} {state : State request}
    {test : Pattern → Bool}
    (read : modalReadout .outgoingUniversal request state test = .decided false) :
    ¬ ModalHolds .outgoingUniversal request test := by
  simp only [modalReadout] at read
  by_cases all : (targets request state).all test = true
  · simp only [all, Bool.not_true, Bool.false_eq_true, if_false] at read
    split at read <;> cases read
  · have notAll : ¬ (targets request state).all test = true := all
    obtain ⟨target, member, rejected⟩ := List.all_eq_false.mp
      (Bool.eq_false_iff.mpr notAll)
    obtain ⟨answer, _, same⟩ := List.mem_map.mp member
    subst target
    intro universal
    have accepted := universal answer.val.target (emitted_step request answer)
    exact rejected accepted

theorem universal_confirmation_sound {request : Request} {state : State request}
    {test : Pattern → Bool}
    (compiled : request.plan = GeneralExecutionAdmission.compile request.plan.snapshot request.plan.permissions)
    (invariant : ∀ first second, Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected)
      first second → test first = test second)
    (read : modalReadout .outgoingUniversal request state test = .decided true) :
    ModalHolds .outgoingUniversal request test := by
  simp only [modalReadout] at read
  by_cases all : (targets request state).all test = true
  · simp only [all, Bool.not_true, Bool.false_eq_true, if_false] at read
    split at read
    · rename_i certified
      simp only [Bool.and_eq_true] at certified
      apply (certified_outgoing_universal (sourceAdmission_sound certified.1 compiled)
        certified.2 test invariant).mp
      exact all
    · cases read
  · have notAll : (targets request state).all test = false := Bool.eq_false_iff.mpr all
    simp [notAll] at read

theorem modal_readout_correct {request : Request} {state : State request} {kind : ModalQuery}
    {test : Pattern → Bool} {answer : Bool}
    (compiled : request.plan = GeneralExecutionAdmission.compile request.plan.snapshot request.plan.permissions)
    (invariant : ∀ first second, Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected)
      first second → test first = test second)
    (read : modalReadout kind request state test = .decided answer) :
    answer = true ↔ ModalHolds kind request test := by
  cases kind <;> cases answer
  · exact ⟨(fun impossible => by cases impossible),
      fun witness => False.elim (possibility_refutation_sound compiled invariant read witness)⟩
  · exact ⟨fun _ => possibility_witness_sound read, fun _ => rfl⟩
  · exact ⟨(fun impossible => by cases impossible),
      fun universal => False.elim (universal_counterexample_sound read universal)⟩
  · exact ⟨fun _ => universal_confirmation_sound compiled invariant read, fun _ => rfl⟩

theorem conclusive_generated_modal_readout {generated : Generated} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {kind : ModalQuery}
    {test : InvariantTest (generated.request bound expected source)} {budget : Nat} {answer : Bool}
    (read : (generated.checkModal bound expected source kind test budget).result = .decided answer) :
    modalReadout kind (generated.request bound expected source)
      (generated.execute bound expected source budget) test.accepts = .decided answer := by
  cases kind <;>
    simp only [Generated.checkModal] at read
  all_goals
    split at read
    · cases read
    · cases status : generated.equationAdmission with
      | none => simp [status] at read
      | some accepted =>
          cases accepted with
          | false => simp [status] at read
          | true => simpa only [status] using read

/-- The public checker has the same two-sided truth contract, including the
actual source's binder normalization and the chosen operational profile. -/
theorem generated_modal_readout_correct {generated : Generated} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {kind : ModalQuery}
    {test : InvariantTest (generated.request bound expected source)} {budget : Nat} {answer : Bool}
    (read : (generated.checkModal bound expected source kind test budget).result = .decided answer) :
    answer = true ↔ ModalHolds kind (generated.request bound expected source) test.accepts :=
  modal_readout_correct rfl test.invariant (conclusive_generated_modal_readout read)

end Mettapedia.OSLF.NativeTypes.Generation
