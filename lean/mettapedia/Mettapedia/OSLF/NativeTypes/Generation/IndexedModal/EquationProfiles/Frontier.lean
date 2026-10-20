import Mettapedia.OSLF.NativeTypes.Generation.Checking
import Mettapedia.OSLF.MeTTaIL.Complete.Coherence
import Mettapedia.OSLF.Framework.GSLTQuotientCoherence

/-!
# Native frontier observations for declared equation and collection profiles

The occurrence frontier retains its equation paths and complete rule receipts.
Its coverage certificate covers equation classes. The local commuting and
firing laws below justify using those same receipts for the larger presented
equality, including declared collection laws. Tests must respect that equality;
tests of a representative's raw shape do not receive a quotient interpretation.

This is a consumer of the existing frontier and coherence proofs. It does not
change the admission rules of `IndexedModal.Joined.Installed`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles

open Mettapedia.OSLF.MeTTaIL Syntax GeneralOccurrenceFrontier
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Complete

/-- Local obligations from which the established tiling theorem derives
firing coherence. No executable coverage or predicate invariance is assumed. -/
structure LocalCertificate (request : Request) : Prop where
  commute : Coherence.LocalCommute
    (GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected)
    (CanonicalBags.StandardStep (Normalized.laws request.plan) (Normalized.extrusions request.plan))
  firing : Coherence.FiringInvariant request.plan request.bound request.expected

theorem LocalCertificate.coherent {request : Request} (certificate : LocalCertificate request) :
    Coherence.Coherent request.plan request.bound request.expected :=
  Coherence.coherent_of_local certificate.commute certificate.firing

/-- The observable part of a native target classifier, with explicit
stability under all equations and collection laws selected by the plan. -/
structure Test (request : Request) where
  accepts : Pattern → Bool
  invariant : ∀ first second,
    Presented.ModelEquiv request.plan request.bound request.expected first second →
    accepts first = accepts second

def Test.predicate {request : Request} (test : Test request) :
    EquationPredicate (Presented.gslt request.plan request.bound request.expected) :=
  ⟨fun target => test.accepts target = true, by
    intro first second equivalent
    change test.accepts first = true ↔ test.accepts second = true
    exact (test.invariant first second equivalent) ▸ Iff.rfl⟩

/-- The existing checker is reused without replacing or compressing receipts. -/
def readout (kind : ModalQuery) (request : Request) (state : State request)
    (test : Test request) : CheckResult :=
  modalReadout kind request state test.accepts

theorem equations_model {request : Request} {first second : Pattern}
    (equivalent : Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected) first second) :
    Presented.ModelEquiv request.plan request.bound request.expected first second :=
  Relation.EqvGen.mono (fun _ _ step => Or.inl step) _ _ equivalent

theorem Test.equationInvariant {request : Request} (test : Test request) :
    ∀ first second, Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected)
      first second → test.accepts first = test.accepts second :=
  fun _ _ equivalent => test.invariant _ _ (equations_model equivalent)

/-- A positive readout retains an actual occurrence answer from the supplied
state, including its original conversions, declaration and premise evidence. -/
theorem positive_receipt {request : Request} {state : State request} {test : Test request}
    (positive : readout .possibility request state test = .decided true) :
    ∃ answer ∈ state.answers, test.accepts answer.val.target = true ∧
      (Presented.gslt request.plan request.bound request.expected).Step request.root answer.val.target := by
  simp only [readout, modalReadout] at positive
  split at positive
  · rename_i found
    obtain ⟨target, member, holds⟩ := List.any_eq_true.mp found
    obtain ⟨answer, answerMember, same⟩ := List.mem_map.mp member
    subst target
    exact ⟨answer, answerMember, holds,
      Presented.step_of_gslt _ _ _ (emitted_step request answer)⟩
  · split at positive <;> cases positive

/-- A presented step is answered by one of the retained source receipts,
up to the full model equality, when the local certificate and frontier
coverage have both been checked. -/
theorem covered_receipt {request : Request} {state : State request}
    (certificate : LocalCertificate request) (admitted : Admitted request)
    (covered : checkCertificate request state = true) {target : Pattern}
    (step : (Presented.gslt request.plan request.bound request.expected).Step request.root target) :
    ∃ answer ∈ state.answers,
      Presented.ModelEquiv request.plan request.bound request.expected answer.val.target target := by
  obtain ⟨reached, equationStep, related⟩ :=
    Coherence.step_of_presented certificate.coherent step (.refl _)
  obtain ⟨answer, member, equationRelated⟩ :=
    (certified_successor_classes admitted covered reached).mpr equationStep
  exact ⟨answer, member, .trans _ _ _ (equations_model equationRelated) related⟩

theorem certified_possibility {request : Request} {state : State request}
    (certificate : LocalCertificate request) (admitted : Admitted request)
    (covered : checkCertificate request state = true) (test : Test request) :
    (targets request state).any test.accepts = true ↔
      gsltDiamond (Presented.gslt request.plan request.bound request.expected) test.predicate request.root := by
  apply Iff.trans ?_ (gsltDiamond_spec
    (Presented.gslt request.plan request.bound request.expected) test.predicate request.root).symm
  constructor
  · intro found
    obtain ⟨target, member, holds⟩ := List.any_eq_true.mp found
    obtain ⟨answer, _, same⟩ := List.mem_map.mp member
    subst target
    exact ⟨answer.val.target, Presented.step_of_gslt _ _ _ (emitted_step request answer), holds⟩
  · rintro ⟨target, step, holds⟩
    obtain ⟨answer, member, related⟩ := covered_receipt certificate admitted covered step
    apply List.any_eq_true.mpr
    exact ⟨answer.val.target, List.mem_map.mpr ⟨answer, member, rfl⟩,
      (test.invariant _ _ related).trans holds⟩

theorem certified_outgoing {request : Request} {state : State request}
    (certificate : LocalCertificate request) (admitted : Admitted request)
    (covered : checkCertificate request state = true) (test : Test request) :
    (targets request state).all test.accepts = true ↔
      ∀ target, (Presented.gslt request.plan request.bound request.expected).Step request.root target →
        test.accepts target = true := by
  constructor
  · intro all target step
    obtain ⟨answer, member, related⟩ := covered_receipt certificate admitted covered step
    exact (test.invariant _ _ related).symm.trans
      (List.all_eq_true.mp all _ (List.mem_map.mpr ⟨answer, member, rfl⟩))
  · intro all
    apply List.all_eq_true.mpr
    intro target member
    obtain ⟨answer, _, same⟩ := List.mem_map.mp member
    subst target
    exact all _ (Presented.step_of_gslt _ _ _ (emitted_step request answer))

theorem possibility_complete {request : Request} {state : State request}
    (certificate : LocalCertificate request) (admitted : Admitted request)
    (covered : checkCertificate request state = true)
    (admission : sourceAdmission request = true) (test : Test request) :
    readout .possibility request state test = .decided true ↔
      gsltDiamond (Presented.gslt request.plan request.bound request.expected) test.predicate request.root := by
  rw [← certified_possibility certificate admitted covered test]
  unfold readout modalReadout
  simp only [admission, covered, Bool.true_and, if_true]
  cases (targets request state).any test.accepts <;> simp

/-- A negative answer requires checked coverage; it excludes responses in
the presented model, not merely in the list of discovered representatives. -/
theorem possibility_refuted {request : Request} {state : State request}
    (certificate : LocalCertificate request)
    (compiled : request.plan = GeneralExecutionAdmission.compile request.plan.snapshot request.plan.permissions)
    (test : Test request)
    (refuted : readout .possibility request state test = .decided false) :
    ¬ gsltDiamond (Presented.gslt request.plan request.bound request.expected) test.predicate request.root := by
  intro succeeds
  obtain ⟨target, step, holds⟩ := (gsltDiamond_spec _ _ _).mp succeeds
  obtain ⟨reached, equationStep, related⟩ :=
    Coherence.step_of_presented certificate.coherent step (.refl _)
  exact possibility_refutation_sound compiled test.equationInvariant refuted
    ⟨reached, equationStep, (test.invariant _ _ related).trans holds⟩

theorem outgoing_complete {request : Request} {state : State request}
    (certificate : LocalCertificate request) (admitted : Admitted request)
    (covered : checkCertificate request state = true)
    (admission : sourceAdmission request = true) (test : Test request) :
    readout .outgoingUniversal request state test = .decided true ↔
      ∀ target, (Presented.gslt request.plan request.bound request.expected).Step request.root target →
        test.accepts target = true := by
  rw [← certified_outgoing certificate admitted covered test]
  unfold readout modalReadout
  simp only [admission, covered, Bool.true_and, if_true]
  cases (targets request state).all test.accepts <;> simp

theorem unfinished_is_unknown {request : Request} {state : State request}
    (empty : state.answers = []) (unfinished : complete request state = false) (test : Test request) :
    readout .possibility request state test = .unknown :=
  unfinished_empty_is_unknown request state empty unfinished test.accepts

/-- The checked native question is the existing generated quotient diamond.
The quotient comparison comes from the framework rather than another modal
semantics for this profile. -/
theorem quotient_question {request : Request} (test : Test request) :
    descendPredicate (Presented.gslt request.plan request.bound request.expected)
        (semanticDiamond _ test.predicate) =
      Mettapedia.OSLF.Framework.GSLTQuotientCoherence.equationQuotientDiamond
        (Presented.gslt request.plan request.bound request.expected)
        (descendPredicate _ test.predicate) :=
  Mettapedia.OSLF.Framework.GSLTQuotientCoherence.descend_semanticDiamond _ _

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles
