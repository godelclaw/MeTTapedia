import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceCertificateSound
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Exact outgoing modal readouts of checked occurrence frontiers

Finite physical receipts cover outgoing successor equation classes. Folding
an equation-invariant test therefore gives outgoing existential and universal
answers. Exhaustive absence requires the retained certificate; it is distinct
from the incoming adjoint OSLF box.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralOccurrenceSemantics

def targets (request : Request) (state : State request) : List Pattern :=
  state.answers.map fun answer => answer.val.target

def targetClasses (request : Request) (state : State request) :
    List (Quotient (Relation.EqvGen.setoid (Equation request.plan request.bound request.expected))) :=
  (targets request state).map (Quotient.mk _)

theorem certified_successor_classes {request : Request} {state : State request}
    (admitted : Admitted request) (checked : checkCertificate request state = true) (target : Pattern) :
    (∃ answer ∈ state.answers, Relation.EqvGen (Equation request.plan request.bound request.expected)
      answer.val.target target) ↔ (gslt request.plan request.bound request.expected).Step request.root target := by
  constructor
  · rintro ⟨answer, _, after⟩
    exact ⟨answer.val.representative, answer.val.firing, answer.property.1.equivalent,
      answer.property.2, after⟩
  · rintro ⟨source, receipt, before, valid, after⟩
    obtain ⟨answer, member, _, firing⟩ := certified_physical_occurrence admitted checked source before receipt valid
    refine ⟨answer, member, ?_⟩
    simpa only [Receipt.target, firing] using after

theorem certified_targetClasses {request : Request} {state : State request}
    (admitted : Admitted request) (checked : checkCertificate request state = true) (target : Pattern) :
    Quotient.mk (Relation.EqvGen.setoid (Equation request.plan request.bound request.expected)) target ∈
      targetClasses request state ↔ (gslt request.plan request.bound request.expected).Step request.root target := by
  rw [← certified_successor_classes admitted checked target]
  simp only [targetClasses, targets, List.mem_map]
  constructor
  · rintro ⟨value, ⟨answer, member, same⟩, equal⟩
    subst value
    exact ⟨answer, member, Quotient.exact equal⟩
  · rintro ⟨answer, member, related⟩
    exact ⟨answer.val.target, ⟨answer, member, rfl⟩, Quotient.sound related⟩

theorem certified_outgoing_diamond {request : Request} {state : State request}
    (admitted : Admitted request) (checked : checkCertificate request state = true)
    (test : Pattern → Bool)
    (invariant : ∀ first second, Relation.EqvGen (Equation request.plan request.bound request.expected)
      first second → test first = test second) :
    (targets request state).any test = true ↔
      ∃ target, (gslt request.plan request.bound request.expected).Step request.root target ∧ test target = true := by
  simp only [List.any_eq_true, targets, List.mem_map]
  constructor
  · rintro ⟨target, ⟨answer, member, same⟩, succeeds⟩
    subst target
    exact ⟨answer.val.target, emitted_step request answer, succeeds⟩
  · rintro ⟨target, step, succeeds⟩
    obtain ⟨answer, member, related⟩ := (certified_successor_classes admitted checked target).mpr step
    exact ⟨answer.val.target, ⟨answer, member, rfl⟩, (invariant _ _ related).trans succeeds⟩

theorem certified_gslt_diamond {request : Request} {state : State request}
    (admitted : Admitted request) (checked : checkCertificate request state = true)
    (test : Pattern → Bool)
    (invariant : ∀ first second, Relation.EqvGen (Equation request.plan request.bound request.expected)
      first second → test first = test second) :
    (targets request state).any test = true ↔
      Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
        (gslt request.plan request.bound request.expected) (fun target => test target = true) request.root :=
  (certified_outgoing_diamond admitted checked test invariant).trans
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond_spec _ _ _).symm

theorem certified_outgoing_universal {request : Request} {state : State request}
    (admitted : Admitted request) (checked : checkCertificate request state = true)
    (test : Pattern → Bool)
    (invariant : ∀ first second, Relation.EqvGen (Equation request.plan request.bound request.expected)
      first second → test first = test second) :
    (targets request state).all test = true ↔
      ∀ target, (gslt request.plan request.bound request.expected).Step request.root target → test target = true := by
  simp only [List.all_eq_true]
  constructor
  · intro universal target step
    obtain ⟨answer, member, related⟩ := (certified_successor_classes admitted checked target).mpr step
    exact (invariant _ _ related).symm.trans
      (universal answer.val.target (List.mem_map.mpr ⟨answer, member, rfl⟩))
  · intro universal target member
    obtain ⟨answer, _, same⟩ := List.mem_map.mp member
    subst target
    exact universal _ (emitted_step request answer)

theorem certified_absence {request : Request} {state : State request}
    (admitted : Admitted request) (checked : checkCertificate request state = true) :
    state.answers = [] ↔ ¬ ∃ target,
      (gslt request.plan request.bound request.expected).Step request.root target := by
  constructor
  · intro empty ⟨target, step⟩
    obtain ⟨answer, member, _⟩ := (certified_successor_classes admitted checked target).mpr step
    simp only [empty, List.not_mem_nil] at member
  · intro absent
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro answer _
    exact absent ⟨answer.val.target, emitted_step request answer⟩

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
