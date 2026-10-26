import Mettapedia.Languages.HOLLight.InferenceAdapters
import Mettapedia.Languages.OpenTheory.TheoryReplay

/-!
# The ten HOL Light inference operations through shared STT

The source revision is `924faf0c3471a04174ffdeb8576ce7cabcb92d64`.
Terms entering this calculus retain their successful source type check.
The source's separate axiom and definition operations are not silently
included among its ten inference operations.

Each operation calls the existing shared kernel. Source-specific beta
admission, transitivity and substitution-list conventions are retained by
the checked adapters. No theorem name establishes derivability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight

open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open SourceSubstitution

inductive InferenceKind where
  | refl | trans | mkComb | abs | beta | assume | eqMp | deductAntisym | instType | inst
deriving DecidableEq, Repr

inductive InferenceRequest where
  | refl (term : CanonicalTerm)
  | trans (left right : Theorem)
  | mkComb (functionEquality argumentEquality : Theorem)
  | abs (binder : SourceVar) (input : Theorem)
  | beta (term : CheckedSourceTerm)
  | assume (term : CanonicalTerm)
  | eqMp (equality premise : Theorem)
  | deductAntisym (left right : Theorem)
  | instType (entries : List (Ty × Ty)) (input : Theorem)
  | inst (entries : List TermMaplet) (input : Theorem)

namespace InferenceRequest

def kind : InferenceRequest → InferenceKind
  | .refl _ => .refl
  | .trans _ _ => .trans
  | .mkComb _ _ => .mkComb
  | .abs _ _ => .abs
  | .beta _ => .beta
  | .assume _ => .assume
  | .eqMp _ _ => .eqMp
  | .deductAntisym _ _ => .deductAntisym
  | .instType _ _ => .instType
  | .inst _ _ => .inst

/-- Occurrences are ordered; repeated use of one theorem is retained. -/
def premises : InferenceRequest → List Theorem
  | .refl _ | .beta _ | .assume _ => []
  | .trans left right | .mkComb left right | .eqMp left right |
      .deductAntisym left right => [left, right]
  | .abs _ input | .instType _ input | .inst _ input => [input]

def check : InferenceRequest → Option Theorem
  | .refl term => checkRefl term
  | .trans left right => checkTrans left right
  | .mkComb left right => checkApp left right
  | .abs binder input => checkAbs binder input
  | .beta term => checkSourceBeta term
  | .assume term => checkAssume term
  | .eqMp equality premise => checkEqMp equality premise
  | .deductAntisym left right => checkDeductAntisym left right
  | .instType entries input =>
      checkTheoremSubstitution (typeOnlySubstitution entries) input
  | .inst entries input => do
      let substitution ← admitTermSubstitution entries
      checkTheoremSubstitution substitution input

/-- Structural rule conditions use the shared kernel's independently proved
relations; the source maplet admission guard is retained before substitution. -/
def Semantics : InferenceRequest → Theorem → Prop
  | .refl term, out => ReflSemantics term out
  | .trans left right, out => TransSemantics left right out
  | .mkComb left right, out => AppSemantics left right out
  | .abs binder input, out => AbsSemantics binder input out
  | .beta term, out => SourceBetaSemantics term out
  | .assume term, out => AssumeSemantics term out
  | .eqMp equality premise, out => EqMpSemantics equality premise out
  | .deductAntisym left right, out => DeductAntisymSemantics left right out
  | .instType entries input, out =>
      TheoremSubstitutionSemantics (typeOnlySubstitution entries) input out
  | .inst entries input, out =>
      ∃ substitution, admitTermSubstitution entries = some substitution ∧
        TheoremSubstitutionSemantics substitution input out

theorem check_eq_some_iff (request : InferenceRequest) (out : Theorem) :
    request.check = some out ↔ request.Semantics out := by
  cases request <;>
    simp [check, Semantics, checkRefl_eq_some_iff, checkTrans_eq_some_iff,
      checkApp_eq_some_iff, checkAbs_eq_some_iff, checkSourceBeta_eq_some_iff,
      checkAssume_eq_some_iff, checkEqMp_eq_some_iff, checkDeductAntisym_eq_some_iff,
      checkTheoremSubstitution_eq_some_iff, Option.bind_eq_some_iff]

theorem Semantics.deterministic {request : InferenceRequest} {out out' : Theorem}
    (first : request.Semantics out) (second : request.Semantics out') : out = out' :=
  Option.some.inj (((check_eq_some_iff request out).mpr first).symm.trans
    ((check_eq_some_iff request out').mpr second))

/-- Inference only propagates the axiom dependencies of its actual premises.
Definition-produced premises need not themselves be primitive inferences. -/
theorem Semantics.outputAxiomsAllowed (policy : AxiomPolicy)
    {request : InferenceRequest} {out : Theorem} (step : request.Semantics out)
    (allowed : ∀ premise ∈ request.premises, policy.AllowsTheorem premise) :
    policy.AllowsTheorem out := by
  cases request with
  | trans left right =>
      exact TransSemantics.outputAxiomsAllowed policy step
        (allowed left (by simp [InferenceRequest.premises]))
        (allowed right (by simp [InferenceRequest.premises]))
  | beta source =>
      obtain ⟨evidence⟩ := step.shared_step
      exact PrimitiveEvidence.outputAxiomsAllowed policy
        (request := .binding (.betaConv source.canonical)) True.intro evidence
  | refl term =>
      obtain ⟨evidence⟩ := (reflSemantics_iff_coreStep _ _).mp step
      exact CoreEvidence.outputAxiomsAllowed policy (request := .refl term) True.intro evidence
  | assume term =>
      obtain ⟨evidence⟩ := (assumeSemantics_iff_coreStep _ _).mp step
      exact CoreEvidence.outputAxiomsAllowed policy (request := .assume term) True.intro evidence
  | mkComb left right =>
      obtain ⟨evidence⟩ := (appSemantics_iff_coreStep _ _ _).mp step
      exact CoreEvidence.outputAxiomsAllowed policy (request := .app left right)
        ⟨allowed left (by simp [InferenceRequest.premises]),
          allowed right (by simp [InferenceRequest.premises])⟩ evidence
  | abs binder input =>
      obtain ⟨evidence⟩ := (absSemantics_iff_bindingStep _ _ _).mp step
      exact BindingEvidence.outputAxiomsAllowed policy (request := .abs binder input)
        (allowed input (by simp [InferenceRequest.premises])) evidence
  | eqMp equality premise =>
      obtain ⟨evidence⟩ := (eqMpSemantics_iff_coreStep _ _ _).mp step
      exact CoreEvidence.outputAxiomsAllowed policy (request := .eqMp equality premise)
        ⟨allowed equality (by simp [InferenceRequest.premises]),
          allowed premise (by simp [InferenceRequest.premises])⟩ evidence
  | deductAntisym left right =>
      obtain ⟨evidence⟩ := (deductAntisymSemantics_iff_coreStep _ _ _).mp step
      exact CoreEvidence.outputAxiomsAllowed policy (request := .deductAntisym left right)
        ⟨allowed left (by simp [InferenceRequest.premises]),
          allowed right (by simp [InferenceRequest.premises])⟩ evidence
  | instType entries input =>
      exact policy.allows_of_axioms_eq out input step.1
        (allowed input (by simp [InferenceRequest.premises]))
  | inst entries input =>
      obtain ⟨_, _, substitutionStep⟩ := step
      exact policy.allows_of_axioms_eq out input substitutionStep.1
        (allowed input (by simp [InferenceRequest.premises]))

private theorem shared_inference (policy : AxiomPolicy) (request : PrimitiveRequest)
    (out : Theorem) (allowed : request.InputAxiomsAllowed policy)
    (step : PrimitiveStep request out)
    (premises : ∀ premise ∈ request.premises, Derives (PolicyPrimitiveRule policy) premise) :
    Derives (PolicyPrimitiveRule policy) out :=
  Derives.node request.premises out ⟨request, rfl, allowed, step⟩ premises

private theorem shared_core {request : CoreRequest} {out : Theorem}
    (step : CoreStep request out) : PrimitiveStep (.core request) out := by
  obtain ⟨evidence⟩ := step
  exact ⟨.core evidence⟩

private theorem shared_binding {request : BindingRequest} {out : Theorem}
    (step : BindingStep request out) : PrimitiveStep (.binding request) out := by
  obtain ⟨evidence⟩ := step
  exact ⟨.binding evidence⟩

/-- Every admitted source inference expands to an actual shared-kernel
derivation, with the same hypotheses and axiom-dependency set. -/
theorem Semantics.shared_derivation (policy : AxiomPolicy)
    {request : InferenceRequest} {out : Theorem} (step : request.Semantics out)
    (premises : ∀ premise ∈ request.premises, Derives (PolicyPrimitiveRule policy) premise) :
    Derives (PolicyPrimitiveRule policy) out := by
  have allowed : ∀ premise ∈ request.premises, policy.AllowsTheorem premise :=
    fun premise member => derives_only_authorized_axioms policy (premises premise member)
  cases request with
  | trans left right =>
      exact TransSemantics.shared_derivation policy step
        (premises left (by simp [InferenceRequest.premises]))
        (premises right (by simp [InferenceRequest.premises]))
  | beta term => exact SourceBetaSemantics.derivation_preservation policy step
  | refl term =>
      exact shared_inference policy (.core (.refl term)) out True.intro
        (shared_core ((reflSemantics_iff_coreStep _ _).mp step)) premises
  | assume term =>
      exact shared_inference policy (.core (.assume term)) out True.intro
        (shared_core ((assumeSemantics_iff_coreStep _ _).mp step)) premises
  | mkComb left right =>
      exact shared_inference policy (.core (.app left right)) out
        ⟨allowed left (by simp [InferenceRequest.premises]),
          allowed right (by simp [InferenceRequest.premises])⟩
        (shared_core ((appSemantics_iff_coreStep _ _ _).mp step)) premises
  | abs binder input =>
      exact shared_inference policy (.binding (.abs binder input)) out
        (allowed input (by simp [InferenceRequest.premises]))
        (shared_binding ((absSemantics_iff_bindingStep _ _ _).mp step)) premises
  | eqMp equality premise =>
      exact shared_inference policy (.core (.eqMp equality premise)) out
        ⟨allowed equality (by simp [InferenceRequest.premises]),
          allowed premise (by simp [InferenceRequest.premises])⟩
        (shared_core ((eqMpSemantics_iff_coreStep _ _ _).mp step)) premises
  | deductAntisym left right =>
      exact shared_inference policy (.core (.deductAntisym left right)) out
        ⟨allowed left (by simp [InferenceRequest.premises]),
          allowed right (by simp [InferenceRequest.premises])⟩
        (shared_core ((deductAntisymSemantics_iff_coreStep _ _ _).mp step)) premises
  | instType entries input =>
      exact shared_inference policy (.subst (typeOnlySubstitution entries) input) out
        (allowed input (by simp [InferenceRequest.premises])) ⟨.subst step⟩ premises
  | inst entries input =>
      obtain ⟨substitution, _, substitutionStep⟩ := step
      exact shared_inference policy (.subst substitution input) out
        (allowed input (by simp [InferenceRequest.premises])) ⟨.subst substitutionStep⟩ premises

end InferenceRequest

/-- The source's extra axiom operation always introduces a hypothesis-free
sequent, authorized by the separately selected object-theory policy. -/
def Rule (policy : AxiomPolicy) (premises : List Theorem) (out : Theorem) : Prop :=
  (∃ request : InferenceRequest, request.premises = premises ∧ request.Semantics out) ∨
  (∃ sequent : Sequent, premises = [] ∧ sequent.hyp = ∅ ∧ policy sequent ∧
    AxiomSemantics sequent out)

/-- General derivation preservation, for every finite source proof and every
explicit axiom policy. Definition extensions are a separate signature step. -/
theorem derives_shared (policy : AxiomPolicy) {out : Theorem}
    (derivation : Derives (Rule policy) out) : Derives (PolicyPrimitiveRule policy) out := by
  apply Derives.least (Derives (PolicyPrimitiveRule policy)) _ derivation
  intro premises out step children
  rcases step with ⟨request, rfl, semantics⟩ | ⟨sequent, rfl, _, admitted, semantics⟩
  · exact InferenceRequest.Semantics.shared_derivation policy semantics children
  · exact derives_of_nullary_check policy (.core (.axiom sequent)) out rfl admitted
      ((checkAxiom_eq_some_iff _ _).mpr semantics)

/-- A finite replay witness is the actual inference request or an explicitly
authorized source axiom. Its printed theorem label has no logical role. -/
inductive RuleRequest where
  | inference (request : InferenceRequest)
  | axiom (sequent : Sequent)

namespace RuleRequest

def premises : RuleRequest → List Theorem
  | .inference request => request.premises
  | .axiom _ => []

def Semantics (policy : AxiomPolicy) : RuleRequest → Theorem → Prop
  | .inference request, out => request.Semantics out
  | .axiom sequent, out => sequent.hyp = ∅ ∧ policy sequent ∧ AxiomSemantics sequent out

def check (policy : AxiomPolicy) [DecidablePred policy] : RuleRequest → Option Theorem
  | .inference request => request.check
  | .axiom sequent =>
      if sequent.hyp = ∅ ∧ policy sequent then checkAxiom sequent else none

theorem check_eq_some_iff (policy : AxiomPolicy) [DecidablePred policy]
    (request : RuleRequest) (out : Theorem) :
    request.check policy = some out ↔ request.Semantics policy out := by
  cases request with
  | inference request => exact InferenceRequest.check_eq_some_iff request out
  | «axiom» sequent =>
      by_cases allowed : sequent.hyp = ∅ ∧ policy sequent
      · simp only [check, if_pos allowed, Semantics, checkAxiom_eq_some_iff]
        exact ⟨fun semantics => ⟨allowed.1, allowed.2, semantics⟩,
          fun semantics => semantics.2.2⟩
      · simp only [check, if_neg allowed, Semantics]
        constructor
        · intro impossible
          cases impossible
        · intro ⟨empty, authorized, _⟩
          exact False.elim (allowed ⟨empty, authorized⟩)

def outputSameB (policy : AxiomPolicy) [DecidablePred policy]
    (request : RuleRequest) (out : Theorem) : Bool :=
  match request.check policy with
  | none => false
  | some checked => checked.structuralSame out

theorem outputSameB_eq_true_iff (policy : AxiomPolicy) [DecidablePred policy]
    (request : RuleRequest) (out : Theorem) :
    request.outputSameB policy out = true ↔ request.Semantics policy out := by
  cases checked : request.check policy with
  | none =>
      constructor
      · simp [outputSameB, checked]
      · intro semantics
        have accepted := (check_eq_some_iff policy request out).mpr semantics
        rw [checked] at accepted
        contradiction
  | some candidate =>
      constructor
      · intro same
        have equal : candidate = out := by simpa [outputSameB, checked] using same
        exact (check_eq_some_iff policy request out).mp (checked.trans (congrArg some equal))
      · intro semantics
        have accepted := (check_eq_some_iff policy request out).mpr semantics
        have equal := Option.some.inj (checked.symm.trans accepted)
        simp [outputSameB, checked, equal]

def isInstance (policy : AxiomPolicy) [DecidablePred policy]
    (request : RuleRequest) (input : List Theorem) (out : Theorem) : Bool :=
  theoremListStructuralSame request.premises input && request.outputSameB policy out

theorem isInstance_eq_true_iff (policy : AxiomPolicy) [DecidablePred policy]
    (request : RuleRequest) (input : List Theorem) (out : Theorem) :
    request.isInstance policy input out = true ↔
      request.premises = input ∧ request.Semantics policy out := by
  simp only [isInstance, Bool.and_eq_true, theoremListStructuralSame_eq_true_iff,
    outputSameB_eq_true_iff]

def requestedAxiom : RuleRequest → Option Sequent
  | .inference _ => none
  | .axiom sequent => some sequent

theorem check_policy_congr (first second : AxiomPolicy) [DecidablePred first] [DecidablePred second]
    (request : RuleRequest)
    (agree : ∀ sequent, request.requestedAxiom = some sequent → (first sequent ↔ second sequent)) :
    request.check first = request.check second := by
  cases request with
  | inference request => rfl
  | «axiom» sequent => simp only [check, agree sequent rfl]

end RuleRequest

/-- Exact checking and admission for all finite source-rule derivations,
using the existing generic certificate interface. -/
def ruleWitness (policy : AxiomPolicy) [DecidablePred policy] : RuleWitness (Rule policy) where
  W := RuleRequest
  isInstance := RuleRequest.isInstance policy
  sound := by
    intro request input out accepted
    obtain ⟨premises, semantics⟩ :=
      (RuleRequest.isInstance_eq_true_iff policy request input out).mp accepted
    cases request with
    | inference request => exact Or.inl ⟨request, premises, semantics⟩
    | «axiom» sequent => exact Or.inr ⟨sequent, premises.symm, semantics⟩
  complete := by
    intro input out step
    rcases step with ⟨request, premises, semantics⟩ |
      ⟨sequent, premises, empty, authorized, semantics⟩
    · exact ⟨.inference request,
        (RuleRequest.isInstance_eq_true_iff policy _ input out).mpr ⟨premises, semantics⟩⟩
    · exact ⟨.axiom sequent,
        (RuleRequest.isInstance_eq_true_iff policy _ input out).mpr
          ⟨premises.symm, empty, authorized, semantics⟩⟩

def inferenceKinds : List InferenceKind :=
  [.refl, .trans, .mkComb, .abs, .beta, .assume, .eqMp, .deductAntisym, .instType, .inst]

theorem inferenceKinds_complete (kind : InferenceKind) : kind ∈ inferenceKinds := by
  cases kind <;> simp [inferenceKinds]

theorem inferenceKinds_nodup : inferenceKinds.Nodup := by decide

theorem inferenceKinds_length : inferenceKinds.length = 10 := rfl

end Mettapedia.Languages.HOLLight
