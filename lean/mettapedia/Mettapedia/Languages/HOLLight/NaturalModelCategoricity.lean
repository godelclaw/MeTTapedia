import Mettapedia.Languages.HOLLight.ReferenceBooleanSemantics
import Mettapedia.Logic.Metaphysics.DedekindCategoricity

/-!
# Categoricity of natural operations interpreted from source formulas

Zero and successor are closed terms in the receiving model. In particular,
zero may retain the source's `NUMERAL _0` wrapper. The formulas use the actual
registered Boolean symbols. Their validity in a full-domain model yields a
Peano structure and a zero/successor-preserving equivalence with `Nat`.
No choice of a particular successor function is built into the interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.NaturalModelCategoricity

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReferenceBooleanSemantics ModelInterpretation

universe w

/-- Source operations, without natural-number laws. -/
structure Signature where
  number : HOL.Ty AtomicTy
  zero : HOL.ClosedTerm Symbol number
  successor : HOL.ClosedTerm Symbol (number.arr number)

namespace Signature

variable (signature : Signature)

def successorSeparation : HOL.ClosedFormula Symbol :=
  universal (negation (.eq
    (.app (HOL.weakenCtx _ signature.successor) (.var .vz))
    (HOL.weakenCtx _ signature.zero)))

def successorInjective : HOL.ClosedFormula Symbol :=
  universal (universal (.eq
    (.eq (.app (HOL.weakenCtx _ signature.successor) (.var (.vs .vz)))
      (.app (HOL.weakenCtx _ signature.successor) (.var .vz)))
    (.eq (.var (.vs .vz)) (.var .vz))))

def induction : HOL.ClosedFormula Symbol :=
  universal (type := signature.number.arr .prop)
    (implication
      (conjunction (.app (.var .vz) (HOL.weakenCtx _ signature.zero))
        (universal (type := signature.number)
          (implication (.app (.var (.vs .vz)) (.var .vz))
            (.app (.var (.vs .vz))
              (.app (HOL.weakenCtx _ signature.successor) (.var .vz))))))
      (universal (type := signature.number) (.app (.var (.vs .vz)) (.var .vz))))

abbrev Carrier (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOL.Ty.denote.{0,w+1} model.Carrier signature.number

def origin (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) : signature.Carrier model :=
  model.denote signature.zero (fun index => nomatch index)

def next (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) : signature.Carrier model → signature.Carrier model :=
  model.denote signature.successor (fun index => nomatch index)

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) (meanings : Meanings model)

theorem denote_zero (valuation : model.Valuation []) :
    model.denote signature.zero valuation = signature.origin model := by
  apply congrArg (model.denote signature.zero)
  funext type index
  exact nomatch index

theorem denote_successor (valuation : model.Valuation []) :
    model.denote signature.successor valuation = signature.next model := by
  apply congrArg (model.denote signature.successor)
  funext type index
  exact nomatch index

include full meanings

theorem successorSeparation_meaning : model.models signature.successorSeparation ↔
    ∀ value, signature.next model value ≠ signature.origin model := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [successorSeparation, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, denote_negation model meanings,
    HOL.HenkinModel.denote_weakenCtx, HOL.HenkinModel.denote, HOL.PreModel.denote,
    HOL.PreModel.extend, signature.denote_zero model, signature.denote_successor model]
  simp only [model.eqv_iff_eq_of_fullDomains full, admitted, forall_true_left]

theorem successorInjective_meaning : model.models signature.successorInjective ↔
    Function.Injective (signature.next model) := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [successorInjective, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, HOL.HenkinModel.denote_weakenCtx,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend,
    signature.denote_successor model]
  simp only [model.eqv_iff_eq_of_fullDomains full, admitted, forall_true_left]
  constructor
  · exact fun valid first second same => (valid first second).mp same
  · exact fun injective first second => ⟨fun same => injective same, congrArg (signature.next model)⟩

theorem induction_meaning : model.models signature.induction ↔
    ∀ predicate : signature.Carrier model → Prop, predicate (signature.origin model) →
      (∀ value, predicate value → predicate (signature.next model value)) →
      ∀ value, predicate value := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [induction, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, denote_implication model meanings,
    denote_conjunction model meanings, HOL.HenkinModel.denote_weakenCtx,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend,
    signature.denote_zero model, signature.denote_successor model]
  simp only [admitted, forall_true_left]
  constructor
  · intro valid predicate atZero atNext
    exact valid (fun value => ULift.up (predicate value)) ⟨atZero, atNext⟩
  · intro principle predicate premises
    exact principle (fun value => (predicate value).down) premises.1 premises.2

/-- All-subsets induction and the interpreted successor facts earn the
algebraic Peano interface used by Dedekind categoricity. -/
def peanoStructure
    (separation : model.models signature.successorSeparation)
    (injectivity : model.models signature.successorInjective)
    (induction : model.models signature.induction) : Metaphysics.PeanoStructure.{w+1} where
  carrier := signature.Carrier model
  zero := signature.origin model
  succ := signature.next model
  succ_inj := (signature.successorInjective_meaning model full meanings).mp injectivity
  succ_ne_zero := (signature.successorSeparation_meaning model full meanings).mp separation
  induction := by
    intro predicate atZero atNext
    apply Set.eq_univ_of_forall
    exact (signature.induction_meaning model full meanings).mp induction predicate atZero atNext

/-- The source carrier is identified with `Nat` through its interpreted
operations, not through a choice of the source's Hilbert-choice witness. -/
noncomputable def naturalEquivalence
    (separation : model.models signature.successorSeparation)
    (injectivity : model.models signature.successorInjective)
    (induction : model.models signature.induction) : Nat ≃ signature.Carrier model :=
  Equiv.ofBijective (signature.peanoStructure model full meanings separation injectivity induction).fromNat
    (signature.peanoStructure model full meanings separation injectivity induction).fromNat_bijective

theorem naturalEquivalence_zero
    (separation : model.models signature.successorSeparation)
    (injectivity : model.models signature.successorInjective)
    (induction : model.models signature.induction) :
    signature.naturalEquivalence model full meanings separation injectivity induction 0 =
      signature.origin model := rfl

theorem naturalEquivalence_succ
    (separation : model.models signature.successorSeparation)
    (injectivity : model.models signature.successorInjective)
    (induction : model.models signature.induction) (n : Nat) :
    signature.naturalEquivalence model full meanings separation injectivity induction (n+1) =
      signature.next model (signature.naturalEquivalence model full meanings separation injectivity induction n) := rfl

end Signature

/-- Three retained source facts, with exact formula readings and no hypotheses.
The fields carry cache membership and translation evidence, not semantic laws. -/
structure CachedFacts (signature : Signature) (state : ProofExecution.Registered.State) where
  separation : Theorem
  injectivity : Theorem
  induction : Theorem
  separation_known : separation ∈ state.cache
  injectivity_known : injectivity ∈ state.cache
  induction_known : induction ∈ state.cache
  separation_closed : separation.sequent.hyp = ∅
  injectivity_closed : injectivity.sequent.hyp = ∅
  induction_closed : induction.sequent.hyp = ∅
  separation_read : Translates [] separation.sequent.concl.term .prop signature.successorSeparation
  injectivity_read : Translates [] injectivity.sequent.concl.term .prop signature.successorInjective
  induction_read : Translates [] induction.sequent.concl.term .prop signature.induction

open SourceProfileModels TypeFamilySemantics

/-- Accepted commands and exact readings of the cached Peano facts determine
the receiving natural carrier up to the stated equivalence. -/
noncomputable def replayNaturalEquivalence (signature : Signature)
    (commands : List ProofExecution.Registered.Command) (after : ProofExecution.Registered.State)
    (accepted : ProofExecution.Registered.replayFrom policy
      (ProofExecution.Registered.empty SourceProfile.primitiveContext) commands = some after)
    (facts : CachedFacts signature after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    Nat ≃ signature.Carrier ((sourceReplayFrame commands after accepted).frame.model other assignment) := by
  let frame := (sourceReplayFrame commands after accepted).frame
  have closed {fact : Theorem} (known : fact ∈ after.cache) {formula : HOL.ClosedFormula Symbol}
      (translated : Translates [] fact.sequent.concl.term .prop formula)
      (noHypotheses : fact.sequent.hyp = ∅) : (frame.model other assignment).models formula := by
    apply frame.cached_models_of_translation other assignment known translated
    intro hypothesis member
    simp [noHypotheses, translatedHypotheses] at member
  exact signature.naturalEquivalence (frame.model other assignment)
    (frame.model_fullDomains other assignment) (replay_meanings commands after accepted other assignment)
    (closed facts.separation_known facts.separation_read facts.separation_closed)
    (closed facts.injectivity_known facts.injectivity_read facts.injectivity_closed)
    (closed facts.induction_known facts.induction_read facts.induction_closed)

#print axioms Signature.peanoStructure
#print axioms Signature.naturalEquivalence
#print axioms replayNaturalEquivalence

end Mettapedia.Languages.HOLLight.NaturalModelCategoricity
