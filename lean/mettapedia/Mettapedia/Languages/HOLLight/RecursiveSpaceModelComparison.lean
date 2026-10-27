import Mettapedia.Languages.HOLLight.NaturalModelCategoricity
import Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics

/-!
# Recursive-space model comparison from interpreted source facts

The formulas retain the registered Boolean symbols and the source ordering of
constructor arguments. Their interpretations supply separation, injectivity
and full predicate induction. A natural-carrier equivalence transports both
constructor tags and child indices. The resulting algebra is isomorphic to the
existing relational recursive space, preserving bottom and constructors.

The source constructor-only recursion statement supplies no bottom equation.
It is not used to claim uniqueness of a recursion with an unspecified bottom.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RecursiveSpaceModelComparison

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReferenceBooleanSemantics ModelInterpretation

universe w

/-- Typed source operations, without algebraic or semantic laws. -/
structure Signature where
  number : HOL.Ty AtomicTy
  payload : HOL.Ty AtomicTy
  space : HOL.Ty AtomicTy
  bottom : HOL.ClosedTerm Symbol space
  construct : HOL.ClosedTerm Symbol (number.arr (payload.arr ((number.arr space).arr space)))

namespace Signature

variable (signature : Signature)

def applyConstructor {context : HOL.Ctx AtomicTy}
    (tag : HOL.Term Symbol context signature.number)
    (payload : HOL.Term Symbol context signature.payload)
    (children : HOL.Term Symbol context (signature.number.arr signature.space)) :
    HOL.Term Symbol context signature.space :=
  .app (.app (.app (HOL.weakenCtx _ signature.construct) tag) payload) children

def constructorSeparation : HOL.ClosedFormula Symbol :=
  universal (type := signature.number) (universal (type := signature.payload)
    (universal (type := signature.number.arr signature.space)
      (negation (.eq
        (signature.applyConstructor (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
        (HOL.weakenCtx _ signature.bottom)))))

def constructorInjective : HOL.ClosedFormula Symbol :=
  let context := [signature.number.arr signature.space, signature.payload, signature.number,
    signature.number.arr signature.space, signature.payload, signature.number]
  let leftTag : HOL.Term Symbol context signature.number := .var (.vs (.vs (.vs (.vs (.vs .vz)))))
  let leftPayload : HOL.Term Symbol context signature.payload := .var (.vs (.vs (.vs (.vs .vz))))
  let leftChildren : HOL.Term Symbol context (signature.number.arr signature.space) := .var (.vs (.vs (.vs .vz)))
  let rightTag : HOL.Term Symbol context signature.number := .var (.vs (.vs .vz))
  let rightPayload : HOL.Term Symbol context signature.payload := .var (.vs .vz)
  let rightChildren : HOL.Term Symbol context (signature.number.arr signature.space) := .var .vz
  let body := HOL.Term.eq
    (.eq (signature.applyConstructor leftTag leftPayload leftChildren)
      (signature.applyConstructor rightTag rightPayload rightChildren))
    (conjunction (.eq leftTag rightTag)
      (conjunction (.eq leftPayload rightPayload) (.eq leftChildren rightChildren)))
  universal (universal (universal (universal (universal (universal body)))))

def induction : HOL.ClosedFormula Symbol :=
  universal (type := signature.space.arr .prop)
    (implication
      (conjunction (.app (.var .vz) (HOL.weakenCtx _ signature.bottom))
        (universal (type := signature.number) (universal (type := signature.payload)
          (universal (type := signature.number.arr signature.space)
            (implication
              (universal (type := signature.number)
                (.app (.var (.vs (.vs (.vs (.vs .vz)))))
                  (.app (.var (.vs .vz)) (.var .vz))))
              (.app (.var (.vs (.vs (.vs .vz))))
                (signature.applyConstructor (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))))))
      (universal (type := signature.space) (.app (.var (.vs .vz)) (.var .vz))))

abbrev Numbers (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOL.Ty.denote.{0,w+1} model.Carrier signature.number

abbrev Payload (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOL.Ty.denote.{0,w+1} model.Carrier signature.payload

abbrev Carrier (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOL.Ty.denote.{0,w+1} model.Carrier signature.space

def origin (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) : signature.Carrier model :=
  model.denote signature.bottom (fun index => nomatch index)

def constructor (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    signature.Numbers model → signature.Payload model →
      (signature.Numbers model → signature.Carrier model) → signature.Carrier model :=
  model.denote signature.construct (fun index => nomatch index)

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)

theorem denote_bottom (valuation : model.Valuation []) :
    model.denote signature.bottom valuation = signature.origin model := by
  apply congrArg (model.denote signature.bottom)
  funext type index
  exact nomatch index

theorem denote_constructor (valuation : model.Valuation []) :
    model.denote signature.construct valuation = signature.constructor model := by
  apply congrArg (model.denote signature.construct)
  funext type index
  exact nomatch index

variable (full : model.FullDomains) (meanings : Meanings model)
include full meanings

theorem constructorSeparation_meaning : model.models signature.constructorSeparation ↔
    ∀ tag payload children, signature.constructor model tag payload children ≠ signature.origin model := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [constructorSeparation, applyConstructor, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, denote_negation model meanings,
    HOL.HenkinModel.denote_weakenCtx, HOL.HenkinModel.denote, HOL.PreModel.denote,
    HOL.PreModel.extend, signature.denote_bottom model, signature.denote_constructor model]
  simp only [model.eqv_iff_eq_of_fullDomains full, admitted, forall_true_left]
  rfl

theorem constructorInjective_meaning : model.models signature.constructorInjective ↔
    ∀ tag payload children tag' payload' children',
      signature.constructor model tag payload children = signature.constructor model tag' payload' children' ↔
        tag = tag' ∧ payload = payload' ∧ children = children' := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [constructorInjective, applyConstructor, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, denote_conjunction model meanings,
    HOL.HenkinModel.denote_weakenCtx, HOL.HenkinModel.denote, HOL.PreModel.denote,
    HOL.PreModel.extend, signature.denote_constructor model]
  simp only [model.eqv_iff_eq_of_fullDomains full, admitted, forall_true_left]
  rfl

theorem induction_meaning : model.models signature.induction ↔
    ∀ property : signature.Carrier model → Prop, property (signature.origin model) →
      (∀ tag payload children, (∀ n, property (children n)) →
        property (signature.constructor model tag payload children)) →
      ∀ value, property value := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [induction, applyConstructor, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, denote_implication model meanings,
    denote_conjunction model meanings, HOL.HenkinModel.denote_weakenCtx,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend,
    signature.denote_bottom model, signature.denote_constructor model]
  simp only [admitted, forall_true_left]
  constructor
  · intro valid property atBottom atConstructor
    exact valid (fun value => ULift.up (property value)) ⟨atBottom,atConstructor⟩
  · intro principle property premises
    exact principle (fun value => (property value).down) premises.1 premises.2

/-- Both uses of the natural carrier are transported: tags covariantly and
the indexing of child functions contravariantly. -/
def algebra (numbers : Nat ≃ signature.Numbers model)
    (separation : model.models signature.constructorSeparation)
    (injectivity : model.models signature.constructorInjective)
    (induction : model.models signature.induction) :
    Mettapedia.TypeTheory.RecursiveSpace.Model (signature.Payload model) (signature.Carrier model) where
  bottom := signature.origin model
  construct := fun tag payload children =>
    signature.constructor model (numbers tag) payload (fun n => children (numbers.symm n))
  construct_ne_bottom := fun tag payload children =>
    (signature.constructorSeparation_meaning model full meanings).mp separation
      (numbers tag) payload (fun n => children (numbers.symm n))
  construct_injective := by
    intro tag payload children tag' payload' children'
    constructor
    · intro same
      obtain ⟨tags,payloads,recursive⟩ :=
        (signature.constructorInjective_meaning model full meanings).mp injectivity _ _ _ _ _ _ |>.mp same
      refine ⟨numbers.injective tags,payloads,?_⟩
      funext n
      simpa only [Equiv.symm_apply_apply] using congrFun recursive (numbers n)
    · rintro ⟨rfl,rfl,rfl⟩
      rfl
  induction := by
    intro property atBottom atConstructor value
    apply (signature.induction_meaning model full meanings).mp induction property atBottom ?_ value
    intro tag payload children hypotheses
    have result := atConstructor (numbers.symm tag) payload (fun n => children (numbers n))
      (fun n => hypotheses (numbers n))
    simpa only [Equiv.apply_symm_apply] using result

noncomputable def relationalEquivalence (numbers : Nat ≃ signature.Numbers model)
    (separation : model.models signature.constructorSeparation)
    (injectivity : model.models signature.constructorInjective)
    (induction : model.models signature.induction)
    [Nonempty (signature.Payload model)] (filler : RecursiveSpaceSemantics.Relation (signature.Payload model)) :
    signature.Carrier model ≃ RecursiveSpaceSemantics.Carrier filler :=
  (Mettapedia.TypeTheory.RecursiveSpace.equivalence
    (signature.algebra model full meanings numbers separation injectivity induction)).symm.trans
      (RecursiveSpaceSemantics.representation filler)

theorem relationalEquivalence_bottom (numbers : Nat ≃ signature.Numbers model)
    (separation : model.models signature.constructorSeparation)
    (injectivity : model.models signature.constructorInjective)
    (induction : model.models signature.induction)
    [Nonempty (signature.Payload model)] (filler : RecursiveSpaceSemantics.Relation (signature.Payload model)) :
    signature.relationalEquivalence model full meanings numbers separation injectivity induction filler
      (signature.origin model) = RecursiveSpaceSemantics.bottom filler := by
  change RecursiveSpaceSemantics.representation filler
    ((Mettapedia.TypeTheory.RecursiveSpace.equivalence
      (signature.algebra model full meanings numbers separation injectivity induction)).symm
        (signature.algebra model full meanings numbers separation injectivity induction).bottom) = _
  rw [Mettapedia.TypeTheory.RecursiveSpace.inverse_bottom]
  rfl

theorem relationalEquivalence_constructor (numbers : Nat ≃ signature.Numbers model)
    (separation : model.models signature.constructorSeparation)
    (injectivity : model.models signature.constructorInjective)
    (induction : model.models signature.induction)
    [Nonempty (signature.Payload model)] (filler : RecursiveSpaceSemantics.Relation (signature.Payload model))
    (tag : signature.Numbers model) (payload : signature.Payload model)
    (children : signature.Numbers model → signature.Carrier model) :
    signature.relationalEquivalence model full meanings numbers separation injectivity induction filler
      (signature.constructor model tag payload children) =
      RecursiveSpaceSemantics.construct filler (numbers.symm tag) payload
        (fun n => signature.relationalEquivalence model full meanings numbers separation injectivity induction filler
          (children (numbers n))) := by
  let algebra := signature.algebra model full meanings numbers separation injectivity induction
  have same : signature.constructor model tag payload children =
      algebra.construct (numbers.symm tag) payload (fun n => children (numbers n)) := by
    simp only [algebra, Signature.algebra, Equiv.apply_symm_apply]
  rw [same]
  change RecursiveSpaceSemantics.representation filler
    ((Mettapedia.TypeTheory.RecursiveSpace.equivalence algebra).symm
      (algebra.construct (numbers.symm tag) payload (fun n => children (numbers n)))) = _
  rw [Mettapedia.TypeTheory.RecursiveSpace.inverse_construct]
  rfl

end Signature

/-- Exact source-fact readings required by the recursive-space interpretation. -/
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
  separation_read : Translates [] separation.sequent.concl.term .prop signature.constructorSeparation
  injectivity_read : Translates [] injectivity.sequent.concl.term .prop signature.constructorInjective
  induction_read : Translates [] induction.sequent.concl.term .prop signature.induction

/-- Both carrier comparisons and their operation laws refer to the same model. -/
structure Correspondence (signature : Signature)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (filler : RecursiveSpaceSemantics.Relation (signature.Payload model)) where
  numbers : Nat ≃ signature.Numbers model
  relation : signature.Carrier model ≃ RecursiveSpaceSemantics.Carrier filler
  bottom : relation (signature.origin model) = RecursiveSpaceSemantics.bottom filler
  constructor : ∀ tag payload children,
    relation (signature.constructor model tag payload children) =
      RecursiveSpaceSemantics.construct filler (numbers.symm tag) payload
        (fun n => relation (children (numbers n)))

namespace Correspondence
open Mettapedia.TypeTheory
variable {signature : Signature} {model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol}
  {filler : RecursiveSpaceSemantics.Relation (signature.Payload model)}
  (comparison : Correspondence signature model filler) [Nonempty (signature.Payload model)]

/-- The received source carrier is compared with structural recursive trees,
using the same relation comparison as the retained source roots. -/
noncomputable def trees : RecursiveSpace.Tree (signature.Payload model) ≃ signature.Carrier model :=
  (RecursiveSpaceSemantics.representation filler).trans comparison.relation.symm

theorem trees_bottom : comparison.trees RecursiveSpace.bottom = signature.origin model := by
  apply comparison.relation.injective
  change comparison.relation (comparison.relation.symm
    (RecursiveSpaceSemantics.representation filler RecursiveSpace.bottom)) = _
  rw [Equiv.apply_symm_apply, comparison.bottom]
  rfl

theorem trees_construct (tag : Nat) (payload : signature.Payload model)
    (children : Nat → RecursiveSpace.Tree (signature.Payload model)) :
    comparison.trees (RecursiveSpace.construct tag payload children) =
      signature.constructor model (comparison.numbers tag) payload
        (fun n => comparison.trees (children (comparison.numbers.symm n))) := by
  apply comparison.relation.injective
  change comparison.relation (comparison.relation.symm
    (RecursiveSpaceSemantics.representation filler (RecursiveSpace.construct tag payload children))) = _
  rw [Equiv.apply_symm_apply, comparison.constructor]
  simp only [Equiv.symm_apply_apply]
  change RecursiveSpaceSemantics.construct filler tag payload
    (fun n => RecursiveSpaceSemantics.representation filler (children n)) = _
  congr 1
  funext n
  exact (comparison.relation.apply_symm_apply _).symm

#print axioms trees_bottom
#print axioms trees_construct
end Correspondence

open SourceProfileModels TypeFamilySemantics

/-- Source replay earns the model and the six interpreted root laws. The
only additional input is exact cache/formula identification. -/
noncomputable def replayCorrespondence (signature : Signature)
    (zero : HOL.ClosedTerm Symbol signature.number)
    (successor : HOL.ClosedTerm Symbol (signature.number.arr signature.number))
    (commands : List ProofExecution.Registered.Command) (after : ProofExecution.Registered.State)
    (accepted : ProofExecution.Registered.replayFrom policy
      (ProofExecution.Registered.empty SourceProfile.primitiveContext) commands = some after)
    (naturalFacts : NaturalModelCategoricity.CachedFacts ⟨signature.number,zero,successor⟩ after)
    (recursiveFacts : CachedFacts signature after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (filler : RecursiveSpaceSemantics.Relation
      (signature.Payload ((sourceReplayFrame commands after accepted).frame.model other assignment))) :
    Correspondence signature ((sourceReplayFrame commands after accepted).frame.model other assignment) filler := by
  let frame := (sourceReplayFrame commands after accepted).frame
  have closed {fact : Theorem} (known : fact ∈ after.cache) {formula : HOL.ClosedFormula Symbol}
      (translated : Translates [] fact.sequent.concl.term .prop formula)
      (noHypotheses : fact.sequent.hyp = ∅) : (frame.model other assignment).models formula := by
    apply frame.cached_models_of_translation other assignment known translated
    intro hypothesis member
    simp [noHypotheses, translatedHypotheses] at member
  have inhabited : Nonempty (signature.Payload (frame.model other assignment)) := by
    change Nonempty (HOL.Ty.denote.{0,w+1} (frame.family.model other assignment).Carrier signature.payload)
    rw [frame.family.carrier]
    have point := holValue (frame.family.operators other) assignment (Ty.fromHOL signature.payload)
      (evaluate (primitiveFamilies (frame.family.operators other)) assignment (Ty.fromHOL signature.payload)).inhabitant
    rw [Ty.toHOL_fromHOL] at point
    exact ⟨point⟩
  letI := inhabited
  let numbers := NaturalModelCategoricity.replayNaturalEquivalence
    ⟨signature.number,zero,successor⟩ commands after accepted naturalFacts other assignment
  have full := frame.model_fullDomains other assignment
  have meanings := replay_meanings commands after accepted other assignment
  have separation := closed recursiveFacts.separation_known recursiveFacts.separation_read recursiveFacts.separation_closed
  have injectivity := closed recursiveFacts.injectivity_known recursiveFacts.injectivity_read recursiveFacts.injectivity_closed
  have induction := closed recursiveFacts.induction_known recursiveFacts.induction_read recursiveFacts.induction_closed
  exact ⟨numbers,
    signature.relationalEquivalence _ full meanings numbers separation injectivity induction filler,
    signature.relationalEquivalence_bottom _ full meanings numbers separation injectivity induction filler,
    signature.relationalEquivalence_constructor _ full meanings numbers separation injectivity induction filler⟩

#print axioms Signature.algebra
#print axioms Signature.relationalEquivalence
#print axioms Signature.relationalEquivalence_constructor
#print axioms replayCorrespondence

end Mettapedia.Languages.HOLLight.RecursiveSpaceModelComparison
