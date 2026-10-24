import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationPredicateFamilySemantics

/-!
# The material-signature proof model as a displayed compiler algebra

The independently defined native proof-family relation realizes the actual
outputs of all eight proof operations and the compiler's binding rules. The
resulting algebra uses a full-domain Henkin model: native dependent products
range over the whole carrier, while the source quantifiers carry admissibility.
The generic fusion theorem can then interpret every computed proof term.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationProofCompilerSemantics
open Presentation
open Mettapedia.Logic HOL.Embedding.ZFSetHenkinInterpretation
open FormationSensitiveHOLInterface
open HOLNativeGenericProofCompiler
open HenkinFamilySemantics
open SetOperationExtensionalProfile (signature reading)
open SetOperationExtensionalOperations (operations)
open SetOperationSignature (proofName)
universe w
variable (model : HOL.HenkinModel.{0,0,w} Unit Symbol) (full : model.FullDomains)

def algebra : GenericSemantics.Algebra reading proofName operations where
  State := State reading model
  Denotes := SetOperationProofFamilySemantics.Proves model
  proofExtension := proofExtension
  objectExtension := objectExtension
  proofVariable := SetOperationProofFamilySemantics.Proves.variable model
  proofWeakening := fun state _ meaning => SetOperationProofFamilySemantics.Proves.weakenProof model state meaning
  objectWeakening := SetOperationProofFamilySemantics.Proves.weakenObject model
  implicationIntro := by
    intro gamma n objects premise conclusion premiseCode body state _ meaning
    exact SetOperationProofFamilySemantics.Proves.implicationIntro model state meaning
  implicationElim := SetOperationProofFamilySemantics.Proves.implicationElim model
  universalIntro := SetOperationProofFamilySemantics.Proves.universalIntro model full
  universalElim := SetOperationProofFamilySemantics.Proves.universalElim model full
  reflexivity := by
    intro gamma n objects type term code out state represented emitted
    simp only [SetOperationExtensionalOperations.emits_reflexivity, Option.some.injEq] at emitted
    subst out
    exact SetOperationPredicateFamilySemantics.reflexivity_realizes model full state.context type
      (fun environment => model.denote term (state.valuation environment))
  symmetry := by
    intro gamma n objects type left right leftCode rightCode comparison out state leftRepresented rightRepresented emitted meaning
    simp only [SetOperationExtensionalOperations.emits_symmetry, Option.some.injEq] at emitted
    subst out
    exact SetOperationPredicateFamilySemantics.symmetry_realizes model full type
      (representation_denotes left leftRepresented state) meaning
  transitivity := by
    intro gamma n objects type left middle right leftCode middleCode rightCode first second out state leftRepresented middleRepresented rightRepresented emitted firstMeaning secondMeaning
    simp only [SetOperationExtensionalOperations.emits_transitivity, Option.some.injEq] at emitted
    subst out
    exact SetOperationPredicateFamilySemantics.transitivity_realizes model full type
      (representation_denotes left leftRepresented state) firstMeaning secondMeaning
  propositionExtensionality := by
    intro gamma n objects left right leftCode rightCode forward backward out state leftRepresented rightRepresented emitted forwardMeaning backwardMeaning
    simp only [SetOperationExtensionalOperations.emits_propositionExtensionality, Option.some.injEq] at emitted
    subst out
    obtain ⟨forwardValue, forwardMeaning⟩ := forwardMeaning
    obtain ⟨backwardValue, backwardMeaning⟩ := backwardMeaning
    exact ⟨_, SetOperationProofFamilySemantics.Denotes.propositionExtensionality
      (representation_denotes left leftRepresented state) (representation_denotes right rightRepresented state)
      forwardMeaning backwardMeaning⟩
  propositionForward := by
    intro gamma n objects left right comparison out state emitted meaning
    simp only [SetOperationExtensionalOperations.emits_propositionForward, Option.some.injEq] at emitted
    subst out
    exact SetOperationPredicateFamilySemantics.propositionForward_realizes model full meaning
  functionCongruence := by
    intro gamma n objects domain result function other argument functionCode otherCode argumentCode comparison out state functionRepresented otherRepresented argumentRepresented emitted meaning
    simp only [SetOperationExtensionalOperations.emits_functionCongruence, Option.some.injEq] at emitted
    subst out
    exact SetOperationPredicateFamilySemantics.functionCongruence_realizes model full domain result
      (representation_denotes function functionRepresented state)
      (representation_denotes argument argumentRepresented state) meaning
  argumentCongruence := by
    intro gamma n objects domain result function left right functionCode leftCode rightCode comparison out state functionRepresented leftRepresented rightRepresented emitted meaning
    simp only [SetOperationExtensionalOperations.emits_argumentCongruence, Option.some.injEq] at emitted
    subst out
    exact SetOperationPredicateFamilySemantics.argumentCongruence_realizes model full domain result
      (representation_denotes function functionRepresented state)
      (representation_denotes left leftRepresented state) meaning
  lambdaCongruence := by
    intro gamma n objects domain codomain left right leftCode rightCode comparison out state leftRepresented rightRepresented emitted meaning
    simp only [SetOperationExtensionalOperations.emits_functionExtensionality, Option.some.injEq] at emitted
    subst out
    have leftMeaning := HenkinFamilySemantics.Denotes.abstractSimple
      (representation_denotes left leftRepresented (objectExtension state domain))
    have rightMeaning := HenkinFamilySemantics.Denotes.abstractSimple
      (representation_denotes right rightRepresented (objectExtension state domain))
    obtain ⟨value, meaning⟩ := meaning
    have pointwise := SetOperationProofFamilySemantics.Denotes.abstraction meaning
    exact ⟨_, SetOperationProofFamilySemantics.Denotes.functionExtensionality leftMeaning rightMeaning pointwise⟩
  functionExtensionality := by
    intro gamma n objects domain codomain function other functionCode otherCode pointwise out state functionRepresented otherRepresented emitted meaning
    simp only [SetOperationExtensionalOperations.emits_functionExtensionality, Option.some.injEq] at emitted
    subst out
    let left := fun environment => model.denote function (state.valuation environment)
    let right := fun environment => model.denote other (state.valuation environment)
    obtain ⟨value, meaning⟩ := meaning
    have familyEq : truthFamily (formulaMeaning state
        (.all (.eq (.app (HOL.weaken function) (.var .vz))
          (.app (HOL.weaken other) (.var .vz))))) =
        truthFamily (fun environment => ∀ argument, model.adm domain argument →
          model.Eqv codomain (left environment argument) (right environment argument)) := by
      congr 1
      funext environment
      simp only [formulaMeaning, HOL.HenkinModel.denote, HOL.PreModel.denote,
        HOL.Soundness.denote_weaken, HOL.PreModel.extend, left, right]
    have meaning' := meaning.cast_family model familyEq
    have pointwiseMeaning := SetOperationProofFamilySemantics.Denotes.convert meaning'
      (SetOperationPredicateFamilySemantics.pointwiseProofEquiv model full domain codomain left right)
    exact ⟨_, SetOperationProofFamilySemantics.Denotes.functionExtensionality
      (representation_denotes function functionRepresented state)
      (representation_denotes other otherRepresented state) pointwiseMeaning⟩
  beta := by
    intro gamma n objects domain codomain argument body argumentCode bodyCode out state argumentRepresented bodyRepresented emitted
    simp only [SetOperationExtensionalOperations.emits_reflexivity, Option.some.injEq] at emitted
    subst out
    have meaning := SetOperationPredicateFamilySemantics.reflexivity_realizes model full state.context codomain
      (fun environment => model.denote (.app (.lam body) argument) (state.valuation environment))
    change SetOperationPredicateFamilySemantics.Realizes model state.context
      HOLPredicateEqualityDerived.reflTerm (fun environment => model.Eqv codomain
        (model.denote (.app (.lam body) argument) (state.valuation environment))
        (model.denote (HOL.instantiate argument body) (state.valuation environment)))
    simpa only [HOL.Soundness.denote_instantiate_term, HOL.HenkinModel.denote,
      HOL.PreModel.denote] using meaning
  eta := by
    intro gamma n objects domain codomain function functionCode pointwise out state functionRepresented pointwiseEmitted emitted
    simp only [SetOperationExtensionalOperations.emits_reflexivity, Option.some.injEq] at pointwiseEmitted
    subst pointwise
    simp only [SetOperationExtensionalOperations.emits_functionExtensionality, Option.some.injEq] at emitted
    subst out
    have functionMeaning := representation_denotes function functionRepresented state
    have weakenedFunction := functionMeaning.rename (Renaming.weaken state.context
      (typeFamily model domain : Family state.context.Environment))
    have newestVariable : HenkinFamilySemantics.Denotes reading model
        (state.context.snoc (typeFamily model domain)) (.var 0) (typeFamily model domain)
        (fun point => point.2) := .var _ 0
    have etaMeaning := HenkinFamilySemantics.Denotes.abstractSimple
      (HenkinFamilySemantics.Denotes.applySimple weakenedFunction newestVariable)
    have etaValueEq : (fun environment argument =>
        model.denote function (state.valuation environment) argument) =
        fun environment => model.denote
          (.lam (.app (HOL.weaken function) (.var .vz))) (state.valuation environment) := by
      funext environment argument
      change model.denote function (state.valuation environment) argument =
        model.denote (HOL.weaken function) (model.extend (state.valuation environment) argument) argument
      rw [HOL.Soundness.denote_weaken]
    obtain ⟨value, meaning⟩ := SetOperationPredicateFamilySemantics.reflexivity_realizes model full
      (state.context.snoc (typeFamily model domain)) codomain
      (fun point => model.denote function (state.valuation point.1) point.2)
    have pointwiseMeaning := SetOperationProofFamilySemantics.Denotes.abstraction meaning
    have realized := SetOperationProofFamilySemantics.Denotes.functionExtensionality
      (left := fun environment => model.denote function (state.valuation environment))
      (right := fun environment => model.denote function (state.valuation environment))
      etaMeaning functionMeaning pointwiseMeaning
    have familyEq : truthFamily (fun environment => model.Eqv (.arr domain codomain)
        (model.denote function (state.valuation environment))
        (model.denote function (state.valuation environment))) =
        truthFamily (formulaMeaning state
          (.eq (.lam (.app (HOL.weaken function) (.var .vz))) function)) := by
      apply congrArg truthFamily
      funext environment
      change model.Eqv (.arr domain codomain) _ _ = model.Eqv (.arr domain codomain)
        (model.denote (.lam (.app (HOL.weaken function) (.var .vz))) (state.valuation environment)) _
      rw [← congrFun etaValueEq environment]
    exact ⟨_, realized.cast_family model familyEq⟩

theorem compile_expanded_proves {gamma : HOL.Ctx Unit}
    {assumptions : List (HOL.Formula Symbol gamma)} {goal : HOL.Formula Symbol gamma}
    (source : HOL.ProofSyntax Symbol assumptions goal) {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin (assumptions.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading model objects)
    (meanings : GenericSemantics.Hypotheses (algebra model full) state hypotheses) :
    SetOperationProofFamilySemantics.Proves model state
      (SetOperationProofCompilation.compile source objects hypotheses)
      (HOL.ImpredicativeConnectives.expand goal) :=
  HOLImpredicativeProofCompilation.translateProof_denotes reading proofName operations
    SetOperationExtensionalOperations.total (algebra model full) source state meanings

theorem compile_proves {gamma : HOL.Ctx Unit}
    {assumptions : List (HOL.Formula Symbol gamma)} {goal : HOL.Formula Symbol gamma}
    (source : HOL.ProofSyntax Symbol assumptions goal) {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin (assumptions.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading model objects)
    (meanings : GenericSemantics.Hypotheses (algebra model full) state hypotheses) :
    SetOperationProofFamilySemantics.Proves model state
      (SetOperationProofCompilation.compile source objects hypotheses) goal := by
  obtain ⟨value, meaning⟩ := compile_expanded_proves model full source state meanings
  have familyEq : truthFamily (formulaMeaning state (HOL.ImpredicativeConnectives.expand goal)) =
      truthFamily (formulaMeaning state goal) := by
    apply congrArg truthFamily
    funext environment
    exact congrArg ULift.down (HOL.ImpredicativeConnectives.denote_expand model goal (state.valuation environment))
  exact ⟨_, meaning.cast_family model familyEq⟩

theorem expand_proves {gamma : HOL.Ctx Unit} {n : Nat} {objects : Sub Tower.Head gamma.length n}
    {state : State reading model objects} {term : Tower.Tm n} {formula : HOL.Formula Symbol gamma}
    (meaning : SetOperationProofFamilySemantics.Proves model state term formula) :
    SetOperationProofFamilySemantics.Proves model state term (HOL.ImpredicativeConnectives.expand formula) := by
  obtain ⟨value, meaning⟩ := meaning
  have familyEq : truthFamily (formulaMeaning state formula) =
      truthFamily (formulaMeaning state (HOL.ImpredicativeConnectives.expand formula)) := by
    apply congrArg truthFamily
    funext environment
    exact (congrArg ULift.down
      (HOL.ImpredicativeConnectives.denote_expand model formula (state.valuation environment))).symm
  exact ⟨_, meaning.cast_family model familyEq⟩

include full

theorem compile_proves_of_original_hypotheses {gamma : HOL.Ctx Unit}
    {assumptions : List (HOL.Formula Symbol gamma)} {goal : HOL.Formula Symbol gamma}
    (source : HOL.ProofSyntax Symbol assumptions goal) {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin (assumptions.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading model objects)
    (meanings : ∀ index, SetOperationProofFamilySemantics.Proves model state (hypotheses index)
      (assumptions.get (index.cast (by simp)))) :
    SetOperationProofFamilySemantics.Proves model state
      (SetOperationProofCompilation.compile source objects hypotheses) goal := by
  apply compile_proves model full source state
  intro index
  have entry : (assumptions.map HOL.ImpredicativeConnectives.expand).get index =
      HOL.ImpredicativeConnectives.expand (assumptions.get (index.cast (by simp))) := by
    simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast]
  change SetOperationProofFamilySemantics.Proves model state (hypotheses index) _
  rw [entry]
  exact expand_proves model (meanings index)

def emptyState : State reading model (gamma := []) (n := 0) Fin.elim0 where
  context := SemanticContext.nil
  valuation := fun _ {_} index => nomatch index
  objectsDenote := by intro type index; nomatch index

include full

theorem compile_closed_proves {goal : HOL.ClosedFormula Symbol} (source : HOL.ProofSyntax Symbol [] goal) :
    SetOperationProofFamilySemantics.Proves model (emptyState model)
      (SetOperationProofCompilation.compile source Fin.elim0 Fin.elim0) goal := by
  apply compile_proves model full source (emptyState model)
  intro index
  nomatch index

theorem extensionalTruth_hasMeaning :
    SetOperationProofFamilySemantics.Proves model (emptyState model)
      SetOperationProofCompilation.extensionalTruthProgram
      (HOL.Term.eq .top .top : HOL.ClosedFormula Symbol) := by
  rw [← SetOperationProofCompilation.extensionalTruth_compiles]
  exact compile_closed_proves model full SetOperationPredicateProofs.extensionalTruth

#print axioms algebra
#print axioms compile_proves
#print axioms compile_closed_proves
#print axioms extensionalTruth_hasMeaning
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationProofCompilerSemantics
