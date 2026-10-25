import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationProofFamilySemantics

/-!
# Predicate-equality proof families and their actual native terms

The intrinsic equality proof fibre compares with the dependent family taking
an admitted predicate and transporting its proof between the two endpoints.
In the chosen full-domain family interpretation, every ambient predicate is
admitted. The codec is constructed from the semantic equality tests and
argument congruence; it is not a native conversion rule.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationPredicateFamilySemantics
open Presentation
open Mettapedia.Logic HOL.Embedding.ZFSetHenkinInterpretation
open HOLNativeGenericProofCompiler.HenkinFamilySemantics
open SetOperationExtensionalProfile (signature reading)
universe w
variable (model : HOL.HenkinModel.{0,0,w} Unit Symbol) (full : model.FullDomains)

def predicateFamily {Environment : Type (max 1 w)} (type : HOL.Ty Unit)
    (left right : Environment → HOL.Ty.denote model.Carrier type) : Family Environment :=
  fun environment => (predicate : HOL.Ty.denote model.Carrier (.arr type .prop)) →
    ULift.{max 1 w} (PLift (predicate (left environment)).down) →
    ULift.{max 1 w} (PLift (predicate (right environment)).down)

def equalityProofEquiv {Environment : Type (max 1 w)} (type : HOL.Ty Unit)
    (left right : Environment → HOL.Ty.denote model.Carrier type) (environment : Environment) :
    truthFamily (fun point => model.Eqv type (left point) (right point)) environment ≃
      predicateFamily model type left right environment where
  toFun comparison := fun predicate input => ULift.up ⟨
    model.predicateEquality_of_eqv (model.functionsRespectEqv_of_fullDomains full)
      (full type (left environment)) (full type (right environment)) comparison.down.down
      predicate (full _ predicate) input.down.down⟩
  invFun transport := ULift.up ⟨model.eqv_of_predicateEquality (full type (left environment))
    (fun predicate _ input => (transport predicate (ULift.up ⟨input⟩)).down.down)⟩
  left_inv _ := @Subsingleton.elim
    (ULift.{max 1 w, 0} (PLift (model.Eqv type (left environment) (right environment)))) inferInstance _ _
  right_inv _ := by
    funext predicate input
    exact @Subsingleton.elim
      (ULift.{max 1 w, 0} (PLift (predicate (right environment)).down)) inferInstance _ _

include full

theorem rawEquality_denotes {n : Nat} {context : SemanticContext.{max 1 w} n}
    (type : HOL.Ty Unit) {leftTerm rightTerm : Tower.Tm n}
    {left right : context.Environment → HOL.Ty.denote model.Carrier type}
    (leftMeaning : Denotes reading model context leftTerm (typeFamily model type) left)
    (rightMeaning : Denotes reading model context rightTerm (typeFamily model type) right) :
    Denotes reading model context (HOLPredicateEqualitySignature.raw signature type leftTerm rightTerm)
      (typeFamily model .prop) (fun environment => ULift.up (model.Eqv type (left environment) (right environment))) := by
  let predicates := typeFamily model (.arr type .prop) (Environment := context.Environment)
  have weakenedLeft := leftMeaning.rename (Renaming.weaken context predicates)
  have weakenedRight := rightMeaning.rename (Renaming.weaken context predicates)
  have predicateVariable : Denotes reading model (context.snoc predicates) (.var 0)
      (typeFamily model (.arr type .prop)) (fun point => point.2) := .var _ 0
  have leftApplication := Denotes.applySimple predicateVariable weakenedLeft
  have rightApplication := Denotes.applySimple predicateVariable weakenedRight
  have implication := Denotes.applySimple
    (Denotes.applySimple (Denotes.implication (signature := reading) (model := model)
      (context.snoc predicates)) leftApplication) rightApplication
  have abstraction := Denotes.abstractSimple implication
  have quantified := Denotes.applySimple
    (Denotes.universal (signature := reading) (model := model) context (.arr type .prop)) abstraction
  have equality : (fun environment : context.Environment => ULift.up
      (model.PredicateEquality type (left environment) (right environment))) =
      fun environment => ULift.up (model.Eqv type (left environment) (right environment)) := by
    funext environment
    apply ULift.ext
    exact propext (model.predicateEquality_iff_eqv_of_fullDomains full type _ _)
  change Denotes reading model context
    (HOLPredicateEqualitySignature.raw signature type leftTerm rightTerm)
    (typeFamily model .prop) _ at quantified
  exact quantified.change_value equality

def Realizes {n : Nat} (context : SemanticContext.{max 1 w} n) (term : Tower.Tm n)
    (formula : context.Environment → Prop) : Prop :=
  ∃ value : Section (truthFamily formula), SetOperationProofFamilySemantics.Denotes model context term
    (truthFamily formula) value

theorem reflexivity_realizes {n : Nat} (context : SemanticContext.{max 1 w} n)
    (type : HOL.Ty Unit) (value : context.Environment → HOL.Ty.denote model.Carrier type) :
    Realizes model context HOLPredicateEqualityDerived.reflTerm
      (fun environment => model.Eqv type (value environment) (value environment)) := by
  let predicates := typeFamily model (.arr type .prop) (Environment := context.Environment)
  let premise : Family (Extension predicates) :=
    truthFamily (fun point => (point.2 (value point.1)).down)
  have newestVariable : SetOperationProofFamilySemantics.Denotes model
      ((context.snoc predicates).snoc premise) (.var 0)
      (fun point => premise point.1) (fun point => point.2) :=
    .underlying (.var _ 0)
  have body := SetOperationProofFamilySemantics.Denotes.abstraction newestVariable
  have lambda := SetOperationProofFamilySemantics.Denotes.abstraction body
  have predicateMeaning : SetOperationProofFamilySemantics.Denotes model context
      HOLPredicateEqualityDerived.reflTerm (predicateFamily model type value value)
      (fun _ _ input => input) := lambda
  exact ⟨mapSection (fun environment => (equalityProofEquiv model full type value value environment).symm)
      (fun _ _ input => input),
    .convert predicateMeaning
      (fun environment => (equalityProofEquiv model full type value value environment).symm)⟩

theorem transport_realizes {n : Nat} {context : SemanticContext.{max 1 w} n} (type : HOL.Ty Unit)
    {left right : context.Environment → HOL.Ty.denote model.Carrier type}
    {comparison predicate input : Tower.Tm n}
    {predicateValue : context.Environment → HOL.Ty.denote model.Carrier (.arr type .prop)}
    (comparisonMeaning : Realizes model context comparison
      (fun environment => model.Eqv type (left environment) (right environment)))
    (predicateMeaning : Denotes reading model context predicate (typeFamily model (.arr type .prop)) predicateValue)
    (inputMeaning : Realizes model context input
      (fun environment => (predicateValue environment (left environment)).down)) :
    Realizes model context (.app (.app comparison predicate) input)
      (fun environment => (predicateValue environment (right environment)).down) := by
  obtain ⟨comparisonValue, comparisonMeaning⟩ := comparisonMeaning
  obtain ⟨inputValue, inputMeaning⟩ := inputMeaning
  have transportMeaning := SetOperationProofFamilySemantics.Denotes.convert comparisonMeaning
    (equalityProofEquiv model full type left right)
  let premise : Family (Extension (typeFamily model (.arr type .prop) : Family context.Environment)) :=
    fun point => ULift.{max 1 w} (PLift (point.2 (left point.1)).down) →
      ULift.{max 1 w} (PLift (point.2 (right point.1)).down)
  have specialized := SetOperationProofFamilySemantics.Denotes.application
    (domain := typeFamily model (.arr type .prop)) (codomain := premise)
    transportMeaning (.underlying predicateMeaning)
  have applied := SetOperationProofFamilySemantics.Denotes.application
    (domain := truthFamily (fun environment => (predicateValue environment (left environment)).down))
    (codomain := fun point => ULift.{max 1 w} (PLift (predicateValue point.1 (right point.1)).down))
    specialized inputMeaning
  exact ⟨_, applied⟩

theorem symmetry_realizes {n : Nat} {context : SemanticContext.{max 1 w} n}
    (type : HOL.Ty Unit) {leftTerm comparison : Tower.Tm n}
    {left right : context.Environment → HOL.Ty.denote model.Carrier type}
    (leftMeaning : Denotes reading model context leftTerm (typeFamily model type) left)
    (comparisonMeaning : Realizes model context comparison
      (fun environment => model.Eqv type (left environment) (right environment))) :
    Realizes model context (HOLPredicateEqualityDerived.symmetry signature type leftTerm comparison)
      (fun environment => model.Eqv type (right environment) (left environment)) := by
  have weakenedLeft := leftMeaning.rename (Renaming.weaken context
    (typeFamily model type : Family context.Environment))
  have newestVariable : Denotes reading model (context.snoc (typeFamily model type)) (.var 0)
      (typeFamily model type) (fun point => point.2) := .var _ 0
  have predicate := Denotes.abstractSimple (rawEquality_denotes model full type newestVariable weakenedLeft)
  exact transport_realizes model full type comparisonMeaning predicate
    (reflexivity_realizes model full context type left)

theorem transitivity_realizes {n : Nat} {context : SemanticContext.{max 1 w} n}
    (type : HOL.Ty Unit) {leftTerm first second : Tower.Tm n}
    {left middle right : context.Environment → HOL.Ty.denote model.Carrier type}
    (leftMeaning : Denotes reading model context leftTerm (typeFamily model type) left)
    (firstMeaning : Realizes model context first (fun environment => model.Eqv type (left environment) (middle environment)))
    (secondMeaning : Realizes model context second (fun environment => model.Eqv type (middle environment) (right environment))) :
    Realizes model context (HOLPredicateEqualityDerived.transitivity signature type leftTerm first second)
      (fun environment => model.Eqv type (left environment) (right environment)) := by
  have weakenedLeft := leftMeaning.rename (Renaming.weaken context
    (typeFamily model type : Family context.Environment))
  have newestVariable : Denotes reading model (context.snoc (typeFamily model type)) (.var 0)
      (typeFamily model type) (fun point => point.2) := .var _ 0
  have predicate := Denotes.abstractSimple (rawEquality_denotes model full type weakenedLeft newestVariable)
  exact transport_realizes model full type secondMeaning predicate firstMeaning

theorem argumentCongruence_realizes {n : Nat} {context : SemanticContext.{max 1 w} n}
    (domain codomain : HOL.Ty Unit) {functionTerm leftTerm comparison : Tower.Tm n}
    {function : context.Environment → HOL.Ty.denote model.Carrier (.arr domain codomain)}
    {left right : context.Environment → HOL.Ty.denote model.Carrier domain}
    (functionMeaning : Denotes reading model context functionTerm (typeFamily model (.arr domain codomain)) function)
    (leftMeaning : Denotes reading model context leftTerm (typeFamily model domain) left)
    (comparisonMeaning : Realizes model context comparison (fun environment => model.Eqv domain (left environment) (right environment))) :
    Realizes model context (HOLPredicateEqualityDerived.congruence signature codomain functionTerm leftTerm comparison)
      (fun environment => model.Eqv codomain (function environment (left environment)) (function environment (right environment))) := by
  have application := Denotes.applySimple functionMeaning leftMeaning
  have weakenedApplication := application.rename (Renaming.weaken context
    (typeFamily model domain : Family context.Environment))
  have weakenedFunction := functionMeaning.rename (Renaming.weaken context
    (typeFamily model domain : Family context.Environment))
  have newestVariable : Denotes reading model (context.snoc (typeFamily model domain)) (.var 0)
      (typeFamily model domain) (fun point => point.2) := .var _ 0
  have predicate := Denotes.abstractSimple (rawEquality_denotes model full codomain
    weakenedApplication (Denotes.applySimple weakenedFunction newestVariable))
  exact transport_realizes model full domain comparisonMeaning predicate
    (reflexivity_realizes model full context codomain (fun environment => function environment (left environment)))

theorem functionCongruence_realizes {n : Nat} {context : SemanticContext.{max 1 w} n}
    (domain codomain : HOL.Ty Unit) {functionTerm argumentTerm comparison : Tower.Tm n}
    {function other : context.Environment → HOL.Ty.denote model.Carrier (.arr domain codomain)}
    {argument : context.Environment → HOL.Ty.denote model.Carrier domain}
    (functionMeaning : Denotes reading model context functionTerm (typeFamily model (.arr domain codomain)) function)
    (argumentMeaning : Denotes reading model context argumentTerm (typeFamily model domain) argument)
    (comparisonMeaning : Realizes model context comparison
      (fun environment => model.Eqv (.arr domain codomain) (function environment) (other environment))) :
    Realizes model context (HOLPredicateEqualityDerived.functionCongruence signature codomain functionTerm argumentTerm comparison)
      (fun environment => model.Eqv codomain (function environment (argument environment)) (other environment (argument environment))) := by
  have application := Denotes.applySimple functionMeaning argumentMeaning
  have weakenedApplication := application.rename (Renaming.weaken context
    (typeFamily model (.arr domain codomain) : Family context.Environment))
  have weakenedArgument := argumentMeaning.rename (Renaming.weaken context
    (typeFamily model (.arr domain codomain) : Family context.Environment))
  have newestVariable : Denotes reading model
      (context.snoc (typeFamily model (.arr domain codomain))) (.var 0)
      (typeFamily model (.arr domain codomain)) (fun point => point.2) := .var _ 0
  have predicate := Denotes.abstractSimple (rawEquality_denotes model full codomain
    weakenedApplication (Denotes.applySimple newestVariable weakenedArgument))
  exact transport_realizes model full (.arr domain codomain) comparisonMeaning predicate
    (reflexivity_realizes model full context codomain (fun environment => function environment (argument environment)))

theorem propositionForward_realizes {n : Nat} {context : SemanticContext.{max 1 w} n}
    {comparison : Tower.Tm n} {left right : context.Environment → HOL.Ty.denote model.Carrier .prop}
    (comparisonMeaning : Realizes model context comparison
      (fun environment => model.Eqv .prop (left environment) (right environment))) :
    Realizes model context (HOLPredicateEqualityDerived.propForward comparison)
      (fun environment => (left environment).down → (right environment).down) := by
  obtain ⟨comparisonValue, comparisonMeaning⟩ := comparisonMeaning
  have transportMeaning := SetOperationProofFamilySemantics.Denotes.convert comparisonMeaning
    (equalityProofEquiv model full .prop left right)
  have identityBody : Denotes reading model (context.snoc (typeFamily model .prop)) (.var 0)
      (typeFamily model .prop) (fun point => point.2) := .var _ 0
  have identityMeaning := Denotes.abstractSimple identityBody
  let premise : Family (Extension (typeFamily model (.arr .prop .prop) : Family context.Environment)) :=
    fun point => ULift.{max 1 w} (PLift (point.2 (left point.1)).down) →
      ULift.{max 1 w} (PLift (point.2 (right point.1)).down)
  have specialized := SetOperationProofFamilySemantics.Denotes.application
    (domain := typeFamily model (.arr .prop .prop)) (codomain := premise)
    transportMeaning (.underlying identityMeaning)
  have implication := SetOperationProofFamilySemantics.Denotes.convert specialized
    (fun environment => implicationProofEquiv (left environment).down (right environment).down)
  exact ⟨_, implication⟩

def pointwiseProofEquiv {Environment : Type (max 1 w)} (domain codomain : HOL.Ty Unit)
    (left right : Environment → HOL.Ty.denote model.Carrier (.arr domain codomain)) (environment : Environment) :
    truthFamily (fun point => ∀ argument, model.adm domain argument →
      model.Eqv codomain (left point argument) (right point argument)) environment ≃
      SetOperationProofFamilySemantics.pointwiseFamily model domain codomain left right environment where
  toFun comparison := fun argument => ULift.up ⟨comparison.down.down argument (full domain argument)⟩
  invFun pointwise := ULift.up ⟨fun argument _ => (pointwise argument).down.down⟩
  left_inv _ := @Subsingleton.elim
    (ULift.{max 1 w, 0} (PLift (∀ argument, model.adm domain argument →
      model.Eqv codomain (left environment argument) (right environment argument)))) inferInstance _ _
  right_inv _ := by
    funext argument
    exact @Subsingleton.elim (ULift.{max 1 w, 0}
      (PLift (model.Eqv codomain (left environment argument) (right environment argument)))) inferInstance _ _

#print axioms equalityProofEquiv
#print axioms rawEquality_denotes
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationPredicateFamilySemantics
