import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationProofCompilation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLHenkinFamilySemantics
import Mettapedia.Logic.HOL.Semantics.PredicateEquality

/-!
# Dependent-family meaning of material-signature proof programs

The native lambda/application interpretation is closed compositionally under
the two fully applied, declared extensionality operations. Their semantic
sections are constructed from their actual argument sections. The relation
does not invoke a proof compiler or take a source derivation as an input.

Function extensionality is qualified at represented source domain and codomain
codes. Partial opaque applications and arbitrary native universe operations
receive no meaning from these two clauses. Semantic recoding retains the
existing codec boundary; it is not native conversion or execution uniqueness.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationProofFamilySemantics
open Presentation
open Mettapedia.Logic HOL.Embedding.ZFSetHenkinInterpretation
open HOLNativeGenericProofCompiler.HenkinFamilySemantics
open SetOperationExtensionalProfile (reading)
open SetOperationExtensionalApplications

universe w
variable (model : HOL.HenkinModel.{0,0,w} Unit Symbol)

theorem truthSections_equal {Environment : Type (max 1 w)} (formula : Environment → Prop)
    (first second : Section (truthFamily formula)) : first = second := by
  funext environment
  exact @Subsingleton.elim (ULift.{max 1 w, 0} (PLift (formula environment)))
    inferInstance (first environment) (second environment)

def propositionSection {Environment : Type (max 1 w)}
    (left right : Environment → HOL.Ty.denote model.Carrier .prop)
    (forward : Section (truthFamily (fun environment => (left environment).down → (right environment).down)))
    (backward : Section (truthFamily (fun environment => (right environment).down → (left environment).down))) :
    Section (truthFamily (fun environment => model.Eqv .prop (left environment) (right environment))) :=
  fun environment => ULift.up ⟨⟨(forward environment).down.down, (backward environment).down.down⟩⟩

def pointwiseFamily {Environment : Type (max 1 w)} (domain codomain : HOL.Ty Unit)
    (left right : Environment → HOL.Ty.denote model.Carrier (.arr domain codomain)) : Family Environment :=
  piFamily (typeFamily model domain)
    (truthFamily (fun point => model.Eqv codomain (left point.1 point.2) (right point.1 point.2)))

def functionSection {Environment : Type (max 1 w)} (domain codomain : HOL.Ty Unit)
    (left right : Environment → HOL.Ty.denote model.Carrier (.arr domain codomain))
    (pointwise : Section (pointwiseFamily model domain codomain left right)) :
    Section (truthFamily (fun environment => model.Eqv (.arr domain codomain) (left environment) (right environment))) :=
  fun environment => ULift.up ⟨fun argument _ => (pointwise environment argument).down.down⟩

inductive Denotes : {n : Nat} → (context : SemanticContext.{max 1 w} n) →
    (term : Tower.Tm n) → (family : Family context.Environment) → Section family → Prop where
  | underlying {n : Nat} {context : SemanticContext.{max 1 w} n} {term : Tower.Tm n}
      {family : Family context.Environment} {value : Section family}
      (meaning : HOLNativeGenericProofCompiler.HenkinFamilySemantics.Denotes
        reading model context term family value) : Denotes context term family value
  | abstraction {n : Nat} {context : SemanticContext.{max 1 w} n}
      {domain : Family context.Environment} {codomain : Family (Extension domain)}
      {body : Tower.Tm (n + 1)} {bodyValue : Section codomain}
      (meaning : Denotes (context.snoc domain) body codomain bodyValue) :
      Denotes context (.lam body) (piFamily domain codomain)
        (fun environment argument => bodyValue ⟨environment, argument⟩)
  | application {n : Nat} {context : SemanticContext.{max 1 w} n}
      {domain : Family context.Environment} {codomain : Family (Extension domain)}
      {function argument : Tower.Tm n} {functionValue : Section (piFamily domain codomain)}
      {argumentValue : Section domain}
      (functionMeaning : Denotes context function (piFamily domain codomain) functionValue)
      (argumentMeaning : Denotes context argument domain argumentValue) :
      Denotes context (.app function argument)
        (fun environment => codomain ⟨environment, argumentValue environment⟩)
        (fun environment => functionValue environment (argumentValue environment))
  | convert {n : Nat} {context : SemanticContext.{max 1 w} n} {term : Tower.Tm n}
      {first second : Family context.Environment} {value : Section first}
      (meaning : Denotes context term first value)
      (equivalence : (environment : context.Environment) → first environment ≃ second environment) :
      Denotes context term second (mapSection equivalence value)
  | propositionExtensionality {n : Nat} {context : SemanticContext.{max 1 w} n}
      {leftTerm rightTerm forwardTerm backwardTerm : Tower.Tm n}
      {left right : context.Environment → HOL.Ty.denote model.Carrier .prop}
      {forwardValue : Section (truthFamily (fun environment => (left environment).down → (right environment).down))}
      {backwardValue : Section (truthFamily (fun environment => (right environment).down → (left environment).down))}
      (leftMeaning : HOLNativeGenericProofCompiler.HenkinFamilySemantics.Denotes
        reading model context leftTerm (typeFamily model .prop) left)
      (rightMeaning : HOLNativeGenericProofCompiler.HenkinFamilySemantics.Denotes
        reading model context rightTerm (typeFamily model .prop) right)
      (forwardMeaning : Denotes context forwardTerm _ forwardValue)
      (backwardMeaning : Denotes context backwardTerm _ backwardValue) :
      Denotes context (propositionExtensionalityApp leftTerm rightTerm forwardTerm backwardTerm)
        (truthFamily (fun environment => model.Eqv .prop (left environment) (right environment)))
        (propositionSection model left right forwardValue backwardValue)
  | functionExtensionality {n : Nat} {context : SemanticContext.{max 1 w} n}
      {domain codomain : HOL.Ty Unit} {leftTerm rightTerm pointwiseTerm : Tower.Tm n}
      {left right : context.Environment → HOL.Ty.denote model.Carrier (.arr domain codomain)}
      {pointwiseValue : Section (pointwiseFamily model domain codomain left right)}
      (leftMeaning : HOLNativeGenericProofCompiler.HenkinFamilySemantics.Denotes
        reading model context leftTerm (typeFamily model (.arr domain codomain)) left)
      (rightMeaning : HOLNativeGenericProofCompiler.HenkinFamilySemantics.Denotes
        reading model context rightTerm (typeFamily model (.arr domain codomain)) right)
      (pointwiseMeaning : Denotes context pointwiseTerm _ pointwiseValue) :
      Denotes context (functionExtensionalityApp
        (FormationSensitiveHOLInterface.typeAt reading.types n domain)
        (FormationSensitiveHOLInterface.typeAt reading.types n codomain) leftTerm rightTerm pointwiseTerm)
        (truthFamily (fun environment => model.Eqv (.arr domain codomain) (left environment) (right environment)))
        (functionSection model domain codomain left right pointwiseValue)

theorem Denotes.change_value {n : Nat} {context : SemanticContext.{max 1 w} n}
    {term : Tower.Tm n} {family : Family context.Environment} {first second : Section family}
    (meaning : Denotes model context term family first) (equal : first = second) :
    Denotes model context term family second := by
  cases equal
  exact meaning

theorem Denotes.cast_family {n : Nat} {context : SemanticContext.{max 1 w} n}
    {term : Tower.Tm n} {first second : Family context.Environment} {value : Section first}
    (meaning : Denotes model context term first value) (equal : first = second) :
    Denotes model context term second (castSection equal value) := by
  cases equal
  exact meaning

theorem Denotes.rename {n m : Nat} {source : SemanticContext.{max 1 w} n}
    {target : SemanticContext.{max 1 w} m} {rho : Ren n m} {morphism : Morphism source target}
    (displayed : Renaming source target rho morphism)
    {term : Tower.Tm n} {family : Family source.Environment} {value : Section family}
    (meaning : Denotes model source term family value) :
    Denotes model target (rename rho term) (morphism.reindexFamily family) (morphism.reindexSection value) := by
  induction meaning generalizing m with
  | underlying meaning => exact .underlying (meaning.rename displayed)
  | @abstraction n context domain codomain body bodyValue meaning ih =>
      exact .abstraction (ih (displayed.lift domain))
  | @application n context domain codomain function argument functionValue argumentValue
      functionMeaning argumentMeaning functionInduction argumentInduction =>
      exact .application (domain := morphism.reindexFamily domain)
        (codomain := (morphism.lift domain).reindexFamily codomain)
        (functionInduction displayed) (argumentInduction displayed)
  | @convert n context term first second value meaning equivalence ih =>
      exact .convert (ih displayed) (fun environment => equivalence (morphism.environment environment))
  | @propositionExtensionality n context leftTerm rightTerm forwardTerm backwardTerm
      left right forwardValue backwardValue leftMeaning rightMeaning forwardMeaning backwardMeaning
      forwardInduction backwardInduction =>
      have interpreted := Denotes.propositionExtensionality
        (leftMeaning.rename displayed) (rightMeaning.rename displayed)
        (forwardInduction displayed) (backwardInduction displayed)
      have termEq : Presentation.rename rho
          (propositionExtensionalityApp leftTerm rightTerm forwardTerm backwardTerm) =
          propositionExtensionalityApp (Presentation.rename rho leftTerm) (Presentation.rename rho rightTerm)
            (Presentation.rename rho forwardTerm) (Presentation.rename rho backwardTerm) := rfl
      rw [termEq]
      exact interpreted.change_value model (truthSections_equal _ _ _)
  | @functionExtensionality n context domain codomain leftTerm rightTerm pointwiseTerm
      left right pointwiseValue leftMeaning rightMeaning pointwiseMeaning pointwiseInduction =>
      have interpreted := Denotes.functionExtensionality (domain := domain) (codomain := codomain)
        (leftMeaning.rename displayed) (rightMeaning.rename displayed) (pointwiseInduction displayed)
      have termEq : Presentation.rename rho
          (functionExtensionalityApp
            (FormationSensitiveHOLInterface.typeAt reading.types n domain)
            (FormationSensitiveHOLInterface.typeAt reading.types n codomain)
            leftTerm rightTerm pointwiseTerm) =
          functionExtensionalityApp
            (FormationSensitiveHOLInterface.typeAt reading.types m domain)
            (FormationSensitiveHOLInterface.typeAt reading.types m codomain)
            (Presentation.rename rho leftTerm) (Presentation.rename rho rightTerm)
            (Presentation.rename rho pointwiseTerm) := by
        simp only [functionExtensionalityApp, Presentation.rename, FormationSensitiveHOLInterface.typeAt_rename]
      rw [termEq]
      exact interpreted.change_value model (truthSections_equal _ _ _)

def Proves {gamma : HOL.Ctx Unit} {n : Nat} {objects : Sub Tower.Head gamma.length n}
    (state : State reading model objects) (term : Tower.Tm n) (formula : HOL.Formula Symbol gamma) : Prop :=
  ∃ value : Section (truthFamily (formulaMeaning state formula)),
    Denotes model state.context term (truthFamily (formulaMeaning state formula)) value

theorem Proves.ofUnderlying {gamma : HOL.Ctx Unit} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {state : State reading model objects}
    {term : Tower.Tm n} {formula : HOL.Formula Symbol gamma}
    (meaning : HOLNativeGenericProofCompiler.HenkinFamilySemantics.Proves state term formula) :
    Proves model state term formula := by
  obtain ⟨value, meaning⟩ := meaning
  exact ⟨value, .underlying meaning⟩

theorem Proves.variable {gamma : HOL.Ctx Unit} {n : Nat} {objects : Sub Tower.Head gamma.length n}
    (state : State reading model objects) (premise : HOL.Formula Symbol gamma) :
    Proves model (proofExtension state premise) (.var 0) premise :=
  .ofUnderlying model (HOLNativeGenericProofCompiler.HenkinFamilySemantics.Proves.variable state premise)

theorem Proves.weakenProof {gamma : HOL.Ctx Unit} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {term : Tower.Tm n}
    {formula premise : HOL.Formula Symbol gamma} (state : State reading model objects)
    (meaning : Proves model state term formula) :
    Proves model (proofExtension state premise) (rename wk term) formula := by
  obtain ⟨value, meaning⟩ := meaning
  exact ⟨fun point => value point.1,
    meaning.rename model (Renaming.weaken state.context (truthFamily (formulaMeaning state premise)))⟩

theorem Proves.weakenObject {gamma : HOL.Ctx Unit} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {term : Tower.Tm n} {formula : HOL.Formula Symbol gamma}
    (state : State reading model objects) (type : HOL.Ty Unit)
    (meaning : Proves model state term formula) :
    Proves model (objectExtension state type) (rename wk term) (HOL.weaken (σ := type) formula) := by
  obtain ⟨value, meaning⟩ := meaning
  have renamed := meaning.rename model (Renaming.weaken state.context (typeFamily model type))
  exact ⟨mapSection (objectWeakeningFamilyEquiv state type formula) (fun point => value point.1),
    .convert renamed (objectWeakeningFamilyEquiv state type formula)⟩

theorem Proves.implicationIntro
    {gamma : HOL.Ctx Unit} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {premise conclusion : HOL.Formula Symbol gamma} {body : Tower.Tm (n + 1)}
    (state : State reading model objects)
    (meaning : Proves model (proofExtension state premise) body conclusion) :
    Proves model state (.lam body) (.imp premise conclusion) := by
  obtain ⟨bodyValue, bodyMeaning⟩ := meaning
  let functionValue : Section
      (piFamily (truthFamily (formulaMeaning state premise))
        (truthFamily (formulaMeaning (proofExtension state premise) conclusion))) :=
    fun environment premiseProof => bodyValue ⟨environment, premiseProof⟩
  refine ⟨mapSection (implicationFamilyEquiv state premise conclusion) functionValue, ?_⟩
  exact Denotes.convert (Denotes.abstraction bodyMeaning)
    (implicationFamilyEquiv state premise conclusion)

/-- Native application denotes source implication elimination. -/
theorem Proves.implicationElim
    {gamma : HOL.Ctx Unit} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {premise conclusion : HOL.Formula Symbol gamma}
    {function argument : Tower.Tm n}
    (state : State reading model objects)
    (functionMeaning : Proves model state function (.imp premise conclusion))
    (argumentMeaning : Proves model state argument premise) :
    Proves model state (.app function argument) conclusion := by
  obtain ⟨functionValue, functionDenotes⟩ := functionMeaning
  obtain ⟨argumentValue, argumentDenotes⟩ := argumentMeaning
  let implicationValue : Section
      (piFamily (truthFamily (formulaMeaning state premise))
        (truthFamily (formulaMeaning (proofExtension state premise) conclusion))) :=
    mapSection (fun environment =>
      (implicationFamilyEquiv state premise conclusion environment).symm)
      functionValue
  have implicationDenotes : Denotes model state.context function
      (piFamily (truthFamily (formulaMeaning state premise))
        (truthFamily (formulaMeaning (proofExtension state premise) conclusion)))
      implicationValue :=
    Denotes.convert functionDenotes (fun environment =>
      (implicationFamilyEquiv state premise conclusion environment).symm)
  refine ⟨fun environment =>
    implicationValue environment (argumentValue environment), ?_⟩
  change Denotes model state.context (.app function argument)
    (fun environment =>
      ULift.{max 1 w, 0}
        (PLift ((model.denote conclusion (state.valuation environment)).down)))
    (fun environment => implicationValue environment (argumentValue environment))
  exact Denotes.application implicationDenotes argumentDenotes


theorem Proves.universalIntro
    (full : model.FullDomains)
    {gamma : HOL.Ctx Unit} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {type : HOL.Ty Unit} {formula : HOL.Formula Symbol (type :: gamma)}
    {body : Tower.Tm (n + 1)}
    (state : State reading model objects)
    (meaning : Proves model (objectExtension state type) body formula) :
    Proves model state (.lam body) (.all formula) := by
  obtain ⟨bodyValue, bodyMeaning⟩ := meaning
  let functionValue : Section
      (piFamily (typeFamily model type)
        (truthFamily (formulaMeaning (objectExtension state type) formula))) :=
    fun environment value => bodyValue ⟨environment, value⟩
  refine ⟨mapSection (universalFamilyEquiv full state type formula) functionValue, ?_⟩
  exact Denotes.convert (Denotes.abstraction bodyMeaning)
    (universalFamilyEquiv full state type formula)


theorem Proves.universalElim
    (full : model.FullDomains)
    {gamma : HOL.Ctx Unit} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {type : HOL.Ty Unit} {formula : HOL.Formula Symbol (type :: gamma)}
    {argument : HOL.Term Symbol gamma type}
    {argumentCode : Tower.Tm gamma.length} {function : Tower.Tm n}
    (state : State reading model objects)
    (represented : FormationSensitiveHOLInterface.represent reading argument = some argumentCode)
    (meaning : Proves model state function (.all formula)) :
    Proves model state (.app function (Presentation.subst objects argumentCode))
      (HOL.instantiate argument formula) := by
  obtain ⟨functionValue, functionMeaning⟩ := meaning
  let universalValue : Section
      (piFamily (typeFamily model type)
        (truthFamily (formulaMeaning (objectExtension state type) formula))) :=
    mapSection (fun environment =>
      (universalFamilyEquiv full state type formula environment).symm)
      functionValue
  have universalMeaning : Denotes model state.context function
      (piFamily (typeFamily model type)
        (truthFamily (formulaMeaning (objectExtension state type) formula)))
      universalValue :=
    Denotes.convert functionMeaning (fun environment =>
      (universalFamilyEquiv full state type formula environment).symm)
  have argumentMeaning := representation_denotes argument represented state
  let appliedValue : Section
      (fun environment =>
        truthFamily (formulaMeaning (objectExtension state type) formula)
          ⟨environment, model.denote argument (state.valuation environment)⟩) :=
    fun environment =>
      universalValue environment
        (model.denote argument (state.valuation environment))
  have appliedMeaning : Denotes model state.context
      (.app function (Presentation.subst objects argumentCode))
      (fun environment =>
        truthFamily (formulaMeaning (objectExtension state type) formula)
          ⟨environment, model.denote argument (state.valuation environment)⟩)
      appliedValue :=
    Denotes.application universalMeaning (.underlying argumentMeaning)
  refine ⟨mapSection (instantiationFamilyEquiv state formula argument) appliedValue, ?_⟩
  exact Denotes.convert appliedMeaning
    (instantiationFamilyEquiv state formula argument)


#print axioms propositionSection
#print axioms functionSection
#print axioms Proves.ofUnderlying
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationProofFamilySemantics
