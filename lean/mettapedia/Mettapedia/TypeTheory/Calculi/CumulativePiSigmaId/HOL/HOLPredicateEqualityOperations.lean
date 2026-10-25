import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLPredicateEqualityDerived
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerSubstitution

/-!
# A constructive proof-operation algebra for predicate equality

Six native equality operations are constructed from implication, quantification,
lambda abstraction and application. Their exact typing laws instantiate the
existing generic HOL compiler interface, and their substitution laws give its
operation naturality. Proposition and function extensionality remain unavailable
in this algebra; adding their declarations is a separate object-theory extension.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLPredicateEqualityOperations
open Presentation Presentation.FormationSensitive FormationSensitiveHOLInterface
open FormationSensitiveHOLGenericProofFamily (proof rawImp)
open HOLPredicateEqualityRules
open HOLNativeGenericProofCompiler
open Mettapedia.Logic
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
variable (source : LogicalSignature Base Const) (proofName : DeclName)

theorem includeSourceTyping {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing source.rules context term type) :
    Typing (rules source proofName) context term type :=
  FormationSensitiveHOLGenericProofFamily.include_typed
    (HOLPredicateEqualitySignature.signature source) proofName typed

theorem includeSourceConversion {n : Nat} {left right : Tower.Tm n}
    (converted : Conv source.rules.headEq left right source.rules.computation) :
    Conv (rules source proofName).headEq left right (rules source proofName).computation := by
  have lifted := converted.mapHead (targetEq := (rules source proofName).headEq)
    (fun head => head)
    (FormationSensitiveHOLGenericProofFamily.sourceMorphism
      (HOLPredicateEqualitySignature.signature source) proofName).headEq
    (FormationSensitiveHOLGenericProofFamily.sourceMorphism
      (HOLPredicateEqualitySignature.signature source) proofName).computation
  simpa only [Tm.mapHead_id] using lifted

theorem equality_proposition {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base}
    {left right : Tower.Tm n}
    (leftTyped : Typing (rules source proofName) context left (typeAt source.types n type))
    (rightTyped : Typing (rules source proofName) context right (typeAt source.types n type)) :
    Typing (rules source proofName) context
      (rawEquality (HOLPredicateEqualitySignature.signature source) type left right)
      (typeAt source.types n .prop) := by
  have operation := includeSourceTyping source proofName
    (closed_typed (HOLPredicateEqualitySignature.equality_typed source type) context)
  simp only [liftClosed, typeAt_rename] at operation
  exact application_typed source proofName
    (application_typed source proofName operation leftTyped) rightTyped

theorem equality_conversion {n : Nat} (type : HOL.Ty Base) (left right : Tower.Tm n) :
    Conv (rules source proofName).headEq
      (proof proofName (rawEquality (HOLPredicateEqualitySignature.signature source) type left right))
      (proof proofName (HOLPredicateEqualitySignature.raw source type left right))
      (rules source proofName).computation :=
  Conv.congApp (.refl _) (includeSourceConversion source proofName
    (HOLPredicateEqualitySignature.application_conversion source type left right))

theorem equality_to_predicate (fresh : source.rules.constantType proofName = none)
    {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base} {left right term : Tower.Tm n}
    (leftTyped : Typing (rules source proofName) context left (typeAt source.types n type))
    (rightTyped : Typing (rules source proofName) context right (typeAt source.types n type))
    (typed : Typing (rules source proofName) context term
      (proof proofName (rawEquality (HOLPredicateEqualitySignature.signature source) type left right))) :
    Typing (rules source proofName) context term
      (proof proofName (HOLPredicateEqualitySignature.raw source type left right)) :=
  .conv typed
    (FormationSensitiveHOLGenericProofFamily.proof_formed
      (HOLPredicateEqualitySignature.signature source) proofName fresh
      (raw_typed source proofName leftTyped rightTyped))
    (.sort Tower.zero) (equality_conversion source proofName type left right)

theorem equality_from_predicate (fresh : source.rules.constantType proofName = none)
    {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base} {left right term : Tower.Tm n}
    (leftTyped : Typing (rules source proofName) context left (typeAt source.types n type))
    (rightTyped : Typing (rules source proofName) context right (typeAt source.types n type))
    (typed : Typing (rules source proofName) context term
      (proof proofName (HOLPredicateEqualitySignature.raw source type left right))) :
    Typing (rules source proofName) context term
      (proof proofName (rawEquality (HOLPredicateEqualitySignature.signature source) type left right)) :=
  .conv typed
    (FormationSensitiveHOLGenericProofFamily.proof_formed
      (HOLPredicateEqualitySignature.signature source) proofName fresh
      (equality_proposition source proofName leftTyped rightTyped))
    (.sort Tower.zero) (.symm _ _ (equality_conversion source proofName type left right))

theorem equality_of_conversion (fresh : source.rules.constantType proofName = none)
    {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base} {left right : Tower.Tm n}
    (leftTyped : Typing (rules source proofName) context left (typeAt source.types n type))
    (rightTyped : Typing (rules source proofName) context right (typeAt source.types n type))
    (converted : Conv (rules source proofName).headEq left right (rules source proofName).computation) :
    Typing (rules source proofName) context HOLPredicateEqualityDerived.reflTerm
      (proof proofName (rawEquality (HOLPredicateEqualitySignature.signature source) type left right)) :=
  .conv (equality_from_predicate source proofName fresh leftTyped leftTyped
      (reflexivity source proofName fresh leftTyped))
    (FormationSensitiveHOLGenericProofFamily.proof_formed
      (HOLPredicateEqualitySignature.signature source) proofName fresh
      (equality_proposition source proofName leftTyped rightTyped))
    (.sort Tower.zero) (Conv.congApp (.refl _) (Conv.congApp (.refl _) converted))

def rawOperations : RawOperations Base where
  reflexivity := some HOLPredicateEqualityDerived.reflTerm
  symmetry := fun type left comparison =>
    some (HOLPredicateEqualityDerived.symmetry source type left comparison)
  transitivity := fun type left first second =>
    some (HOLPredicateEqualityDerived.transitivity source type left first second)
  propositionExtensionality := fun _ _ _ _ => none
  propositionForward := fun comparison => some (HOLPredicateEqualityDerived.propForward comparison)
  functionCongruence := fun type function argument comparison =>
    some (HOLPredicateEqualityDerived.functionCongruence source type function argument comparison)
  argumentCongruence := fun type function argument comparison =>
    some (HOLPredicateEqualityDerived.congruence source type function argument comparison)
  functionExtensionality := fun _ _ _ _ _ => none

def operations (fresh : source.rules.constantType proofName = none) :
    Operations (HOLPredicateEqualitySignature.signature source) proofName where
  fresh := fresh
  target := rules source proofName
  proofMorphism := Rules.Morphism.identity _
  raw := rawOperations source
  reflexivity_typed := by
    intro n context type left right out emitted leftTyped rightTyped converted
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    exact equality_of_conversion source proofName fresh
      (includeSourceTyping source proofName leftTyped)
      (includeSourceTyping source proofName rightTyped) converted
  symmetry_typed := by
    intro n context type left right comparison out emitted leftTyped rightTyped comparisonTyped
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    have left := includeSourceTyping source proofName leftTyped
    have right := includeSourceTyping source proofName rightTyped
    exact equality_from_predicate source proofName fresh right left
      (HOLPredicateEqualityDerived.symmetry_typed source proofName fresh left right
        (equality_to_predicate source proofName fresh left right comparisonTyped))
  transitivity_typed := by
    intro n context type left middle right first second out emitted leftTyped middleTyped rightTyped firstTyped secondTyped
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    have left := includeSourceTyping source proofName leftTyped
    have middle := includeSourceTyping source proofName middleTyped
    have right := includeSourceTyping source proofName rightTyped
    exact equality_from_predicate source proofName fresh left right
      (HOLPredicateEqualityDerived.transitivity_typed source proofName fresh left middle right
        (equality_to_predicate source proofName fresh left middle firstTyped)
        (equality_to_predicate source proofName fresh middle right secondTyped))
  propositionExtensionality_typed := by
    intro n context left right forward backward out emitted
    contradiction
  propositionForward_typed := by
    intro n context left right comparison out emitted leftTyped rightTyped comparisonTyped
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    have left := includeSourceTyping source proofName leftTyped
    have right := includeSourceTyping source proofName rightTyped
    exact HOLPredicateEqualityDerived.propForward_typed source proofName fresh left right
      (equality_to_predicate source proofName fresh left right comparisonTyped)
  functionCongruence_typed := by
    intro n context domain result function other argument comparison out emitted functionTyped otherTyped argumentTyped comparisonTyped
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    have function := includeSourceTyping source proofName functionTyped
    have other := includeSourceTyping source proofName otherTyped
    have argument := includeSourceTyping source proofName argumentTyped
    exact equality_from_predicate source proofName fresh
      (application_typed source proofName function argument)
      (application_typed source proofName other argument)
      (HOLPredicateEqualityDerived.functionCongruence_typed source proofName fresh function other argument
        (equality_to_predicate source proofName fresh function other comparisonTyped))
  argumentCongruence_typed := by
    intro n context domain result function left right comparison out emitted functionTyped leftTyped rightTyped comparisonTyped
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    have function := includeSourceTyping source proofName functionTyped
    have left := includeSourceTyping source proofName leftTyped
    have right := includeSourceTyping source proofName rightTyped
    exact equality_from_predicate source proofName fresh
      (application_typed source proofName function left)
      (application_typed source proofName function right)
      (HOLPredicateEqualityDerived.congruence_typed source proofName fresh function left right
        (equality_to_predicate source proofName fresh left right comparisonTyped))
  functionExtensionality_typed := by
    intro n context domain codomain function other pointwise out emitted
    contradiction

theorem natural : (rawOperations source).Natural := by
  constructor <;> intros <;> simp [rawOperations]

#print axioms operations
#print axioms natural
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLPredicateEqualityOperations
