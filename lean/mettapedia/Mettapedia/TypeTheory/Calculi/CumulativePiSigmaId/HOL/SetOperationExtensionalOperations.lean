import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationExtensionalApplications
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeProofCompilerCompleteness

/-!
# All eight proof operations at the common material signature

The six constructed predicate-equality operations run in the extended declared
presentation. The two additional capabilities apply the explicitly typed
extensionality constants. Universal proof decoding and the proved equality
comparison prepare the pointwise premise at its exact dependent product.
Every optional operation is computationally available, with its typing and
substitution laws; this algebra can therefore host every retained HOL rule.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationExtensionalOperations
open Presentation Presentation.FormationSensitive FormationSensitiveHOLInterface
open Mettapedia.Logic
open HOLNativeGenericProofCompiler
open SetOperationExtensionalProfile
open SetOperationExtensionalApplications
open SetOperationSignature (proofName)

private def constructive : Operations reading proofName :=
  HOLPredicateEqualityOperations.operations signature proofName fresh

def rawOperations : RawOperations Unit :=
  { constructive.raw with
    propositionExtensionality := fun left right forward backward =>
      some (propositionExtensionalityApp left right forward backward)
    functionExtensionality := fun domain codomain function other pointwise =>
      some (functionExtensionalityApp domain codomain function other pointwise) }

theorem pointwise_conversion {n : Nat} (domain codomain : HOL.Ty Unit)
    (function other : Tower.Tm n) :
    Conv rules.headEq
      (proof (FormationSensitiveHOLGenericProofFamily.universalProposition reading domain
        (.lam (rawEquality reading codomain
          (.app (rename wk function) (.var 0)) (.app (rename wk other) (.var 0))))))
      (pointwiseEquality (typeAt SetOperationSignature.types n domain)
        (typeAt SetOperationSignature.types n codomain) function other) rules.computation := by
  have universal := FormationSensitiveHOLGenericProofFamily.universal_lambda_conversion
    reading proofName domain (rawEquality reading codomain
      (.app (rename wk function) (.var 0)) (.app (rename wk other) (.var 0)))
  have body : Conv rules.headEq
      (proof (rawEquality reading codomain
        (.app (rename wk function) (.var 0)) (.app (rename wk other) (.var 0))))
      (proof (rawEqualityAt (rename wk (typeAt SetOperationSignature.types n codomain))
        (.app (rename wk function) (.var 0)) (.app (rename wk other) (.var 0)))) rules.computation := by
    rw [typeAt_rename, rawEqualityAt_typeAt]
    exact HOLPredicateEqualityOperations.equality_conversion signature proofName codomain _ _
  exact .trans _ _ _ universal (Conv.congPi (.refl _) body)

def operations : Operations reading proofName where
  fresh := fresh
  target := rules
  proofMorphism := constructive.proofMorphism
  raw := rawOperations
  reflexivity_typed := constructive.reflexivity_typed
  symmetry_typed := constructive.symmetry_typed
  transitivity_typed := constructive.transitivity_typed
  propositionForward_typed := constructive.propositionForward_typed
  functionCongruence_typed := constructive.functionCongruence_typed
  argumentCongruence_typed := constructive.argumentCongruence_typed
  propositionExtensionality_typed := by
    intro n context left right forward backward out emitted leftTyped rightTyped forwardTyped backwardTyped
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    have left := HOLPredicateEqualityOperations.includeSourceTyping signature proofName leftTyped
    have right := HOLPredicateEqualityOperations.includeSourceTyping signature proofName rightTyped
    apply HOLPredicateEqualityOperations.equality_from_predicate signature proofName fresh left right
    simpa only [← rawEqualityAt_typeAt, reading_types, typeAt_prop, proof] using
      propositionExtensionalityApp_typed left right forwardTyped backwardTyped
  functionExtensionality_typed := by
    intro n context domain codomain function other pointwise out emitted functionTyped otherTyped pointwiseTyped
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    have domainTyped := includeSourceTyping (SetOperationSignature.simple_type_formed domain context)
    have codomainTyped := includeSourceTyping (SetOperationSignature.simple_type_formed codomain context)
    have functionInTarget := HOLPredicateEqualityOperations.includeSourceTyping signature proofName functionTyped
    have otherInTarget := HOLPredicateEqualityOperations.includeSourceTyping signature proofName otherTyped
    have functionArrow : Typing rules context function
        (arrow (typeAt SetOperationSignature.types n domain) (typeAt SetOperationSignature.types n codomain)) := by
      simpa only [arrow_typeAt, reading_types] using functionInTarget
    have otherArrow : Typing rules context other
        (arrow (typeAt SetOperationSignature.types n domain) (typeAt SetOperationSignature.types n codomain)) := by
      simpa only [arrow_typeAt, reading_types] using otherInTarget
    have prepared := Typing.conv pointwiseTyped
      (pointwiseEquality_formed domainTyped codomainTyped functionArrow otherArrow)
      (.sort Tower.zero) (pointwise_conversion domain codomain function other)
    have applied := functionExtensionalityApp_typed domainTyped codomainTyped functionArrow otherArrow prepared
    apply HOLPredicateEqualityOperations.equality_from_predicate signature proofName fresh functionInTarget otherInTarget
    simpa only [arrow_typeAt, rawEqualityAt_typeAt, reading_types, proof] using applied

theorem total : operations.raw.Total := by
  constructor <;> intros <;> rfl

@[simp] theorem emits_reflexivity {n : Nat} : operations.raw.reflexivity (n := n) =
    some HOLPredicateEqualityDerived.reflTerm := rfl

@[simp] theorem emits_symmetry {n : Nat} (type : HOL.Ty Unit) (left comparison : Tower.Tm n) :
    operations.raw.symmetry type left comparison =
      some (HOLPredicateEqualityDerived.symmetry signature type left comparison) := rfl

@[simp] theorem emits_transitivity {n : Nat} (type : HOL.Ty Unit) (left first second : Tower.Tm n) :
    operations.raw.transitivity type left first second =
      some (HOLPredicateEqualityDerived.transitivity signature type left first second) := rfl

@[simp] theorem emits_propositionExtensionality {n : Nat} (left right forward backward : Tower.Tm n) :
    operations.raw.propositionExtensionality left right forward backward =
      some (propositionExtensionalityApp left right forward backward) := rfl

@[simp] theorem emits_propositionForward {n : Nat} (comparison : Tower.Tm n) :
    operations.raw.propositionForward comparison = some (HOLPredicateEqualityDerived.propForward comparison) := rfl

@[simp] theorem emits_functionCongruence {n : Nat} (type : HOL.Ty Unit) (function argument comparison : Tower.Tm n) :
    operations.raw.functionCongruence type function argument comparison =
      some (HOLPredicateEqualityDerived.functionCongruence signature type function argument comparison) := rfl

@[simp] theorem emits_argumentCongruence {n : Nat} (type : HOL.Ty Unit) (function argument comparison : Tower.Tm n) :
    operations.raw.argumentCongruence type function argument comparison =
      some (HOLPredicateEqualityDerived.congruence signature type function argument comparison) := rfl

@[simp] theorem emits_functionExtensionality {n : Nat} (domain codomain function other pointwise : Tower.Tm n) :
    operations.raw.functionExtensionality domain codomain function other pointwise =
      some (functionExtensionalityApp domain codomain function other pointwise) := rfl

theorem natural : operations.raw.Natural := by
  constructor <;> intros <;>
    simp [operations, rawOperations, constructive, HOLPredicateEqualityOperations.operations,
      HOLPredicateEqualityOperations.rawOperations, propositionExtensionalityApp,
      functionExtensionalityApp, subst]

#print axioms pointwise_conversion
#print axioms operations
#print axioms total
#print axioms natural
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationExtensionalOperations
