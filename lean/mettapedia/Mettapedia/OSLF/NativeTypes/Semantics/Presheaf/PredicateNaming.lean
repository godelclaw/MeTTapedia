import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.FixedPointEvaluation
import Mettapedia.TypeTheory.ContextualPiEta

/-!
# Complete native predicate naming and generic application

A supplied native function gives a genuine section of the predicate binder.
Substitution of its generic variable recovers that exact supplied function.
The corresponding application retains the complete argument and predicate
readout. This is the actual CwF beta law, not a global predicate lookup.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateNaming

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open PredicateVariables NativeLocalTypeFormers NativeLocalTypeOperations
open ContextualLocalUniverses ContextualModelTelescopes
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open ContextualTypeOperations

universe u
variable {C : Type u} [Category.{u} C] {P : Cᵒᵖ ⥤ Type u}

theorem projection_section (A : NativeType P) (value : A.decoded.sections) :
    sectionLift A.decoded value ≫ totalProjection A.decoded = 𝟙 P := by
  ext world parameter
  rfl

theorem generic_value_beta (A : NativeType P) (value : A.decoded.sections) :
    Value.substitute
      (⟨A.reindex (totalProjection A.decoded), (NativeModel C).toCwf.vz A⟩ :
        NativeValue (totalSpace A.decoded)) (sectionLift A.decoded value) =
      ⟨A, value⟩ := by
  apply Sigma.ext
  · change (A.reindex (totalProjection A.decoded)).reindex (sectionLift A.decoded value) = A
    rw [← LocalType.reindex_comp]
    change A.reindex (sectionLift A.decoded value ≫ totalProjection A.decoded) = A
    rw [projection_section]
    exact LocalType.reindex_id A
  · exact vz_selfExtend (C := (NativeModel C).toCwf) value

theorem weakened_generic_beta (A : NativeType P)
    (function : (predicate A).decoded.sections) :
    (⟨predicate ((argumentType A).reindex (sectionLift (predicate A).decoded function)),
      weakenFunction (argumentType A) (generic A)
        (sectionLift (predicate A).decoded function)⟩ : NativeValue P) =
      ⟨predicate A, function⟩ := by
  have first : (⟨(predicate A).reindex (totalProjection (predicate A).decoded),
      (NativeModel C).toCwf.vz (predicate A)⟩ :
        NativeValue (totalSpace (predicate A).decoded)) =
      ⟨predicate (argumentType A), generic A⟩ :=
    nativeValue_cast (predicate_reindex A _) _
  have substituted := congrArg (fun value : NativeValue (totalSpace (predicate A).decoded) =>
    value.substitute (sectionLift (predicate A).decoded function)) first
  have converted := nativeValue_cast
    (predicate_reindex (argumentType A) (sectionLift (predicate A).decoded function))
    (ContextualLocalUniverses.substituteTerm (type := predicate (argumentType A))
      (generic A) (sectionLift (predicate A).decoded function))
  exact converted.symm.trans (substituted.symm.trans (generic_value_beta (predicate A) function))

theorem argument_beta (A : NativeType P) (value : A.decoded.sections)
    (function : (predicate A).decoded.sections) :
    (⟨(argumentType A).reindex (sectionLift (predicate A).decoded function),
      ContextualLocalUniverses.substituteTerm (type := argumentType A)
        (ContextualLocalUniverses.substituteTerm (type := A) value
          (totalProjection (predicate A).decoded))
        (sectionLift (predicate A).decoded function)⟩ : NativeValue P) = ⟨A, value⟩ := by
  change Value.substitute (Value.substitute (⟨A, value⟩ : NativeValue P)
    (totalProjection (predicate A).decoded)) (sectionLift (predicate A).decoded function) = _
  rw [← Value.substitute_composition]
  change Value.substitute (⟨A, value⟩ : NativeValue P)
    (sectionLift (predicate A).decoded function ≫ totalProjection (predicate A).decoded) = _
  rw [projection_section]
  exact Value.substitute_identity _

theorem application_values_equal {first second : NativeType P}
    (beforeFunction : (predicate first).decoded.sections)
    (afterFunction : (predicate second).decoded.sections)
    (beforeArgument : first.decoded.sections) (afterArgument : second.decoded.sections)
    (functions : (⟨predicate first, beforeFunction⟩ : NativeValue P) =
      ⟨predicate second, afterFunction⟩)
    (arguments : (⟨first, beforeArgument⟩ : NativeValue P) = ⟨second, afterArgument⟩) :
    nativeHolds (FixedPointSyntax.applicationValue first beforeFunction beforeArgument) =
      nativeHolds (FixedPointSyntax.applicationValue second afterFunction afterArgument) := by
  have types := congrArg Sigma.fst arguments
  cases types
  have functionSame := eq_of_heq (Sigma.mk.inj functions).2
  have argumentSame := eq_of_heq (Sigma.mk.inj arguments).2
  rw [functionSame, argumentSame]

theorem value_weaken_beta (binder : NativeType P) (value : NativeValue P)
    (argument : binder.decoded.sections) :
    (value.substitute (totalProjection binder.decoded)).substitute
      (sectionLift binder.decoded argument) = value := by
  rw [← Value.substitute_composition]
  change value.substitute (sectionLift binder.decoded argument ≫ totalProjection binder.decoded) = value
  rw [projection_section]
  exact Value.substitute_identity _

theorem weakened_function_beta (A : NativeType P)
    (function : (predicate A).decoded.sections) (argument : A.decoded.sections) :
    (⟨predicate ((A.reindex (totalProjection A.decoded)).reindex
        (sectionLift A.decoded argument)),
      weakenFunction (A.reindex (totalProjection A.decoded))
        (weakenFunction A function (totalProjection A.decoded))
        (sectionLift A.decoded argument)⟩ : NativeValue P) =
      ⟨predicate A, function⟩ := by
  have first := nativeValue_cast (predicate_reindex A (totalProjection A.decoded))
    (ContextualLocalUniverses.substituteTerm (type := predicate A) function (totalProjection A.decoded))
  have substituted := congrArg (fun value : NativeValue (totalSpace A.decoded) =>
    value.substitute (sectionLift A.decoded argument)) first
  have converted := nativeValue_cast
    (predicate_reindex (A.reindex (totalProjection A.decoded)) (sectionLift A.decoded argument))
    (ContextualLocalUniverses.substituteTerm
      (type := predicate (A.reindex (totalProjection A.decoded)))
      (weakenFunction A function (totalProjection A.decoded)) (sectionLift A.decoded argument))
  exact converted.symm.trans (substituted.symm.trans
    (value_weaken_beta A (⟨predicate A, function⟩ : NativeValue P) argument))

theorem bound_tested (A : NativeType P) (value : A.decoded.sections) :
    (boundMembership A).preimage
      (sectionLift (argumentType A).decoded
        (ContextualLocalUniverses.substituteTerm (type := A) value
          (totalProjection (predicate A).decoded))) =
      FixedPointEvaluation.testedMembership A value := by
  rw [boundMembership, ← application_substitution]
  exact application_values_equal _ _ _ _
    (weakened_function_beta (argumentType A) (generic A) _)
    (generic_value_beta (argumentType A) _)

theorem generic_application_body (A : NativeType P)
    (function : (predicate A).decoded.sections) :
    nativeHolds (FixedPointSyntax.applicationValue
      (A.reindex (totalProjection A.decoded))
      (weakenFunction A function (totalProjection A.decoded))
      ((NativeModel C).toCwf.vz A)) =
        nativeHolds ((functionEquiv A (nativeOmega (totalSpace A.decoded))).symm function) := by
  rw [FixedPointSyntax.applicationValue_holds, functionBody_substitution,
    PresheafNativePropositionSubstitution.nativeHolds_substituteNative,
    ← Subfunctor.preimage_comp]
  have square : sectionLift (A.reindex (totalProjection A.decoded)).decoded
      ((NativeModel C).toCwf.vz A) ≫ totalReindexMap (totalProjection A.decoded) A.decoded =
        𝟙 (totalSpace A.decoded) :=
    ContextualPiEta.lifted_generic_identity (C := (NativeModel C).toCwf) A
  rw [square]
  ext world value
  rfl

theorem bound_body (A : NativeType P) :
    boundMembership A =
      nativeHolds ((functionEquiv (argumentType A)
        (nativeOmega (totalSpace (argumentType A).decoded))).symm (generic A)) :=
  generic_application_body (argumentType A) (generic A)

theorem named_argument_type (A : NativeType P) (function : (predicate A).decoded.sections) :
    (argumentType A).reindex (sectionLift (predicate A).decoded function) = A := by
  rw [argumentType, ← ContextualLocalUniverses.LocalType.reindex_comp]
  change A.reindex (sectionLift (predicate A).decoded function ≫
    totalProjection (predicate A).decoded) = A
  rw [projection_section]
  exact ContextualLocalUniverses.LocalType.reindex_id A

def typeContext {first second : NativeType P} (same : first = second) :
    totalSpace first.decoded ≅ totalSpace second.decoded :=
  eqToIso (congrArg (fun type : NativeType P => totalSpace type.decoded) same)

theorem body_values_equal {first second : NativeType P} (same : first = second)
    (before : (predicate first).decoded.sections) (after : (predicate second).decoded.sections)
    (functions : (⟨predicate first, before⟩ : NativeValue P) = ⟨predicate second, after⟩) :
    nativeHolds ((functionEquiv first (nativeOmega (totalSpace first.decoded))).symm before) =
      (nativeHolds ((functionEquiv second (nativeOmega (totalSpace second.decoded))).symm after)).preimage
        (typeContext same).hom := by
  cases same
  have equal := eq_of_heq (Sigma.mk.inj functions).2
  rw [equal]
  ext world value
  rfl

theorem named_body (A : NativeType P) (meaning : Subfunctor (totalSpace A.decoded)) :
    (boundMembership A).preimage
      (totalReindexMap (sectionLift (predicate A).decoded
        (NativeLocalTypeOperations.lam (nativeQuote meaning))) (argumentType A).decoded) =
      meaning.preimage (typeContext
        (named_argument_type A (NativeLocalTypeOperations.lam (nativeQuote meaning)))).hom := by
  rw [bound_body, ← PresheafNativePropositionSubstitution.nativeHolds_substituteNative,
    ← functionBody_substitution]
  rw [body_values_equal (named_argument_type A (NativeLocalTypeOperations.lam (nativeQuote meaning)))
    _ _ (weakened_generic_beta A (NativeLocalTypeOperations.lam (nativeQuote meaning)))]
  unfold NativeLocalTypeOperations.lam
  rw [Equiv.symm_apply_apply, nativeHolds_nativeQuote]

private theorem typeContext_value {first second : NativeType P} (same : first = second)
    (world : Cᵒᵖ) (value : (totalSpace first.decoded).obj world) :
    ((typeContext same).hom.app world value).1 = value.1 ∧
      HEq ((typeContext same).hom.app world value).2 value.2 := by
  cases same
  exact ⟨rfl, HEq.rfl⟩

theorem named_argument_projection (A : NativeType P)
    (function : (predicate A).decoded.sections) :
    totalReindexMap (sectionLift (predicate A).decoded function) (argumentType A).decoded ≫
      FixedPointEvaluation.atomProjection A =
        (typeContext (named_argument_type A function)).hom := by
  ext world value
  have components := typeContext_value (named_argument_type A function) world value
  exact Sigma.ext components.1.symm components.2.symm

/-- The generic local predicate, pulled back to an actual supplied native
function, computes that function's complete application readout. -/
theorem tested_naming (A : NativeType P) (value : A.decoded.sections)
    (function : (predicate A).decoded.sections) :
    (FixedPointEvaluation.testedMembership A value).preimage
      (sectionLift (predicate A).decoded function) =
        nativeHolds (FixedPointSyntax.applicationValue A function value) := by
  rw [FixedPointEvaluation.testedMembership, ← application_substitution]
  exact application_values_equal _ _ _ _ (weakened_generic_beta A function)
    (argument_beta A value function)

/-- Reifying an independently specified complete predicate and substituting
its name into the binder recovers the predicate at the supplied argument. -/
theorem tested_reified (A : NativeType P) (value : A.decoded.sections)
    (meaning : Subfunctor (totalSpace A.decoded)) :
    (FixedPointEvaluation.testedMembership A value).preimage
      (sectionLift (predicate A).decoded (NativeLocalTypeOperations.lam (nativeQuote meaning))) =
        meaning.preimage (sectionLift A.decoded value) := by
  rw [tested_naming, PredicateReification.application_reified]

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateNaming
