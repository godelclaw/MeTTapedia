import Mettapedia.GSLT.Topos.NativePowerEvaluationReadout
import Mettapedia.TypeTheory.PresheafNativePropositionSubstitution

/-!
# Native classifier readback at every complete generalized value

The native proposition presentation cast changes neither the returned sieve
nor its truth readout. This makes actual native application readouts available
to the local function-object comparison without a predicate oracle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.Topos.NativePowerNativeReadout

open _root_.CategoryTheory Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafParameterFamilies DisplayedPresheafPi
open NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout PresheafPredicateGenericTruth
open NativePowerPiComparison

universe u
variable {C : Type u} [Category.{u} C] {P : Cᵒᵖ ⥤ Type u}

private theorem section_cast_value {first second : DisplayedFamily P}
    (same : first = second) (witness : first.sections) (point : P.Elements) :
    HEq ((cast (congrArg (fun family : DisplayedFamily P => ↥family.sections) same)
      witness).val point) (witness.val point) := by
  cases same
  rfl

theorem nativeTermEquiv_value (witness : (nativeOmega P).decoded.sections)
    (point : P.Elements) : (nativeTermEquiv P witness).val point = witness.val point := by
  exact eq_of_heq (section_cast_value (nativeOmega_decode P) witness point)

/-- An actual returned native proposition is true exactly when its returned
sieve is maximal; the complete presentation cast retains the value. -/
theorem nativeHolds_member (witness : (nativeOmega P).decoded.sections)
    (world : Cᵒᵖ) (parameter : P.obj world) :
    parameter ∈ (nativeHolds witness).obj world ↔
      witness.val ⟨world, parameter⟩ = (⊤ : Sieve world.unop) := by
  unfold nativeHolds
  exact (holds_member_iff (nativeTermEquiv P witness) world parameter).trans
    (Iff.of_eq (congrArg (fun sieve : Sieve world.unop => sieve = ⊤)
      (nativeTermEquiv_value witness (show P.Elements from ⟨world, parameter⟩))))

/-- The native evaluator's returned truth object has the independent
characteristic-map interpretation, including all complete section values. -/
theorem nativeHolds_characteristic (witness : (nativeOmega P).decoded.sections) :
    nativeHolds witness = (truthPredicate C).preimage
      (sectionCharacteristic (nativeTermEquiv P witness)) := by
  ext world parameter
  change parameter ∈ (holds (nativeTermEquiv P witness)).obj world ↔
    (nativeTermEquiv P witness).val ⟨world, parameter⟩ ∈ (truthPredicate C).obj world
  exact (holds_member_iff _ world parameter).trans (truth_iff_top _ _).symm

theorem propositionFamilyEq (P : Cᵒᵖ ⥤ Type u) :
    (nativeOmega P).decoded = parameterFamily P (omegaFunctor (C := C)) :=
  (nativeOmega_decode P).trans (propositions_constant P)

def propositionBody (witness : (nativeOmega P).decoded.sections) :
    (parameterFamily P (omegaFunctor (C := C))).sections :=
  cast (congrArg (fun family : DisplayedFamily P => ↥family.sections)
    (propositionFamilyEq P)) witness

theorem propositionBody_value (witness : (nativeOmega P).decoded.sections)
    (point : P.Elements) : (propositionBody witness).val point = witness.val point :=
  eq_of_heq (section_cast_value (propositionFamilyEq P) witness point)

theorem nativeHolds_body (witness : (nativeOmega P).decoded.sections) :
    nativeHolds witness = (truthPredicate C).preimage (parameterName (propositionBody witness)) := by
  ext world parameter
  change parameter ∈ (nativeHolds witness).obj world ↔
    (propositionBody witness).val ⟨world, parameter⟩ ∈ (truthPredicate C).obj world
  exact (nativeHolds_member witness world parameter).trans
    ((Iff.of_eq (congrArg (fun sieve : Sieve world.unop => sieve = ⊤)
      (propositionBody_value witness (show P.Elements from ⟨world, parameter⟩)))).symm.trans
        (truth_iff_top _ _).symm)

private theorem inverse_body_cast (domain : DisplayedFamily P)
    {first second : DisplayedFamily (totalSpace domain)} (same : first = second)
    (function : (piDisplayed domain first).sections) :
    cast (congrArg (fun family : DisplayedFamily (totalSpace domain) => ↥family.sections) same)
      ((piSectionEquiv domain first).symm function) =
      (piSectionEquiv domain second).symm
        ((Functor.sectionsFunctor P.Elements).map
          (eqToHom (congrArg (piDisplayed domain) same)) function) := by
  cases same
  simp

/-- Decode the complete native function and codomain with the earned Π
isomorphism and classifier-family equality. -/
noncomputable def decodedFunction (A : NativeType P)
    (function : (NativeLocalTypeFormers.pi A
      (nativeOmega (totalSpace A.decoded))).decoded.sections) :
    (piDisplayed A.decoded (parameterFamily (totalSpace A.decoded)
      (omegaFunctor (C := C)))).sections :=
  (Functor.sectionsFunctor P.Elements).map
    ((piDecodeIso A (nativeOmega (totalSpace A.decoded))).hom ≫
      eqToHom (congrArg (piDisplayed A.decoded)
        (propositionFamilyEq (totalSpace A.decoded)))) function

theorem native_uncurry_body (A : NativeType P)
    (function : (NativeLocalTypeFormers.pi A
      (nativeOmega (totalSpace A.decoded))).decoded.sections) :
    propositionBody ((functionEquiv A (nativeOmega (totalSpace A.decoded))).symm function) =
      (piSectionEquiv A.decoded (parameterFamily (totalSpace A.decoded)
        (omegaFunctor (C := C)))).symm (decodedFunction A function) := by
  rw [propositionBody, NativePowerApplicationComparison.uncurry_decode]
  have result := inverse_body_cast A.decoded
    (propositionFamilyEq (totalSpace A.decoded))
    ((Functor.sectionsFunctor P.Elements).map
      (piDecodeIso A (nativeOmega (totalSpace A.decoded))).hom function)
  simpa only [decodedFunction, Functor.map_comp, types_comp_apply] using result

theorem native_uncurry_readout (A : NativeType P)
    (function : (NativeLocalTypeFormers.pi A
      (nativeOmega (totalSpace A.decoded))).decoded.sections) :
    nativeHolds ((functionEquiv A (nativeOmega (totalSpace A.decoded))).symm function) =
      (truthPredicate C).preimage (parameterName
        ((piSectionEquiv A.decoded (parameterFamily (totalSpace A.decoded)
          (omegaFunctor (C := C)))).symm (decodedFunction A function))) := by
  rw [nativeHolds_body, native_uncurry_body]

end Mettapedia.GSLT.Topos.NativePowerNativeReadout
