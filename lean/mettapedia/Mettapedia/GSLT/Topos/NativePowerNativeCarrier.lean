import Mettapedia.GSLT.Topos.NativePowerNativeReadout

/-!
# Native predicate application on a closed carrier

The carrier comparison transports the complete dependent evaluation body.
The result is generic membership in the actual local power presheaf, pulled
back through the actual native function and argument context maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.Topos.NativePowerNativeCarrier

open _root_.CategoryTheory Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafParameterFamilies DisplayedPresheafPi
open NativeLocalTypeFormers NativeLocalTypeOperations
open NativePowerNativeReadout NativePowerEvaluationReadout
open PresheafNativePropositionReadout PresheafPredicateGenericTruth

universe u
variable {C : Type u} [Category.{u} C] {P : Cᵒᵖ ⥤ Type u}

noncomputable abbrev powerFamily (domain : DisplayedFamily P) :=
  piDisplayed domain (parameterFamily (totalSpace domain) (omegaFunctor (C := C)))

def carrierContext {first second : DisplayedFamily P} (same : first = second) :
    totalSpace first ≅ totalSpace second := eqToIso (congrArg totalSpace same)

noncomputable def powerFamilyComparison {first second : DisplayedFamily P} (same : first = second) :
    powerFamily first ≅ powerFamily second := eqToIso (congrArg powerFamily same)

theorem uncurry_domain_comparison {first second : DisplayedFamily P} (same : first = second)
    (function : (powerFamily first).sections) :
    ((truthPredicate C).preimage (parameterName
      ((piSectionEquiv second (parameterFamily (totalSpace second)
        (omegaFunctor (C := C)))).symm
        ((Functor.sectionsFunctor P.Elements).map
          (powerFamilyComparison same).hom function)))).preimage (carrierContext same).hom =
      (truthPredicate C).preimage (parameterName
        ((piSectionEquiv first (parameterFamily (totalSpace first)
          (omegaFunctor (C := C)))).symm function)) := by
  cases same
  simp only [powerFamilyComparison, carrierContext, eqToIso_refl, Iso.refl_hom]
  ext world parameter
  rfl

noncomputable def representedFunction (A : Cᵒᵖ ⥤ Type u) (native : NativeType P)
    (constant : native.decoded = parameterFamily P A)
    (function : (NativeLocalTypeFormers.pi native
      (nativeOmega (totalSpace native.decoded))).decoded.sections) :
    (NativePowerPiComparison.dependent P A (omegaFunctor (C := C))).sections :=
  (Functor.sectionsFunctor P.Elements).map (powerFamilyComparison constant).hom
    (decodedFunction native function)

noncomputable def evaluation (A : Cᵒᵖ ⥤ Type u) (native : NativeType P)
    (constant : native.decoded = parameterFamily P A)
    (function : (NativeLocalTypeFormers.pi native
      (nativeOmega (totalSpace native.decoded))).decoded.sections) :
    totalSpace native.decoded ⟶ NativePowerPredicates.product A :=
  (carrierContext constant).hom ≫
    NativePowerEvaluationReadout.evaluation P A (representedFunction A native constant function)

/-- Full native application-body readout agrees with independent local
predicate membership, including its actual argument/context transport. -/
theorem native_membership (A : Cᵒᵖ ⥤ Type u) (native : NativeType P)
    (constant : native.decoded = parameterFamily P A)
    (function : (NativeLocalTypeFormers.pi native
      (nativeOmega (totalSpace native.decoded))).decoded.sections) :
    nativeHolds ((functionEquiv native (nativeOmega (totalSpace native.decoded))).symm function) =
      (NativePowerPredicates.membership A).preimage (evaluation A native constant function) := by
  rw [native_uncurry_readout]
  rw [evaluation, Subfunctor.preimage_comp,
    NativePowerEvaluationReadout.evaluation_membership]
  exact (uncurry_domain_comparison constant (decodedFunction native function)).symm

end Mettapedia.GSLT.Topos.NativePowerNativeCarrier
