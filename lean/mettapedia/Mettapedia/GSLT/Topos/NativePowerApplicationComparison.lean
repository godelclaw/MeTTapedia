import Mettapedia.GSLT.Topos.NativePowerPiComparison
import Mettapedia.TypeTheory.NativeLocalTypeOperations

/-!
# The native dependent-product readback preserves its evaluation body

The native presentation comparison retains application, not merely carrier
isomorphism. Complete natural sections are decoded through the same earned
Π base-change comparison as the native function operations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.NativePowerApplicationComparison

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open DisplayedPresheafPi DisplayedPresheafPiSubstitution NativeLocalTypeFormers
open NativeLocalTypeOperations

universe u
variable {C : Type u} [Category.{u} C] {P : Cᵒᵖ ⥤ Type u}

private theorem inverse_cast (domain : DisplayedFamily P)
    {first second : DisplayedFamily (totalSpace domain)} (same : first = second)
    (function : (piDisplayed domain first).sections) :
    cast (congrArg (fun family : DisplayedFamily (totalSpace domain) => ↥family.sections) same)
      ((piSectionEquiv domain first).symm function) =
      (piSectionEquiv domain second).symm
        ((Functor.sectionsFunctor P.Elements).map
          (eqToHom (congrArg (piDisplayed domain) same)) function) := by
  cases same
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem uncurry_decode (A : NativeType P) (B : NativeType (totalSpace A.decoded))
    (function : (NativeLocalTypeFormers.pi A B).decoded.sections) :
    (functionEquiv A B).symm function =
      (piSectionEquiv A.decoded B.decoded).symm
        ((Functor.sectionsFunctor P.Elements).map (piDecodeIso A B).hom function) := by
  simp only [functionEquiv, Equiv.symm_trans_apply, piDecodeIso,
    Iso.trans_hom, Iso.symm_hom, Functor.map_comp, types_comp_apply]
  exact inverse_cast A.decoded (parameterBody_decode A B)
    ((Functor.sectionsFunctor P.Elements).map
      (piSubstitutionIso (formerName A B) (parameterDomain A B) (parameterBody A B)).inv function)

end Mettapedia.GSLT.Topos.NativePowerApplicationComparison
