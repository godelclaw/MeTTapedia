import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticVectors

/-! # Pointwise coherence for actual displayed-section casts -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticCasts

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open DisplayedPresheafTransport

universe u
variable {W : Type u} [Category.{u} W] {P : Wᵒᵖ ⥤ Type u}

theorem sectionValue_heq {first second : DisplayedFamily.{u,u,u,u} P}
    (families : first = second) {left : first.sections} {right : second.sections}
    (sections : HEq left right) (point : P.Elements) :
    HEq (left.val point) (right.val point) := by
  cases families
  cases sections
  rfl

theorem castIsoValue_heq {first second : DisplayedFamily.{u,u,u,u} P}
    (families : first = second) (point : P.Elements) (value : first.obj point) :
    HEq ((eqToIso families).hom.app point value) value := by
  cases families
  rfl

open ContextualModelTelescopes ContextualLocalUniverses NativeLocalTypeFormers
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

theorem variable_cast {S : Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Symbols}
    (model : Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.ModelData S W)
    {n : Nat} (context : Scope W n) (position : Fin n) (A B : NativeType context.1)
    (value : A.decoded.sections) (lookup : context.2.lookup position = ⟨A,value⟩) (types : A = B) :
    model.evaluateTerm context (.var position) =
      some ⟨B, cast (congrArg ((NativeModel W).toCwf.Tm context.1) types) value⟩ := by
  change some (context.2.lookup position) = _
  apply congrArg some
  apply lookup.trans
  apply Sigma.ext types
  exact (cast_heq _ _).symm

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticCasts
