import Mettapedia.GSLT.Logic.RelativePushout

/-!
# Complete relative pushouts against an identity arrow

The chosen candidate is the supplied second span object. The other
candidate's second leg is the actual unique mediator, and all three
factor equations are checked.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.RelativePushout

open _root_.CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C]

theorem hasRelativePushouts_identity_left {source target : C} (arrow : source ⟶ target) :
    HasRelativePushouts (𝟙 source) arrow := by
  intro bound left right square
  let selected : Candidate (𝟙 source) arrow left right :=
    { apex := target
      inl := arrow
      inr := 𝟙 target
      down := right
      comm := (Category.id_comp arrow).trans (Category.comp_id arrow).symm
      fac_left := square.symm.trans (Category.id_comp left)
      fac_right := Category.id_comp right }
  refine ⟨selected, fun other => ⟨other.inr, ?_, ?_⟩⟩
  · exact ⟨(Category.id_comp other.inl).symm.trans other.comm |>.symm,
      Category.id_comp other.inr, other.fac_right⟩
  · intro alternative equations
    exact (Category.id_comp alternative).symm.trans equations.2.1

end Mettapedia.GSLT.RelativePushout
