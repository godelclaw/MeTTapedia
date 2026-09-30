import Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphism
import Mettapedia.GraphTheory.FourColor.OpenTangleClosedWitness

/-!
# Colouring witnesses under exact open-tangle representation changes

The dart isomorphism transports a genuine colouring and reads back every
boundary colour. Inverse transport recovers the original assignment. These
are representation changes, not graph reductions or Kempe recolouring steps.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphism.Iso

open GoertzelV24OpenTangleComposition OpenTangleClosedWitness

variable {V I B W J C : Type*}
  {P : OpenTangleData V I B} {Q : OpenTangleData W J C} (e : Iso P Q)

def mapColor (c : I ⊕ B → Color) : J ⊕ C → Color := c ∘ e.darts.symm

@[simp] theorem mapColor_dart (c : I ⊕ B → Color) (d : I ⊕ B) :
    e.mapColor c (e.darts d) = c d := by simp [mapColor]

@[simp] theorem mapColor_boundary (c : I ⊕ B → Color) (b : B) :
    e.mapColor c (.inr (e.boundary b)) = c (.inr b) := by
  exact mapColor_dart e c (.inr b)

theorem mapColor_valid {c : I ⊕ B → Color} (hc : IsColor P c) :
    IsColor Q (e.mapColor c) := by
  refine ⟨?_, ?_, fun d => hc.2.2 (e.darts.symm d)⟩
  · intro j
    change c (.inl (e.interior.symm (Q.interiorAlpha j))) = c (.inl (e.interior.symm j))
    have ha : e.interior.symm (Q.interiorAlpha j) =
        P.interiorAlpha (e.interior.symm j) := e.symm.alpha j
    rw [ha]
    exact hc.1 _
  · intro d f hv hn
    apply hc.2.1 _ (e.darts.symm.injective.ne hn)
    apply e.vertex.injective
    rw [e.vert, e.vert]
    change Q.vertOf (e.darts (e.darts.symm d)) = Q.vertOf (e.darts (e.darts.symm f))
    simpa only [Equiv.apply_symm_apply] using hv

@[simp] theorem mapColor_symm (c : I ⊕ B → Color) :
    e.symm.mapColor (e.mapColor c) = c := by
  funext d
  cases d <;> simp [mapColor, darts, symm]

/-- Exact representation transport is a bijection of whole assignments.
No analogous counting claim is made about a graph reduction. -/
def coloringEquiv : {c : I ⊕ B → Color // IsColor P c} ≃
    {c : J ⊕ C → Color // IsColor Q c} where
  toFun c := ⟨e.mapColor c.1, e.mapColor_valid c.2⟩
  invFun c := ⟨e.symm.mapColor c.1, e.symm.mapColor_valid c.2⟩
  left_inv c := Subtype.ext (e.mapColor_symm c.1)
  right_inv c := by
    apply Subtype.ext
    funext d
    cases d <;> simp [mapColor, darts, symm]

end Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphism.Iso
