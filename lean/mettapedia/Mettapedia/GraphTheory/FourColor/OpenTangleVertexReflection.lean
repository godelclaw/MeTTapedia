import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamCubic

/-!
# Recovering exterior vertex geometry from a sewn map

The unchanged exterior inherits cubicity and cyclic vertex rotations
from the closed composite. Replacement therefore needs no additional
assumptions about these properties of the exterior.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleVertexReflection

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24CompositeSeamMultigraph GoertzelV24CompositeSeamCubic
open GoertzelV24FaceDualConnectedness

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W I J L R : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  (outside : OpenTangleData V I L) (inside : OpenTangleData W J R) (m : L ≃ R)

theorem exterior_isCubic (h : (outside.composeRotationSystem inside m).IsCubic) :
    OpenIsCubic outside := by
  intro v
  rw [← card_dartsAt_inl outside inside m v]
  exact h (.inl v)

theorem exterior_rotationCyclic
    (h : VertexRotationCyclic (outside.composeRotationSystem inside m)) :
    OpenRotationCyclic outside := by
  intro d d' hv
  have hs := h (composeDartEquiv (.inl d)) (composeDartEquiv (.inl d')) (by
    change (compositeRS outside inside m).vertOf (reassoc (.inl d)) =
      (compositeRS outside inside m).vertOf (reassoc (.inl d'))
    simp only [vertOf_reassoc, disjointVertOf, hv])
  change Equiv.Perm.SameCycle
    ((composeDartEquiv.symm.trans (Equiv.sumCongr outside.rho inside.rho)).trans composeDartEquiv)
    (composeDartEquiv (.inl d)) (composeDartEquiv (.inl d')) at hs
  obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
  rw [conjEquiv_pow, Equiv.symm_apply_apply] at hn
  have he := composeDartEquiv.injective hn
  rw [sumCongr_pow_inl] at he
  exact ⟨n, by rw [zpow_natCast]; exact Sum.inl.inj he⟩

end
end Mettapedia.GraphTheory.FourColor.OpenTangleVertexReflection
