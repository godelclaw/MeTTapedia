import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleComposition
import Mettapedia.GraphTheory.FourColor.RotationSystemExactTransport

/-!
# Exchanging the two displayed sides of a closed sewing

The two presentations have exactly the same darts, edges and rotations
up to exchanging their tags and inverting the seam matching. The marked
outer dart may change; all fields of the spherical cubic minimality class
are preserved by the exact transport.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleCompositionSwap

open GoertzelV24OpenTangleComposition
open GoertzelV24TwoEdgeCutMinimality

variable {V W I J L R : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  (A : OpenTangleData V I L) (B : OpenTangleData W J R) (m : L ≃ R)

noncomputable def darts : (A.composeRotationSystem B m).D ≃
    (B.composeRotationSystem A m.symm).D :=
  Equiv.sumCongr (Equiv.sumComm I J) (Equiv.sumComm L R)

theorem darts_reassoc (x : (I ⊕ L) ⊕ (J ⊕ R)) :
    darts A B m (composeDartEquiv x) = composeDartEquiv (Sum.swap x) := by
  rcases x with (i | l) | (j | r) <;> rfl

theorem alpha (d : (A.composeRotationSystem B m).D) :
    darts A B m ((A.composeRotationSystem B m).alpha d) =
      (B.composeRotationSystem A m.symm).alpha (darts A B m d) := by
  rcases d with (i | j) | (l | r) <;> rfl

theorem vertex (d : (A.composeRotationSystem B m).D) :
    Equiv.sumComm V W ((A.composeRotationSystem B m).vertOf d) =
      (B.composeRotationSystem A m.symm).vertOf (darts A B m d) := by
  rcases d with (i | j) | (l | r) <;> rfl

theorem rotation (d : (A.composeRotationSystem B m).D) :
    darts A B m ((A.composeRotationSystem B m).rho d) =
      (B.composeRotationSystem A m.symm).rho (darts A B m d) := by
  obtain ⟨x, rfl⟩ := composeDartEquiv.surjective d
  change darts A B m (composeDartEquiv ((Equiv.sumCongr A.rho B.rho)
    (composeDartEquiv.symm (composeDartEquiv x)))) = composeDartEquiv
    ((Equiv.sumCongr B.rho A.rho) (composeDartEquiv.symm (darts A B m (composeDartEquiv x))))
  rw [Equiv.symm_apply_apply, darts_reassoc, darts_reassoc, Equiv.symm_apply_apply]
  cases x <;> rfl

/-- Geometry transports in either direction by exchanging the two sides. -/
theorem mapClass
    (h : BridgelessSphericalCubicMapData (A.composeRotationSystem B m)) :
    BridgelessSphericalCubicMapData (B.composeRotationSystem A m.symm) :=
  RotationSystemExactTransport.mapClass _ _ (darts A B m) (Equiv.sumComm V W)
    (alpha A B m) (vertex A B m) (rotation A B m) h

end Mettapedia.GraphTheory.FourColor.OpenTangleCompositionSwap
