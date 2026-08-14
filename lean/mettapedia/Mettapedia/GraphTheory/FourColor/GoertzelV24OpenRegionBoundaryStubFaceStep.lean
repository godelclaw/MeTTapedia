import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionRotation

/-!
# Face steps at open-region boundary stubs

A deleted-region opening gives every exposed ambient half-edge a new
degree-one stub.  The cap-collar calculation must use the opened rotation's
actual face permutation, rather than a drawing of the deleted cap.  This small
generic lemma is its first step: from a stub, `phi = rho * alpha` crosses to
the retained endpoint and then follows the retained vertex rotation.

It does not compute a whole boundary orbit or assert a cyclic order for any
particular cap; those are source-specific C-2 obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionBoundaryStubFaceStep

open GoertzelV24OpenRegionRotation
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A face-permutation step out of a fresh degree-one stub is literally the
retained rotation after crossing its unique stub edge. -/
@[simp]
theorem rotationSystem_phi_stub
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (boundary : BoundaryDart RS keep) :
    (rotationSystem RS keep outer).phi (Sum.inr boundary) =
      Sum.inl (retainedRho RS keep boundary.1) := by
  rw [RotationSystem.phi_apply, rotationSystem_alpha_stub,
    rotationSystem_rho_old]

end

end GoertzelV24OpenRegionBoundaryStubFaceStep

end Mettapedia.GraphTheory.FourColor
