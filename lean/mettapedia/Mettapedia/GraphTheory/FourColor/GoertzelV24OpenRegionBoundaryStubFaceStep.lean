import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence

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
open GoertzelV24FaceOrbitIncidence

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

/-- The old retained dart and fresh stub dart of one exposed edge already lie
on the same opened facial orbit.  The remaining collar calculation is only
about joining the orbits of *different* exposed edges. -/
theorem dartOrbitFace_oldBoundary_eq_stub
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (boundary : BoundaryDart RS keep) :
    dartOrbitFace (rotationSystem RS keep outer) (Sum.inl boundary.1) =
      dartOrbitFace (rotationSystem RS keep outer) (Sum.inr boundary) := by
  have hstep :
      (rotationSystem RS keep outer).phi (Sum.inl boundary.1) =
        Sum.inr boundary := by
    rw [RotationSystem.phi_apply,
      rotationSystem_alpha_old_of_boundary,
      rotationSystem_rho_stub]
    rfl
  calc
    dartOrbitFace (rotationSystem RS keep outer) (Sum.inl boundary.1) =
        dartOrbitFace (rotationSystem RS keep outer)
          ((rotationSystem RS keep outer).phi (Sum.inl boundary.1)) :=
      (dartOrbitFace_phi_eq (rotationSystem RS keep outer)
        (Sum.inl boundary.1)).symm
    _ = dartOrbitFace (rotationSystem RS keep outer) (Sum.inr boundary) :=
      congrArg (dartOrbitFace (rotationSystem RS keep outer)) hstep

end

end GoertzelV24OpenRegionBoundaryStubFaceStep

end Mettapedia.GraphTheory.FourColor
