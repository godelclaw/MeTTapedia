import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceTwoSided
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk

/-!
# The facial dual as an actual rotation system

The dual retains darts, edge names, and the edge involution.  Its vertices are
the primal face orbits and its vertex rotation is the primal face permutation.
Local two-sidedness of the primal supplies looplessness of the dual.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualRotationSystem

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided

noncomputable section

universe u v

variable {V : Type u} {E : Type v}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The facial dual of a locally two-sided rotation system. -/
def rotationSystem (RS : RotationSystem V E)
    (htwoSided : OrbitFacesTwoSided RS) :
    RotationSystem (OrbitFace RS) E where
  D := RS.D
  edgeOf := RS.edgeOf
  vertOf := dartOrbitFace RS
  alpha := RS.alpha
  rho := RS.phi
  alpha_involutive := RS.alpha_involutive
  alpha_fixfree := RS.alpha_fixfree
  edge_alpha := RS.edge_alpha
  edge_fiber_two := RS.edge_fiber_two
  vert_rho := dartOrbitFace_phi_eq RS
  outer := RS.outer
  no_self_loops := htwoSided

@[simp] theorem rotationSystem_edgeOf (RS : RotationSystem V E)
    (htwoSided : OrbitFacesTwoSided RS) (dart : RS.D) :
    (rotationSystem RS htwoSided).edgeOf dart = RS.edgeOf dart := rfl

@[simp] theorem rotationSystem_vertOf (RS : RotationSystem V E)
    (htwoSided : OrbitFacesTwoSided RS) (dart : RS.D) :
    (rotationSystem RS htwoSided).vertOf dart = dartOrbitFace RS dart := rfl

@[simp] theorem rotationSystem_alpha (RS : RotationSystem V E)
    (htwoSided : OrbitFacesTwoSided RS) (dart : RS.D) :
    (rotationSystem RS htwoSided).alpha dart = RS.alpha dart := rfl

@[simp] theorem rotationSystem_rho (RS : RotationSystem V E)
    (htwoSided : OrbitFacesTwoSided RS) (dart : RS.D) :
    (rotationSystem RS htwoSided).rho dart = RS.phi dart := rfl

/-- The dual face permutation is the primal vertex rotation. -/
@[simp] theorem rotationSystem_phi (RS : RotationSystem V E)
    (htwoSided : OrbitFacesTwoSided RS) (dart : RS.D) :
    (rotationSystem RS htwoSided).phi dart = RS.rho dart := by
  simp [RotationSystem.phi_apply, RS.alpha_involutive]

/-- A facial orbit is exactly one cyclic vertex rotation in the dual. -/
theorem vertexRotationCyclic (RS : RotationSystem V E)
    (htwoSided : OrbitFacesTwoSided RS) :
    VertexRotationCyclic (rotationSystem RS htwoSided) := by
  intro left right heq
  exact Quotient.exact heq

/-- If every primal face orbit has three darts, its dual is cubic. -/
theorem isCubic_of_face_card_three (RS : RotationSystem V E)
    (htwoSided : OrbitFacesTwoSided RS)
    (hfaces : ∀ face : OrbitFace RS, (orbitFaceDarts RS face).card = 3) :
    (rotationSystem RS htwoSided).IsCubic := by
  intro face
  change (Finset.univ.filter fun dart : RS.D => dartOrbitFace RS dart = face).card = 3
  exact hfaces face

end

end GoertzelV24DualRotationSystem

end Mettapedia.GraphTheory.FourColor
