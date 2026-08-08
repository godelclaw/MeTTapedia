import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceBoundaryLinearAlgebra

/-!
# Facial boundaries with dart multiplicity

The existing quotient-face boundary map records edge support, so it requires
every edge to have two distinct incident faces.  A framed annular tangle has
degree-one boundary edges whose two darts lie on the same hole face.  Such a
bridge must occur twice and cancel over `F2`, not occur once.

This module defines the multiplicity-correct boundary map by summing the face
coefficient over the two darts above each edge.  It agrees with the existing
map in the two-sided case and remains correct on bridge edges.  This is the
linear-algebra interface needed to separate the faces along closed radial and
chord walls without pretending that the annular stub edges are two-sided.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrbitFaceParityBoundary

open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The `F2` facial boundary map with dart multiplicity.  At each edge it
sums the labels of the two dart-side faces; if both darts belong to the same
face, that coefficient occurs twice and cancels. -/
def orbitFaceParityBoundaryLinearMap (RS : RotationSystem V E) :
    (OrbitFace RS → F2) →ₗ[F2] (E → F2) where
  toFun coefficients edge :=
    ∑ dart ∈ RS.dartsOn edge,
      coefficients (dartOrbitFace RS dart)
  map_add' := by
    intro left right
    funext edge
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
  map_smul' := by
    intro scalar coefficients
    funext edge
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

@[simp] theorem orbitFaceParityBoundaryLinearMap_apply
    (RS : RotationSystem V E) (coefficients : OrbitFace RS → F2)
    (edge : E) :
    orbitFaceParityBoundaryLinearMap RS coefficients edge =
      ∑ dart ∈ RS.dartsOn edge,
        coefficients (dartOrbitFace RS dart) :=
  rfl

/-- The multiplicity-correct edge coordinate is the sum of the two dart-side
face labels, without a two-sidedness hypothesis. -/
theorem orbitFaceParityBoundaryLinearMap_apply_edgeOf
    (RS : RotationSystem V E) (coefficients : OrbitFace RS → F2)
    (dart : RS.D) :
    orbitFaceParityBoundaryLinearMap RS coefficients (RS.edgeOf dart) =
      coefficients (dartOrbitFace RS dart) +
        coefficients (dartOrbitFace RS (RS.alpha dart)) := by
  rw [orbitFaceParityBoundaryLinearMap_apply]
  have hdart : dart ∈ RS.dartsOn (RS.edgeOf dart) :=
    (RS.mem_dartsOn).2 rfl
  rw [RS.dartsOn_eq_pair_of_mem hdart]
  have hnotmem : dart ∉ ({RS.alpha dart} : Finset RS.D) := by
    simpa using (RS.alpha_fixfree dart).symm
  rw [Finset.sum_insert hnotmem, Finset.sum_singleton]

/-- A one-sided edge contributes zero: its repeated face coefficient cancels
over `F2`. -/
theorem orbitFaceParityBoundaryLinearMap_apply_edgeOf_eq_zero_of_sameFace
    (RS : RotationSystem V E) (coefficients : OrbitFace RS → F2)
    (dart : RS.D)
    (hsame : dartOrbitFace RS dart =
      dartOrbitFace RS (RS.alpha dart)) :
    orbitFaceParityBoundaryLinearMap RS coefficients (RS.edgeOf dart) = 0 := by
  rw [orbitFaceParityBoundaryLinearMap_apply_edgeOf, hsame]
  exact zmod2_add_self _

/-- On a two-sided rotation system, dart multiplicity and ordinary facial
support define the same boundary map. -/
theorem orbitFaceParityBoundaryLinearMap_eq_orbitFaceBoundaryLinearMap
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS) :
    orbitFaceParityBoundaryLinearMap RS =
      orbitFaceBoundaryLinearMap RS := by
  apply LinearMap.ext
  intro coefficients
  funext edge
  rcases RS.dartsOn_nonempty edge with ⟨dart, hdart⟩
  have hedge : RS.edgeOf dart = edge := (RS.mem_dartsOn).1 hdart
  rw [← hedge,
    orbitFaceParityBoundaryLinearMap_apply_edgeOf,
    orbitFaceBoundaryLinearMap_apply_edgeOf RS htwoSided]

end

end GoertzelV24OrbitFaceParityBoundary

end Mettapedia.GraphTheory.FourColor
