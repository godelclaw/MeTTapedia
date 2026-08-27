import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceBoundaryLinearAlgebra

/-!
# Separation, read off the boundary map

The boundary map sends a face-coefficient vector to the edge vector

    edge ↦ ∑ over all faces of (coefficient, when the edge lies on that face).

With two-sided faces an edge lies on exactly two of them, so that sum
collapses: the value at an edge is the sum of the coefficients of its two
sides, and nothing else contributes.

That collapse is the whole content of separation.  Read a coefficient vector
as the indicator of a set `S` of faces.  Then an edge is in the image vector
exactly when *one* of its two faces lies in `S`; edges with both faces in
`S`, or neither, contribute nothing.  So the image vector is precisely the
edge cut between `S` and its complement — no edge outside it crosses.

Combined with the fact that facial boundaries span the cycle space, this
says every cycle is such a cut, which is the dual form of the combinatorial
separation that planar arguments usually import from topology.

What is *not* here: the transfer of this statement from faces to vertices,
which is what a maximality argument would consume.  It is recorded as the
remaining step rather than glossed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FaceSeparation

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24FaceBoundaryLinearAlgebra

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The boundary map is the two-sided sum.**  At an edge, the boundary map
returns the sum of the coefficients of the edge's two faces. -/
theorem orbitFaceBoundaryLinearMap_apply_eq_pair_sum
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (coefficients : OrbitFace RS → F2) (dart : RS.D) :
    orbitFaceBoundaryLinearMap RS coefficients (RS.edgeOf dart)
      = coefficients (dartOrbitFace RS dart)
        + coefficients (dartOrbitFace RS (RS.alpha dart)) := by
  classical
  show (∑ face : OrbitFace RS,
      if RS.edgeOf dart ∈ orbitFaceBoundary RS face then coefficients face
        else 0) = _
  rw [← Finset.sum_filter, orbitFace_incidentFaces_eq_dartSide_pair
    RS htwoSided dart]
  exact Finset.sum_pair (htwoSided dart)

/-- **Separation.**  An edge lies in the image of a face-set indicator
exactly when its two sides fall on opposite sides of the set. -/
theorem mem_image_iff_separates
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (coefficients : OrbitFace RS → F2) (dart : RS.D) :
    orbitFaceBoundaryLinearMap RS coefficients (RS.edgeOf dart) ≠ 0
      ↔ coefficients (dartOrbitFace RS dart)
          ≠ coefficients (dartOrbitFace RS (RS.alpha dart)) := by
  rw [orbitFaceBoundaryLinearMap_apply_eq_pair_sum RS htwoSided]
  constructor
  · intro hne heq
    apply hne
    rw [heq]
    exact CharTwo.add_self_eq_zero _
  · intro hne hzero
    apply hne
    have := add_eq_zero_iff_eq_neg.mp hzero
    rwa [CharTwo.neg_eq] at this

end GoertzelV24FaceSeparation

end Mettapedia.GraphTheory.FourColor
