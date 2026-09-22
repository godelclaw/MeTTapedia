import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk

/-!
# The Excess Identity in exact form, and what it does not bound

The compositional note derives the finiteness of the profile category from the
Excess Identity, in the words "bounded defect forces hexagonal bulk, and
hexagonal bulk has finitely many interface behaviours".  The first clause is
the one this file examines.

Discrete Gauss--Bonnet on a spherical cubic map is already proved here:
the total curvature `∑ (6 - |f|)` over quotient facial cycles is `12`.  That
is a statement about a *signed* total.  Splitting it by face size gives the
Excess Identity in the form the route actually needs,

  `∑_{|f| < 6} (6 - |f|)  =  12 + ∑_{|f| > 6} (|f| - 6)`,

and in that form it is visible that the identity bounds neither side
separately.  The small-face excess is `12` only when the large-face excess
vanishes, that is, only in fullerene scope.  Off that scope the number of
defective faces is `12` plus a quantity the identity leaves free.

Nothing here refutes the route.  It locates a premise: "bounded defect" is an
additional hypothesis about the map, not a consequence of sphericity and
cubicity.  The existing fullerene-scope corollary
`orbitFaceTotalCurvature_eq_faceDefectSet_card_of_fullerene` is exactly the
special case where that premise is free.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ExcessIdentityScope

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Faces smaller than a hexagon. -/
noncomputable def smallFaces (RS : RotationSystem V E) : Finset (OrbitFace RS) :=
  Finset.univ.filter fun face => (orbitFaceBoundary RS face).card < 6

/-- Faces larger than a hexagon. -/
noncomputable def largeFaces (RS : RotationSystem V E) : Finset (OrbitFace RS) :=
  Finset.univ.filter fun face => 6 < (orbitFaceBoundary RS face).card

/-- The positive curvature carried by the small faces. -/
noncomputable def smallExcess (RS : RotationSystem V E) : Int :=
  ∑ face ∈ smallFaces RS, ((6 : Int) - (orbitFaceBoundary RS face).card)

/-- The negative curvature carried by the large faces, counted positively.
This is the quantity written `W₋` in the route's notes. -/
noncomputable def largeExcess (RS : RotationSystem V E) : Int :=
  ∑ face ∈ largeFaces RS, (((orbitFaceBoundary RS face).card : Int) - 6)

theorem smallExcess_nonneg (RS : RotationSystem V E) : 0 ≤ smallExcess RS := by
  apply Finset.sum_nonneg
  intro face hface
  have h : (orbitFaceBoundary RS face).card < 6 := by
    simpa [smallFaces] using hface
  have : ((orbitFaceBoundary RS face).card : Int) < 6 := by exact_mod_cast h
  linarith

theorem largeExcess_nonneg (RS : RotationSystem V E) : 0 ≤ largeExcess RS := by
  apply Finset.sum_nonneg
  intro face hface
  have h : 6 < (orbitFaceBoundary RS face).card := by
    simpa [largeFaces] using hface
  have : (6 : Int) < ((orbitFaceBoundary RS face).card : Int) := by exact_mod_cast h
  linarith

/-- Total curvature splits into the two excesses: hexagons contribute nothing,
and the remaining faces contribute with opposite signs. -/
theorem orbitFaceTotalCurvature_eq_sub (RS : RotationSystem V E) :
    orbitFaceTotalCurvature RS = smallExcess RS - largeExcess RS := by
  classical
  unfold orbitFaceTotalCurvature smallExcess largeExcess smallFaces largeFaces
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (OrbitFace RS))
      (fun face => (orbitFaceBoundary RS face).card < 6)]
  rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter fun face => ¬ (orbitFaceBoundary RS face).card < 6)
      (fun face => 6 < (orbitFaceBoundary RS face).card)]
  have hzero :
      ∑ face ∈ (Finset.univ.filter fun face => ¬ (orbitFaceBoundary RS face).card < 6).filter
          (fun face => ¬ 6 < (orbitFaceBoundary RS face).card),
          ((6 : Int) - (orbitFaceBoundary RS face).card) = 0 := by
    apply Finset.sum_eq_zero
    intro face hface
    simp only [Finset.mem_filter, not_lt] at hface
    have h6 : (orbitFaceBoundary RS face).card = 6 := le_antisymm hface.2 hface.1.2
    rw [h6]
    norm_num
  have hlarge :
      ∑ face ∈ (Finset.univ.filter fun face => ¬ (orbitFaceBoundary RS face).card < 6).filter
          (fun face => 6 < (orbitFaceBoundary RS face).card),
          ((6 : Int) - (orbitFaceBoundary RS face).card) =
        - ∑ face ∈ Finset.univ.filter (fun face => 6 < (orbitFaceBoundary RS face).card),
            (((orbitFaceBoundary RS face).card : Int) - 6) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr
    · ext face
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨le_of_lt h, h⟩
    · intro face _; ring
  rw [hlarge, hzero]
  ring

/-- **The Excess Identity.**  On any spherical cubic map with simple facial
boundaries, the small-face excess exceeds the large-face excess by exactly
twelve.

Both sides are free: the identity fixes their difference, not either one. -/
theorem excess_identity (RS : RotationSystem V E)
    (hsphere : OrbitSphericalCubicMapData RS)
    (hsimple : OrbitFaceBoundarySimple RS) :
    smallExcess RS = 12 + largeExcess RS := by
  have h := orbitFaceTotalCurvature_eq_twelve RS hsphere hsimple
  rw [orbitFaceTotalCurvature_eq_sub] at h
  linarith

/-- The small-face excess is twelve exactly when no face is larger than a
hexagon.  This is the precise scope of the route's "bounded defect": it is
bought by the identity only in fullerene scope, and is otherwise an extra
hypothesis about the map. -/
theorem smallExcess_eq_twelve_iff (RS : RotationSystem V E)
    (hsphere : OrbitSphericalCubicMapData RS)
    (hsimple : OrbitFaceBoundarySimple RS) :
    smallExcess RS = 12 ↔ largeExcess RS = 0 := by
  have h := excess_identity RS hsphere hsimple
  constructor
  · intro h12; omega
  · intro h0; omega

end GoertzelV24ExcessIdentityScope

end Mettapedia.GraphTheory.FourColor
