import Mathlib.Tactic
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk

/-!
# Global conservation for classical discharging scores

The classical unavoidability proof assigns an integer potential to each
dart.  Crossing an edge transfers the difference between the opposite and
current potentials.  These transfers cancel globally because the edge map is
a permutation.  Consequently the sum of all face scores is ten times the
all-face curvature, hence exactly `120` on a cubic sphere.

No restriction on face lengths is used here.  Long faces contribute their
ordinary negative curvature.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateDischargingScore

open scoped BigOperators

open GoertzelV24CurvatureScope
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Curvature computed from the number of darts in each facial cycle. -/
noncomputable def orbitFaceDartTotalCurvature
    (RS : RotationSystem V E) : Int :=
  ∑ face : OrbitFace RS,
    ((6 : Int) - ((orbitFaceDarts RS face).card : Int))

/-- All-face Gauss--Bonnet in the facial-dart presentation.  Repeated edge
visits, if present, retain their multiplicity. -/
theorem orbitFaceDartTotalCurvature_eq_twelve
    (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS) :
    orbitFaceDartTotalCurvature RS = 12 := by
  have hvertices := RS.card_darts_eq_three_times_card_vertices hsphere.cubic
  have hedges := RS.card_darts_eq_twice_card_edges
  have hfaces := sum_card_orbitFaceDarts_eq_card_darts RS
  have hverticesInt : (Fintype.card RS.D : Int) =
      3 * Fintype.card V := by
    exact_mod_cast hvertices
  have hedgesInt : (Fintype.card RS.D : Int) =
      2 * Fintype.card E := by
    exact_mod_cast hedges
  have hfacesInt :
      (∑ face : OrbitFace RS,
        ((orbitFaceDarts RS face).card : Int)) =
          Fintype.card RS.D := by
    exact_mod_cast hfaces
  unfold orbitFaceDartTotalCurvature
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  linarith [hsphere.euler, hverticesInt, hedgesInt, hfacesInt]

/-- Edge-antisymmetric transfer induced by a dart potential. -/
def dartTransfer (RS : RotationSystem V E)
    (potential : RS.D → Int) (dart : RS.D) : Int :=
  potential (RS.alpha dart) - potential dart

/-- Transfers cancel over all darts because `alpha` is a permutation. -/
theorem sum_dartTransfer_eq_zero
    (RS : RotationSystem V E) (potential : RS.D → Int) :
    (∑ dart : RS.D, dartTransfer RS potential dart) = 0 := by
  unfold dartTransfer
  rw [Finset.sum_sub_distrib]
  rw [Equiv.sum_comp RS.alpha potential]
  exact sub_self _

/-- Summing a dart value within every quotient face is the same as summing it
once over all darts. -/
theorem sum_orbitFaceDartSums_eq_sum_darts
    (RS : RotationSystem V E) (value : RS.D → Int) :
    (∑ face : OrbitFace RS,
        ∑ dart ∈ orbitFaceDarts RS face, value dart) =
      ∑ dart : RS.D, value dart := by
  classical
  change
    (∑ face ∈ (Finset.univ : Finset (OrbitFace RS)),
        ∑ dart ∈ (Finset.univ.filter fun dart : RS.D =>
          dartOrbitFace RS dart = face), value dart) =
      ∑ dart ∈ (Finset.univ : Finset RS.D), value dart
  exact Finset.sum_fiberwise_of_maps_to
    (fun dart _hdart => Finset.mem_univ (dartOrbitFace RS dart)) value

/-- Transfer accumulated around one facial cycle. -/
noncomputable def orbitFaceTransfer
    (RS : RotationSystem V E) (potential : RS.D → Int)
    (face : OrbitFace RS) : Int :=
  ∑ dart ∈ orbitFaceDarts RS face, dartTransfer RS potential dart

/-- Classical face score: ten units of combinatorial curvature plus the
net potential transfer around the face. -/
noncomputable def orbitFaceScore
    (RS : RotationSystem V E) (potential : RS.D → Int)
    (face : OrbitFace RS) : Int :=
  10 * ((6 : Int) - ((orbitFaceDarts RS face).card : Int)) +
    orbitFaceTransfer RS potential face

/-- Every dart potential gives the same global score `120` on a cubic
sphere.  The local rule catalogue affects only how the score is bounded, not
this conservation law. -/
theorem sum_orbitFaceScore_eq_oneHundredTwenty
    (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS)
    (potential : RS.D → Int) :
    (∑ face : OrbitFace RS, orbitFaceScore RS potential face) = 120 := by
  have hcurvature := orbitFaceDartTotalCurvature_eq_twelve RS hsphere
  have htransfer :
      (∑ face : OrbitFace RS, orbitFaceTransfer RS potential face) = 0 := by
    unfold orbitFaceTransfer
    rw [sum_orbitFaceDartSums_eq_sum_darts]
    exact sum_dartTransfer_eq_zero RS potential
  change
    (∑ face : OrbitFace RS,
      ((6 : Int) - ((orbitFaceDarts RS face).card : Int))) = 12 at hcurvature
  unfold orbitFaceScore
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcurvature, htransfer]
  norm_num

/-- A positive-score face exists for every dart potential. -/
theorem exists_orbitFaceScore_pos
    (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS)
    (potential : RS.D → Int) :
    ∃ face : OrbitFace RS, 0 < orbitFaceScore RS potential face := by
  by_contra hnone
  push Not at hnone
  have hnonpositive :
      (∑ face : OrbitFace RS, orbitFaceScore RS potential face) ≤ 0 := by
    exact Finset.sum_nonpos fun face _hface => hnone face
  rw [sum_orbitFaceScore_eq_oneHundredTwenty RS hsphere potential] at hnonpositive
  omega

/-- The same face score, based at an oriented facial dart. -/
noncomputable def hubScore
    (RS : RotationSystem V E) (potential : RS.D → Int)
    (dart : RS.D) : Int :=
  orbitFaceScore RS potential (dartOrbitFace RS dart)

/-- Advancing around a face preserves its score. -/
theorem hubScore_phi_eq
    (RS : RotationSystem V E) (potential : RS.D → Int) (dart : RS.D) :
    hubScore RS potential (RS.phi dart) = hubScore RS potential dart := by
  unfold hubScore
  rw [dartOrbitFace_phi_eq]

/-- Any finite rotation around a face preserves its score. -/
theorem hubScore_phi_iterate_eq
    (RS : RotationSystem V E) (potential : RS.D → Int)
    (steps : Nat) (dart : RS.D) :
    hubScore RS potential ((RS.phi : RS.D → RS.D)^[steps] dart) =
      hubScore RS potential dart := by
  unfold hubScore
  rw [dartOrbitFace_phi_iterate_eq]

/-- A positive-score hub dart exists. -/
theorem exists_hubScore_pos
    (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS)
    (potential : RS.D → Int) :
    ∃ dart : RS.D, 0 < hubScore RS potential dart := by
  obtain ⟨face, hface⟩ := exists_orbitFaceScore_pos RS hsphere potential
  obtain ⟨dart, hdart⟩ := exists_dartOrbitFace_eq RS face
  refine ⟨dart, ?_⟩
  simpa [hubScore, hdart] using hface

end ClassicalCertificateDischargingScore

end Mettapedia.GraphTheory.FourColor
