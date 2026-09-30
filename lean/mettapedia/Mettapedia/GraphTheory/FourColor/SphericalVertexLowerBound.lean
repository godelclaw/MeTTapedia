import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk

/-! # Twenty vertices from spherical cubic incidence and minimum face length

The actual quotient faces partition the darts. If every face uses at least
five distinct edges, it uses at least five darts. Euler and cubic incidence
then imply at least twenty vertices. Repeated edge visits need no additional
assumption: forgetting them can only decrease the boundary length.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalVertexLowerBound

open GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceCurvatureBulk

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem twenty_le_card_vertices (RS : RotationSystem V E)
    (hsphere : OrbitSphericalCubicMapData RS)
    (hminimum : ∀ face : OrbitFace RS, 5 ≤ (orbitFaceBoundary RS face).card) :
    20 ≤ Fintype.card V := by
  have hf : 5 * Fintype.card (OrbitFace RS) ≤ Fintype.card RS.D := calc
    _ = ∑ _face : OrbitFace RS, (5 : ℕ) := by simp [Nat.mul_comm]
    _ ≤ ∑ face : OrbitFace RS, (orbitFaceDarts RS face).card :=
      Finset.sum_le_sum fun face _ =>
        (hminimum face).trans (orbitFaceBoundary_card_le_orbitFaceDarts_card RS face)
    _ = _ := sum_card_orbitFaceDarts_eq_card_darts RS
  have hv := RS.card_darts_eq_three_times_card_vertices hsphere.cubic
  have he := RS.card_darts_eq_twice_card_edges
  have hf' : (5 : ℤ) * Fintype.card (OrbitFace RS) ≤ Fintype.card RS.D := by exact_mod_cast hf
  have hv' : (Fintype.card RS.D : ℤ) = 3 * Fintype.card V := by exact_mod_cast hv
  have he' : (Fintype.card RS.D : ℤ) = 2 * Fintype.card E := by exact_mod_cast he
  have heuler := hsphere.euler
  omega

/-- A face with more than five darts makes the twenty-vertex bound strict.
This uses an actual orbit, so repeated boundary edges are harmless. -/
theorem twenty_lt_card_vertices_of_long_face (RS : RotationSystem V E)
    (hsphere : OrbitSphericalCubicMapData RS)
    (hminimum : ∀ face : OrbitFace RS, 5 ≤ (orbitFaceBoundary RS face).card)
    (hlong : ∃ face : OrbitFace RS, 5 < (orbitFaceDarts RS face).card) :
    20 < Fintype.card V := by
  classical
  have hf : 5 * Fintype.card (OrbitFace RS) < Fintype.card RS.D := calc
    _ = ∑ _face : OrbitFace RS, (5 : ℕ) := by simp [Nat.mul_comm]
    _ < ∑ face : OrbitFace RS, (orbitFaceDarts RS face).card := by
      apply Finset.sum_lt_sum
      · exact fun face _ => (hminimum face).trans
          (orbitFaceBoundary_card_le_orbitFaceDarts_card RS face)
      · obtain ⟨face, hface⟩ := hlong
        exact ⟨face, Finset.mem_univ _, hface⟩
    _ = _ := sum_card_orbitFaceDarts_eq_card_darts RS
  have hv := RS.card_darts_eq_three_times_card_vertices hsphere.cubic
  have he := RS.card_darts_eq_twice_card_edges
  have hf' : (5 : ℤ) * Fintype.card (OrbitFace RS) < Fintype.card RS.D := by exact_mod_cast hf
  have hv' : (Fintype.card RS.D : ℤ) = 3 * Fintype.card V := by exact_mod_cast hv
  have he' : (Fintype.card RS.D : ℤ) = 2 * Fintype.card E := by exact_mod_cast he
  have heuler := hsphere.euler
  omega

end Mettapedia.GraphTheory.FourColor.SphericalVertexLowerBound
