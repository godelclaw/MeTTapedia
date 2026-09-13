import Mettapedia.Analysis.AngularCurlTransport
import Mettapedia.Analysis.AngularCurlCurvatureBound

/-!
# Deformation stress bounded by angular dissipation

The absolute-value estimate is made after the radial cancellation.
Its coefficient is a bound for entries of the actual deformation matrix;
no global bound for that coefficient is supplied here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlDecomposition

open scoped RealInnerProductSpace
open WeightedCurlCancellation
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem norm_curlJetAdjoint_le (b : R3) (j : Fin 3) : ‖curlJetAdjoint b j‖ ≤ ‖b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  fin_cases j <;>
    simp [curlJetAdjoint, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Matrix.cons_val_two] <;>
    nlinarith only [sq_nonneg (b 0), sq_nonneg (b 1), sq_nonneg (b 2)]

theorem abs_deformationStress_le (a : R3) (D : Fin 3 → R3) (j k : Fin 3) :
    |deformationStress a D j k| ≤ 2 * ‖a‖ ^ 2 * ‖angularCurl a D‖ * ‖angularJet a D k‖ := by
  rw [deformationStress_eq_angularJet, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * ‖a‖ ^ 2)]
  calc
    _ ≤ 2 * ‖a‖ ^ 2 * (‖curlJetAdjoint (angularCurl a D) j‖ * ‖angularJet a D k‖) := by
      gcongr
      exact abs_real_inner_le_norm _ _
    _ ≤ 2 * ‖a‖ ^ 2 * (‖angularCurl a D‖ * ‖angularJet a D k‖) := by
      gcongr
      exact norm_curlJetAdjoint_le _ _
    _ = _ := by ring

theorem abs_deformationWork_le (a : R3) (D : Fin 3 → R3) (B : Fin 3 → Fin 3 → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hB : ∀ j k, |B j k| ≤ M) :
    |deformationWork a D B| ≤ 36 * M * angularDensity a D := by
  have hc := norm_curlJet_le_sum (angularJet a D)
  have hs := sum_norm_sq_le_three (angularJet a D)
  have hbase : |deformationWork a D B| ≤
      6 * M * ‖a‖ ^ 2 * ‖angularCurl a D‖ * (∑ k : Fin 3, ‖angularJet a D k‖) := by
    calc
      _ ≤ ∑ j : Fin 3, |∑ k : Fin 3, B j k * deformationStress a D j k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, |B j k * deformationStress a D j k| := by
        apply Finset.sum_le_sum
        intro j _
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, M * (2 * ‖a‖ ^ 2 * ‖angularCurl a D‖ * ‖angularJet a D k‖) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul (hB j k) (abs_deformationStress_le a D j k) (abs_nonneg _) hM
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  calc
    _ ≤ 6 * M * ‖a‖ ^ 2 * ‖angularCurl a D‖ * (∑ k : Fin 3, ‖angularJet a D k‖) := hbase
    _ ≤ 12 * M * ‖a‖ ^ 2 * (∑ k : Fin 3, ‖angularJet a D k‖) ^ 2 := by
      change ‖angularCurl a D‖ ≤ _ at hc
      have h := mul_le_mul_of_nonneg_left hc
        (show 0 ≤ 6 * M * ‖a‖ ^ 2 * (∑ k : Fin 3, ‖angularJet a D k‖) by positivity)
      nlinarith only [h]
    _ ≤ 36 * M * (‖a‖ ^ 2 * ∑ k : Fin 3, ‖angularJet a D k‖ ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ 12 * M * ‖a‖ ^ 2 by positivity)
      nlinarith only [h]
    _ = _ := by rw [weighted_sum_norm_angularJet_sq]

end Mettapedia.Analysis.AngularCurlDecomposition
