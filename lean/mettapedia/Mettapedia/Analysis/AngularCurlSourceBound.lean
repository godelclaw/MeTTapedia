import Mettapedia.Analysis.AngularCurlCurvatureBound

/-!
# Angular first variation under a bounded differentiable source

The estimate uses only the source value and its first derivative. For a
linear source `S a`, bounds on `S` and its derivative give a weighted
first-jet cost and an eighth-power cost. It does not require a second-jet
bound for vorticity or a supremum of its first derivative.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlDecomposition

open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem abs_angularCurlDensityRate_le (a : R3) (D : Fin 3 → R3)
    (v : R3) (E : Fin 3 → R3) :
    |angularCurlDensityRate a D v E| ≤
      96 * ‖a‖ ^ 5 * ‖v‖ * (∑ j : Fin 3, ‖D j‖) ^ 2 +
        32 * ‖a‖ ^ 6 * (∑ j : Fin 3, ‖D j‖) * (∑ j : Fin 3, ‖E j‖) := by
  have hb : |angularCurlDensityRate a D v E| ≤
      2 * (‖a‖ * ‖v‖) * ‖angularCurl a D‖ ^ 2 +
        2 * ‖a‖ ^ 2 * (‖angularCurl a D‖ * ‖angularCurlRate a D v E‖) := by
    unfold angularCurlDensityRate
    apply (abs_add_le _ _).trans
    simp only [abs_mul, abs_of_nonneg (sq_nonneg ‖a‖),
      abs_of_nonneg (sq_nonneg ‖angularCurl a D‖), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    gcongr <;> exact abs_real_inner_le_norm _ _
  calc
    _ ≤ _ := hb
    _ ≤ 2 * (‖a‖ * ‖v‖) * (4 * ‖a‖ ^ 2 * ∑ j : Fin 3, ‖D j‖) ^ 2 +
        2 * ‖a‖ ^ 2 * ((4 * ‖a‖ ^ 2 * ∑ j : Fin 3, ‖D j‖) *
          (8 * ‖a‖ * ‖v‖ * (∑ j : Fin 3, ‖D j‖) +
            4 * ‖a‖ ^ 2 * ∑ j : Fin 3, ‖E j‖)) := by
      gcongr <;> first | exact norm_angularCurl_le a D | exact norm_angularCurlRate_le a D v E
    _ = _ := by ring

/-- The derivative coefficient is explicit and need not be a vorticity
Lipschitz constant. For a linear source it bounds the differentiated operator. -/
theorem abs_angularCurlDensityRate_le_of_source_bounds (a : R3) (D : Fin 3 → R3)
    (v : R3) (E : Fin 3 → R3) (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hv : ‖v‖ ≤ M * ‖a‖) (hE : ∀ j, ‖E j‖ ≤ M * ‖D j‖ + N * ‖a‖) :
    |angularCurlDensityRate a D v E| ≤
      (384 * M + 144 * N) * (‖a‖ ^ 6 * ∑ j : Fin 3, ‖D j‖ ^ 2) + 48 * N * ‖a‖ ^ 8 := by
  have he : (∑ j : Fin 3, ‖E j‖) ≤ M * (∑ j : Fin 3, ‖D j‖) + 3 * N * ‖a‖ := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hE j)
    simp only [Fin.sum_univ_three] at h ⊢
    linarith only [h]
  have hbase : |angularCurlDensityRate a D v E| ≤
      128 * M * ‖a‖ ^ 6 * (∑ j : Fin 3, ‖D j‖) ^ 2 +
        96 * N * ‖a‖ ^ 7 * (∑ j : Fin 3, ‖D j‖) := by
    calc
      _ ≤ _ := abs_angularCurlDensityRate_le a D v E
      _ ≤ 96 * ‖a‖ ^ 5 * (M * ‖a‖) * (∑ j : Fin 3, ‖D j‖) ^ 2 +
          32 * ‖a‖ ^ 6 * (∑ j : Fin 3, ‖D j‖) *
            (M * (∑ j : Fin 3, ‖D j‖) + 3 * N * ‖a‖) := by gcongr
      _ = _ := by ring
  have hy : 2 * ‖a‖ ^ 7 * (∑ j : Fin 3, ‖D j‖) ≤
      ‖a‖ ^ 8 + ‖a‖ ^ 6 * (∑ j : Fin 3, ‖D j‖) ^ 2 := by
    nlinarith only [sq_nonneg (‖a‖ ^ 4 - ‖a‖ ^ 3 * (∑ j : Fin 3, ‖D j‖))]
  have hyn := mul_le_mul_of_nonneg_left hy (show 0 ≤ 48 * N by positivity)
  have hd := mul_le_mul_of_nonneg_left (sum_norm_sq_le_three D)
    (show 0 ≤ (128 * M + 48 * N) * ‖a‖ ^ 6 by positivity)
  nlinarith only [hbase, hyn, hd]

end Mettapedia.Analysis.AngularCurlDecomposition
