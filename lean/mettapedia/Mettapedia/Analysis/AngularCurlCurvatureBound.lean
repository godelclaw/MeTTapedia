import Mettapedia.Analysis.AngularCurlSecondVariation

/-!
# A polynomial upper bound for angular diffusion curvature

Both amplitude-gradient and mixed-second-jet costs remain explicit.
There is no division by vorticity amplitude, strain gap or angular curl.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlDecomposition

open scoped RealInnerProductSpace
open WeightedCurlCancellation
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem norm_curlJet_le_sum (D : Fin 3 → R3) :
    ‖curlJet D‖ ≤ 2 * ∑ j : Fin 3, ‖D j‖ := by
  have h := norm_curlJet_sq_le D
  have hsum : (∑ j : Fin 3, ‖D j‖ ^ 2) ≤ (∑ j : Fin 3, ‖D j‖) ^ 2 := by
    simp only [Fin.sum_univ_three]
    nlinarith only [mul_nonneg (norm_nonneg (D 0)) (norm_nonneg (D 1)),
      mul_nonneg (norm_nonneg (D 0)) (norm_nonneg (D 2)),
      mul_nonneg (norm_nonneg (D 1)) (norm_nonneg (D 2))]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith only [h, hsum, sq_nonneg (∑ j : Fin 3, ‖D j‖)]

theorem norm_angularJet_le (a : R3) (D : Fin 3 → R3) (j : Fin 3) :
    ‖angularJet a D j‖ ≤ 2 * ‖a‖ ^ 2 * ‖D j‖ := by
  calc
    _ ≤ ‖‖a‖ ^ 2 • D j‖ + ‖⟪a, D j⟫ • a‖ := norm_sub_le _ _
    _ = ‖a‖ ^ 2 * ‖D j‖ + |⟪a, D j⟫| * ‖a‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖a‖)]
    _ ≤ ‖a‖ ^ 2 * ‖D j‖ + (‖a‖ * ‖D j‖) * ‖a‖ := by
      gcongr
      exact abs_real_inner_le_norm _ _
    _ = _ := by ring

theorem norm_angularCurl_le (a : R3) (D : Fin 3 → R3) :
    ‖angularCurl a D‖ ≤ 4 * ‖a‖ ^ 2 * ∑ j : Fin 3, ‖D j‖ := by
  calc
    _ ≤ 2 * ∑ j : Fin 3, ‖angularJet a D j‖ := norm_curlJet_le_sum _
    _ ≤ 2 * ∑ j : Fin 3, 2 * ‖a‖ ^ 2 * ‖D j‖ := by
      gcongr with j
      exact norm_angularJet_le a D j
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem norm_angularJetRate_le (a : R3) (D : Fin 3 → R3)
    (v : R3) (E : Fin 3 → R3) (j : Fin 3) :
    ‖angularJetRate a D v E j‖ ≤ 4 * ‖a‖ * ‖v‖ * ‖D j‖ + 2 * ‖a‖ ^ 2 * ‖E j‖ := by
  have h : ‖angularJetRate a D v E j‖ ≤ ‖(2 * ⟪a, v⟫) • D j‖ + ‖‖a‖ ^ 2 • E j‖ +
      ‖(⟪v, D j⟫ + ⟪a, E j⟫) • a‖ + ‖⟪a, D j⟫ • v‖ := by
    unfold angularJetRate
    exact (norm_sub_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖a‖),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hb : 2 * |⟪a, v⟫| * ‖D j‖ + ‖a‖ ^ 2 * ‖E j‖ +
      |⟪v, D j⟫ + ⟪a, E j⟫| * ‖a‖ + |⟪a, D j⟫| * ‖v‖ ≤
      2 * (‖a‖ * ‖v‖) * ‖D j‖ + ‖a‖ ^ 2 * ‖E j‖ +
      (‖v‖ * ‖D j‖ + ‖a‖ * ‖E j‖) * ‖a‖ + (‖a‖ * ‖D j‖) * ‖v‖ := by
    gcongr
    · exact abs_real_inner_le_norm _ _
    · exact (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))
    · exact abs_real_inner_le_norm _ _
  calc
    _ ≤ _ := h.trans hb
    _ = _ := by ring

theorem norm_angularCurlRate_le (a : R3) (D : Fin 3 → R3)
    (v : R3) (E : Fin 3 → R3) :
    ‖angularCurlRate a D v E‖ ≤ 8 * ‖a‖ * ‖v‖ * (∑ j : Fin 3, ‖D j‖) +
      4 * ‖a‖ ^ 2 * ∑ j : Fin 3, ‖E j‖ := by
  calc
    _ ≤ 2 * ∑ j : Fin 3, ‖angularJetRate a D v E j‖ := norm_curlJet_le_sum _
    _ ≤ 2 * ∑ j : Fin 3, (4 * ‖a‖ * ‖v‖ * ‖D j‖ + 2 * ‖a‖ ^ 2 * ‖E j‖) := by
      gcongr with j
      exact norm_angularJetRate_le a D v E j
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

theorem norm_angularJetSecondVariation_le (a : R3) (D : Fin 3 → R3)
    (v : R3) (E : Fin 3 → R3) (j : Fin 3) :
    ‖angularJetSecondVariation a D v E j‖ ≤ 4 * ‖v‖ ^ 2 * ‖D j‖ + 8 * ‖a‖ * ‖v‖ * ‖E j‖ := by
  have h : ‖angularJetSecondVariation a D v E j‖ ≤
      ‖(2 * ‖v‖ ^ 2) • D j‖ + ‖(4 * ⟪a, v⟫) • E j‖ +
        ‖(2 * ⟪v, E j⟫) • a‖ + ‖(2 * (⟪v, D j⟫ + ⟪a, E j⟫)) • v‖ := by
    unfold angularJetSecondVariation
    exact (norm_sub_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖v‖),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at h
  calc
    _ ≤ 2 * ‖v‖ ^ 2 * ‖D j‖ + 4 * |⟪a, v⟫| * ‖E j‖ +
        2 * |⟪v, E j⟫| * ‖a‖ + 2 * |⟪v, D j⟫ + ⟪a, E j⟫| * ‖v‖ := h
    _ ≤ 2 * ‖v‖ ^ 2 * ‖D j‖ + 4 * (‖a‖ * ‖v‖) * ‖E j‖ +
        2 * (‖v‖ * ‖E j‖) * ‖a‖ + 2 * (‖v‖ * ‖D j‖ + ‖a‖ * ‖E j‖) * ‖v‖ := by
      gcongr
      · exact abs_real_inner_le_norm _ _
      · exact abs_real_inner_le_norm _ _
      · exact (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))
    _ = _ := by ring

theorem norm_angularCurlSecondVariation_le (a : R3) (D : Fin 3 → R3)
    (v : R3) (E : Fin 3 → R3) :
    ‖angularCurlSecondVariation a D v E‖ ≤ 8 * ‖v‖ ^ 2 * (∑ j : Fin 3, ‖D j‖) +
      16 * ‖a‖ * ‖v‖ * ∑ j : Fin 3, ‖E j‖ := by
  calc
    _ ≤ 2 * ∑ j : Fin 3, ‖angularJetSecondVariation a D v E j‖ := norm_curlJet_le_sum _
    _ ≤ 2 * ∑ j : Fin 3, (4 * ‖v‖ ^ 2 * ‖D j‖ + 8 * ‖a‖ * ‖v‖ * ‖E j‖) := by
      gcongr with j
      exact norm_angularJetSecondVariation_le a D v E j
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

theorem angularCurlDensitySecondVariation_le_norm_sums (a : R3) (D : Fin 3 → R3)
    (v : R3) (E : Fin 3 → R3) :
    angularCurlDensitySecondVariation a D v E ≤
      672 * ‖a‖ ^ 4 * ‖v‖ ^ 2 * (∑ j : Fin 3, ‖D j‖) ^ 2 +
        224 * ‖a‖ ^ 6 * (∑ j : Fin 3, ‖E j‖) ^ 2 := by
  let H := angularCurl a D
  let H₁ := angularCurlRate a D v E
  let H₂ := angularCurlSecondVariation a D v E
  let d := ∑ j : Fin 3, ‖D j‖
  let e := ∑ j : Fin 3, ‖E j‖
  have hd : 0 ≤ d := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have he : 0 ≤ e := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hc : ⟪a, v⟫ * ⟪H, H₁⟫ ≤ (‖a‖ * ‖v‖) * (‖H‖ * ‖H₁‖) := by
    calc
      _ ≤ |⟪a, v⟫ * ⟪H, H₁⟫| := le_abs_self _
      _ = |⟪a, v⟫| * |⟪H, H₁⟫| := abs_mul _ _
      _ ≤ _ := mul_le_mul (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _) (abs_nonneg _) (by positivity)
  have hc₁ := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 8 by norm_num)
  have hc₂ := mul_le_mul_of_nonneg_left ((le_abs_self ⟪H, H₂⟫).trans (abs_real_inner_le_norm _ _))
    (show 0 ≤ 2 * ‖a‖ ^ 2 by positivity)
  calc
    _ ≤ 2 * ‖v‖ ^ 2 * ‖H‖ ^ 2 + 8 * (‖a‖ * ‖v‖) * (‖H‖ * ‖H₁‖) +
        2 * ‖a‖ ^ 2 * ‖H₁‖ ^ 2 + 2 * ‖a‖ ^ 2 * (‖H‖ * ‖H₂‖) := by
      change 2 * ‖v‖ ^ 2 * ‖H‖ ^ 2 + 8 * ⟪a, v⟫ * ⟪H, H₁⟫ +
        2 * ‖a‖ ^ 2 * ‖H₁‖ ^ 2 + 2 * ‖a‖ ^ 2 * ⟪H, H₂⟫ ≤ _
      nlinarith only [hc₁, hc₂]
    _ ≤ 2 * ‖v‖ ^ 2 * (4 * ‖a‖ ^ 2 * d) ^ 2 +
        8 * (‖a‖ * ‖v‖) * ((4 * ‖a‖ ^ 2 * d) * (8 * ‖a‖ * ‖v‖ * d + 4 * ‖a‖ ^ 2 * e)) +
        2 * ‖a‖ ^ 2 * (8 * ‖a‖ * ‖v‖ * d + 4 * ‖a‖ ^ 2 * e) ^ 2 +
        2 * ‖a‖ ^ 2 * ((4 * ‖a‖ ^ 2 * d) * (8 * ‖v‖ ^ 2 * d + 16 * ‖a‖ * ‖v‖ * e)) := by
      gcongr <;> first | exact norm_angularCurl_le a D | exact norm_angularCurlRate_le a D v E |
        exact norm_angularCurlSecondVariation_le a D v E
    _ ≤ _ := by
      change _ ≤ 672 * ‖a‖ ^ 4 * ‖v‖ ^ 2 * d ^ 2 + 224 * ‖a‖ ^ 6 * e ^ 2
      nlinarith only [sq_nonneg (‖a‖ ^ 2 * ‖v‖ * d - ‖a‖ ^ 3 * e)]

theorem sum_norm_sq_le_three (D : Fin 3 → R3) :
    (∑ j : Fin 3, ‖D j‖) ^ 2 ≤ 3 * ∑ j : Fin 3, ‖D j‖ ^ 2 := by
  simp only [Fin.sum_univ_three]
  nlinarith only [sq_nonneg (‖D 0‖ - ‖D 1‖), sq_nonneg (‖D 0‖ - ‖D 2‖),
    sq_nonneg (‖D 1‖ - ‖D 2‖)]

theorem angularCurlDensitySecondVariation_le (a : R3) (D : Fin 3 → R3)
    (v : R3) (E : Fin 3 → R3) :
    angularCurlDensitySecondVariation a D v E ≤
      2016 * ‖a‖ ^ 4 * ‖v‖ ^ 2 * (∑ j : Fin 3, ‖D j‖ ^ 2) +
        672 * ‖a‖ ^ 6 * ∑ j : Fin 3, ‖E j‖ ^ 2 := by
  have h₁ := mul_le_mul_of_nonneg_left (sum_norm_sq_le_three D)
    (show 0 ≤ 672 * ‖a‖ ^ 4 * ‖v‖ ^ 2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left (sum_norm_sq_le_three E)
    (show 0 ≤ 224 * ‖a‖ ^ 6 by positivity)
  nlinarith only [angularCurlDensitySecondVariation_le_norm_sums a D v E, h₁, h₂]

end Mettapedia.Analysis.AngularCurlDecomposition
