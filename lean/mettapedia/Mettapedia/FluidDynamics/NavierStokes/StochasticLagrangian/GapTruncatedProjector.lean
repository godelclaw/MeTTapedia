import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralGapTiltWeight

/-!
# Quantitative gap truncation of the expanding projector

Multiplying the top projector by a linear gap ramp removes its collision
discontinuity with a global Lipschitz estimate. Dividing by the truncated
gap retains a quantitative bound, rather than merely continuity. The
constants below are convenient bounds, not sharp perturbation constants.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GapTruncatedProjector

open scoped BigOperators RealInnerProductSpace
open PancakeStrainSpectralFrame PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeTopEigenvalueDerivative StrainEigenvalueContinuity SpectralGapTiltWeight

local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem abs_trace_sub_le (A B : SymmetricStrain) :
    |LinearMap.trace ℝ R3 A.1.toLinearMap - LinearMap.trace ℝ R3 B.1.toLinearMap| ≤
      3 * ‖A.1 - B.1‖ := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  rw [LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ b,
    ← Finset.sum_sub_distrib]
  have hp (j : Fin 3) : |⟪b j, A.1 (b j)⟫ - ⟪b j, B.1 (b j)⟫| ≤ ‖A.1 - B.1‖ := by
    rw [← inner_sub_right]
    have h := (abs_real_inner_le_norm (b j) ((A.1 - B.1) (b j))).trans
      (mul_le_mul_of_nonneg_left ((A.1 - B.1).le_opNorm (b j)) (norm_nonneg _))
    simpa only [b.norm_eq_one, one_mul, mul_one, sub_apply] using h
  have h : |∑ j : Fin 3, (⟪b j, A.1 (b j)⟫ - ⟪b j, B.1 (b j)⟫)| ≤
      ∑ _j : Fin 3, ‖A.1 - B.1‖ := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hp j))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, ContinuousLinearMap.coe_coe] using h

theorem abs_topGap_sub_le (A B : SymmetricStrain) :
    |topGap A - topGap B| ≤ 6 * ‖A.1 - B.1‖ := by
  have ht := lipschitzWith_topEigenvalue.dist_le_mul A B
  have hb := lipschitzWith_thirdEigenvalue.dist_le_mul A B
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm] at ht hb
  have htr := abs_trace_sub_le A B
  have hA := trace_eq_sum_orderedEigenvalues A
  have hB := trace_eq_sum_orderedEigenvalues B
  rcases abs_le.mp ht with ⟨htl, htu⟩
  rcases abs_le.mp hb with ⟨hbl, hbu⟩
  rcases abs_le.mp htr with ⟨hrl, hru⟩
  unfold topGap
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_gapCutoff_sub_le (gamma : ℝ) (hg : 0 < gamma) (a b : ℝ) :
    |gapCutoff gamma a - gapCutoff gamma b| ≤ |a - b| / gamma := by
  have hmax := abs_max_sub_max_le_max (0 : ℝ) (min 1 ((a - gamma) / gamma))
    0 (min 1 ((b - gamma) / gamma))
  have hmin := abs_min_sub_min_le_max (1 : ℝ) ((a - gamma) / gamma)
    1 ((b - gamma) / gamma)
  simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (_ : ℝ))] at hmax hmin
  have h := hmax.trans hmin
  have he : (a - gamma) / gamma - (b - gamma) / gamma = (a - b) / gamma := by ring
  simpa only [gapCutoff, he, abs_div, abs_of_pos hg] using h

theorem norm_topEigenlineProjector (S : SymmetricStrain) : ‖topEigenlineProjector S‖ = 1 := by
  simp only [topEigenlineProjector, PancakeEigenframePerturbation.lineProjector,
    InnerProductSpace.norm_rankOne, (orderedEigenframe S.1 S.2).eigenbasis.norm_eq_one, mul_one]

def gatedProjector (gamma : ℝ) (S : SymmetricStrain) : R3 →L[ℝ] R3 :=
  gapCutoff gamma (topGap S) • topEigenlineProjector S

theorem norm_gatedProjector_le_one (gamma : ℝ) (S : SymmetricStrain) :
    ‖gatedProjector gamma S‖ ≤ 1 := by
  rw [gatedProjector, norm_smul, norm_topEigenlineProjector, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (gapCutoff_nonneg _ _)]
  exact gapCutoff_le_one _ _

theorem norm_gatedProjector_sub_le (gamma : ℝ) (hg : 0 < gamma) (A B : SymmetricStrain) :
    ‖gatedProjector gamma A - gatedProjector gamma B‖ ≤ (14 / gamma) * ‖A.1 - B.1‖ := by
  have hc := (abs_gapCutoff_sub_le gamma hg (topGap A) (topGap B)).trans
    (div_le_div_of_nonneg_right (abs_topGap_sub_le A B) hg.le)
  have hid : gatedProjector gamma A - gatedProjector gamma B =
      (gapCutoff gamma (topGap A) - gapCutoff gamma (topGap B)) • topEigenlineProjector A +
      gapCutoff gamma (topGap B) • (topEigenlineProjector A - topEigenlineProjector B) := by
    unfold gatedProjector
    module
  by_cases hz : gapCutoff gamma (topGap B) = 0
  · rw [hid, hz, _root_.zero_smul ℝ (topEigenlineProjector A - topEigenlineProjector B),
      add_zero, norm_smul, norm_topEigenlineProjector,
      mul_one, Real.norm_eq_abs]
    rw [hz] at hc
    calc
      _ ≤ 6 * ‖A.1 - B.1‖ / gamma := hc
      _ ≤ _ := by
        have h := div_nonneg (norm_nonneg (A.1 - B.1)) hg.le
        simp only [div_eq_mul_inv] at h ⊢
        nlinarith only [h]
  · have hgap : gamma < topGap B := lt_of_not_ge (fun h ↦ hz (gapCutoff_eq_zero _ _ hg h))
    by_cases hclose : ‖A.1 - B.1‖ < topGap B / 2
    · have hp := norm_topEigenlineProjector_sub_le_of_norm_sub_lt_half_topGap A B
        (hg.trans hgap) hclose
      have hratio : 8 / topGap B ≤ 8 / gamma := div_le_div_of_nonneg_left (by norm_num) hg hgap.le
      have hp' := hp.trans (mul_le_mul_of_nonneg_right hratio (norm_nonneg _))
      rw [hid]
      have hn := norm_add_le
        ((gapCutoff gamma (topGap A) - gapCutoff gamma (topGap B)) • topEigenlineProjector A)
        (gapCutoff gamma (topGap B) • (topEigenlineProjector A - topEigenlineProjector B))
      simp only [norm_smul, norm_topEigenlineProjector, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (gapCutoff_nonneg gamma (topGap B))] at hn
      have hm := mul_le_mul_of_nonneg_right (gapCutoff_le_one gamma (topGap B))
        (norm_nonneg (topEigenlineProjector A - topEigenlineProjector B))
      simp only [div_eq_mul_inv] at hc hp' ⊢
      nlinarith only [hn, hc, hp', hm]
    · have hn := (norm_sub_le (gatedProjector gamma A) (gatedProjector gamma B)).trans
        (add_le_add (norm_gatedProjector_le_one gamma A) (norm_gatedProjector_le_one gamma B))
      have hlarge : gamma ≤ 2 * ‖A.1 - B.1‖ := by linarith [le_of_not_gt hclose]
      have hdiv : 1 ≤ 2 * ‖A.1 - B.1‖ / gamma := (le_div_iff₀ hg).mpr (by simpa using hlarge)
      simp only [div_eq_mul_inv] at hdiv ⊢
      nlinarith only [hn, hdiv]

def inverseGapProjector (gamma : ℝ) (S : SymmetricStrain) : R3 →L[ℝ] R3 :=
  (max (topGap S) gamma)⁻¹ • gatedProjector gamma S

theorem norm_inverseGapProjector_le (gamma : ℝ) (hg : 0 < gamma) (S : SymmetricStrain) :
    ‖inverseGapProjector gamma S‖ ≤ 1 / gamma := by
  rw [inverseGapProjector, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (hg.trans_le (le_max_right _ _)))]
  exact (mul_le_mul_of_nonneg_left (norm_gatedProjector_le_one gamma S) (by positivity)).trans
    (by simpa only [mul_one, one_div] using inv_anti₀ hg (le_max_right (topGap S) gamma))

theorem abs_inv_max_sub_le (gamma : ℝ) (hg : 0 < gamma) (a b : ℝ) :
    |(max a gamma)⁻¹ - (max b gamma)⁻¹| ≤ |a - b| / gamma ^ 2 := by
  have ha := hg.trans_le (le_max_right a gamma)
  have hb := hg.trans_le (le_max_right b gamma)
  rw [inv_sub_inv (ne_of_gt ha) (ne_of_gt hb), abs_div,
    abs_of_pos (mul_pos ha hb), abs_sub_comm]
  have hden : gamma ^ 2 ≤ max a gamma * max b gamma := by
    nlinarith only [mul_le_mul (le_max_right a gamma) (le_max_right b gamma) hg.le ha.le]
  exact (div_le_div_of_nonneg_right (abs_max_sub_max_le_abs a b gamma) (mul_pos ha hb).le).trans
    (div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hg) hden)

theorem norm_inverseGapProjector_sub_le (gamma : ℝ) (hg : 0 < gamma) (A B : SymmetricStrain) :
    ‖inverseGapProjector gamma A - inverseGapProjector gamma B‖ ≤
      (20 / gamma ^ 2) * ‖A.1 - B.1‖ := by
  have hid : inverseGapProjector gamma A - inverseGapProjector gamma B =
      (max (topGap A) gamma)⁻¹ • (gatedProjector gamma A - gatedProjector gamma B) +
      ((max (topGap A) gamma)⁻¹ - (max (topGap B) gamma)⁻¹) • gatedProjector gamma B := by
    unfold inverseGapProjector
    module
  have hratio : (max (topGap A) gamma)⁻¹ ≤ 1 / gamma := by
    simpa only [one_div] using inv_anti₀ hg (le_max_right (topGap A) gamma)
  have hscalar := (abs_inv_max_sub_le gamma hg (topGap A) (topGap B)).trans
    (div_le_div_of_nonneg_right (abs_topGap_sub_le A B) (sq_nonneg gamma))
  rw [hid]
  have hn := norm_add_le
    ((max (topGap A) gamma)⁻¹ • (gatedProjector gamma A - gatedProjector gamma B))
    (((max (topGap A) gamma)⁻¹ - (max (topGap B) gamma)⁻¹) • gatedProjector gamma B)
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (hg.trans_le (le_max_right (topGap A) gamma)))] at hn
  have hfirst := mul_le_mul hratio (norm_gatedProjector_sub_le gamma hg A B)
    (norm_nonneg _) (by positivity : 0 ≤ 1 / gamma)
  have hsecond := mul_le_mul hscalar (norm_gatedProjector_le_one gamma B)
    (norm_nonneg _) (by positivity : 0 ≤ 6 * ‖A.1 - B.1‖ / gamma ^ 2)
  calc
    _ ≤ (1 / gamma) * ((14 / gamma) * ‖A.1 - B.1‖) + 6 * ‖A.1 - B.1‖ / gamma ^ 2 * 1 :=
      hn.trans (add_le_add hfirst hsecond)
    _ = _ := by ring

theorem lipschitzWith_inverseGapProjector (gamma : ℝ) (hg : 0 < gamma) :
    LipschitzWith ⟨20 / gamma ^ 2, by positivity⟩ (inverseGapProjector gamma) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  rw [Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
  exact norm_inverseGapProjector_sub_le gamma hg A B

end Mettapedia.FluidDynamics.NavierStokes.GapTruncatedProjector
