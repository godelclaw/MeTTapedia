import Mettapedia.Analysis.AnnularRieszKernel

/-!
# Explicitly radial smooth Riesz regularization

The cutoff is a one-dimensional bump evaluated at the squared Euclidean
norm. Its invariance under every linear isometry is therefore proved,
independently of the choice used to construct the scalar bump.

The compact symbols agree with a contractive radial weight times the
second-order Riesz entries. The weights tend to one at every frequency
of norm at least one. A radial Schwartz potential is constructed as well.
No radiality of an existing periodic kernel, or uniform spatial moment
bound for this new family, is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialRieszRegularization

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform ContDiff Topology

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

def scalarBump : ContDiffBump (0 : ℝ) := ⟨1, 4, by norm_num, by norm_num⟩

def lowPass (x : Rd) : ℝ := scalarBump (‖x‖ ^ 2)

theorem lowPass_nonneg (x : Rd) : 0 ≤ lowPass x := scalarBump.nonneg

theorem lowPass_le_one (x : Rd) : lowPass x ≤ 1 := scalarBump.le_one

theorem lowPass_eq_one (x : Rd) (hx : ‖x‖ ≤ 1) : lowPass x = 1 := by
  apply scalarBump.one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
  change ‖x‖ ^ 2 ≤ 1
  nlinarith [norm_nonneg x]

theorem lowPass_eq_zero (x : Rd) (hx : 2 ≤ ‖x‖) : lowPass x = 0 := by
  apply scalarBump.zero_of_le_dist
  simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
  change 4 ≤ ‖x‖ ^ 2
  nlinarith

theorem contDiff_lowPass : ContDiff ℝ ∞ (lowPass (d := d)) :=
  scalarBump.contDiff.comp (contDiff_norm_sq ℝ)

theorem lowPass_isometry (A : Rd ≃ₗᵢ[ℝ] Rd) (x : Rd) : lowPass (A x) = lowPass x := by
  simp only [lowPass, A.norm_map]

def weight (N : ℕ) (x : Rd) : ℝ :=
  (1 - lowPass ((2 : ℝ) • x)) * lowPass (((1 / 2 : ℝ) ^ N) • x)

theorem weight_nonneg (N : ℕ) (x : Rd) : 0 ≤ weight N x :=
  mul_nonneg (sub_nonneg.mpr (lowPass_le_one _)) (lowPass_nonneg _)

theorem weight_le_one (N : ℕ) (x : Rd) : weight N x ≤ 1 := by
  apply (mul_le_mul_of_nonneg_left (lowPass_le_one _) (sub_nonneg.mpr (lowPass_le_one _))).trans
  simpa only [mul_one] using sub_le_self (1 : ℝ) (lowPass_nonneg ((2 : ℝ) • x))

theorem weight_eq_zero_of_norm_le (N : ℕ) (x : Rd) (hx : ‖x‖ ≤ 1 / 2) : weight N x = 0 := by
  have h : lowPass ((2 : ℝ) • x) = 1 := lowPass_eq_one _ (by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith)
  simp only [weight, h, sub_self, zero_mul]

theorem contDiff_weight (N : ℕ) : ContDiff ℝ ∞ (weight (d := d) N) := by
  have hs : ContDiff ℝ ∞ (fun x : Rd ↦ (2 : ℝ) • x) := contDiff_id.const_smul 2
  have h₁ : ContDiff ℝ ∞ (fun x : Rd ↦ lowPass ((2 : ℝ) • x)) :=
    (contDiff_lowPass (d := d)).comp hs
  have hs₂ : ContDiff ℝ ∞ (fun x : Rd ↦ ((1 / 2 : ℝ) ^ N) • x) :=
    contDiff_id.const_smul _
  have h₂ : ContDiff ℝ ∞ (fun x : Rd ↦ lowPass (((1 / 2 : ℝ) ^ N) • x)) :=
    (contDiff_lowPass (d := d)).comp hs₂
  exact (contDiff_const.sub h₁).mul h₂

theorem weight_isometry (N : ℕ) (A : Rd ≃ₗᵢ[ℝ] Rd) (x : Rd) : weight N (A x) = weight N x := by
  simp only [weight, ← A.map_smul, lowPass_isometry]

theorem hasCompactSupport_weight (N : ℕ) : HasCompactSupport (weight (d := d) N) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Rd) (2 * 2 ^ N))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  have hscale : (1 / 2 : ℝ) ^ N * 2 ^ N = 1 := by rw [← mul_pow]; norm_num
  have h : 2 ≤ ‖((1 / 2 : ℝ) ^ N) • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have hmul := mul_le_mul_of_nonneg_left (le_of_not_ge hn) (by positivity : 0 ≤ (1 / 2 : ℝ) ^ N)
    nlinarith [hscale]
  exact hx (by simp only [weight, lowPass_eq_zero _ h, mul_zero])

theorem weight_eq_lowPass_sub (N : ℕ) (x : Rd) :
    weight N x = lowPass (((1 / 2 : ℝ) ^ N) • x) - lowPass ((2 : ℝ) • x) := by
  by_cases hx : 1 ≤ ‖x‖
  · have hz := lowPass_eq_zero ((2 : ℝ) • x) (by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith)
    simp only [weight, hz, sub_zero, one_mul]
  · have ho : lowPass (((1 / 2 : ℝ) ^ N) • x) = 1 := lowPass_eq_one _ (by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      have hp : (1 / 2 : ℝ) ^ N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      exact (mul_le_mul_of_nonneg_right hp (norm_nonneg x)).trans (by simpa using le_of_not_ge hx))
    simp only [weight, ho, mul_one]

theorem tendsto_weight (x : Rd) (hx : 1 ≤ ‖x‖) :
    Tendsto (fun N : ℕ ↦ weight N x) atTop (𝓝 1) := by
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).smul_const x
  have h := contDiff_lowPass.continuous.continuousAt.tendsto.comp hp
  have hz : lowPass ((2 : ℝ) • x) = 0 := lowPass_eq_zero _ (by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith)
  simpa only [weight, hz, sub_zero, one_mul, zero_smul, lowPass_eq_one 0 (by simp),
    Function.comp_def] using h

def denominator (x : Rd) : ℝ := ‖x‖ ^ 2 + lowPass ((4 : ℝ) • x)

theorem denominator_pos (x : Rd) : 0 < denominator x := by
  by_cases hx : x = 0
  · simp only [denominator, hx, smul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
      lowPass_eq_one 0 (by simp), zero_add, zero_lt_one]
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hx)) (lowPass_nonneg _)

theorem contDiff_denominator : ContDiff ℝ ∞ (denominator (d := d)) := by
  have hs : ContDiff ℝ ∞ (fun x : Rd ↦ (4 : ℝ) • x) := contDiff_id.const_smul 4
  have h : ContDiff ℝ ∞ (fun x : Rd ↦ lowPass ((4 : ℝ) • x)) :=
    (contDiff_lowPass (d := d)).comp hs
  exact (contDiff_norm_sq ℝ).add h

theorem denominator_eq_norm_sq (N : ℕ) (x : Rd) (hx : weight N x ≠ 0) :
    denominator x = ‖x‖ ^ 2 := by
  have hn : 1 / 2 < ‖x‖ := by
    by_contra h
    exact hx (weight_eq_zero_of_norm_le N x (le_of_not_gt h))
  have hz := lowPass_eq_zero ((4 : ℝ) • x) (by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    linarith)
  simp only [denominator, hz, add_zero]

def potentialEntry (N : ℕ) (x : Rd) : ℝ := weight N x / denominator x

theorem contDiff_potentialEntry (N : ℕ) : ContDiff ℝ ∞ (potentialEntry (d := d) N) :=
  (contDiff_weight N).div contDiff_denominator (fun x ↦ (denominator_pos x).ne')

theorem hasCompactSupport_potentialEntry (N : ℕ) :
    HasCompactSupport (potentialEntry (d := d) N) := by
  have he : potentialEntry (d := d) N = weight N * (fun x ↦ (denominator x)⁻¹) := by
    funext x
    exact div_eq_mul_inv _ _
  rw [he]
  exact (hasCompactSupport_weight N).mul_right

def potentialSymbol (N : ℕ) : 𝓢(Rd, ℂ) :=
  ((hasCompactSupport_potentialEntry (d := d) N).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (contDiff_potentialEntry (d := d) N))

def potential (N : ℕ) : 𝓢(Rd, ℂ) := 𝓕⁻ (potentialSymbol N)

theorem potentialSymbol_isometry (N : ℕ) (A : Rd ≃ₗᵢ[ℝ] Rd) (x : Rd) :
    potentialSymbol N (A x) = potentialSymbol N x := by
  change (potentialEntry N (A x) : ℂ) = (potentialEntry N x : ℂ)
  simp only [potentialEntry, weight_isometry, denominator, A.norm_map, ← A.map_smul, lowPass_isometry]

theorem potential_isometry (N : ℕ) (A : Rd ≃ₗᵢ[ℝ] Rd) (x : Rd) :
    potential N (A x) = potential N x := by
  have he : ((potentialSymbol N : 𝓢(Rd, ℂ)) : Rd → ℂ) ∘ A = potentialSymbol N :=
    funext (potentialSymbol_isometry N A)
  simpa only [potential, SchwartzMap.fourierInv_coe, he] using
    (Real.fourierInv_comp_linearIsometry A (potentialSymbol N : Rd → ℂ) x).symm

def entry (N : ℕ) (i j : Fin d) (x : Rd) : ℝ := x i * x j * potentialEntry N x

theorem entry_eq_weight_mul (N : ℕ) (i j : Fin d) (x : Rd) :
    entry N i j x = weight N x * AnnularRieszKernel.rieszEntry i j x := by
  by_cases hx : weight N x = 0
  · simp only [entry, potentialEntry, hx, zero_div, mul_zero, zero_mul]
  · simp only [entry, potentialEntry, denominator_eq_norm_sq N x hx, AnnularRieszKernel.rieszEntry]
    ring

end Mettapedia.Analysis.RadialRieszRegularization
