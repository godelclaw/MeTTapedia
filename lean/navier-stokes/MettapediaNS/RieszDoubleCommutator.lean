import NavierStokes.R3.HeatKernelCommutator
import NavierStokes.R3.RieszPairing

/-!
# Second cutoff differences for the actual double Riesz transform

The upstream single commutator is applied twice, before taking norms. Its
heat kernel consequently carries the square of the multiplier difference.
The Fourier operator, heat representation, and absolute-integrability
arguments are imported, not reconstructed here.
-/

noncomputable section

open Set MeasureTheory
open NavierStokesR3.ProblemStatement NavierStokesR3.Comparison
open scoped ENNReal

namespace Mettapedia.Analysis.RieszDoubleCommutator

/-- The second commutator kernel, retaining both cutoff differences. -/
def kernel (i j : Fin 3) (φ : Space → ℝ) (x y : Space) : ℝ :=
  heatCommutatorKernel i j φ x y * cutoffSquareDifference φ x y

theorem kernel_eq_integral (i j : Fin 3) (φ : Space → ℝ) (x y : Space) :
    kernel i j φ x y = ∫ s in Ioi (0 : ℝ),
      heatKernelSecond s i j (x - y) * cutoffSquareDifference φ x y ^ 2 := by
  simp only [kernel, heatCommutatorKernel, cancelledTimeKernel, ← integral_mul_const]
  congr 1
  funext s
  ring

theorem measurable_kernel (i j : Fin 3) {φ : Space → ℝ} (hφ : Measurable φ) :
    Measurable (Function.uncurry (kernel i j φ)) := by
  exact (heatCommutatorKernel_measurable i j hφ).mul
    (((hφ.comp measurable_snd).pow_const 2).sub ((hφ.comp measurable_fst).pow_const 2))

/-- Both differences survive in the pointwise majorant. No derivative of the
source is taken, and no sign is discarded in the preceding identity. -/
theorem norm_kernel_le (i j : Fin 3) {φ : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖) (x y : Space) :
    ‖kernel i j φ x y‖ ≤ heatKernelTimeConstant * (max (2 * L) 1) ^ 2 *
      (‖x - y‖ ^ (-3 : ℝ) * (min (‖x - y‖ / R) 1) ^ 2) := by
  have h₁ := heatCommutatorKernel_bound i j hR hφ hLip x y
  have h₂ := cutoffSquareDifference_abs_le_scaled_min hR hφ hLip x y
  rw [kernel, norm_mul, Real.norm_eq_abs (cutoffSquareDifference φ x y)]
  calc
    _ ≤ ((heatKernelTimeConstant * max (2 * L) 1) * radialCommutatorKernel R (x - y)) *
        (max (2 * L) 1 * min (‖x - y‖ / R) 1) :=
      mul_le_mul h₁ h₂ (abs_nonneg _)
        (mul_nonneg (mul_nonneg heatKernelTimeConstant_pos.le
          (le_trans zero_le_one (le_max_right _ _))) (radialCommutatorKernel_nonneg hR _))
    _ = _ := by unfold radialCommutatorKernel; ring

/-- The actual Fourier-defined iterated commutator is an absolutely convergent
kernel integral. The three tests represent `ψ`, `φ² ψ`, and `φ⁴ ψ`. -/
theorem riesz_double_commutator_eq_integral (i j : Fin 3)
    {φ : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (ψ ψh ψhh : ComplexTest)
    (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x)
    (hψhh : ∀ x, ψhh x = φ x ^ 2 • ψh x) (x : Space) :
    rieszTest i j ψhh x - (2 : ℝ) • (φ x ^ 2 • rieszTest i j ψh x) +
      φ x ^ 4 • rieszTest i j ψ x = ∫ y, kernel i j φ x y • ψ y := by
  have h₁ := riesz_commutator_eq_heatKernel i j hR hφm hφ hLip
    ψh ψhh hψhh (ψh.memLp 4) x
  have h₂ := riesz_commutator_eq_heatKernel i j hR hφm hφ hLip
    ψ ψh hψh (ψ.memLp 4) x
  have hi₁ := heatKernel_commutator_section_integrable i j hR hφm hφ hLip
    (ψh.memLp 4) x
  have hi₂ := heatKernel_commutator_section_integrable i j hR hφm hφ hLip
    (ψ.memLp 4) x
  calc
    _ = (rieszTest i j ψhh x - φ x ^ 2 • rieszTest i j ψh x) -
        φ x ^ 2 • (rieszTest i j ψh x - φ x ^ 2 • rieszTest i j ψ x) := by
      simp only [smul_sub, smul_smul]
      module
    _ = (∫ y, heatCommutatorKernel i j φ x y • ψh y) -
        φ x ^ 2 • ∫ y, heatCommutatorKernel i j φ x y • ψ y := by rw [h₁, h₂]
    _ = ∫ y, (heatCommutatorKernel i j φ x y • ψh y -
        φ x ^ 2 • (heatCommutatorKernel i j φ x y • ψ y)) := by
      rw [← integral_smul]
      exact (integral_sub hi₁ (hi₂.smul (φ x ^ 2))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hψh y]
      exact cutoffSquareDifference_smul (heatCommutatorKernel i j φ x y) φ (ψ y) x y

/-- An `L²` majorant obtained from the upstream `L^(4/3)` radial kernel by
mathlib's power change of exponent. -/
def radialMajorant (R : ℝ) (z : Space) : ℝ :=
  R ^ (-1 : ℝ) * ‖radialCommutatorKernel R z‖ ^ (2 / 3 : ℝ)

private theorem radial_secondDifference_le_one (z : Space) :
    ‖z‖ ^ (-3 : ℝ) * (min ‖z‖ 1) ^ 2 ≤
      ‖radialCommutatorKernel 1 z‖ ^ (2 / 3 : ℝ) := by
  by_cases hz : z = 0
  · simp [hz]
  have hn := norm_pos_iff.mpr hz
  rw [Real.norm_eq_abs, abs_of_nonneg (radialCommutatorKernel_nonneg zero_lt_one z)]
  unfold radialCommutatorKernel
  rw [div_one]
  by_cases hsmall : ‖z‖ ≤ 1
  · rw [min_eq_left hsmall]
    have heq : ‖z‖ ^ (-3 : ℝ) * ‖z‖ = ‖z‖ ^ (-2 : ℝ) := by
      calc
        _ = ‖z‖ ^ (-3 : ℝ) * ‖z‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hn]; norm_num
    have heq₂ : ‖z‖ ^ (-3 : ℝ) * ‖z‖ ^ 2 = ‖z‖ ^ (-1 : ℝ) := by
      rw [← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_add hn]
      norm_num
    rw [heq, heq₂, ← Real.rpow_mul hn.le]
    exact Real.rpow_le_rpow_of_exponent_ge hn hsmall (by norm_num)
  · rw [min_eq_right (le_of_not_ge hsmall), one_pow, mul_one,
      ← Real.rpow_mul hn.le]
    exact Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hsmall) (by norm_num)

theorem radial_secondDifference_le {R : ℝ} (hR : 0 < R) (z : Space) :
    ‖z‖ ^ (-3 : ℝ) * (min (‖z‖ / R) 1) ^ 2 ≤ radialMajorant R z := by
  have hn : ‖R⁻¹ • z‖ = ‖z‖ / R := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR),
      div_eq_mul_inv, mul_comm]
  have hscale : radialMajorant R z =
      R ^ (-3 : ℝ) * ‖radialCommutatorKernel 1 (R⁻¹ • z)‖ ^ (2 / 3 : ℝ) := by
    rw [radialMajorant, radialCommutatorKernel_scale hR, norm_mul,
      Real.norm_of_nonneg (Real.rpow_nonneg hR.le _),
      Real.mul_rpow (Real.rpow_nonneg hR.le _) (norm_nonneg _),
      ← Real.rpow_mul hR.le, ← mul_assoc, ← Real.rpow_add hR]
    norm_num
  rw [hscale]
  calc
    _ = R ^ (-3 : ℝ) * (‖R⁻¹ • z‖ ^ (-3 : ℝ) * (min ‖R⁻¹ • z‖ 1) ^ 2) := by
      calc
        _ = radialCommutatorKernel R z * min (‖z‖ / R) 1 := by
          unfold radialCommutatorKernel; ring
        _ = _ := by
          rw [radialCommutatorKernel_scale hR]
          simp only [radialCommutatorKernel, div_one, hn]
          ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (radial_secondDifference_le_one _)
      (Real.rpow_nonneg hR.le _)

theorem memLp_radialMajorant {R : ℝ} (hR : 0 < R) :
    MemLp (radialMajorant R) 2 volume := by
  have h := (radialCommutatorKernel_memLp hR).norm_rpow_div (2 / 3)
  have hexp : (4 / 3 : ℝ≥0∞) / (2 / 3) = 2 := by
    calc
      _ = (4 * (3 : ℝ≥0∞)⁻¹) / (2 * (3 : ℝ≥0∞)⁻¹) := rfl
      _ = 4 / 2 := ENNReal.mul_div_mul_right 4 2 (by norm_num) (by norm_num)
      _ = 2 := by
        rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, mul_div_assoc,
          ENNReal.div_self (by norm_num) (by norm_num), mul_one]
  rw [hexp] at h
  change MemLp (fun z => R ^ (-1 : ℝ) * ‖radialCommutatorKernel R z‖ ^ (2 / 3 : ℝ)) 2 volume
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using
    h.const_mul (R ^ (-1 : ℝ))

theorem lpNorm_radialMajorant {R : ℝ} (hR : 0 < R) :
    comparisonLpNorm 2 (radialMajorant R) =
      comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
        R ^ (-(3 / 2) : ℝ) := by
  have hexp : (2 : ℝ≥0∞) * ENNReal.ofReal (2 / 3 : ℝ) = 4 / 3 := by
    norm_num [ENNReal.ofReal_div_of_pos, ← mul_div_assoc]
  change comparisonLpNorm 2 (fun z => R ^ (-1 : ℝ) •
    (‖radialCommutatorKernel R z‖ ^ (2 / 3 : ℝ))) = _
  rw [NavierStokesR3.PairedKernelBound.lpNorm_const_smul_of_nonneg
    (Real.rpow_nonneg hR.le _)]
  unfold comparisonLpNorm
  rw [eLpNorm_norm_rpow _ (by norm_num : (0 : ℝ) < 2 / 3), hexp,
    ← ENNReal.toReal_rpow]
  change R ^ (-1 : ℝ) * comparisonLpNorm (4 / 3) (radialCommutatorKernel R) ^ (2 / 3 : ℝ) = _
  have hnorm : 0 ≤ comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) := ENNReal.toReal_nonneg
  rw [radialCommutatorKernel_lpNorm_scale hR,
    Real.mul_rpow hnorm (Real.rpow_nonneg hR.le _),
    ← Real.rpow_mul hR.le]
  calc
    _ = comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
        (R ^ (-1 : ℝ) * R ^ ((-(3 / 4) : ℝ) * (2 / 3))) := by ring
    _ = _ := by rw [← Real.rpow_add hR]; norm_num [comparisonLpNorm]

theorem norm_kernel_le_radialMajorant (i j : Fin 3) {φ : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖) (x y : Space) :
    ‖kernel i j φ x y‖ ≤
      (heatKernelTimeConstant * (max (2 * L) 1) ^ 2) * radialMajorant R (x - y) :=
  (norm_kernel_le i j hR hφ hLip x y).trans
    (mul_le_mul_of_nonneg_left (radial_secondDifference_le hR _)
      (mul_nonneg heatKernelTimeConstant_pos.le (sq_nonneg _)))

/-- A square-integrable source suffices for actual section integrability. -/
theorem kernel_section_memLp (i j : Fin 3) {φ : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖) (x : Space) :
    MemLp (kernel i j φ x) 2 volume := by
  have hm : AEStronglyMeasurable (kernel i j φ x) volume :=
    ((measurable_kernel i j hφm).comp measurable_prodMk_left).aestronglyMeasurable
  have hk := ((memLp_radialMajorant hR).const_mul
    (heatKernelTimeConstant * (max (2 * L) 1) ^ 2)).comp_measurePreserving
      (volume.measurePreserving_sub_left x)
  exact hk.mono' hm (Filter.Eventually.of_forall (norm_kernel_le_radialMajorant i j hR hφ hLip x))

theorem integrable_kernel_smul (i j : Fin 3) {φ : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    {f : Space → ℂ} (hf : MemLp f 2 volume) (x : Space) :
    Integrable (fun y => kernel i j φ x y • f y) volume :=
  memLp_one_iff_integrable.mp (hf.smul (kernel_section_memLp i j hR hφm hφ hLip x))

/-- Uniform `L²`-to-pointwise control, with the improved `R^(-3/2)` scaling.
This is a spatial estimate; the cutoff's Lipschitz parameter is explicit. -/
theorem norm_integral_kernel_smul_le (i j : Fin 3) {φ : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    {f : Space → ℂ} (hf : MemLp f 2 volume) (x : Space) :
    ‖∫ y, kernel i j φ x y • f y‖ ≤
      (heatKernelTimeConstant * (max (2 * L) 1) ^ 2) *
        comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
        R ^ (-(3 / 2) : ℝ) * comparisonLpNorm 2 f := by
  let D := heatKernelTimeConstant * (max (2 * L) 1) ^ 2
  have hD : 0 ≤ D := mul_nonneg heatKernelTimeConstant_pos.le (sq_nonneg _)
  have hk := kernel_section_memLp i j hR hφm hφ hLip x
  have hkbound : comparisonLpNorm 2 (kernel i j φ x) ≤ D * comparisonLpNorm 2 (radialMajorant R) := by
    have hb := eLpNorm_mono_ae_real (p := (2 : ℝ≥0∞)) (μ := volume)
      (Filter.Eventually.of_forall (norm_kernel_le_radialMajorant i j hR hφ hLip x))
    have hi := ((memLp_radialMajorant hR).const_mul D).comp_measurePreserving
      (volume.measurePreserving_sub_left x)
    have ht := ENNReal.toReal_mono hi.eLpNorm_ne_top hb
    change comparisonLpNorm 2 (kernel i j φ x) ≤
      comparisonLpNorm 2 (fun y => D • radialMajorant R (x - y)) at ht
    rw [NavierStokesR3.PairedKernelBound.lpNorm_const_smul_of_nonneg hD,
      NavierStokesR3.PairedKernelBound.lpNorm_sub_left
        (memLp_radialMajorant hR).aestronglyMeasurable x] at ht
    exact ht
  have hmul := eLpNorm_smul_le_mul_eLpNorm (𝕜 := ℝ) (p := 2) (q := 2) (r := 1)
    hf.aestronglyMeasurable hk.aestronglyMeasurable
  have hnorm := ENNReal.toReal_mono (ENNReal.mul_ne_top hk.eLpNorm_ne_top hf.eLpNorm_ne_top) hmul
  change comparisonLpNorm 1 (fun y => kernel i j φ x y • f y) ≤ _ at hnorm
  rw [NavierStokesR3.PairedKernelBound.lpNorm_one_eq_integral_norm
    (integrable_kernel_smul i j hR hφm hφ hLip hf x).aestronglyMeasurable,
    ENNReal.toReal_mul] at hnorm
  calc
    _ ≤ ∫ y, ‖kernel i j φ x y • f y‖ := norm_integral_le_integral_norm _
    _ ≤ comparisonLpNorm 2 (kernel i j φ x) * comparisonLpNorm 2 f := hnorm
    _ ≤ (D * comparisonLpNorm 2 (radialMajorant R)) * comparisonLpNorm 2 f :=
      mul_le_mul_of_nonneg_right hkbound ENNReal.toReal_nonneg
    _ = _ := by rw [lpNorm_radialMajorant hR]; dsimp [D]; ring

theorem norm_riesz_double_commutator_le (i j : Fin 3)
    {φ : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (ψ ψh ψhh : ComplexTest)
    (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x)
    (hψhh : ∀ x, ψhh x = φ x ^ 2 • ψh x) (x : Space) :
    ‖rieszTest i j ψhh x - (2 : ℝ) • (φ x ^ 2 • rieszTest i j ψh x) +
      φ x ^ 4 • rieszTest i j ψ x‖ ≤
      (heatKernelTimeConstant * (max (2 * L) 1) ^ 2) *
        comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
        R ^ (-(3 / 2) : ℝ) * comparisonLpNorm 2 (fun x => ψ x) := by
  rw [riesz_double_commutator_eq_integral i j hR hφm hφ hLip ψ ψh ψhh hψh hψhh x]
  exact norm_integral_kernel_smul_le i j hR hφm hφ hLip (ψ.memLp 2) x

/-- Self-adjointness turns the signed quadratic localization defect into half
the double commutator pairing. This is bilinear; for real tests it is the
usual real quadratic-form identity. -/
theorem localization_defect_eq_double_commutator (i j : Fin 3)
    (φ : Space → ℝ) (ψ ψh ψhh : ComplexTest)
    (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x)
    (hψhh : ∀ x, ψhh x = φ x ^ 2 • ψh x) :
    (2 : ℂ) * ((∫ x, ψh x * rieszTest i j ψh x) -
      ∫ x, ψhh x * rieszTest i j ψ x) =
      -(∫ x, ψ x * (rieszTest i j ψhh x -
        (2 : ℝ) • (φ x ^ 2 • rieszTest i j ψh x) + φ x ^ 4 • rieszTest i j ψ x)) := by
  have hi₀ := NavierStokesR3.RieszTestOperators.integrable_mul_rieszTest i j ψhh ψ.integrable
  have hi₁ := NavierStokesR3.RieszTestOperators.integrable_mul_rieszTest i j ψh ψh.integrable
  have hi₂ := NavierStokesR3.RieszTestOperators.integrable_mul_rieszTest i j ψ ψhh.integrable
  have hexpand : (fun x => ψ x * (rieszTest i j ψhh x -
      (2 : ℝ) • (φ x ^ 2 • rieszTest i j ψh x) + φ x ^ 4 • rieszTest i j ψ x)) =
      (fun x => (ψ x * rieszTest i j ψhh x - (2 : ℂ) * (ψh x * rieszTest i j ψh x)) +
        ψhh x * rieszTest i j ψ x) := by
    funext x
    rw [hψhh x, hψh x]
    simp only [Algebra.smul_def, map_pow, map_ofNat]
    ring
  have hs : (∫ x, ψ x * rieszTest i j ψhh x) = ∫ x, ψhh x * rieszTest i j ψ x := by
    calc
      _ = ∫ x, rieszTest i j ψhh x * ψ x := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact mul_comm _ _
      _ = _ := NavierStokesR3.RieszTestOperators.rieszTest_selfAdjoint i j ψhh ψ
  have hiC : Integrable (fun x => (2 : ℂ) * (ψh x * rieszTest i j ψh x)) := hi₁.const_mul 2
  have hiSub : Integrable (fun x => ψ x * rieszTest i j ψhh x -
      (2 : ℂ) * (ψh x * rieszTest i j ψh x)) := hi₀.sub hiC
  rw [hexpand, integral_add hiSub hi₂, integral_sub hi₀ hiC, integral_const_mul, hs]
  ring

/-- The signed localization defect has a source `L¹`-`L²` estimate, not the
single-commutator `L¹`-`L⁴` cost. The estimate does not control the physical-time
growth of the cutoff parameters or identify a general NS residual with this defect. -/
theorem norm_localization_defect_le (i j : Fin 3)
    {φ : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (ψ ψh ψhh : ComplexTest)
    (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x)
    (hψhh : ∀ x, ψhh x = φ x ^ 2 • ψh x) :
    ‖(∫ x, ψh x * rieszTest i j ψh x) - ∫ x, ψhh x * rieszTest i j ψ x‖ ≤
      (heatKernelTimeConstant * (max (2 * L) 1) ^ 2 / 2) *
        comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
        R ^ (-(3 / 2) : ℝ) * comparisonLpNorm 1 (fun x => ψ x) *
        comparisonLpNorm 2 (fun x => ψ x) := by
  let C := (heatKernelTimeConstant * (max (2 * L) 1) ^ 2) *
    comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
    R ^ (-(3 / 2) : ℝ) * comparisonLpNorm 2 (fun x => ψ x)
  have hb : ‖∫ x, ψ x * (rieszTest i j ψhh x -
      (2 : ℝ) • (φ x ^ 2 • rieszTest i j ψh x) + φ x ^ 4 • rieszTest i j ψ x)‖ ≤
      comparisonLpNorm 1 (fun x => ψ x) * C := by
    calc
      _ ≤ ∫ x, ‖ψ x‖ * C := norm_integral_le_of_norm_le (ψ.integrable.norm.mul_const C)
        (Filter.Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (norm_riesz_double_commutator_le i j hR hφm hφ hLip ψ ψh ψhh hψh hψhh x)
            (norm_nonneg _))
      _ = _ := by
        rw [integral_mul_const, ← NavierStokesR3.PairedKernelBound.lpNorm_one_eq_integral_norm
          ψ.integrable.aestronglyMeasurable]
  have heq := congrArg norm (localization_defect_eq_double_commutator i j φ ψ ψh ψhh hψh hψhh)
  simp only [norm_mul, norm_neg] at heq
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num] at heq
  rw [← heq] at hb
  calc
    _ ≤ comparisonLpNorm 1 (fun x => ψ x) * C / 2 := by linarith
    _ = _ := by dsimp [C]; ring

end Mettapedia.Analysis.RieszDoubleCommutator
