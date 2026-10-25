import Mettapedia.QuantumTheory.AmplitudeSemantics
import Mettapedia.ProbabilityTheory.Moments.PowerCalibration
import Mettapedia.Analysis.CosinePowerIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Uniform-phase calibration of a power-law observation

The sample space, probability measure, and complex amplitudes are specified
independently of the Gamma expression used to evaluate their moments. The
normalization result concerns this declared power-law and uniform-phase model.
-/

namespace Mettapedia.QuantumTheory

open MeasureTheory AddCircle Real Set
open scoped ENNReal

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev Phase := AddCircle (1 : ℝ)
abbrev phaseMeasure : Measure Phase := AddCircle.haarAddCircle

/-- The standard unit-modulus character, with one complete turn per unit period. -/
noncomputable def phase (θ : Phase) : ℂ := fourier 1 θ

theorem continuous_phase : Continuous phase := (fourier 1).continuous

theorem phase_norm (θ : Phase) : ‖phase θ‖ = 1 := by
  change ‖fourier 1 θ‖ = 1
  rw [fourier_one]
  exact Circle.norm_coe _

theorem phase_add (θ φ : Phase) : phase (θ + φ) = phase θ * phase φ := by
  simp [phase, AddCircle.toCircle_add]

/-- A single uniformly distributed relative phase. -/
noncomputable def phaseMeanPower (p : ℝ) : ℝ :=
  ∫ θ, ‖(1 : ℂ) + phase θ‖ ^ p ∂phaseMeasure

/-- Two independently uniform source phases. -/
noncomputable def independentPhaseMeanPower (p : ℝ) : ℝ :=
  ∫ pair : Phase × Phase, ‖phase pair.1 + phase pair.2‖ ^ p
    ∂(phaseMeasure.prod phaseMeasure)

theorem continuous_phase_power {p : ℝ} (hp : 0 < p) :
    Continuous (fun θ => ‖(1 : ℂ) + phase θ‖ ^ p) :=
  (continuous_const.add continuous_phase).norm.rpow_const (fun _ => Or.inr hp.le)

theorem integrable_phase_power {p : ℝ} (hp : 0 < p) :
    Integrable (fun θ => ‖(1 : ℂ) + phase θ‖ ^ p) phaseMeasure :=
  (continuous_phase_power hp).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_independent_phase_power {p : ℝ} (hp : 0 < p) :
    Integrable (fun pair : Phase × Phase => ‖phase pair.1 + phase pair.2‖ ^ p)
      (phaseMeasure.prod phaseMeasure) := by
  have hc : Continuous (fun pair : Phase × Phase => ‖phase pair.1 + phase pair.2‖ ^ p) :=
    ((continuous_phase.comp continuous_fst).add
      (continuous_phase.comp continuous_snd)).norm.rpow_const (fun _ => Or.inr hp.le)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Removing a common unit phase preserves every power observation. -/
theorem common_phase_power (θ φ : Phase) (p : ℝ) :
    ‖phase θ + phase (φ + θ)‖ ^ p = ‖(1 : ℂ) + phase φ‖ ^ p := by
  rw [phase_add]
  have heq : phase θ + phase φ * phase θ = ((1 : ℂ) + phase φ) * phase θ := by ring
  rw [heq, norm_mul, phase_norm, mul_one]

theorem independent_phase_mean_eq_relative {p : ℝ} (hp : 0 < p) :
    independentPhaseMeanPower p = phaseMeanPower p := by
  have hinner (θ : Phase) :
      (∫ φ, ‖phase θ + phase φ‖ ^ p ∂phaseMeasure) = phaseMeanPower p := by
    rw [← integral_add_right_eq_self (fun φ : Phase => ‖phase θ + phase φ‖ ^ p) θ]
    simp_rw [common_phase_power]
    rfl
  rw [independentPhaseMeanPower, integral_prod _ (integrable_independent_phase_power hp)]
  simp_rw [hinner]
  simp

/-- Half a period changes the sign of the source amplitude. -/
theorem phase_half_shift (θ : Phase) :
    phase (θ + ((1 / 2 : ℝ) : Phase)) = -phase θ := by
  simpa [phase] using fourier_add_half_inv_index (T := 1) (n := 1)
    (by decide) (by norm_num) θ

/-- The second moment is obtained from phase symmetry, independently of Gamma evaluation. -/
theorem phaseMeanPower_two : phaseMeanPower 2 = 2 := by
  have hp : Integrable (fun θ : Phase => ‖(1 : ℂ) + phase θ‖ ^ 2) phaseMeasure := by
    simpa using integrable_phase_power (p := 2) (by norm_num)
  have hm : Integrable (fun θ : Phase => ‖(1 : ℂ) - phase θ‖ ^ 2) phaseMeasure :=
    ((continuous_const.sub continuous_phase).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heq := integral_add_right_eq_self (μ := phaseMeasure)
    (fun θ : Phase => ‖(1 : ℂ) + phase θ‖ ^ 2) (((1 / 2 : ℝ) : Phase))
  simp_rw [phase_half_shift, ← sub_eq_add_neg] at heq
  have hpoint (θ : Phase) : ‖(1 : ℂ) + phase θ‖ ^ 2 + ‖(1 : ℂ) - phase θ‖ ^ 2 = 4 := by
    have hu : Complex.normSq (phase θ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, phase_norm]
      norm_num
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply] at hu ⊢
    nlinarith [hu]
  have hsum : (∫ θ, ‖(1 : ℂ) + phase θ‖ ^ 2 ∂phaseMeasure) +
      (∫ θ, ‖(1 : ℂ) - phase θ‖ ^ 2 ∂phaseMeasure) = 4 := by
    rw [← integral_add hp hm]
    calc
      _ = ∫ _θ : Phase, (4 : ℝ) ∂phaseMeasure :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = 4 := by simp
  rw [heq] at hsum
  have hvalue : phaseMeanPower 2 = ∫ θ, ‖(1 : ℂ) + phase θ‖ ^ 2 ∂phaseMeasure := by
    simp [phaseMeanPower]
  linarith

open Mettapedia.ProbabilityTheory.Moments

theorem phase_powerMoment {p : ℝ} (hp : 0 < p) :
    powerMoment phaseMeasure (fun θ => (1 : ℂ) + phase θ) p =
      ENNReal.ofReal (phaseMeanPower p) := by
  rw [phaseMeanPower, ofReal_integral_eq_lintegral_ofReal (integrable_phase_power hp)
    (Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg _) _))]
  apply lintegral_congr
  intro θ
  simpa only [ofReal_norm] using!
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg ((1 : ℂ) + phase θ)) hp.le

/-- Normalization identifies the positive exponent, with no exponent equality in the premises. -/
theorem phase_normalization_iff {p : ℝ} (hp : 0 < p) : phaseMeanPower p = 2 ↔ p = 2 := by
  have hf : AEStronglyMeasurable (fun θ => (1 : ℂ) + phase θ) phaseMeasure :=
    (continuous_const.add continuous_phase).aestronglyMeasurable
  have h2 : powerMoment phaseMeasure (fun θ => (1 : ℂ) + phase θ) 2 = 2 := by
    rw [phase_powerMoment (by norm_num), phaseMeanPower_two]
    norm_num
  have hcal := powerMoment_eq_iff hf hp (show (0 : ℝ) < 2 by norm_num)
    (show 1 < powerMoment phaseMeasure (fun θ => (1 : ℂ) + phase θ) 2 by rw [h2]; norm_num)
    (show powerMoment phaseMeasure (fun θ => (1 : ℂ) + phase θ) 2 ≠ ∞ by rw [h2]; simp)
  refine ⟨fun heq => hcal.1 ?_, fun heq => heq ▸ phaseMeanPower_two⟩
  rw [phase_powerMoment hp, heq, h2]
  norm_num

theorem phase_real_re (t : ℝ) : (phase (t : Phase)).re = cos (2 * π * t) := by
  change (fourier (T := 1) 1 (t : Phase)).re = _
  rw [fourier_coe_apply]
  simp [Complex.exp_re]

/-- The geometric half-angle formula, prior to integration. -/
theorem phase_pair_norm (t : ℝ) :
    ‖(1 : ℂ) + phase (t : Phase)‖ = 2 * |cos (π * t)| := by
  have hs : ‖(1 : ℂ) + phase (t : Phase)‖ ^ 2 = 4 * cos (π * t) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    simp [Complex.normSq_eq_norm_sq, phase_norm, phase_real_re]
    rw [mul_assoc 2 π t, cos_two_mul]
    ring
  nlinarith [sq_abs (cos (π * t)), norm_nonneg ((1 : ℂ) + phase (t : Phase)),
    abs_nonneg (cos (π * t))]

/-- The normalized circle expectation is an integral over one actual period. -/
theorem phaseMeanPower_eq_interval (p : ℝ) :
    phaseMeanPower p = ∫ t in (-(1 : ℝ) / 2)..(1 / 2), ‖(1 : ℂ) + phase (t : Phase)‖ ^ p := by
  have h := AddCircle.intervalIntegral_preimage 1 (-(1 : ℝ) / 2)
    (fun θ : Phase => ‖(1 : ℂ) + phase θ‖ ^ p)
  simpa only [phaseMeanPower, phaseMeasure, AddCircle.integral_haarAddCircle,
    inv_one, one_smul, show -(1 : ℝ) / 2 + 1 = 1 / 2 by ring] using h.symm

/-- Geometric reduction of the phase moment to the positive quadrant cosine integral. -/
theorem phaseMeanPower_eq_scaled_cosine {p : ℝ} (hp : 0 < p) :
    phaseMeanPower p =
      (2 : ℝ) ^ (p + 1) / π * (∫ t in (0 : ℝ)..π / 2, cos t ^ p) := by
  have hc : Continuous (fun t : ℝ => cos t ^ p) :=
    continuous_cos.rpow_const (fun _ => Or.inr hp.le)
  have hleft : (∫ t in (-(π / 2))..(0 : ℝ), cos t ^ p) =
      ∫ t in (0 : ℝ)..π / 2, cos t ^ p := by
    simpa using (intervalIntegral.integral_comp_neg (f := fun t : ℝ => cos t ^ p)
      (a := 0) (b := π / 2)).symm
  have heven : (∫ t in (-(π / 2))..π / 2, cos t ^ p) =
      2 * ∫ t in (0 : ℝ)..π / 2, cos t ^ p := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (-(π / 2)) 0) (hc.intervalIntegrable 0 (π / 2)), hleft]
    ring
  rw [phaseMeanPower_eq_interval]
  calc
    _ = ∫ t in (-(1 : ℝ) / 2)..(1 / 2), (2 : ℝ) ^ p * cos (π * t) ^ p := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : -(1 : ℝ) / 2 ≤ 1 / 2)] at ht
      have hcos : 0 ≤ cos (π * t) := cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
      · change ‖(1 : ℂ) + phase (t : Phase)‖ ^ p = (2 : ℝ) ^ p * cos (π * t) ^ p
        rw [phase_pair_norm, abs_of_nonneg hcos, Real.mul_rpow (by norm_num) hcos]
      · nlinarith [mul_le_mul_of_nonneg_left ht.1 pi_pos.le]
      · nlinarith [mul_le_mul_of_nonneg_left ht.2 pi_pos.le]
    _ = (2 : ℝ) ^ p * (π⁻¹ * (2 * ∫ t in (0 : ℝ)..π / 2, cos t ^ p)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_left (fun t : ℝ => cos t ^ p) pi_ne_zero]
      simp only [smul_eq_mul, show π * (-(1 : ℝ) / 2) = -(π / 2) by ring,
        show π * ((1 : ℝ) / 2) = π / 2 by ring, heven]
    _ = _ := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring

/-- An independently specified Gamma expression; it does not define the expectation. -/
noncomputable def phaseGammaRatio (p : ℝ) : ℝ :=
  Gamma (p + 1) / Gamma (p / 2 + 1) ^ 2

theorem phaseMeanPower_eq_gamma {p : ℝ} (hp : 0 < p) :
    phaseMeanPower p = phaseGammaRatio p := by
  rw [phaseMeanPower_eq_scaled_cosine hp]
  exact Mettapedia.Analysis.scaled_integral_cos_rpow_eq_gamma hp

theorem independentPhaseMeanPower_eq_gamma {p : ℝ} (hp : 0 < p) :
    independentPhaseMeanPower p = phaseGammaRatio p :=
  (independent_phase_mean_eq_relative hp).trans (phaseMeanPower_eq_gamma hp)

theorem gamma_normalization_iff {p : ℝ} (hp : 0 < p) : phaseGammaRatio p = 2 ↔ p = 2 := by
  rw [← phaseMeanPower_eq_gamma hp]
  exact phase_normalization_iff hp

theorem independent_phase_normalization_iff {p : ℝ} (hp : 0 < p) :
    independentPhaseMeanPower p = 2 ↔ p = 2 := by
  rw [independent_phase_mean_eq_relative hp]
  exact phase_normalization_iff hp

/-- The positive Gamma-normalized exponent exists uniquely, without assuming its value. -/
theorem phase_calibration_exponent_unique :
    ∃! p : ℝ, 0 < p ∧ phaseGammaRatio p = 2 := by
  refine ⟨2, ⟨by norm_num, (gamma_normalization_iff (by norm_num)).2 rfl⟩, ?_⟩
  intro p hp
  exact (gamma_normalization_iff hp.1).1 hp.2

/-- Within the specified power-law family, the calibrated observation is squared norm. -/
theorem calibrated_readout_eq_normSq {p : ℝ} (hp : 0 < p)
    (hnorm : independentPhaseMeanPower p = 2) (z : ℂ) :
    ‖z‖ ^ p = Complex.normSq z := by
  rw [(independent_phase_normalization_iff hp).1 hnorm]
  simpa using Complex.sq_norm z

theorem calibrated_rational_readout {p : ℝ} (hp : 0 < p)
    (hnorm : independentPhaseMeanPower p = 2)
    (z : Mettapedia.Algebra.RationalComplexAmplitude.Amplitude) :
    (Mettapedia.Algebra.RationalComplexAmplitude.born z : ℝ) =
      ‖Mettapedia.Algebra.RationalComplexAmplitude.intoComplex z‖ ^ p := by
  rw [calibrated_readout_eq_normSq hp hnorm]
  exact Mettapedia.Algebra.RationalComplexAmplitude.born_agrees_complex z

/-- A separate positive exponent has mean six, so mean-rate normalization is substantive. -/
theorem phaseMeanPower_four : phaseMeanPower 4 = 6 := by
  rw [phaseMeanPower_eq_gamma (by norm_num)]
  have h5 := Real.Gamma_nat_eq_factorial 4
  have h3 := Real.Gamma_nat_eq_factorial 2
  norm_num at h5 h3
  norm_num [phaseGammaRatio, h5, h3]

theorem independent_phase_mean_two : independentPhaseMeanPower 2 = 2 :=
  (independent_phase_mean_eq_relative (by norm_num)).trans phaseMeanPower_two

theorem independent_phase_mean_four : independentPhaseMeanPower 4 = 6 :=
  (independent_phase_mean_eq_relative (by norm_num)).trans phaseMeanPower_four

theorem fourth_power_not_calibrated : independentPhaseMeanPower 4 ≠ 2 := by
  rw [independent_phase_mean_four]
  norm_num

/-- Reusing one uniform phase locks the sources together. Their mean is then `2^p`. -/
theorem locked_phase_mean (p : ℝ) :
    (∫ θ, ‖phase θ + phase θ‖ ^ p ∂phaseMeasure) = (2 : ℝ) ^ p := by
  have hnorm (θ : Phase) : ‖phase θ + phase θ‖ = 2 := by
    rw [← two_mul, norm_mul, phase_norm]
    norm_num
  simp_rw [hnorm]
  simp

/-- Uniform marginal phases do not suffice: the locked second moment is four. -/
theorem locked_second_moment_is_four :
    (∫ θ, ‖phase θ + phase θ‖ ^ (2 : ℝ) ∂phaseMeasure) = 4 := by
  rw [locked_phase_mean]
  norm_num

end

end Mettapedia.QuantumTheory
