import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierTriadSineLaw

/-!
# Exact paired stretching and the sharp triad sine bound

For the symmetric rank-one strain `S(k,a) = (a ⊗ k + k ⊗ a)/2`,

`S(k,a) (l × b) + S(l,b) (k × a) = (k × l) × (a × b)`.

This identity holds for arbitrary complex amplitudes and keeps the cancellation between
the two interactions. Applied to the actual unit-torus Biot–Savart amplitudes, it improves
the paired stretching sine bound from factor two to factor one. This is a spatial algebraic
estimate; it supplies no time-integrated control of a Navier–Stokes solution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPairedStretchIdentity

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
  PancakePeriodicVorticityEquation PancakeFrequencyProjectorCommutator
  PancakeGalerkinKineticEnergy PancakeSameSectorDissipation FourierPancakePairDepletion
  FourierTriadSineLaw FourierShellFeeding FourierVorticitySource FourierRelaxation
  PancakeIncomingLowSourceEnergy PancakeInfinitePressureCoefficients

/-- The symmetric rank-one strain acting on a coefficient, before Fourier phases. -/
def strainAction (k a w : VelocityCoefficient) : VelocityCoefficient :=
  (1 / 2 : ℂ) • (coefficientDot a w • k + coefficientDot k w • a)

/-- Pairing the interactions gives a double cross product, with no transversality assumption. -/
theorem strain_pair_cross (k l a b : VelocityCoefficient) :
    strainAction k a (coefficientCross l b) + strainAction l b (coefficientCross k a) =
      coefficientCross (coefficientCross k l) (coefficientCross a b) := by
  ext i
  fin_cases i <;> simp [strainAction, coefficientCross, coefficientDot, Fin.sum_univ_three] <;> ring

theorem strainAction_smul (k a w : VelocityCoefficient) (c : ℂ) :
    strainAction k a (c • w) = c • strainAction k a w := by
  unfold strainAction
  rw [coefficientDot_smul_right, coefficientDot_smul_right]
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- The complex Lagrange identity in the actual Euclidean coefficient norm. -/
theorem cross_coefficientEnergy (a b : VelocityCoefficient) :
    coefficientEnergy (coefficientCross a b) = coefficientEnergy a * coefficientEnergy b -
      Complex.normSq (∑ i : Fin 3, conj (a i) * b i) := by
  simp [coefficientEnergy, coefficientCross, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, Fin.sum_univ_three]
  ring

/-- The sharp cross-product bound includes arbitrary complex phases. -/
theorem norm_coefficientCross_le (a b : VelocityCoefficient) :
    ‖coefficientVec (coefficientCross a b)‖ ≤ ‖coefficientVec a‖ * ‖coefficientVec b‖ := by
  have h := cross_coefficientEnergy a b
  simp only [← norm_coefficientVec_sq] at h
  nlinarith [Complex.normSq_nonneg (∑ i : Fin 3, conj (a i) * b i),
    norm_nonneg (coefficientVec (coefficientCross a b)),
    mul_nonneg (norm_nonneg (coefficientVec a)) (norm_nonneg (coefficientVec b))]

theorem physical_strain_eq (p : Wavevector) (a b : VelocityCoefficient) :
    unitTorusStrainStretchAmp p a b = unitTorusDerivativePhase •
      strainAction (wavevectorCoefficient p) (unitTorusBiotSavartAmp p a) b := by
  ext i
  simp only [unitTorusStrainStretchAmp, strainAction, coefficientDot_wavevector_left,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- The paired physical Fourier symbol, with both derivative phases retained exactly. -/
theorem pair_stretch_cross {p r : Wavevector} (hp : p ≠ 0) (hr : r ≠ 0)
    {a b : VelocityCoefficient} (hpa : modeDot p a = 0) (hrb : modeDot r b = 0) :
    unitTorusStrainStretchAmp p a b + unitTorusStrainStretchAmp r b a =
      (unitTorusDerivativePhase * unitTorusDerivativePhase) •
        coefficientCross (wavevectorCoefficient (wavevectorCross p r))
          (coefficientCross (unitTorusBiotSavartAmp p a) (unitTorusBiotSavartAmp r b)) := by
  let U := unitTorusBiotSavartAmp p a
  let V := unitTorusBiotSavartAmp r b
  have ha : a = unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient p) U := by
    rw [wavevector_cross_biotSavart hp hpa, smul_smul,
      mul_inv_cancel₀ unitTorusDerivativePhase_ne_zero, one_smul]
  have hb : b = unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient r) V := by
    rw [wavevector_cross_biotSavart hr hrb, smul_smul,
      mul_inv_cancel₀ unitTorusDerivativePhase_ne_zero, one_smul]
  rw [physical_strain_eq, physical_strain_eq, wavevectorCoefficient_cross]
  change unitTorusDerivativePhase • strainAction (wavevectorCoefficient p) U b +
    unitTorusDerivativePhase • strainAction (wavevectorCoefficient r) V a =
      (unitTorusDerivativePhase * unitTorusDerivativePhase) •
        coefficientCross (coefficientCross (wavevectorCoefficient p) (wavevectorCoefficient r))
          (coefficientCross U V)
  rw [hb, ha, strainAction_smul, strainAction_smul, smul_smul, smul_smul, ← smul_add,
    strain_pair_cross]

/-- The sharp paired-stretch bound has constant one, including complex Fourier phases. -/
theorem norm_pair_stretch_le_sine {p r : Wavevector} (hp : p ≠ 0) (hr : r ≠ 0)
    {a b : VelocityCoefficient} (hpa : modeDot p a = 0) (hrb : modeDot r b = 0) :
    ‖coefficientVec (unitTorusStrainStretchAmp p a b + unitTorusStrainStretchAmp r b a)‖ ≤
      sine p r * ‖coefficientVec a‖ * ‖coefficientVec b‖ := by
  rw [pair_stretch_cross hp hr hpa hrb, norm_cv_smul, norm_mul, norm_derivativePhase]
  have hp0 : 0 < ‖frequencyVec p‖ := by linarith [one_le_norm_frequencyVec hp]
  have hr0 : 0 < ‖frequencyVec r‖ := by linarith [one_le_norm_frequencyVec hr]
  have hpi := Real.pi_pos
  calc
    _ ≤ (2 * Real.pi * (2 * Real.pi)) *
        (‖frequencyVec (wavevectorCross p r)‖ *
          (‖coefficientVec (unitTorusBiotSavartAmp p a)‖ *
            ‖coefficientVec (unitTorusBiotSavartAmp r b)‖)) := by
      gcongr
      exact (norm_cross_le _ _).trans
        (mul_le_mul_of_nonneg_left (norm_coefficientCross_le _ _) (norm_nonneg _))
    _ ≤ (2 * Real.pi * (2 * Real.pi)) *
        (‖frequencyVec (wavevectorCross p r)‖ *
          (‖coefficientVec a‖ / (2 * Real.pi * ‖frequencyVec p‖) *
            (‖coefficientVec b‖ / (2 * Real.pi * ‖frequencyVec r‖)))) := by
      gcongr
      · exact norm_biotSavart_le hp a
      · exact norm_biotSavart_le hr b
    _ = _ := by unfold sine; field_simp

theorem wavevectorCross_add_right (p r : Wavevector) :
    wavevectorCross p (p + r) = wavevectorCross p r := by
  ext i
  fin_cases i <;> simp [wavevectorCross] <;> ring

theorem wavevectorCross_add_left (p r : Wavevector) :
    wavevectorCross (p + r) r = wavevectorCross p r := by
  ext i
  fin_cases i <;> simp [wavevectorCross] <;> ring

/-- When two high inputs produce a low output, their relative angle supplies an output gain. -/
theorem sine_le_output_ratio {p r : Wavevector} (hp : p ≠ 0) (hr : r ≠ 0) :
    sine p r ≤ ‖frequencyVec (p + r)‖ / max ‖frequencyVec p‖ ‖frequencyVec r‖ := by
  have hp0 : 0 < ‖frequencyVec p‖ := by linarith [one_le_norm_frequencyVec hp]
  have hr0 : 0 < ‖frequencyVec r‖ := by linarith [one_le_norm_frequencyVec hr]
  have hP := norm_frequencyVec_cross_le p (p + r)
  have hR := norm_frequencyVec_cross_le (p + r) r
  rw [wavevectorCross_add_right] at hP
  rw [wavevectorCross_add_left] at hR
  unfold sine
  rcases le_total ‖frequencyVec p‖ ‖frequencyVec r‖ with h | h
  · rw [max_eq_right h, div_le_div_iff₀ (mul_pos hp0 hr0) hr0]
    nlinarith [mul_le_mul_of_nonneg_right hP hr0.le]
  · rw [max_eq_left h, div_le_div_iff₀ (mul_pos hp0 hr0) hp0]
    nlinarith [mul_le_mul_of_nonneg_right hR hp0.le]

/-- The paired output vanishes to first order in the output frequency, uniformly in the axes. -/
theorem norm_pair_stretch_le_output_ratio {p r : Wavevector} (hp : p ≠ 0) (hr : r ≠ 0)
    {a b : VelocityCoefficient} (hpa : modeDot p a = 0) (hrb : modeDot r b = 0) :
    ‖coefficientVec (unitTorusStrainStretchAmp p a b + unitTorusStrainStretchAmp r b a)‖ ≤
      (‖frequencyVec (p + r)‖ / max ‖frequencyVec p‖ ‖frequencyVec r‖) *
        ‖coefficientVec a‖ * ‖coefficientVec b‖ := by
  refine (norm_pair_stretch_le_sine hp hr hpa hrb).trans ?_
  gcongr
  exact sine_le_output_ratio hp hr

/-- The exact identity assembles over a finite Fourier block, retaining the complex phases. -/
theorem two_smul_pancakeStretch_eq_cross (u : FourierVelocity) (P : Finset Wavevector)
    (hP0 : (0 : Wavevector) ∉ P) (k : Wavevector) :
    (2 : ℂ) • pancakeStretch u P k =
      ∑ p ∈ P.filter (fun p ↦ k - p ∈ P),
        (unitTorusDerivativePhase * unitTorusDerivativePhase) •
          coefficientCross (wavevectorCoefficient (wavevectorCross p (k - p)))
            (coefficientCross (unitTorusBiotSavartAmp p (fourierCurl u p))
              (unitTorusBiotSavartAmp (k - p) (fourierCurl u (k - p)))) := by
  rw [two_smul_pancakeStretch]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  obtain ⟨hpP, hkpP⟩ := Finset.mem_filter.mp hp
  exact pair_stretch_cross (fun hz ↦ hP0 (hz ▸ hpP)) (fun hz ↦ hP0 (hz ▸ hkpP))
    (fourierCurl_transverse p u) (fourierCurl_transverse (k - p) u)

/-- The finite output bound keeps each pair's angle instead of replacing it by a cone width. -/
theorem norm_pancakeStretch_le_weighted (u : FourierVelocity) (P : Finset Wavevector)
    (hP0 : (0 : Wavevector) ∉ P) (k : Wavevector) :
    ‖coefficientVec (pancakeStretch u P k)‖ ≤
      (1 / 2 : ℝ) * ∑ p ∈ P.filter (fun p ↦ k - p ∈ P),
        sine p (k - p) * curlMass u p * curlMass u (k - p) := by
  have hle : ‖coefficientVec ((2 : ℂ) • pancakeStretch u P k)‖ ≤
      ∑ p ∈ P.filter (fun p ↦ k - p ∈ P),
        sine p (k - p) * curlMass u p * curlMass u (k - p) := by
    rw [two_smul_pancakeStretch, PancakeFixedOutputVelocityBound.coefficientVec_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
    obtain ⟨hpP, hkpP⟩ := Finset.mem_filter.mp hp
    exact norm_pair_stretch_le_sine (fun hz ↦ hP0 (hz ▸ hpP))
      (fun hz ↦ hP0 (hz ▸ hkpP)) (fourierCurl_transverse p u)
      (fourierCurl_transverse (k - p) u)
  rw [norm_cv_smul] at hle
  norm_num only [Complex.norm_ofNat] at hle
  linarith

end Mettapedia.FluidDynamics.NavierStokes.FourierPairedStretchIdentity
