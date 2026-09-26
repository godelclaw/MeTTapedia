import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierBeltPolarization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPairedStretchSchur

/-!
# Paired stretching of approximately polarized Fourier belts

A belt restricts the frequency direction and the velocity polarization.
The paired symbol keeps the output-frequency gain, including for the axial
polarization error. These are finite Fourier estimates at a fixed time.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierSingleBeltStretch

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
  PancakePeriodicVorticityEquation PancakeFrequencyProjectorCommutator
  PancakeGalerkinKineticEnergy PancakeIncomingLowSourceEnergy PancakeInfinitePressureCoefficients
  FourierVorticitySource FourierPancakePairDepletion FourierTriadSineLaw FourierRelaxation
  FourierPairedStretchIdentity FourierPairedStretchSchur FourierSingleConeStretch
  FourierBeltKernel FourierBeltPolarization

/-- The actual velocity's axial component is small relative to its Euclidean coefficient norm. -/
def AxiallySmall (n : Fin 3 → ℝ) (α : ℝ) (a : VelocityCoefficient) : Prop :=
  ‖coefficientDot a (axisCoefficient n)‖ ≤ α * ‖coefficientVec a‖

/-- Both derivative phases and the velocity-vorticity normalization are retained. -/
theorem norm_pair_stretch_le_polarized (u : FourierVelocity) (n : Fin 3 → ℝ)
    (hn : ∑ i : Fin 3, (n i) ^ 2 = 1) (p r : Wavevector) (hp : p ≠ 0) (hr : r ≠ 0)
    (hpa : modeDot p (u p) = 0) (hrb : modeDot r (u r) = 0)
    (δ α β : ℝ) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hpdot : ‖coefficientDot (wavevectorCoefficient p) (axisCoefficient n)‖ ≤
      δ * ‖frequencyVec p‖)
    (hrdot : ‖coefficientDot (wavevectorCoefficient r) (axisCoefficient n)‖ ≤
      δ * ‖frequencyVec r‖)
    (ha : AxiallySmall n α (u p)) (hb : AxiallySmall n β (u r)) :
    ‖coefficientVec (unitTorusStrainStretchAmp p (fourierCurl u p) (fourierCurl u r) +
      unitTorusStrainStretchAmp r (fourierCurl u r) (fourierCurl u p))‖ ≤
        (8 * δ + 2 * α + 2 * β) *
          (‖frequencyVec (p + r)‖ / max ‖frequencyVec p‖ ‖frequencyVec r‖) *
            curlMass u p * curlMass u r := by
  have hp0 : 0 < ‖frequencyVec p‖ := by linarith [one_le_norm_frequencyVec hp]
  have hr0 : 0 < ‖frequencyVec r‖ := by linarith [one_le_norm_frequencyVec hr]
  have hpBio := physicalBiotSavart_fourierCurl p u (frequencyVec_ne_zero hp) hpa
  have hrBio := physicalBiotSavart_fourierCurl r u (frequencyVec_ne_zero hr) hrb
  have hpNorm : ‖coefficientVec (u p)‖ ≤
      curlMass u p / (2 * Real.pi * ‖frequencyVec p‖) := by
    simpa only [hpBio, curlMass] using norm_biotSavart_le hp (fourierCurl u p)
  have hrNorm : ‖coefficientVec (u r)‖ ≤
      curlMass u r / (2 * Real.pi * ‖frequencyVec r‖) := by
    simpa only [hrBio, curlMass] using norm_biotSavart_le hr (fourierCurl u r)
  have hgeom := norm_doubleCross_le_polarized n hn p r (u p) (u r)
    δ α β hδ hδhalf hp0 hr0 hpa hrb hpdot hrdot hα hβ ha hb
  rw [← wavevectorCoefficient_cross] at hgeom
  have hC : 0 ≤ 8 * δ + 2 * α + 2 * β := by positivity
  have hpi := Real.pi_pos
  have hmp := curlMass_nonneg u p
  have hmr := curlMass_nonneg u r
  rw [pair_stretch_cross hp hr (fourierCurl_transverse p u) (fourierCurl_transverse r u),
    hpBio, hrBio, norm_cv_smul, norm_mul, norm_derivativePhase]
  calc
    _ ≤ (2 * Real.pi * (2 * Real.pi)) *
        ((8 * δ + 2 * α + 2 * β) * ‖frequencyVec (wavevectorCross p r)‖ *
          ‖coefficientVec (u p)‖ * ‖coefficientVec (u r)‖) := by
      exact mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ ≤ (2 * Real.pi * (2 * Real.pi)) *
        ((8 * δ + 2 * α + 2 * β) * ‖frequencyVec (wavevectorCross p r)‖ *
          (curlMass u p / (2 * Real.pi * ‖frequencyVec p‖)) *
          (curlMass u r / (2 * Real.pi * ‖frequencyVec r‖))) := by gcongr
    _ = (8 * δ + 2 * α + 2 * β) * sine p r * curlMass u p * curlMass u r := by
      unfold sine
      field_simp
    _ ≤ _ := by
      gcongr
      exact sine_le_output_ratio hp hr

/-- Critical-width belts with axial fraction at most `A/N` have the corresponding depleted pair. -/
theorem norm_pair_stretch_le_belt (u : FourierVelocity) (n : Fin 3 → ℝ)
    (hn : ∑ i : Fin 3, (n i) ^ 2 = 1) (N : ℕ) (hN : 2 ≤ N) (A : ℝ) (hA : 0 ≤ A)
    (p r : Wavevector) (hpc : InBeltShell N n p) (hrc : InBeltShell N n r)
    (hpa : modeDot p (u p) = 0) (hrb : modeDot r (u r) = 0)
    (ha : AxiallySmall n (A / N) (u p)) (hb : AxiallySmall n (A / N) (u r)) :
    ‖coefficientVec (unitTorusStrainStretchAmp p (fourierCurl u p) (fourierCurl u r) +
      unitTorusStrainStretchAmp r (fourierCurl u r) (fourierCurl u p))‖ ≤
        ((8 + 4 * A) / N) *
          (‖frequencyVec (p + r)‖ / max ‖frequencyVec p‖ ‖frequencyVec r‖) *
            curlMass u p * curlMass u r := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hp0 : p ≠ 0 := by
    intro hp
    have he : frequencyVec (0 : Wavevector) = 0 := by
      ext i
      simp [frequencyVec, coefficientVec, wavevectorCoefficient]
    have hh := hpc.1
    rw [hp, he, norm_zero] at hh
    nlinarith
  have hr0 : r ≠ 0 := by
    intro hr
    have he : frequencyVec (0 : Wavevector) = 0 := by
      ext i
      simp [frequencyVec, coefficientVec, wavevectorCoefficient]
    have hh := hrc.1
    rw [hr, he, norm_zero] at hh
    nlinarith
  have hdot : ∀ k, InBeltShell N n k →
      ‖coefficientDot (wavevectorCoefficient k) (axisCoefficient n)‖ ≤
        (1 / (N : ℝ)) * ‖frequencyVec k‖ := by
    intro k hk
    rw [coefficientDot_comm, axis_mode_dot_norm]
    simpa only [FourierSlabKernel.InSlab, one_div, div_eq_mul_inv, mul_comm, mul_one] using hk.2.2
  have h := norm_pair_stretch_le_polarized u n hn p r hp0 hr0 hpa hrb
    (1 / N) (A / N) (A / N) (by positivity)
    ((div_le_div_iff₀ hNpos (by norm_num)).mpr (by linarith))
    (by positivity) (by positivity) (hdot p hpc) (hdot r hrc) ha hb
  convert h using 1; ring

/-- The finite block pairs both orders before estimating the actual stretching output. -/
theorem norm_pancakeStretch_le_belt (u : FourierVelocity) (P : Finset Wavevector)
    (n : Fin 3 → ℝ) (hn : ∑ i : Fin 3, (n i) ^ 2 = 1)
    (N : ℕ) (hN : 2 ≤ N) (A : ℝ) (hA : 0 ≤ A)
    (hP : ∀ k ∈ P, InBeltShell N n k) (htr : ∀ k ∈ P, modeDot k (u k) = 0)
    (hpolar : ∀ k ∈ P, AxiallySmall n (A / N) (u k)) (k : Wavevector) :
    ‖coefficientVec (pancakeStretch u P k)‖ ≤
      (1 / 2 : ℝ) * ∑ p ∈ P.filter (fun p ↦ k - p ∈ P),
        ((8 + 4 * A) / N) *
          (‖frequencyVec (p + (k - p))‖ / max ‖frequencyVec p‖ ‖frequencyVec (k - p)‖) *
            curlMass u p * curlMass u (k - p) := by
  have hle : ‖coefficientVec ((2 : ℂ) • pancakeStretch u P k)‖ ≤
      ∑ p ∈ P.filter (fun p ↦ k - p ∈ P),
        ((8 + 4 * A) / N) *
          (‖frequencyVec (p + (k - p))‖ / max ‖frequencyVec p‖ ‖frequencyVec (k - p)‖) *
            curlMass u p * curlMass u (k - p) := by
    rw [two_smul_pancakeStretch, PancakeFixedOutputVelocityBound.coefficientVec_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
    obtain ⟨hpP, hkpP⟩ := Finset.mem_filter.mp hp
    exact norm_pair_stretch_le_belt u n hn N hN A hA p (k - p)
      (hP p hpP) (hP (k - p) hkpP) (htr p hpP) (htr (k - p) hkpP)
      (hpolar p hpP) (hpolar (k - p) hkpP)
  rw [norm_cv_smul] at hle
  norm_num only [Complex.norm_ofNat] at hle
  linarith

/-- One approximately polarized belt has a scale-independent bound by its input vorticity energy. -/
theorem weighted_stretch_le_energy (u : FourierVelocity) (P K : Finset Wavevector)
    (n : Fin 3 → ℝ) (hn : ∑ i : Fin 3, (n i) ^ 2 = 1)
    (N : ℕ) (hN : 2 ≤ N) (A : ℝ) (hA : 0 ≤ A)
    (hP : ∀ k ∈ P, InBeltShell N n k) (htr : ∀ k ∈ P, modeDot k (u k) = 0)
    (hpolar : ∀ k ∈ P, AxiallySmall n (A / N) (u k)) :
    (∑ k ∈ K, (1 / ‖frequencyVec k‖ ^ 2) * ‖coefficientVec (pancakeStretch u P k)‖) ≤
      (3456 + 1728 * A) * ∑ p ∈ P, coefficientEnergy (fourierCurl u p) := by
  let B := fun p r ↦ beltKernel N p r * curlMass u p * curlMass u r
  have hB : ∀ p r, 0 ≤ B p r := fun p r ↦
    mul_nonneg (mul_nonneg (beltKernel_nonneg N p r) (curlMass_nonneg u p)) (curlMass_nonneg u r)
  have hrow : ∀ p ∈ P, ∑ r ∈ P, beltKernel N p r ≤ 864 :=
    belt_row_le P N (by omega) n hn hP
  have hcol : ∀ r ∈ P, ∑ p ∈ P, beltKernel N p r ≤ 864 := by
    intro r hr
    simpa only [beltKernel_comm N _ r] using hrow r hr
  have hs := finite_schur_energy_bound P (beltKernel N) (curlMass u) 864
    (beltKernel_nonneg N) hrow hcol
  calc
    _ ≤ ((8 + 4 * A) / 2) * ∑ k ∈ K, ∑ p ∈ P.filter (fun p ↦ k - p ∈ P), B p (k - p) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ ↦ ?_
      refine (mul_le_mul_of_nonneg_left
        (norm_pancakeStretch_le_belt u P n hn N hN A hA hP htr hpolar k)
        (by positivity : 0 ≤ 1 / ‖frequencyVec k‖ ^ 2)).trans_eq ?_
      rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      simp only [B, beltKernel, show p + (k - p) = k from by abel]
      ring
    _ ≤ ((8 + 4 * A) / 2) * ∑ p ∈ P, ∑ r ∈ P, B p r :=
      mul_le_mul_of_nonneg_left (sum_output_pairs_le P K B hB) (by positivity)
    _ ≤ ((8 + 4 * A) / 2) * (864 * ∑ p ∈ P, curlMass u p ^ 2) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      simp only [curlMass, norm_coefficientVec_sq]
      ring

end Mettapedia.FluidDynamics.NavierStokes.FourierSingleBeltStretch
