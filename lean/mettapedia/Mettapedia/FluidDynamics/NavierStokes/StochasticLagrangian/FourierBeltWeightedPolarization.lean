import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierSingleBeltStretch

/-!
# Energy-weighted axial polarization in a Fourier belt

An axial component is weighted by its actual mode amplitude. This permits a
small amount of strongly axial velocity without imposing a small axial
fraction on every mode. The quantities below use the physical unit-torus
curl and axial derivative normalization.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierBeltWeightedPolarization

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
  PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy
  PancakeViscousMisalignmentAbsorption FourierRelaxation FourierSingleConeStretch
  FourierBeltKernel FourierBeltPolarization FourierSingleBeltStretch NormalizedPressureTrace
  FourierPairedStretchSchur PancakePeriodicVorticityEquation FourierPancakePairDepletion

/-- The zero coefficient has zero axial fraction by the usual real division convention. -/
def axialFraction (n : Fin 3 → ℝ) (a : VelocityCoefficient) : ℝ :=
  ‖coefficientDot a (axisCoefficient n)‖ / ‖coefficientVec a‖

theorem axialFraction_nonneg (n : Fin 3 → ℝ) (a : VelocityCoefficient) :
    0 ≤ axialFraction n a := by unfold axialFraction; positivity

theorem axiallySmall_fraction (n : Fin 3 → ℝ) (a : VelocityCoefficient) :
    AxiallySmall n (axialFraction n a) a := by
  by_cases hz : ‖coefficientVec a‖ = 0
  · have hd : ‖coefficientDot a (axisCoefficient n)‖ = 0 := by
      apply le_antisymm
      · simpa only [hz, zero_mul] using
          (norm_coefficientDot_le_product a (axisCoefficient n))
      · exact norm_nonneg _
    simp [AxiallySmall, axialFraction, hz, hd]
  · unfold AxiallySmall axialFraction
    rw [div_mul_cancel₀ _ hz]

/-- The magnitude of the actual spatial gradient of the axial velocity coefficient. -/
def axialMass (n : Fin 3 → ℝ) (u : FourierVelocity) (k : Wavevector) : ℝ :=
  2 * Real.pi * ‖frequencyVec k‖ * ‖coefficientDot (u k) (axisCoefficient n)‖

theorem axialMass_nonneg (n : Fin 3 → ℝ) (u : FourierVelocity) (k : Wavevector) :
    0 ≤ axialMass n u k := by unfold axialMass; positivity

theorem curlMass_eq_frequency_mul (u : FourierVelocity) (k : Wavevector)
    (hu : modeDot k (u k) = 0) :
    curlMass u k = 2 * Real.pi * ‖frequencyVec k‖ * ‖coefficientVec (u k)‖ := by
  have hs : curlMass u k ^ 2 =
      (2 * Real.pi * ‖frequencyVec k‖ * ‖coefficientVec (u k)‖) ^ 2 := by
    rw [curlMass, norm_coefficientVec_sq, fourierCurl_energy k u hu,
      ← norm_coefficientVec_sq]
    ring
  exact (sq_eq_sq₀ (curlMass_nonneg u k) (by positivity)).mp hs

theorem axialFraction_mul_curlMass (n : Fin 3 → ℝ) (u : FourierVelocity) (k : Wavevector)
    (hu : modeDot k (u k) = 0) :
    axialFraction n (u k) * curlMass u k = axialMass n u k := by
  rw [curlMass_eq_frequency_mul u k hu]
  by_cases hz : ‖coefficientVec (u k)‖ = 0
  · have hd : ‖coefficientDot (u k) (axisCoefficient n)‖ = 0 := by
      apply le_antisymm
      · simpa only [hz, zero_mul] using
          (norm_coefficientDot_le_product (u k) (axisCoefficient n))
      · exact norm_nonneg _
    simp [axialFraction, axialMass, hz, hd]
  · unfold axialFraction axialMass
    field_simp

/-- A pointwise axial bound implies the weighted one, with the same physical normalization. -/
theorem axialEnergy_le_of_pointwise (n : Fin 3 → ℝ) (u : FourierVelocity)
    (P : Finset Wavevector) (α : ℝ)
    (htr : ∀ k ∈ P, modeDot k (u k) = 0)
    (hpolar : ∀ k ∈ P, AxiallySmall n α (u k)) :
    (∑ p ∈ P, axialMass n u p ^ 2) ≤
      α ^ 2 * ∑ p ∈ P, coefficientEnergy (fourierCurl u p) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  have hm : axialMass n u p ≤ α * curlMass u p := by
    rw [curlMass_eq_frequency_mul u p (htr p hp)]
    unfold axialMass
    have h := mul_le_mul_of_nonneg_left (hpolar p hp)
      (by positivity : 0 ≤ 2 * Real.pi * ‖frequencyVec p‖)
    simpa only [AxiallySmall, mul_assoc, mul_left_comm, mul_comm] using h
  have h := pow_le_pow_left₀ (axialMass_nonneg n u p) hm 2
  simpa only [mul_pow, curlMass, norm_coefficientVec_sq] using h

/-- The existing scaled Young-Schur estimate closes a mixed term from a squared-energy ratio. -/
theorem schur_mixed_le_of_energy {ι : Type*} (s : Finset ι)
    (W : ι → ι → ℝ) (x y : ι → ℝ) (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hW : ∀ p r, 0 ≤ W p r)
    (hrow : ∀ p ∈ s, ∑ r ∈ s, W p r ≤ C)
    (hcol : ∀ r ∈ s, ∑ p ∈ s, W p r ≤ C)
    (henergy : (∑ p ∈ s, y p ^ 2) ≤ A ^ 2 * ∑ p ∈ s, x p ^ 2) :
    (∑ p ∈ s, ∑ r ∈ s, W p r * y p * x r) ≤ C * A * ∑ p ∈ s, x p ^ 2 := by
  rcases hA.eq_or_lt with hAzero | hApos
  · have hzero : (∑ p ∈ s, y p ^ 2) = 0 := by
      apply le_antisymm
      · simpa only [← hAzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] using henergy
      · exact Finset.sum_nonneg fun p _ ↦ sq_nonneg (y p)
    have hy : ∀ p ∈ s, y p = 0 := by
      intro p hp
      have hsq := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ ↦ sq_nonneg (y p))).mp hzero p hp
      nlinarith only [hsq]
    have hs : (∑ p ∈ s, ∑ r ∈ s, W p r * y p * x r) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      simp only [hy p hp, mul_zero, zero_mul, Finset.sum_const_zero]
    simp only [hs, ← hAzero, mul_zero, zero_mul, le_refl]
  · have h := finite_schur_bilinear_young s W y x C (1 / A) (by positivity) hW hrow hcol
    have hpaid : C * ((1 / A) * (∑ p ∈ s, y p ^ 2) + (∑ p ∈ s, x p ^ 2) / (1 / A)) ≤
        2 * (C * A * ∑ p ∈ s, x p ^ 2) := by
      calc
        _ ≤ C * ((1 / A) * (A ^ 2 * ∑ p ∈ s, x p ^ 2) +
            (∑ p ∈ s, x p ^ 2) / (1 / A)) := by gcongr
        _ = _ := by field_simp; ring
    linarith only [h.trans hpaid]

/-- The actual paired symbol, with axial errors measured in absolute mode mass. -/
theorem norm_pair_stretch_le_axialMass (u : FourierVelocity) (n : Fin 3 → ℝ)
    (hn : ∑ i : Fin 3, (n i) ^ 2 = 1) (N : ℕ) (hN : 2 ≤ N)
    (p r : Wavevector) (hpc : InBeltShell N n p) (hrc : InBeltShell N n r)
    (hpa : modeDot p (u p) = 0) (hrb : modeDot r (u r) = 0) :
    ‖coefficientVec (unitTorusStrainStretchAmp p (fourierCurl u p) (fourierCurl u r) +
      unitTorusStrainStretchAmp r (fourierCurl u r) (fourierCurl u p))‖ ≤
        (‖frequencyVec (p + r)‖ / max ‖frequencyVec p‖ ‖frequencyVec r‖) *
          ((8 / N) * curlMass u p * curlMass u r +
            2 * axialMass n u p * curlMass u r + 2 * curlMass u p * axialMass n u r) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hnonzero : ∀ k, InBeltShell N n k → k ≠ 0 := by
    intro k hk he
    have hz : frequencyVec (0 : Wavevector) = 0 := by
      ext i
      simp [frequencyVec, coefficientVec, wavevectorCoefficient]
    have hh := hk.1
    rw [he, hz, norm_zero] at hh
    nlinarith
  have hdot : ∀ k, InBeltShell N n k →
      ‖coefficientDot (wavevectorCoefficient k) (axisCoefficient n)‖ ≤
        (1 / (N : ℝ)) * ‖frequencyVec k‖ := by
    intro k hk
    rw [coefficientDot_comm, axis_mode_dot_norm]
    simpa only [FourierSlabKernel.InSlab, one_div, div_eq_mul_inv, mul_comm, mul_one] using hk.2.2
  have h := norm_pair_stretch_le_polarized u n hn p r (hnonzero p hpc) (hnonzero r hrc)
    hpa hrb (1 / N) (axialFraction n (u p)) (axialFraction n (u r)) (by positivity)
    ((div_le_div_iff₀ hNpos (by norm_num)).mpr (by linarith))
    (axialFraction_nonneg n _) (axialFraction_nonneg n _) (hdot p hpc) (hdot r hrc)
    (axiallySmall_fraction n _) (axiallySmall_fraction n _)
  refine h.trans_eq ?_
  rw [← axialFraction_mul_curlMass n u p hpa, ← axialFraction_mul_curlMass n u r hrb]
  ring

/-- The same scale-independent belt bound follows from a single axial energy ratio. -/
theorem weighted_stretch_le_energy (u : FourierVelocity) (P K : Finset Wavevector)
    (n : Fin 3 → ℝ) (hn : ∑ i : Fin 3, (n i) ^ 2 = 1)
    (N : ℕ) (hN : 2 ≤ N) (A : ℝ) (hA : 0 ≤ A)
    (hP : ∀ k ∈ P, InBeltShell N n k) (htr : ∀ k ∈ P, modeDot k (u k) = 0)
    (henergy : (∑ p ∈ P, axialMass n u p ^ 2) ≤
      (A / N) ^ 2 * ∑ p ∈ P, coefficientEnergy (fourierCurl u p)) :
    (∑ k ∈ K, (1 / ‖frequencyVec k‖ ^ 2) * ‖coefficientVec (pancakeStretch u P k)‖) ≤
      (3456 + 1728 * A) * ∑ p ∈ P, coefficientEnergy (fourierCurl u p) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let W := fun p r ↦ (N : ℝ) * beltKernel N p r
  let x := curlMass u
  let y := axialMass n u
  let B := fun p r ↦ W p r * ((8 / N) * x p * x r + 2 * y p * x r + 2 * x p * y r)
  have hW : ∀ p r, 0 ≤ W p r := fun p r ↦ mul_nonneg hNpos.le (beltKernel_nonneg N p r)
  have hB : ∀ p r, 0 ≤ B p r := by
    intro p r
    have hxp := curlMass_nonneg u p
    have hxr := curlMass_nonneg u r
    have hyp := axialMass_nonneg n u p
    have hyr := axialMass_nonneg n u r
    dsimp [B, x, y]
    apply mul_nonneg (hW p r)
    positivity
  have hrow : ∀ p ∈ P, ∑ r ∈ P, W p r ≤ 864 * N := by
    intro p hp
    simpa only [W, ← Finset.mul_sum, mul_comm (N : ℝ) 864] using
      mul_le_mul_of_nonneg_left (belt_row_le P N (by omega) n hn hP p hp) hNpos.le
  have hcol : ∀ r ∈ P, ∑ p ∈ P, W p r ≤ 864 * N := by
    intro r hr
    simpa only [W, beltKernel_comm N _ r] using hrow r hr
  have hxx := finite_schur_energy_bound P W x (864 * N) hW hrow hcol
  have henergy' : (∑ p ∈ P, y p ^ 2) ≤ (A / N) ^ 2 * ∑ p ∈ P, x p ^ 2 := by
    simpa only [x, y, curlMass, norm_coefficientVec_sq] using henergy
  have hyx := schur_mixed_le_of_energy P W x y (864 * N) (A / N)
    (by positivity) (by positivity) hW hrow hcol henergy'
  have hxy : (∑ p ∈ P, ∑ r ∈ P, W p r * x p * y r) =
      ∑ p ∈ P, ∑ r ∈ P, W p r * y p * x r := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun p _ ↦ ?_
    dsimp [W]
    rw [beltKernel_comm N p r]
    ring
  have hpair : ∀ p ∈ P, ∀ r ∈ P,
      (1 / ‖frequencyVec (p + r)‖ ^ 2) * ‖coefficientVec
        (unitTorusStrainStretchAmp p (fourierCurl u p) (fourierCurl u r) +
          unitTorusStrainStretchAmp r (fourierCurl u r) (fourierCurl u p))‖ ≤ B p r := by
    intro p hp r hr
    refine (mul_le_mul_of_nonneg_left
      (norm_pair_stretch_le_axialMass u n hn N hN p r (hP p hp) (hP r hr)
        (htr p hp) (htr r hr)) (by positivity : 0 ≤ 1 / ‖frequencyVec (p + r)‖ ^ 2)).trans_eq ?_
    dsimp [B, W, x, y, beltKernel]
    field_simp
  have hsplit : (∑ p ∈ P, ∑ r ∈ P, B p r) =
      (8 / N) * (∑ p ∈ P, ∑ r ∈ P, W p r * x p * x r) +
        2 * (∑ p ∈ P, ∑ r ∈ P, W p r * y p * x r) +
        2 * (∑ p ∈ P, ∑ r ∈ P, W p r * x p * y r) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun r _ ↦ ?_
    dsimp [B]
    ring
  have hpaid : (1 / 2 : ℝ) * ∑ p ∈ P, ∑ r ∈ P, B p r ≤
      (3456 + 1728 * A) * ∑ p ∈ P, x p ^ 2 := by
    rw [hsplit, hxy]
    calc
      _ ≤ (1 / 2 : ℝ) * ((8 / N) * ((864 * N) * ∑ p ∈ P, x p ^ 2) +
          2 * ((864 * N) * (A / N) * ∑ p ∈ P, x p ^ 2) +
          2 * ((864 * N) * (A / N) * ∑ p ∈ P, x p ^ 2)) := by gcongr
      _ = _ := by field_simp; ring
  exact (weighted_stretch_le_pair_majorant u P K (fun k ↦ 1 / ‖frequencyVec k‖ ^ 2)
    (fun _ ↦ by positivity) B hB hpair).trans
      (by simpa only [x, curlMass, norm_coefficientVec_sq] using hpaid)

end Mettapedia.FluidDynamics.NavierStokes.FourierBeltWeightedPolarization
