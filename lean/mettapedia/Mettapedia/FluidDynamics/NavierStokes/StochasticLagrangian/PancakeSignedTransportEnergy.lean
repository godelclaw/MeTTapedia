import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeEvolvingFilter

/-!
# Signed energy transfer across Fourier filters

An individual hard-boundary transport coefficient can grow with frequency.
Its signed quadratic energy transfer has additional structure: the physical
transport matrix is skew-Hermitian for conjugate-symmetric source data.
This module keeps that cancellation before taking absolute values.

All statements concern the existing physical finite Fourier transport
operator.  They do not control strain stretching, establish the endpoint
misalignment budget, or construct a Navier--Stokes solution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSignedTransportEnergy

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakePeriodicComplexStretch PancakePeriodicVorticityEquation
open PancakeBlockReality PancakeEvolvingFilter
open PancakeMaterialTransportCommutator

theorem modeDot_complexBiotSavartAmp_self (k : Wavevector)
    (w : VelocityCoefficient) : modeDot k (complexBiotSavartAmp k w) = 0 := by
  simp [modeDot, complexBiotSavartAmp, coefficientCross,
    wavevectorCoefficient, Fin.sum_univ_three]
  ring

theorem modeDot_sub_left (q l : Wavevector) (w : VelocityCoefficient) :
    modeDot (q - l) w = modeDot q w - modeDot l w := by
  simp only [modeDot, Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]

theorem modeDot_conjugate (k : Wavevector) (w : VelocityCoefficient) :
    modeDot k (coefficientConjugate w) = conj (modeDot k w) := by
  simp [modeDot, coefficientConjugate, map_sum, map_mul]

/-- Matrix of the physical negative-advection operator on Fourier modes. -/
def transportMatrix (sources : Finset Wavevector) (omega : FourierVelocity)
    (q l : Wavevector) : ℂ :=
  if q - l ∈ sources then
    modeDot l (complexBiotSavartAmp (q - l) (omega (q - l))) else 0

/-- This matrix is the actual finite convolution, not a replacement model. -/
theorem finiteTransport_eq_matrix (sources receivers : Finset Wavevector)
    (omega eta : FourierVelocity) (q : Wavevector) :
    finiteUnitTorusNegativeTransportCoeff sources receivers omega eta q =
      ∑ l ∈ receivers, transportMatrix sources omega q l • eta l := by
  classical
  rw [finiteUnitTorusNegativeTransportCoeff_eq_doubleSum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hm : q - l ∈ sources
  · rw [Finset.sum_eq_single (q - l)]
    · simp [transportMatrix, hm, unitTorusNegativeTransportAmp_eq]
    · intro k hk hne
      have h : k + l ≠ q := by
        intro he
        exact hne (eq_sub_iff_add_eq.mpr he)
      simp [h]
    · exact fun hh ↦ (hh hm).elim
  · rw [transportMatrix, if_neg hm, zero_smul]
    apply Finset.sum_eq_zero
    intro k hk
    have h : k + l ≠ q := by
      intro he
      exact hm (eq_sub_iff_add_eq.mpr he ▸ hk)
    simp [h]

/-- Reality of the source and Biot--Savart transversality give the exact
skew-Hermitian symmetry, including the zero source mode. -/
theorem transportMatrix_skew (sources : Finset Wavevector)
    (omega : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (q l : Wavevector) :
    transportMatrix sources omega l q = -conj (transportMatrix sources omega q l) := by
  classical
  have hn : l - q = -(q - l) := by abel
  have hm : l - q ∈ sources ↔ q - l ∈ sources := by rw [hn, hs]
  by_cases h : q - l ∈ sources
  · unfold transportMatrix
    rw [if_pos h, if_pos (hm.mpr h), hn, hr,
      complexBiotSavartAmp_neg_conjugate]
    have hd := modeDot_complexBiotSavartAmp_self (q - l) (omega (q - l))
    rw [modeDot_sub_left, sub_eq_zero] at hd
    simp only [modeDot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    change -modeDot q (coefficientConjugate
        (complexBiotSavartAmp (q - l) (omega (q - l)))) = _
    rw [modeDot_conjugate, hd]
    rfl
  · simp [transportMatrix, h, show l - q ∉ sources from fun hh ↦ h (hm.mp hh)]

/-- Signed transfer into mode `q` from receiver mode `l`, without the
factor two in the derivative of squared energy. -/
def transportFlux (sources : Finset Wavevector) (omega eta : FourierVelocity)
    (q l : Wavevector) : ℝ :=
  (coefficientHermitian (eta q) (transportMatrix sources omega q l • eta l)).re

theorem hermitian_neg_conj_smul_swap (u v : VelocityCoefficient) (a : ℂ) :
    (coefficientHermitian v ((-conj a) • u)).re =
      -(coefficientHermitian u (a • v)).re := by
  simp only [coefficientHermitian, Pi.smul_apply, smul_eq_mul, Complex.re_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem transportFlux_antisymmetric (sources : Finset Wavevector)
    (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k)) (q l : Wavevector) :
    transportFlux sources omega eta l q = -transportFlux sources omega eta q l := by
  unfold transportFlux
  rw [transportMatrix_skew sources omega hs hr]
  exact hermitian_neg_conj_smul_swap _ _ _

/-- A weighted signed sum is half the sum of weight differences. -/
theorem sum_weighted_antisymmetric {ι : Type*} (s : Finset ι)
    (f : ι → ι → ℝ) (w : ι → ℝ)
    (ha : ∀ q l, f l q = -f q l) :
    2 * (∑ q ∈ s, ∑ l ∈ s, w q * f q l) =
      ∑ q ∈ s, ∑ l ∈ s, (w q - w l) * f q l := by
  have he : (∑ q ∈ s, ∑ l ∈ s, w l * f q l) =
      -(∑ q ∈ s, ∑ l ∈ s, w q * f q l) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro l hl
    rw [ha q l, mul_neg]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [he]
  ring

theorem hermitian_sum_right {ι : Type*} (s : Finset ι)
    (u : VelocityCoefficient) (v : ι → VelocityCoefficient) :
    coefficientHermitian u (∑ i ∈ s, v i) =
      ∑ i ∈ s, coefficientHermitian u (v i) := by
  simp only [coefficientHermitian, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- Exact signed energy flux of the existing physical transport operator.
The weight can be the square of a smooth Fourier filter or a hard selector. -/
theorem weighted_transport_energy_identity
    (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (w : Wavevector → ℝ) :
    2 * (∑ q ∈ modes, w q *
      (coefficientHermitian (eta q)
        (finiteUnitTorusNegativeTransportCoeff sources modes omega eta q)).re) =
      ∑ q ∈ modes, ∑ l ∈ modes,
        (w q - w l) * transportFlux sources omega eta q l := by
  simp_rw [finiteTransport_eq_matrix, hermitian_sum_right, Complex.re_sum,
    Finset.mul_sum]
  simpa only [transportFlux, Finset.mul_sum] using
    sum_weighted_antisymmetric modes (transportFlux sources omega eta) w
      (transportFlux_antisymmetric sources omega eta hs hr)

/-- All internal transport cancels from the unweighted Galerkin energy. -/
theorem total_transport_energy_zero
    (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k)) :
    (∑ q ∈ modes, (coefficientHermitian (eta q)
      (finiteUnitTorusNegativeTransportCoeff sources modes omega eta q)).re) = 0 := by
  have h := weighted_transport_energy_identity sources modes omega eta hs hr (fun _ ↦ 1)
  simp only [one_mul, sub_self, zero_mul, Finset.sum_const_zero] at h
  linarith

/-- A partition of quadratic frequency weights cancels its total signed
transport flux exactly, without any bound on the individual crossings. -/
theorem partition_transport_energy_zero {ι : Type*} (cells : Finset ι)
    (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (weight : ι → Wavevector → ℝ)
    (hp : ∀ q ∈ modes, ∑ i ∈ cells, weight i q ^ 2 = 1) :
    (∑ i ∈ cells, ∑ q ∈ modes, weight i q ^ 2 *
      (coefficientHermitian (eta q)
        (finiteUnitTorusNegativeTransportCoeff sources modes omega eta q)).re) = 0 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have he : (∑ q ∈ modes, (∑ i ∈ cells, weight i q ^ 2) *
      (coefficientHermitian (eta q)
        (finiteUnitTorusNegativeTransportCoeff sources modes omega eta q)).re) =
      ∑ q ∈ modes, (coefficientHermitian (eta q)
        (finiteUnitTorusNegativeTransportCoeff sources modes omega eta q)).re := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [hp q hq, one_mul]
  rw [he]
  exact total_transport_energy_zero sources modes omega eta hs hr

/-- Differentiating a quadratic partition supplies the filter-rate
cancellation; it is not an additional zero-rate hypothesis. -/
theorem partition_filter_rate_zero {ι : Type*} (cells : Finset ι)
    (weight : ℝ → ι → ℝ) (rate : ι → ℝ) (t : ℝ)
    (hd : ∀ i ∈ cells, HasDerivAt (fun tau ↦ weight tau i) (rate i) t)
    (hp : ∀ tau, ∑ i ∈ cells, weight tau i ^ 2 = 1) :
    ∑ i ∈ cells, 2 * weight t i * rate i = 0 := by
  have hsum : HasDerivAt (fun tau ↦ ∑ i ∈ cells, weight tau i ^ 2)
      (∑ i ∈ cells, 2 * weight t i * rate i) t := by
    simpa using HasDerivAt.fun_sum (fun i hi ↦ (hd i hi).pow 2)
  have he : (fun tau ↦ ∑ i ∈ cells, weight tau i ^ 2) = (fun _ : ℝ ↦ 1) := funext hp
  rw [he] at hsum
  exact hsum.unique (hasDerivAt_const t (1 : ℝ))

theorem hermitian_real_smul_self (u : VelocityCoefficient) (a : ℝ) :
    (coefficientHermitian u ((a : ℂ) • u)).re = a * coefficientEnergy u := by
  simp only [coefficientHermitian, Pi.smul_apply, smul_eq_mul, Complex.re_sum,
    coefficientEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- The physical viscous symbol is a real nonpositive multiplier. -/
theorem viscous_energy_pair (nu : ℝ) (eta : FourierVelocity) (q : Wavevector) :
    (coefficientHermitian (eta q) (unitTorusViscousVorticityCoeff nu eta q)).re =
      -nu * (2 * Real.pi) ^ 2 * (∑ i : Fin 3, (q i : ℝ) ^ 2) *
        coefficientEnergy (eta q) := by
  have hs : modeSquare q = ((∑ i : Fin 3, (q i : ℝ) ^ 2 : ℝ) : ℂ) := by
    simp [modeSquare, sq, Complex.ofReal_sum]
  have hm : (nu : ℂ) * unitTorusDerivativePhase ^ 2 * modeSquare q =
      ((-nu * (2 * Real.pi) ^ 2 * (∑ i : Fin 3, (q i : ℝ) ^ 2) : ℝ) : ℂ) := by
    rw [hs]
    simp [unitTorusDerivativePhase, mul_pow, Complex.I_sq]
  rw [unitTorusViscousVorticityCoeff, hm]
  exact hermitian_real_smul_self _ _

theorem hermitian_add_right (u v w : VelocityCoefficient) :
    coefficientHermitian u (v + w) =
      coefficientHermitian u v + coefficientHermitian u w := by
  simp [coefficientHermitian, mul_add, Finset.sum_add_distrib]

/-- Exact weighted balance of the physical finite vorticity RHS.  Transport
retains its signed weight difference, while diffusion keeps its sign. -/
theorem weighted_vorticity_energy_identity
    (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (weight : Wavevector → ℝ) (nu : ℝ) :
    2 * (∑ q ∈ modes, weight q ^ 2 *
      (coefficientHermitian (eta q)
        (finiteUnitTorusVorticityRHS sources modes omega eta nu q)).re) =
      (∑ q ∈ modes, ∑ l ∈ modes,
        (weight q ^ 2 - weight l ^ 2) * transportFlux sources omega eta q l) +
      2 * (∑ q ∈ modes, weight q ^ 2 *
        (coefficientHermitian (eta q)
          (finiteUnitTorusStretchingCoeff sources modes omega eta q)).re) -
      2 * nu * (2 * Real.pi) ^ 2 *
        (∑ q ∈ modes, weight q ^ 2 *
          (∑ i : Fin 3, (q i : ℝ) ^ 2) * coefficientEnergy (eta q)) := by
  have ht := weighted_transport_energy_identity sources modes omega eta hs hr
    (fun q ↦ weight q ^ 2)
  simp only [finiteUnitTorusVorticityRHS, finiteUnitTorusNonstretchingCoeff,
    hermitian_add_right, Complex.add_re, viscous_energy_pair, mul_add,
    Finset.sum_add_distrib]
  rw [← ht]
  have hv : (∑ q ∈ modes, weight q ^ 2 *
      (-nu * (2 * Real.pi) ^ 2 * (∑ i : Fin 3, (q i : ℝ) ^ 2) *
        coefficientEnergy (eta q))) =
      -nu * (2 * Real.pi) ^ 2 * (∑ q ∈ modes, weight q ^ 2 *
        (∑ i : Fin 3, (q i : ℝ) ^ 2) * coefficientEnergy (eta q)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [hv]
  ring

/-- Coefficient energy is differentiated in the same Euclidean normalization
as the existing finite Parseval theorem. -/
theorem hasDerivAt_coefficientEnergy
    (eta : ℝ → VelocityCoefficient) (etaDot : VelocityCoefficient) (t : ℝ)
    (hd : ∀ i, HasDerivAt (fun tau ↦ eta tau i) (etaDot i) t) :
    HasDerivAt (fun tau ↦ coefficientEnergy (eta tau))
      (2 * (coefficientHermitian (eta t) etaDot).re) t := by
  have hc (i : Fin 3) : HasDerivAt (fun tau ↦ Complex.normSq (eta tau i))
      (2 * (conj (eta t i) * etaDot i).re) t := by
    have hre := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hd i)).pow 2
    have him := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hd i)).pow 2
    convert hre.add him using 1
    · rfl
    · rfl
    · funext tau
      simp [Complex.normSq_apply, pow_two]
    · simp [Complex.mul_re]
      ring
  simpa only [coefficientEnergy, coefficientHermitian, Complex.re_sum,
    Finset.mul_sum] using HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) ↦ hc i)

/-- The weighted energy contains both the filter-motion rate and the
physical coefficient rate. -/
theorem hasDerivAt_weightedEnergy
    (modes : Finset Wavevector)
    (weight : ℝ → Wavevector → ℝ) (weightDot : Wavevector → ℝ)
    (eta : ℝ → FourierVelocity) (etaDot : FourierVelocity) (t : ℝ)
    (hw : ∀ q ∈ modes, HasDerivAt (fun tau ↦ weight tau q) (weightDot q) t)
    (he : ∀ q ∈ modes, ∀ i, HasDerivAt (fun tau ↦ eta tau q i) (etaDot q i) t) :
    HasDerivAt (fun tau ↦ ∑ q ∈ modes, weight tau q ^ 2 * coefficientEnergy (eta tau q))
      ((∑ q ∈ modes, 2 * weight t q * weightDot q * coefficientEnergy (eta t q)) +
        2 * (∑ q ∈ modes, weight t q ^ 2 *
          (coefficientHermitian (eta t q) (etaDot q)).re)) t := by
  have hh := HasDerivAt.fun_sum (fun q hq ↦
    ((hw q hq).pow 2).mul (hasDerivAt_coefficientEnergy (fun tau ↦ eta tau q)
      (etaDot q) t (he q hq)))
  convert hh using 1
  · rfl
  · rfl
  · rfl
  · simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    ring

/-- Full differential balance for an evolving real Fourier filter under
the physical finite vorticity equation.  No term is discarded. -/
theorem hasDerivAt_filteredVorticityEnergy
    (sources modes : Finset Wavevector) (omega : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (weight : ℝ → Wavevector → ℝ) (weightDot : Wavevector → ℝ)
    (eta : ℝ → FourierVelocity) (nu t : ℝ)
    (hw : ∀ q ∈ modes, HasDerivAt (fun tau ↦ weight tau q) (weightDot q) t)
    (he : ∀ q ∈ modes, ∀ i, HasDerivAt (fun tau ↦ eta tau q i)
      (finiteUnitTorusVorticityRHS sources modes omega (eta t) nu q i) t) :
    HasDerivAt (fun tau ↦ ∑ q ∈ modes, weight tau q ^ 2 * coefficientEnergy (eta tau q))
      ((∑ q ∈ modes, 2 * weight t q * weightDot q * coefficientEnergy (eta t q)) +
        ((∑ q ∈ modes, ∑ l ∈ modes,
          (weight t q ^ 2 - weight t l ^ 2) * transportFlux sources omega (eta t) q l) +
        2 * (∑ q ∈ modes, weight t q ^ 2 *
          (coefficientHermitian (eta t q)
            (finiteUnitTorusStretchingCoeff sources modes omega (eta t) q)).re) -
        2 * nu * (2 * Real.pi) ^ 2 *
          (∑ q ∈ modes, weight t q ^ 2 *
            (∑ i : Fin 3, (q i : ℝ) ^ 2) * coefficientEnergy (eta t q)))) t := by
  have h := hasDerivAt_weightedEnergy modes weight weightDot eta
    (finiteUnitTorusVorticityRHS sources modes omega (eta t) nu) t hw he
  rw [weighted_vorticity_energy_identity sources modes omega (eta t) hs hr (weight t) nu] at h
  exact h

/-- Direction-selective quadratic energies retain the difference of their
mode-dependent self-adjoint operators.  A scalar partition alone does not
remove this term.  Orthogonal line/plane projectors are particular cases. -/
theorem selfAdjoint_weight_transport_identity
    (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (A : Wavevector → VelocityCoefficient → VelocityCoefficient)
    (hself : ∀ q u v, coefficientHermitian (A q u) v = coefficientHermitian u (A q v))
    (hscalar : ∀ q (a : ℂ) v, A q (a • v) = a • A q v) :
    2 * (∑ q ∈ modes, (coefficientHermitian (A q (eta q))
      (finiteUnitTorusNegativeTransportCoeff sources modes omega eta q)).re) =
      ∑ q ∈ modes, ∑ l ∈ modes,
        (coefficientHermitian (eta q)
          (transportMatrix sources omega q l • (A q (eta l) - A l (eta l)))).re := by
  let f (q l : Wavevector) : ℝ :=
    (coefficientHermitian (A q (eta q))
      (transportMatrix sources omega q l • eta l)).re
  have hp (q l : Wavevector) : f q l + f l q =
      (coefficientHermitian (eta q)
        (transportMatrix sources omega q l • (A q (eta l) - A l (eta l)))).re := by
    dsimp only [f]
    rw [transportMatrix_skew sources omega hs hr q l]
    rw [hermitian_neg_conj_smul_swap]
    rw [hself, hscalar]
    rw [smul_sub, coefficientHermitian_sub_right, Complex.sub_re]
    ring
  have hsum : (∑ q ∈ modes, ∑ l ∈ modes, (f q l + f l q)) =
      2 * (∑ q ∈ modes, ∑ l ∈ modes, f q l) := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun q l ↦ f l q)]
    ring
  simp_rw [finiteTransport_eq_matrix, hermitian_sum_right, Complex.re_sum]
  change 2 * (∑ q ∈ modes, ∑ l ∈ modes, f q l) = _
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro l hl
  exact hp q l

/-- A common frozen self-adjoint directional weight does enjoy exact
transport cancellation.  The variable-projector difference above records
precisely what changes when different blocks use different directions. -/
theorem frozen_selfAdjoint_transport_zero
    (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (A : VelocityCoefficient → VelocityCoefficient)
    (hself : ∀ u v, coefficientHermitian (A u) v = coefficientHermitian u (A v))
    (hscalar : ∀ (a : ℂ) v, A (a • v) = a • A v) :
    (∑ q ∈ modes, (coefficientHermitian (A (eta q))
      (finiteUnitTorusNegativeTransportCoeff sources modes omega eta q)).re) = 0 := by
  have h := selfAdjoint_weight_transport_identity sources modes omega eta hs hr
    (fun _ ↦ A) (fun _ ↦ hself) (fun _ ↦ hscalar)
  simp [coefficientHermitian] at h
  simpa [coefficientHermitian] using h

theorem hermitian_smul_left (u v : VelocityCoefficient) (a : ℂ) :
    coefficientHermitian (a • u) v = conj a * coefficientHermitian u v := by
  simp only [coefficientHermitian, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem hermitian_conj_symm (u v : VelocityCoefficient) :
    conj (coefficientHermitian u v) = coefficientHermitian v u := by
  simp only [coefficientHermitian, map_sum, map_mul, starRingEnd_self_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem hermitian_sub_left (u v w : VelocityCoefficient) :
    coefficientHermitian (u - v) w =
      coefficientHermitian u w - coefficientHermitian v w := by
  simp [coefficientHermitian, map_sub, sub_mul, Finset.sum_sub_distrib]

/-- The route's existing misalignment projector is self-adjoint, including
its defined value at a degenerate coherent reference. -/
theorem misalignmentComponent_selfAdjoint (q : Wavevector) (u v : VelocityCoefficient) :
    coefficientHermitian (misalignmentComponent q u) v =
      coefficientHermitian u (misalignmentComponent q v) := by
  simp only [misalignmentComponent, hermitian_sub_left, coefficientHermitian_sub_right,
    coherentComponent, coherentScalar, hermitian_smul_left, coefficientHermitian_smul_right,
    map_div₀, coherentDenominator, hermitian_conj_symm]
  ring

theorem misalignmentComponent_smul (q : Wavevector) (a : ℂ) (v : VelocityCoefficient) :
    misalignmentComponent q (a • v) = a • misalignmentComponent q v := by
  simp only [misalignmentComponent, coherentComponent, coherentScalar,
    coefficientHermitian_smul_right, mul_div_assoc, mul_smul, smul_sub]

/-- Exact transport remainder for the very same coherent/misaligned
projection used by the pancake field estimates. -/
theorem misalignment_transport_identity
    (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k)) :
    2 * (∑ q ∈ modes, (coefficientHermitian (misalignmentComponent q (eta q))
      (finiteUnitTorusNegativeTransportCoeff sources modes omega eta q)).re) =
      ∑ q ∈ modes, ∑ l ∈ modes,
        (coefficientHermitian (eta q)
          (transportMatrix sources omega q l •
            (misalignmentComponent q (eta l) - misalignmentComponent l (eta l)))).re :=
  selfAdjoint_weight_transport_identity sources modes omega eta hs hr
    misalignmentComponent misalignmentComponent_selfAdjoint misalignmentComponent_smul

theorem misalignmentComponent_idempotent (q : Wavevector) (v : VelocityCoefficient) :
    misalignmentComponent q (misalignmentComponent q v) = misalignmentComponent q v := by
  have hc : coherentComponent q (misalignmentComponent q v) = 0 := by
    by_cases h : coherentDenominator q = 0
    · simp [coherentComponent, coherentScalar, h]
    · simp [coherentComponent, coherentScalar,
        coefficientHermitian_periodicCoherentMode_misalignment_eq_zero v h]
  exact sub_eq_self.mpr hc

/-- The fixed Fourier misalignment projector differentiates the actual
coefficient path, with no differentiability of a moving eigenframe assumed. -/
theorem hasDerivAt_misalignmentComponent
    (q : Wavevector) (eta : ℝ → VelocityCoefficient)
    (etaDot : VelocityCoefficient) (t : ℝ)
    (he : ∀ i, HasDerivAt (fun tau ↦ eta tau i) (etaDot i) t) (i : Fin 3) :
    HasDerivAt (fun tau ↦ misalignmentComponent q (eta tau) i)
      (misalignmentComponent q etaDot i) t := by
  have hh : HasDerivAt (fun tau ↦ coefficientHermitian (periodicCoherentMode q) (eta tau))
      (coefficientHermitian (periodicCoherentMode q) etaDot) t := by
    exact HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) ↦
      (he j).const_mul (conj (periodicCoherentMode q j)))
  exact (he i).sub ((hh.div_const (coherentDenominator q)).mul_const (periodicCoherentMode q i))

/-- The derivative of actual finite misalignment energy pairs the projected
coefficient with the unprojected equation rate, by self-adjoint idempotence. -/
theorem hasDerivAt_misalignmentEnergy
    (modes : Finset Wavevector) (eta : ℝ → FourierVelocity)
    (etaDot : FourierVelocity) (t : ℝ)
    (he : ∀ q ∈ modes, ∀ i, HasDerivAt (fun tau ↦ eta tau q i) (etaDot q i) t) :
    HasDerivAt (fun tau ↦ ∑ q ∈ modes, coefficientEnergy (misalignmentComponent q (eta tau q)))
      (2 * (∑ q ∈ modes,
        (coefficientHermitian (misalignmentComponent q (eta t q)) (etaDot q)).re)) t := by
  have hh (q : Wavevector) (hq : q ∈ modes) := hasDerivAt_coefficientEnergy
    (fun tau ↦ misalignmentComponent q (eta tau q))
    (misalignmentComponent q (etaDot q)) t
    (hasDerivAt_misalignmentComponent q (fun tau ↦ eta tau q) (etaDot q) t (he q hq))
  have hp (q : Wavevector) :
      coefficientHermitian (misalignmentComponent q (eta t q))
          (misalignmentComponent q (etaDot q)) =
        coefficientHermitian (misalignmentComponent q (eta t q)) (etaDot q) := by
    rw [← misalignmentComponent_selfAdjoint, misalignmentComponent_idempotent]
  simpa only [hp, Finset.mul_sum] using HasDerivAt.fun_sum hh

/-- Along finite transport dynamics, the entire change of misalignment
energy is the explicit projector mismatch.  This is an equality, not the
time-integrated estimate required by `MisalignmentStrainBudget`. -/
theorem hasDerivAt_transportMisalignmentEnergy
    (sources modes : Finset Wavevector) (omega : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (eta : ℝ → FourierVelocity) (t : ℝ)
    (he : ∀ q ∈ modes, ∀ i, HasDerivAt (fun tau ↦ eta tau q i)
      (finiteUnitTorusNegativeTransportCoeff sources modes omega (eta t) q i) t) :
    HasDerivAt (fun tau ↦ ∑ q ∈ modes, coefficientEnergy (misalignmentComponent q (eta tau q)))
      (∑ q ∈ modes, ∑ l ∈ modes,
        (coefficientHermitian (eta t q)
          (transportMatrix sources omega q l •
            (misalignmentComponent q (eta t l) - misalignmentComponent l (eta t l)))).re) t := by
  have h := hasDerivAt_misalignmentEnergy modes eta
    (finiteUnitTorusNegativeTransportCoeff sources modes omega (eta t)) t he
  rw [misalignment_transport_identity sources modes omega (eta t) hs hr] at h
  exact h

theorem viscous_misalignment_energy_pair (nu : ℝ) (eta : FourierVelocity) (q : Wavevector) :
    (coefficientHermitian (misalignmentComponent q (eta q))
      (unitTorusViscousVorticityCoeff nu eta q)).re =
      -nu * (2 * Real.pi) ^ 2 * (∑ i : Fin 3, (q i : ℝ) ^ 2) *
        coefficientEnergy (misalignmentComponent q (eta q)) := by
  have hp : coefficientHermitian (misalignmentComponent q (eta q))
      (unitTorusViscousVorticityCoeff nu eta q) =
      coefficientHermitian (misalignmentComponent q (eta q))
        (unitTorusViscousVorticityCoeff nu (fun k ↦ misalignmentComponent k (eta k)) q) := by
    conv_lhs =>
      rw [← misalignmentComponent_idempotent q (eta q), misalignmentComponent_selfAdjoint]
    simp only [unitTorusViscousVorticityCoeff, misalignmentComponent_smul]
  rw [hp]
  exact viscous_energy_pair nu (fun k ↦ misalignmentComponent k (eta k)) q

/-- The genuine finite vorticity equation gives a misalignment energy
balance with three exact channels: projector mismatch, stretching, and
negative viscous dissipation.  The reference direction is fixed here. -/
theorem hasDerivAt_vorticityMisalignmentEnergy
    (sources modes : Finset Wavevector) (omega : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (eta : ℝ → FourierVelocity) (nu t : ℝ)
    (he : ∀ q ∈ modes, ∀ i, HasDerivAt (fun tau ↦ eta tau q i)
      (finiteUnitTorusVorticityRHS sources modes omega (eta t) nu q i) t) :
    HasDerivAt (fun tau ↦ ∑ q ∈ modes, coefficientEnergy (misalignmentComponent q (eta tau q)))
      ((∑ q ∈ modes, ∑ l ∈ modes,
        (coefficientHermitian (eta t q)
          (transportMatrix sources omega q l •
            (misalignmentComponent q (eta t l) - misalignmentComponent l (eta t l)))).re) +
        2 * (∑ q ∈ modes,
          (coefficientHermitian (misalignmentComponent q (eta t q))
            (finiteUnitTorusStretchingCoeff sources modes omega (eta t) q)).re) -
        2 * nu * (2 * Real.pi) ^ 2 * (∑ q ∈ modes,
          (∑ i : Fin 3, (q i : ℝ) ^ 2) * coefficientEnergy (misalignmentComponent q (eta t q)))) t := by
  have h := hasDerivAt_misalignmentEnergy modes eta
    (finiteUnitTorusVorticityRHS sources modes omega (eta t) nu) t he
  have hid := misalignment_transport_identity sources modes omega (eta t) hs hr
  have hv : (∑ q ∈ modes,
      (coefficientHermitian (misalignmentComponent q (eta t q))
        (unitTorusViscousVorticityCoeff nu (eta t) q)).re) =
      -nu * (2 * Real.pi) ^ 2 * (∑ q ∈ modes,
        (∑ i : Fin 3, (q i : ℝ) ^ 2) * coefficientEnergy (misalignmentComponent q (eta t q))) := by
    simp_rw [viscous_misalignment_energy_pair]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have heq : 2 * (∑ q ∈ modes,
      (coefficientHermitian (misalignmentComponent q (eta t q))
        (finiteUnitTorusVorticityRHS sources modes omega (eta t) nu q)).re) =
      (∑ q ∈ modes, ∑ l ∈ modes,
        (coefficientHermitian (eta t q)
          (transportMatrix sources omega q l •
            (misalignmentComponent q (eta t l) - misalignmentComponent l (eta t l)))).re) +
        2 * (∑ q ∈ modes,
          (coefficientHermitian (misalignmentComponent q (eta t q))
            (finiteUnitTorusStretchingCoeff sources modes omega (eta t) q)).re) -
        2 * nu * (2 * Real.pi) ^ 2 * (∑ q ∈ modes,
          (∑ i : Fin 3, (q i : ℝ) ^ 2) * coefficientEnergy (misalignmentComponent q (eta t q))) := by
    simp only [finiteUnitTorusVorticityRHS, finiteUnitTorusNonstretchingCoeff,
      hermitian_add_right, Complex.add_re, Finset.sum_add_distrib]
    rw [hv, ← hid]
    ring
  rw [heq] at h
  exact h

end Mettapedia.FluidDynamics.NavierStokes.PancakeSignedTransportEnergy
