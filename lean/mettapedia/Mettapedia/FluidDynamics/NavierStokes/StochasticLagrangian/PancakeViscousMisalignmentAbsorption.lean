import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFrequencyProjectorCommutator

/-!
# Projected-amplitude transport and viscous absorption

Transport of the already-misaligned field has zero total energy rate.
Subtracting it retains the misaligned output amplitude in the projector
commutator.  A weighted finite Schur estimate then permits a prescribed
amount of misalignment energy to absorb the transfer, at an explicit
quadratic source-vorticity cost.

The reference frame and finite pancake sector are fixed.  These estimates
do not bound hard-selector crossings, moving-frame terms, or the source
time norm, and do not construct solution trajectories.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeViscousMisalignmentAbsorption

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakePeriodicVorticityEquation PancakeBlockReality
open PancakePeriodicComplexStretch
open PancakeSignedTransportEnergy PancakeFrequencyProjectorCommutator
open PancakeSquareDyadicSectorProjector PancakeFrameCovariance

def misalignedField (eta : FourierVelocity) : FourierVelocity :=
  fun q ↦ misalignmentComponent q (eta q)

def fullEnergy (modes : Finset Wavevector) (eta : FourierVelocity) : ℝ :=
  ∑ q ∈ modes, coefficientEnergy (eta q)

def misalignedEnergy (modes : Finset Wavevector) (eta : FourierVelocity) : ℝ :=
  fullEnergy modes (misalignedField eta)

def sourceAmplitude (sources : Finset Wavevector) (omega : FourierVelocity) : ℝ :=
  ∑ k ∈ sources, ‖coefficientVec (omega k)‖

def transportEnergyRate (sources modes : Finset Wavevector)
    (omega eta : FourierVelocity) : ℝ :=
  2 * ∑ q ∈ modes, (coefficientHermitian (misalignedField eta q)
    (finiteUnitTorusNegativeTransportCoeff sources modes omega eta q)).re

def stretchingEnergyRate (sources modes : Finset Wavevector)
    (omega eta : FourierVelocity) : ℝ :=
  2 * ∑ q ∈ modes, (coefficientHermitian (misalignedField eta q)
    (finiteUnitTorusStretchingCoeff sources modes omega eta q)).re

def misalignedDissipation (modes : Finset Wavevector) (eta : FourierVelocity) : ℝ :=
  ∑ q ∈ modes, (∑ i : Fin 3, (q i : ℝ) ^ 2) * coefficientEnergy (misalignedField eta q)

theorem fullEnergy_nonneg (modes : Finset Wavevector) (eta : FourierVelocity) :
    0 ≤ fullEnergy modes eta := by
  unfold fullEnergy coefficientEnergy
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

theorem misalignedEnergy_nonneg (modes : Finset Wavevector) (eta : FourierVelocity) :
    0 ≤ misalignedEnergy modes eta := fullEnergy_nonneg _ _

theorem sourceAmplitude_nonneg (sources : Finset Wavevector) (omega : FourierVelocity) :
    0 ≤ sourceAmplitude sources omega := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- The output projector may be removed inside a pairing against its own
range, by the already checked self-adjointness and idempotence. -/
theorem hermitian_misaligned_project_right (q : Wavevector) (u v : VelocityCoefficient) :
    coefficientHermitian (misalignmentComponent q u) (misalignmentComponent q v) =
      coefficientHermitian (misalignmentComponent q u) v := by
  rw [← misalignmentComponent_selfAdjoint, misalignmentComponent_idempotent]

/-- Subtracting transport of the projected field leaves an exact commutator
paired with the misaligned amplitude, rather than with full vorticity. -/
theorem transportEnergyRate_eq_projected_commutator
    (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k)) :
    transportEnergyRate sources modes omega eta =
      2 * ∑ q ∈ modes, ∑ l ∈ modes,
        (coefficientHermitian (misalignedField eta q)
          (transportMatrix sources omega q l •
            (misalignmentComponent q (eta l) - misalignedField eta l))).re := by
  have hp (q l : Wavevector) :
      coefficientHermitian (misalignedField eta q)
        (transportMatrix sources omega q l •
          (misalignmentComponent q (eta l) - misalignedField eta l)) =
      coefficientHermitian (misalignedField eta q)
          (transportMatrix sources omega q l • eta l) -
        coefficientHermitian (misalignedField eta q)
          (transportMatrix sources omega q l • misalignedField eta l) := by
    dsimp only [misalignedField]
    rw [smul_sub, coefficientHermitian_sub_right,
      ← misalignmentComponent_smul, hermitian_misaligned_project_right]
  have hz := total_transport_energy_zero sources modes omega (misalignedField eta) hs hr
  simp_rw [finiteTransport_eq_matrix, hermitian_sum_right, Complex.re_sum] at hz
  unfold transportEnergyRate
  simp_rw [finiteTransport_eq_matrix, hermitian_sum_right, Complex.re_sum,
    hp, Complex.sub_re, Finset.sum_sub_distrib]
  rw [hz, sub_zero]

/-- Weighted finite Schur bound with different input and output amplitudes.
The positive parameter may subsequently be chosen to match dissipation. -/
theorem finite_schur_bilinear_young {ι : Type*} (s : Finset ι)
    (a : ι → ι → ℝ) (b c : ι → ℝ) (A r : ℝ) (hr : 0 < r)
    (ha : ∀ q l, 0 ≤ a q l)
    (hrow : ∀ q ∈ s, ∑ l ∈ s, a q l ≤ A)
    (hcol : ∀ l ∈ s, ∑ q ∈ s, a q l ≤ A) :
    2 * (∑ q ∈ s, ∑ l ∈ s, a q l * b q * c l) ≤
      A * (r * (∑ q ∈ s, b q ^ 2) + (∑ l ∈ s, c l ^ 2) / r) := by
  have hp (q l : ι) : 2 * (a q l * b q * c l) ≤
      r * (a q l * b q ^ 2) + (a q l * c l ^ 2) / r := by
    have h := mul_nonneg (ha q l) (sq_nonneg (r * b q - c l))
    apply (mul_le_mul_iff_right₀ hr).mp
    have hd : (a q l * c l ^ 2 / r) * r = a q l * c l ^ 2 := div_mul_cancel₀ _ hr.ne'
    nlinarith
  have hsum := Finset.sum_le_sum (s := s) fun q hq ↦
    Finset.sum_le_sum (s := s) fun l hl ↦ hp q l
  have hrow' : (∑ q ∈ s, ∑ l ∈ s, a q l * b q ^ 2) ≤ A * ∑ q ∈ s, b q ^ 2 := by
    simp only [← Finset.sum_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun q hq ↦
      mul_le_mul_of_nonneg_right (hrow q hq) (sq_nonneg _)
  have hcol' : (∑ q ∈ s, ∑ l ∈ s, a q l * c l ^ 2) ≤ A * ∑ l ∈ s, c l ^ 2 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l hl ↦
      mul_le_mul_of_nonneg_right (hcol l hl) (sq_nonneg _)
  simp only [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib] at hsum
  calc
    _ ≤ r * (∑ q ∈ s, ∑ l ∈ s, a q l * b q ^ 2) +
        (∑ q ∈ s, ∑ l ∈ s, a q l * c l ^ 2) / r := hsum
    _ ≤ r * (A * ∑ q ∈ s, b q ^ 2) + (A * ∑ l ∈ s, c l ^ 2) / r := by gcongr
    _ = _ := by ring

theorem projected_pair_le
    {N : ℕ} (hN : 2 ≤ N) (sources : Finset Wavevector)
    (omega eta : FourierVelocity) (q l : Wavevector)
    (hq : InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (hl : InOrientedSquarePancakeConeAnnulus identityFrame N l) :
    |(coefficientHermitian (misalignedField eta q) (transportMatrix sources omega q l •
      (misalignmentComponent q (eta l) - misalignedField eta l))).re| ≤
        384 * sourceWeight sources omega q l *
          ‖coefficientVec (misalignedField eta q)‖ * ‖coefficientVec (eta l)‖ := by
  classical
  by_cases hm : q - l ∈ sources
  · have h := pancake_transport_projector_commutator_le hN sources omega q l (eta l) hq hl
    calc
      _ ≤ ‖coefficientVec (misalignedField eta q)‖ *
          ‖coefficientVec (transportMatrix sources omega q l •
            (misalignmentComponent q (eta l) - misalignedField eta l))‖ :=
        abs_hermitian_re_le _ _
      _ ≤ ‖coefficientVec (misalignedField eta q)‖ *
          (384 * ‖coefficientVec (omega (q - l))‖ * ‖coefficientVec (eta l)‖) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = _ := by rw [sourceWeight, if_pos hm]; ring
  · simp [transportMatrix, sourceWeight, hm, coefficientHermitian]

/-- The Schur estimate retains both the misalignment energy and the full
receiver energy, with a free balancing parameter. -/
theorem transportEnergyRate_young
    {N : ℕ} (hN : 2 ≤ N) (sources modes : Finset Wavevector)
    (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (r : ℝ) (hrpos : 0 < r) :
    |transportEnergyRate sources modes omega eta| ≤
      384 * sourceAmplitude sources omega *
        (r * misalignedEnergy modes eta + fullEnergy modes eta / r) := by
  let f (q l : Wavevector) : ℝ :=
    (coefficientHermitian (misalignedField eta q) (transportMatrix sources omega q l •
      (misalignmentComponent q (eta l) - misalignedField eta l))).re
  let b (q : Wavevector) : ℝ := ‖coefficientVec (misalignedField eta q)‖
  let c (q : Wavevector) : ℝ := ‖coefficientVec (eta q)‖
  have hsum : |∑ q ∈ modes, ∑ l ∈ modes, f q l| ≤
      384 * (∑ q ∈ modes, ∑ l ∈ modes, sourceWeight sources omega q l * b q * c l) := by
    calc
      _ ≤ ∑ q ∈ modes, ∑ l ∈ modes, |f q l| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun q _ ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ q ∈ modes, ∑ l ∈ modes, 384 * sourceWeight sources omega q l * b q * c l := by
        apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro l hl
        exact projected_pair_le hN sources omega eta q l (hmode q hq) (hmode l hl)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        apply Finset.sum_congr rfl
        intro l hl
        ring
  have hschur := finite_schur_bilinear_young modes (sourceWeight sources omega)
    b c (sourceAmplitude sources omega) r hrpos (sourceWeight_nonneg sources omega)
    (fun q _ ↦ sum_sourceWeight_row_le sources modes omega q)
    (fun l _ ↦ sum_sourceWeight_column_le sources modes omega l)
  have hb : (∑ q ∈ modes, b q ^ 2) = misalignedEnergy modes eta := by
    simp [b, misalignedEnergy, fullEnergy, norm_coefficientVec_sq]
  have hc : (∑ q ∈ modes, c q ^ 2) = fullEnergy modes eta := by
    simp [c, fullEnergy, norm_coefficientVec_sq]
  rw [hb, hc] at hschur
  rw [transportEnergyRate_eq_projected_commutator sources modes omega eta hs hr,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  change 2 * |∑ q ∈ modes, ∑ l ∈ modes, f q l| ≤ _
  nlinarith

/-- Optimize the free Schur parameter, including the zero-source case. -/
theorem optimize_bilinear_young (rate B E F delta : ℝ)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hd : 0 < delta)
    (h : ∀ r : ℝ, 0 < r → rate ≤ B * (r * E + F / r)) :
    rate ≤ delta * E + B ^ 2 / delta * F := by
  by_cases hzero : B = 0
  · have hh := h 1 (by norm_num)
    rw [hzero] at hh ⊢
    simp only [zero_mul, zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero] at hh ⊢
    exact hh.trans (mul_nonneg hd.le hE)
  · have hp : 0 < B := lt_of_le_of_ne hB (Ne.symm hzero)
    have hh := h (delta / B) (div_pos hd hp)
    have he : B * (delta / B * E + F / (delta / B)) = delta * E + B ^ 2 / delta * F := by
      field_simp [hzero, hd.ne']
    exact hh.trans_eq he

/-- A prescribed misalignment-energy cost replaces the full-energy linear
cost.  The source amplitude is squared and remains an explicit obligation. -/
theorem transportEnergyRate_absorb_delta
    {N : ℕ} (hN : 2 ≤ N) (sources modes : Finset Wavevector)
    (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (delta : ℝ) (hd : 0 < delta) :
    |transportEnergyRate sources modes omega eta| ≤
      delta * misalignedEnergy modes eta +
        (384 * sourceAmplitude sources omega) ^ 2 / delta * fullEnergy modes eta :=
  optimize_bilinear_young _ _ _ _ _
    (mul_nonneg (by norm_num) (sourceAmplitude_nonneg _ _))
    (misalignedEnergy_nonneg _ _) hd
    (transportEnergyRate_young hN sources modes omega eta hs hr hmode)

/-- The actual square-dyadic shell supplies the dissipative frequency
factor; it is not an assumed lower bound on the energy. -/
theorem misalignedDissipation_ge_shell
    {N : ℕ} (hN : 2 ≤ N) (modes : Finset Wavevector) (eta : FourierVelocity)
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q) :
    (N : ℝ) ^ 4 * misalignedEnergy modes eta ≤ misalignedDissipation modes eta := by
  unfold misalignedEnergy fullEnergy misalignedDissipation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hlow := (pancake_frequency_bounds hN q (hmode q hq)).2.2.1
  have hfreq : (N : ℝ) ^ 4 ≤ ∑ i : Fin 3, (q i : ℝ) ^ 2 := by
    rw [← norm_frequencyVec_sq]
    nlinarith [norm_nonneg (frequencyVec q), sq_nonneg (N : ℝ)]
  exact mul_le_mul_of_nonneg_right hfreq (PancakeArbitraryDataBlocks.coefficientEnergy_nonneg _)

/-- Half of the physical viscous dissipation absorbs same-shell transport,
leaving an explicit `A²/(nu N⁴)` full-energy cost. -/
theorem transportEnergyRate_absorb_viscosity
    {N : ℕ} (hN : 2 ≤ N) (sources modes : Finset Wavevector)
    (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (nu : ℝ) (hnu : 0 < nu) :
    |transportEnergyRate sources modes omega eta| ≤
      nu * (2 * Real.pi) ^ 2 * misalignedDissipation modes eta +
        (384 * sourceAmplitude sources omega) ^ 2 /
          (nu * (2 * Real.pi) ^ 2 * (N : ℝ) ^ 4) * fullEnergy modes eta := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd : 0 < nu * (2 * Real.pi) ^ 2 * (N : ℝ) ^ 4 := by positivity
  have h := transportEnergyRate_absorb_delta hN sources modes omega eta hs hr hmode _ hd
  have hc := mul_le_mul_of_nonneg_left (misalignedDissipation_ge_shell hN modes eta hmode)
    (show 0 ≤ nu * (2 * Real.pi) ^ 2 by positivity)
  nlinarith

/-- The source cost remaining after absorbing half the physical diffusion. -/
def residualSourceCost (N : ℕ) (nu : ℝ) (sources modes : Finset Wavevector)
    (omega eta : FourierVelocity) : ℝ :=
  (384 * sourceAmplitude sources omega) ^ 2 /
    (nu * (2 * Real.pi) ^ 2 * (N : ℝ) ^ 4) * fullEnergy modes eta

def totalEnergyRate (nu : ℝ) (sources modes : Finset Wavevector)
    (omega eta : FourierVelocity) : ℝ :=
  transportEnergyRate sources modes omega eta + stretchingEnergyRate sources modes omega eta -
    2 * nu * (2 * Real.pi) ^ 2 * misalignedDissipation modes eta

/-- The named energy rate is the derivative of the existing finite
misalignment energy under the physical coefficient equation. -/
theorem hasDerivAt_misalignedEnergy_rhs
    (sources modes : Finset Wavevector) (omega : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (eta : ℝ → FourierVelocity) (nu t : ℝ)
    (he : ∀ q ∈ modes, ∀ i, HasDerivAt (fun tau ↦ eta tau q i)
      (finiteUnitTorusVorticityRHS sources modes omega (eta t) nu q i) t) :
    HasDerivAt (fun tau ↦ misalignedEnergy modes (eta tau))
      (totalEnergyRate nu sources modes omega (eta t)) t := by
  have h := hasDerivAt_vorticityMisalignmentEnergy sources modes omega hs hr eta nu t he
  rw [← misalignment_transport_identity sources modes omega (eta t) hs hr] at h
  exact h

/-- The checked PDE balance after viscous absorption.  Stretching is kept
signed and explicit; it is not declared controlled by this theorem. -/
theorem totalEnergyRate_add_dissipation_le
    {N : ℕ} (hN : 2 ≤ N) (sources modes : Finset Wavevector)
    (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (nu : ℝ) (hnu : 0 < nu) :
    totalEnergyRate nu sources modes omega eta +
        nu * (2 * Real.pi) ^ 2 * misalignedDissipation modes eta ≤
      stretchingEnergyRate sources modes omega eta + residualSourceCost N nu sources modes omega eta := by
  have h := transportEnergyRate_absorb_viscosity hN sources modes omega eta hs hr hmode nu hnu
  have hraw := le_abs_self (transportEnergyRate sources modes omega eta)
  unfold totalEnergyRate residualSourceCost
  linarith

theorem misalignedEnergy_deriv_add_dissipation_le
    {N : ℕ} (hN : 2 ≤ N) (sources modes : Finset Wavevector)
    (omega : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (eta : ℝ → FourierVelocity) (nu t : ℝ) (hnu : 0 < nu)
    (he : ∀ q ∈ modes, ∀ i, HasDerivAt (fun tau ↦ eta tau q i)
      (finiteUnitTorusVorticityRHS sources modes omega (eta t) nu q i) t) :
    deriv (fun tau ↦ misalignedEnergy modes (eta tau)) t +
        nu * (2 * Real.pi) ^ 2 * misalignedDissipation modes (eta t) ≤
      stretchingEnergyRate sources modes omega (eta t) +
        residualSourceCost N nu sources modes omega (eta t) := by
  rw [(hasDerivAt_misalignedEnergy_rhs sources modes omega hs hr eta nu t he).deriv]
  exact totalEnergyRate_add_dissipation_le hN sources modes omega (eta t) hs hr hmode nu hnu

/-- Integrate a differential energy inequality without discarding the
terminal energy.  Integrability of all displayed rates is explicit. -/
theorem integrated_energy_inequality (E rate D F : ℝ → ℝ) (C T : ℝ)
    (hT : 0 ≤ T)
    (hE : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt E (rate t) t)
    (hi : IntervalIntegrable rate MeasureTheory.volume 0 T)
    (hD : IntervalIntegrable D MeasureTheory.volume 0 T)
    (hF : IntervalIntegrable F MeasureTheory.volume 0 T)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, rate t + C * D t ≤ F t) :
    E T + C * (∫ t in (0 : ℝ)..T, D t) ≤ E 0 + ∫ t in (0 : ℝ)..T, F t := by
  have hmon := intervalIntegral.integral_mono_on hT (hi.add (hD.const_mul C)) hF hbound
  have hFTC : (∫ t in (0 : ℝ)..T, rate t) = E T - E 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hE t (by simpa [Set.uIcc_of_le hT] using ht)) hi
  rw [intervalIntegral.integral_add hi (hD.const_mul C),
    intervalIntegral.integral_const_mul, hFTC] at hmon
  linarith

/-- Time-integrated same-sector energy estimate along the physical finite
vorticity equation.  No horizon-uniform bound on its remaining right-hand
side is asserted. -/
theorem integrated_misalignedEnergy_after_absorption
    {N : ℕ} (hN : 2 ≤ N) (sources modes : Finset Wavevector)
    (omega eta : ℝ → FourierVelocity) (nu T : ℝ) (hnu : 0 < nu) (hT : 0 ≤ T)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, omega t (-k) = coefficientConjugate (omega t k))
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ eta tau q i)
        (finiteUnitTorusVorticityRHS sources modes (omega t) (eta t) nu q i) t)
    (hi : IntervalIntegrable (fun t ↦ totalEnergyRate nu sources modes (omega t) (eta t))
      MeasureTheory.volume 0 T)
    (hD : IntervalIntegrable (fun t ↦ misalignedDissipation modes (eta t)) MeasureTheory.volume 0 T)
    (hF : IntervalIntegrable (fun t ↦ stretchingEnergyRate sources modes (omega t) (eta t) +
      residualSourceCost N nu sources modes (omega t) (eta t)) MeasureTheory.volume 0 T) :
    misalignedEnergy modes (eta T) + nu * (2 * Real.pi) ^ 2 *
        (∫ t in (0 : ℝ)..T, misalignedDissipation modes (eta t)) ≤
      misalignedEnergy modes (eta 0) + ∫ t in (0 : ℝ)..T,
        (stretchingEnergyRate sources modes (omega t) (eta t) +
          residualSourceCost N nu sources modes (omega t) (eta t)) :=
  integrated_energy_inequality _ _ _ _ _ _ hT
    (fun t ht ↦ hasDerivAt_misalignedEnergy_rhs sources modes (omega t) hs (hr t ht) eta nu t (he t ht))
    hi hD hF
    (fun t ht ↦ totalEnergyRate_add_dissipation_le hN sources modes (omega t) (eta t)
      hs (hr t ht) hmode nu hnu)

/-- Euclidean coefficient energy respects the physical complex multiplier. -/
theorem coefficientEnergy_smul (a : ℂ) (v : VelocityCoefficient) :
    coefficientEnergy (a • v) = ‖a‖ ^ 2 * coefficientEnergy v := by
  rw [← norm_coefficientVec_sq, show coefficientVec (a • v) = a • coefficientVec v from rfl,
    norm_smul, mul_pow, norm_coefficientVec_sq]

/-- The exact complex Lagrange identity for a real Fourier frequency. -/
theorem cross_coefficientEnergy (k : Wavevector) (w : VelocityCoefficient) :
    coefficientEnergy (coefficientCross (wavevectorCoefficient k) w) =
      ‖frequencyVec k‖ ^ 2 * coefficientEnergy w - Complex.normSq (modeDot k w) := by
  rw [norm_frequencyVec_sq]
  simp [coefficientEnergy, coefficientCross, wavevectorCoefficient, modeDot,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Fin.sum_univ_three]
  ring

theorem complexBiotSavart_coefficientEnergy (k : Wavevector) (w : VelocityCoefficient)
    (hk : frequencyVec k ≠ 0) (hw : modeDot k w = 0) :
    coefficientEnergy (complexBiotSavartAmp k w) = coefficientEnergy w / ‖frequencyVec k‖ ^ 2 := by
  rw [complexBiotSavartAmp, coefficientEnergy_smul, cross_coefficientEnergy, hw]
  simp only [map_zero, sub_zero, norm_div, norm_one, norm_modeSquare]
  field_simp [norm_ne_zero_iff.mpr hk]

/-- The physical unit-torus Biot--Savart velocity controls source vorticity
with the exact frequency and `2π` factors. -/
theorem physicalBiotSavart_energy_identity (k : Wavevector) (w : VelocityCoefficient)
    (hk : frequencyVec k ≠ 0) (hw : modeDot k w = 0) :
    (2 * Real.pi) ^ 2 * ‖frequencyVec k‖ ^ 2 *
      coefficientEnergy (unitTorusBiotSavartAmp k w) = coefficientEnergy w := by
  have hp : ‖unitTorusDerivativePhase‖ = 2 * Real.pi := by
    simp [unitTorusDerivativePhase, Real.pi_pos.le]
  rw [unitTorusBiotSavartAmp, coefficientEnergy_smul,
    complexBiotSavart_coefficientEnergy k w hk hw, norm_neg, norm_inv, hp]
  field_simp [Real.pi_ne_zero, norm_ne_zero_iff.mpr hk]

/-- Kinetic energy of the actual finite source velocity, recovered by the
already defined physical Biot--Savart symbol. -/
def sourceKineticEnergy (sources : Finset Wavevector) (omega : FourierVelocity) : ℝ :=
  ∑ k ∈ sources, coefficientEnergy (unitTorusBiotSavartAmp k (omega k))

/-- A fixed source-set frequency moment.  Its dependence on the cutoff is
explicit; it must not be treated as a universal constant. -/
def sourceFrequencyMoment (sources : Finset Wavevector) : ℝ :=
  ∑ k ∈ sources, ‖frequencyVec k‖ ^ 2

/-- The source Fourier `ℓ¹` vorticity cost is controlled by the kinetic
energy of its physical velocity and the explicit source frequency moment. -/
theorem sourceAmplitude_sq_le_kinetic (sources : Finset Wavevector) (omega : FourierVelocity)
    (hk : ∀ k ∈ sources, frequencyVec k ≠ 0)
    (hw : ∀ k ∈ sources, modeDot k (omega k) = 0) :
    sourceAmplitude sources omega ^ 2 ≤
      (2 * Real.pi) ^ 2 * sourceFrequencyMoment sources * sourceKineticEnergy sources omega := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq sources
    (fun k ↦ ‖frequencyVec k‖) (fun k ↦ ‖coefficientVec (omega k)‖ / ‖frequencyVec k‖)
  have he : (∑ k ∈ sources, ‖frequencyVec k‖ *
      (‖coefficientVec (omega k)‖ / ‖frequencyVec k‖)) = sourceAmplitude sources omega := by
    apply Finset.sum_congr rfl
    intro k hmem
    field_simp [norm_ne_zero_iff.mpr (hk k hmem)]
  have hb : (∑ k ∈ sources, (‖coefficientVec (omega k)‖ / ‖frequencyVec k‖) ^ 2) =
      (2 * Real.pi) ^ 2 * sourceKineticEnergy sources omega := by
    rw [sourceKineticEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hmem
    rw [div_pow, norm_coefficientVec_sq]
    apply (div_eq_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hk k hmem)))).mpr
    have hh := physicalBiotSavart_energy_identity k (omega k) (hk k hmem) (hw k hmem)
    nlinarith
  rw [he, hb] at hcs
  change sourceAmplitude sources omega ^ 2 ≤
    (2 * Real.pi) ^ 2 * (∑ k ∈ sources, ‖frequencyVec k‖ ^ 2) * sourceKineticEnergy sources omega
  nlinarith

/-- After physical curl inversion, the residual source cost has no hidden
source `ℓ¹` norm.  The source frequency moment remains, and grows if its
cutoff grows. -/
theorem residualSourceCost_le_kinetic
    {N : ℕ} (hN : 2 ≤ N) (nu : ℝ) (hnu : 0 < nu)
    (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (hk : ∀ k ∈ sources, frequencyVec k ≠ 0)
    (hw : ∀ k ∈ sources, modeDot k (omega k) = 0) :
    residualSourceCost N nu sources modes omega eta ≤
      384 ^ 2 * sourceFrequencyMoment sources / (nu * (N : ℝ) ^ 4) *
        sourceKineticEnergy sources omega * fullEnergy modes eta := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd : 0 < nu * (2 * Real.pi) ^ 2 * (N : ℝ) ^ 4 := by positivity
  have hb := sourceAmplitude_sq_le_kinetic sources omega hk hw
  unfold residualSourceCost
  rw [mul_pow]
  calc
    _ ≤ (384 ^ 2 * ((2 * Real.pi) ^ 2 * sourceFrequencyMoment sources *
        sourceKineticEnergy sources omega)) /
        (nu * (2 * Real.pi) ^ 2 * (N : ℝ) ^ 4) * fullEnergy modes eta := by
      apply mul_le_mul_of_nonneg_right _ (fullEnergy_nonneg _ _)
      exact (div_le_div_iff_of_pos_right hd).mpr (mul_le_mul_of_nonneg_left hb (by positivity))
    _ = _ := by
      field_simp [hnu.ne', hn.ne', Real.pi_ne_zero]

end Mettapedia.FluidDynamics.NavierStokes.PancakeViscousMisalignmentAbsorption
