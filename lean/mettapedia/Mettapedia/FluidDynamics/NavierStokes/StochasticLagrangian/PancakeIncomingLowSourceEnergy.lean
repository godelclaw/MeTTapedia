import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSameSectorDissipation

/-!
# Incoming low-source energy and output-frequency dissipation

Incompressibility moves the transport derivative to the output frequency.
Diffusion can therefore absorb incoming transport even across a hard sector
boundary.  For sources no higher than the output frequencies, stretching
has the same estimate.  A rectangular Schur estimate retains every receiver
mode and leaves a source-velocity cost times full receiver enstrophy.

The source cutoff is explicit.  This module does not bound high-source
interactions, moving reference frames, or construct arbitrary-data solutions.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeIncomingLowSourceEnergy

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeBlockReality PancakeMaterialTransportCommutator
open PancakeSignedTransportEnergy PancakeFrequencyProjectorCommutator
open PancakeViscousMisalignmentAbsorption PancakeSameSectorDissipation
open PancakeSquareDyadicSectorProjector PancakeFrameCovariance

def physicalVelocity (omega : FourierVelocity) : FourierVelocity :=
  fun k ↦ unitTorusBiotSavartAmp k (omega k)

def velocityAmplitude (sources : Finset Wavevector) (omega : FourierVelocity) : ℝ :=
  sourceAmplitude sources (physicalVelocity omega)

theorem norm_derivativePhase : ‖unitTorusDerivativePhase‖ = 2 * Real.pi := by
  simp [unitTorusDerivativePhase, Real.pi_pos.le]

/-- No receiver-frequency loss: the physical source velocity is transverse
to the source shift, so its dot product with input and output agrees. -/
theorem physical_transport_output_derivative (q l : Wavevector) (w : VelocityCoefficient) :
    modeDot l (unitTorusBiotSavartAmp (q - l) w) =
      modeDot q (unitTorusBiotSavartAmp (q - l) w) := by
  have hz : modeDot (q - l) (unitTorusBiotSavartAmp (q - l) w) = 0 := by
    rw [unitTorusBiotSavartAmp, modeDot_smul, modeDot_complexBiotSavartAmp_self, mul_zero]
  rw [modeDot_sub_left, sub_eq_zero] at hz
  exact hz.symm

theorem norm_physical_transport_output_le (q l : Wavevector) (w v : VelocityCoefficient) :
    ‖coefficientVec (unitTorusNegativeTransportAmp (q - l) l w v)‖ ≤
      3 * (2 * Real.pi) * ‖frequencyVec q‖ *
        ‖coefficientVec (unitTorusBiotSavartAmp (q - l) w)‖ * ‖coefficientVec v‖ := by
  change ‖(-(unitTorusDerivativePhase *
      modeDot l (unitTorusBiotSavartAmp (q - l) w))) • coefficientVec v‖ ≤ _
  rw [norm_smul, norm_neg, norm_mul, norm_derivativePhase,
    physical_transport_output_derivative]
  have h : ‖modeDot q (unitTorusBiotSavartAmp (q - l) w)‖ ≤
      3 * ‖frequencyVec q‖ * ‖coefficientVec (unitTorusBiotSavartAmp (q - l) w)‖ :=
    norm_coefficientDot_le (wavevectorCoefficient q) _
  calc
    _ ≤ (2 * Real.pi) * (3 * ‖frequencyVec q‖ *
        ‖coefficientVec (unitTorusBiotSavartAmp (q - l) w)‖) * ‖coefficientVec v‖ := by gcongr
    _ = _ := by ring

theorem norm_physical_strain_velocity_le (k : Wavevector) (w v : VelocityCoefficient) :
    ‖coefficientVec (unitTorusStrainStretchAmp k w v)‖ ≤
      3 * (2 * Real.pi) * ‖frequencyVec k‖ *
        ‖coefficientVec (unitTorusBiotSavartAmp k w)‖ * ‖coefficientVec v‖ := by
  let u := unitTorusBiotSavartAmp k w
  change ‖((1 / 2 : ℂ) * unitTorusDerivativePhase) •
    (coefficientDot u v • frequencyVec k + modeDot k v • coefficientVec u)‖ ≤ _
  rw [norm_smul, norm_mul, norm_derivativePhase]
  have hh : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hh]
  have hd := norm_coefficientDot_le u v
  have hk : ‖modeDot k v‖ ≤ 3 * ‖frequencyVec k‖ * ‖coefficientVec v‖ :=
    norm_coefficientDot_le (wavevectorCoefficient k) v
  calc
    _ ≤ ((1 / 2 : ℝ) * (2 * Real.pi)) *
        (‖coefficientDot u v • frequencyVec k‖ + ‖modeDot k v • coefficientVec u‖) := by
      gcongr
      exact norm_add_le _ _
    _ = ((1 / 2 : ℝ) * (2 * Real.pi)) *
        (‖coefficientDot u v‖ * ‖frequencyVec k‖ + ‖modeDot k v‖ * ‖coefficientVec u‖) := by
      simp only [norm_smul]
    _ ≤ ((1 / 2 : ℝ) * (2 * Real.pi)) *
        ((3 * ‖coefficientVec u‖ * ‖coefficientVec v‖) * ‖frequencyVec k‖ +
          (3 * ‖frequencyVec k‖ * ‖coefficientVec v‖) * ‖coefficientVec u‖) := by gcongr
    _ = _ := by ring

/-- Rectangular Schur--Young estimate.  Output and receiver mode sets need
not agree, so incoming interactions are not omitted. -/
theorem rectangular_schur_young {ι κ : Type*} (outputs : Finset ι) (receivers : Finset κ)
    (a : ι → κ → ℝ) (b : ι → ℝ) (c : κ → ℝ) (A r : ℝ) (hr : 0 < r)
    (ha : ∀ q l, 0 ≤ a q l)
    (hrow : ∀ q ∈ outputs, ∑ l ∈ receivers, a q l ≤ A)
    (hcol : ∀ l ∈ receivers, ∑ q ∈ outputs, a q l ≤ A) :
    2 * (∑ q ∈ outputs, ∑ l ∈ receivers, a q l * b q * c l) ≤
      A * (r * (∑ q ∈ outputs, b q ^ 2) + (∑ l ∈ receivers, c l ^ 2) / r) := by
  have hp (q : ι) (l : κ) : 2 * (a q l * b q * c l) ≤
      r * (a q l * b q ^ 2) + (a q l * c l ^ 2) / r := by
    have h := mul_nonneg (ha q l) (sq_nonneg (r * b q - c l))
    apply (mul_le_mul_iff_right₀ hr).mp
    have hd : (a q l * c l ^ 2 / r) * r = a q l * c l ^ 2 := div_mul_cancel₀ _ hr.ne'
    nlinarith
  have hsum := Finset.sum_le_sum (s := outputs) fun q hq ↦
    Finset.sum_le_sum (s := receivers) fun l hl ↦ hp q l
  have hrow' : (∑ q ∈ outputs, ∑ l ∈ receivers, a q l * b q ^ 2) ≤
      A * ∑ q ∈ outputs, b q ^ 2 := by
    simp only [← Finset.sum_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun q hq ↦ mul_le_mul_of_nonneg_right (hrow q hq) (sq_nonneg _)
  have hcol' : (∑ q ∈ outputs, ∑ l ∈ receivers, a q l * c l ^ 2) ≤
      A * ∑ l ∈ receivers, c l ^ 2 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l hl ↦ mul_le_mul_of_nonneg_right (hcol l hl) (sq_nonneg _)
  simp only [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib] at hsum
  calc
    _ ≤ r * (∑ q ∈ outputs, ∑ l ∈ receivers, a q l * b q ^ 2) +
        (∑ q ∈ outputs, ∑ l ∈ receivers, a q l * c l ^ 2) / r := hsum
    _ ≤ r * (A * ∑ q ∈ outputs, b q ^ 2) + (A * ∑ l ∈ receivers, c l ^ 2) / r := by gcongr
    _ = _ := by ring

def incomingNonlinearCoeff (sources receivers : Finset Wavevector)
    (omega eta : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  finiteUnitTorusNegativeTransportCoeff sources receivers omega eta q +
    finiteUnitTorusStretchingCoeff sources receivers omega eta q

def incomingEnergyRate (sources receivers outputs : Finset Wavevector)
    (omega eta : FourierVelocity) : ℝ :=
  2 * ∑ q ∈ outputs, (coefficientHermitian (misalignedField eta q)
    (incomingNonlinearCoeff sources receivers omega eta q)).re

theorem incomingNonlinearCoeff_eq_receiverSum (sources receivers : Finset Wavevector)
    (omega eta : FourierVelocity) (q : Wavevector) :
    incomingNonlinearCoeff sources receivers omega eta q =
      ∑ l ∈ receivers, if q - l ∈ sources then
        unitTorusNegativeTransportAmp (q - l) l (omega (q - l)) (eta l) +
          unitTorusStrainStretchAmp (q - l) (omega (q - l)) (eta l) else 0 := by
  classical
  rw [incomingNonlinearCoeff, finiteTransport_eq_matrix, finiteStretching_eq_receiverSum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hm : q - l ∈ sources
  · simp [transportMatrix, hm, unitTorusNegativeTransportAmp_eq]
  · simp [transportMatrix, hm]

theorem incoming_pair_le (sources : Finset Wavevector) (omega eta : FourierVelocity)
    (q l : Wavevector) (hlow : ∀ k ∈ sources, ‖frequencyVec k‖ ≤ ‖frequencyVec q‖) :
    |(coefficientHermitian (misalignedField eta q)
      (if q - l ∈ sources then
        unitTorusNegativeTransportAmp (q - l) l (omega (q - l)) (eta l) +
          unitTorusStrainStretchAmp (q - l) (omega (q - l)) (eta l) else 0)).re| ≤
      (6 * (2 * Real.pi)) * sourceWeight sources (physicalVelocity omega) q l *
        (‖frequencyVec q‖ * ‖coefficientVec (misalignedField eta q)‖) * ‖coefficientVec (eta l)‖ := by
  classical
  by_cases hm : q - l ∈ sources
  · rw [if_pos hm, sourceWeight, if_pos hm]
    have ht := norm_physical_transport_output_le q l (omega (q - l)) (eta l)
    have hst := norm_physical_strain_velocity_le (q - l) (omega (q - l)) (eta l)
    have hh := hlow (q - l) hm
    have hb : ‖coefficientVec
        (unitTorusNegativeTransportAmp (q - l) l (omega (q - l)) (eta l) +
          unitTorusStrainStretchAmp (q - l) (omega (q - l)) (eta l))‖ ≤
        (6 * (2 * Real.pi)) * ‖frequencyVec q‖ *
          ‖coefficientVec (physicalVelocity omega (q - l))‖ * ‖coefficientVec (eta l)‖ := by
      change ‖coefficientVec (unitTorusNegativeTransportAmp (q - l) l (omega (q - l)) (eta l)) +
        coefficientVec (unitTorusStrainStretchAmp (q - l) (omega (q - l)) (eta l))‖ ≤ _
      calc
        _ ≤ ‖coefficientVec (unitTorusNegativeTransportAmp (q - l) l (omega (q - l)) (eta l))‖ +
            ‖coefficientVec (unitTorusStrainStretchAmp (q - l) (omega (q - l)) (eta l))‖ := norm_add_le _ _
        _ ≤ 3 * (2 * Real.pi) * ‖frequencyVec q‖ *
            ‖coefficientVec (unitTorusBiotSavartAmp (q - l) (omega (q - l)))‖ * ‖coefficientVec (eta l)‖ +
            3 * (2 * Real.pi) * ‖frequencyVec (q - l)‖ *
            ‖coefficientVec (unitTorusBiotSavartAmp (q - l) (omega (q - l)))‖ * ‖coefficientVec (eta l)‖ :=
          add_le_add ht hst
        _ ≤ 3 * (2 * Real.pi) * ‖frequencyVec q‖ *
            ‖coefficientVec (unitTorusBiotSavartAmp (q - l) (omega (q - l)))‖ * ‖coefficientVec (eta l)‖ +
            3 * (2 * Real.pi) * ‖frequencyVec q‖ *
            ‖coefficientVec (unitTorusBiotSavartAmp (q - l) (omega (q - l)))‖ * ‖coefficientVec (eta l)‖ := by
          gcongr
        _ = _ := by dsimp only [physicalVelocity]; ring
    calc
      _ ≤ ‖coefficientVec (misalignedField eta q)‖ * ‖coefficientVec
          (unitTorusNegativeTransportAmp (q - l) l (omega (q - l)) (eta l) +
            unitTorusStrainStretchAmp (q - l) (omega (q - l)) (eta l))‖ := abs_hermitian_re_le _ _
      _ ≤ ‖coefficientVec (misalignedField eta q)‖ *
          ((6 * (2 * Real.pi)) * ‖frequencyVec q‖ *
            ‖coefficientVec (physicalVelocity omega (q - l))‖ * ‖coefficientVec (eta l)‖) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = _ := by ring
  · simp [hm, sourceWeight, coefficientHermitian]

/-- The input energy is that of all receivers, not only the selected output
sector.  The output amplitude is weighted by its dissipative frequency. -/
theorem incomingEnergyRate_young (sources receivers outputs : Finset Wavevector)
    (omega eta : FourierVelocity)
    (hlow : ∀ q ∈ outputs, ∀ k ∈ sources, ‖frequencyVec k‖ ≤ ‖frequencyVec q‖)
    (r : ℝ) (hr : 0 < r) :
    |incomingEnergyRate sources receivers outputs omega eta| ≤
      (6 * (2 * Real.pi)) * velocityAmplitude sources omega *
        (r * misalignedDissipation outputs eta + fullEnergy receivers eta / r) := by
  classical
  let f (q l : Wavevector) : ℝ := (coefficientHermitian (misalignedField eta q)
    (if q - l ∈ sources then
      unitTorusNegativeTransportAmp (q - l) l (omega (q - l)) (eta l) +
        unitTorusStrainStretchAmp (q - l) (omega (q - l)) (eta l) else 0)).re
  let b (q : Wavevector) : ℝ := ‖frequencyVec q‖ * ‖coefficientVec (misalignedField eta q)‖
  let c (q : Wavevector) : ℝ := ‖coefficientVec (eta q)‖
  have hsum : |∑ q ∈ outputs, ∑ l ∈ receivers, f q l| ≤
      (6 * (2 * Real.pi)) * (∑ q ∈ outputs, ∑ l ∈ receivers,
        sourceWeight sources (physicalVelocity omega) q l * b q * c l) := by
    calc
      _ ≤ ∑ q ∈ outputs, ∑ l ∈ receivers, |f q l| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun q _ ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ q ∈ outputs, ∑ l ∈ receivers,
          (6 * (2 * Real.pi)) * sourceWeight sources (physicalVelocity omega) q l * b q * c l :=
        Finset.sum_le_sum fun q hq ↦ Finset.sum_le_sum fun l _ ↦
          incoming_pair_le sources omega eta q l (hlow q hq)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        apply Finset.sum_congr rfl
        intro l hl
        ring
  have hschur := rectangular_schur_young outputs receivers
    (sourceWeight sources (physicalVelocity omega)) b c (velocityAmplitude sources omega) r hr
    (sourceWeight_nonneg _ _)
    (fun q _ ↦ sum_sourceWeight_row_le sources receivers (physicalVelocity omega) q)
    (fun l _ ↦ sum_sourceWeight_column_le sources outputs (physicalVelocity omega) l)
  have hb : (∑ q ∈ outputs, b q ^ 2) = misalignedDissipation outputs eta := by
    simp only [b, mul_pow, norm_frequencyVec_sq, norm_coefficientVec_sq, misalignedDissipation]
  have hc : (∑ q ∈ receivers, c q ^ 2) = fullEnergy receivers eta := by
    simp [c, fullEnergy, norm_coefficientVec_sq]
  rw [hb, hc] at hschur
  unfold incomingEnergyRate
  simp_rw [incomingNonlinearCoeff_eq_receiverSum, hermitian_sum_right, Complex.re_sum]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  change 2 * |∑ q ∈ outputs, ∑ l ∈ receivers, f q l| ≤ _
  nlinarith [Real.pi_pos]

theorem misalignedDissipation_nonneg (outputs : Finset Wavevector) (eta : FourierVelocity) :
    0 ≤ misalignedDissipation outputs eta := by
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
    (PancakeArbitraryDataBlocks.coefficientEnergy_nonneg _)

def lowSourceCost (nu : ℝ) (sources receivers : Finset Wavevector)
    (omega eta : FourierVelocity) : ℝ :=
  36 * velocityAmplitude sources omega ^ 2 / nu * fullEnergy receivers eta

/-- Incoming low-source transport and stretching spend only half the
physical diffusion.  No output/receiver equality or buffered cutoff is used. -/
theorem incomingEnergyRate_absorb (sources receivers outputs : Finset Wavevector)
    (omega eta : FourierVelocity)
    (hlow : ∀ q ∈ outputs, ∀ k ∈ sources, ‖frequencyVec k‖ ≤ ‖frequencyVec q‖)
    (nu : ℝ) (hnu : 0 < nu) :
    |incomingEnergyRate sources receivers outputs omega eta| ≤
      nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs eta +
        lowSourceCost nu sources receivers omega eta := by
  have hd : 0 < nu * (2 * Real.pi) ^ 2 := by positivity
  have hb := optimize_bilinear_young
    (|incomingEnergyRate sources receivers outputs omega eta|)
    ((6 * (2 * Real.pi)) * velocityAmplitude sources omega)
    (misalignedDissipation outputs eta) (fullEnergy receivers eta)
    (nu * (2 * Real.pi) ^ 2)
    (mul_nonneg (by positivity) (sourceAmplitude_nonneg sources (physicalVelocity omega)))
    (misalignedDissipation_nonneg _ _) hd (incomingEnergyRate_young sources receivers outputs omega eta hlow)
  have he : ((6 * (2 * Real.pi)) * velocityAmplitude sources omega) ^ 2 /
      (nu * (2 * Real.pi) ^ 2) = 36 * velocityAmplitude sources omega ^ 2 / nu := by
    field_simp [hnu.ne', Real.pi_ne_zero]
    ring
  rw [he] at hb
  exact hb

/-- The physical source velocity amplitude costs its retained mode count,
not a source-frequency moment. -/
theorem velocityAmplitude_sq_le_card_kinetic (sources : Finset Wavevector) (omega : FourierVelocity) :
    velocityAmplitude sources omega ^ 2 ≤
      (sources.card : ℝ) * sourceKineticEnergy sources omega := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq sources (fun _ ↦ (1 : ℝ))
    (fun k ↦ ‖coefficientVec (physicalVelocity omega k)‖)
  simpa [velocityAmplitude, sourceAmplitude, sourceKineticEnergy, physicalVelocity,
    norm_coefficientVec_sq] using h

theorem lowSourceCost_le_kinetic (nu : ℝ) (hnu : 0 < nu)
    (sources receivers : Finset Wavevector) (omega eta : FourierVelocity) :
    lowSourceCost nu sources receivers omega eta ≤
      36 * (sources.card : ℝ) / nu * sourceKineticEnergy sources omega * fullEnergy receivers eta := by
  unfold lowSourceCost
  calc
    _ ≤ 36 * ((sources.card : ℝ) * sourceKineticEnergy sources omega) / nu * fullEnergy receivers eta := by
      apply mul_le_mul_of_nonneg_right _ (fullEnergy_nonneg _ _)
      exact (div_le_div_iff_of_pos_right hnu).mpr
        (mul_le_mul_of_nonneg_left (velocityAmplitude_sq_le_card_kinetic sources omega) (by positivity))
    _ = _ := by ring

/-- Differentiation on the output sector retains the entire receiver
convolution.  The source and receiver sets are unrestricted here. -/
theorem hasDerivAt_misalignedEnergy_fullReceiver
    (sources receivers outputs : Finset Wavevector) (omega : FourierVelocity)
    (eta : ℝ → FourierVelocity) (nu t : ℝ)
    (he : ∀ q ∈ outputs, ∀ i, HasDerivAt (fun tau ↦ eta tau q i)
      (finiteUnitTorusVorticityRHS sources receivers omega (eta t) nu q i) t) :
    HasDerivAt (fun tau ↦ misalignedEnergy outputs (eta tau))
      (incomingEnergyRate sources receivers outputs omega (eta t) -
        2 * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs (eta t)) t := by
  have h := hasDerivAt_misalignmentEnergy outputs eta
    (finiteUnitTorusVorticityRHS sources receivers omega (eta t) nu) t he
  have hv : (∑ q ∈ outputs,
      (coefficientHermitian (misalignmentComponent q (eta t q))
        (unitTorusViscousVorticityCoeff nu (eta t) q)).re) =
      -nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs (eta t) := by
    simp_rw [viscous_misalignment_energy_pair]
    rw [misalignedDissipation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    dsimp only [misalignedField]
    ring
  have heq : 2 * (∑ q ∈ outputs,
      (coefficientHermitian (misalignmentComponent q (eta t q))
        (finiteUnitTorusVorticityRHS sources receivers omega (eta t) nu q)).re) =
      incomingEnergyRate sources receivers outputs omega (eta t) -
        2 * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs (eta t) := by
    simp only [finiteUnitTorusVorticityRHS, finiteUnitTorusNonstretchingCoeff,
      incomingEnergyRate, incomingNonlinearCoeff, misalignedField,
      hermitian_add_right, Complex.add_re, Finset.sum_add_distrib]
    rw [hv]
    ring
  rw [heq] at h
  exact h

def lowSources (cutoff : ℝ) (sources : Finset Wavevector) : Finset Wavevector :=
  sources.filter fun k ↦ ‖frequencyVec k‖ ≤ cutoff

def highSources (cutoff : ℝ) (sources : Finset Wavevector) : Finset Wavevector :=
  sources.filter fun k ↦ ¬ ‖frequencyVec k‖ ≤ cutoff

/-- Exact source decomposition of the physical nonlinear coefficient.
Every receiver is retained in both source channels. -/
theorem incomingNonlinearCoeff_low_add_high (cutoff : ℝ)
    (sources receivers : Finset Wavevector) (omega eta : FourierVelocity) (q : Wavevector) :
    incomingNonlinearCoeff sources receivers omega eta q =
      incomingNonlinearCoeff (lowSources cutoff sources) receivers omega eta q +
        incomingNonlinearCoeff (highSources cutoff sources) receivers omega eta q := by
  classical
  have ht : finiteUnitTorusNegativeTransportCoeff (lowSources cutoff sources) receivers omega eta q +
      finiteUnitTorusNegativeTransportCoeff (highSources cutoff sources) receivers omega eta q =
        finiteUnitTorusNegativeTransportCoeff sources receivers omega eta q := by
    simp only [finiteUnitTorusNegativeTransportCoeff_eq_doubleSum, lowSources, highSources]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hs : finiteUnitTorusStretchingCoeff (lowSources cutoff sources) receivers omega eta q +
      finiteUnitTorusStretchingCoeff (highSources cutoff sources) receivers omega eta q =
        finiteUnitTorusStretchingCoeff sources receivers omega eta q := by
    simp only [finiteUnitTorusStretchingCoeff_eq_doubleSum, lowSources, highSources]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  unfold incomingNonlinearCoeff
  rw [← ht, ← hs]
  abel

theorem incomingEnergyRate_low_add_high (cutoff : ℝ)
    (sources receivers outputs : Finset Wavevector) (omega eta : FourierVelocity) :
    incomingEnergyRate sources receivers outputs omega eta =
      incomingEnergyRate (lowSources cutoff sources) receivers outputs omega eta +
        incomingEnergyRate (highSources cutoff sources) receivers outputs omega eta := by
  unfold incomingEnergyRate
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [incomingNonlinearCoeff_low_add_high cutoff, hermitian_add_right, Complex.add_re]

/-- The full finite equation now leaves only the explicit high-source
channel after absorbing all incoming low-source interactions. -/
theorem misalignedEnergy_deriv_lowSource_absorption
    (cutoff : ℝ) (sources receivers outputs : Finset Wavevector) (omega : FourierVelocity)
    (houtput : ∀ q ∈ outputs, cutoff ≤ ‖frequencyVec q‖)
    (eta : ℝ → FourierVelocity) (nu t : ℝ) (hnu : 0 < nu)
    (he : ∀ q ∈ outputs, ∀ i, HasDerivAt (fun tau ↦ eta tau q i)
      (finiteUnitTorusVorticityRHS sources receivers omega (eta t) nu q i) t) :
    deriv (fun tau ↦ misalignedEnergy outputs (eta tau)) t +
      nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs (eta t) ≤
        incomingEnergyRate (highSources cutoff sources) receivers outputs omega (eta t) +
          lowSourceCost nu (lowSources cutoff sources) receivers omega (eta t) := by
  rw [(hasDerivAt_misalignedEnergy_fullReceiver sources receivers outputs omega eta nu t he).deriv,
    incomingEnergyRate_low_add_high cutoff]
  have hlow : ∀ q ∈ outputs, ∀ k ∈ lowSources cutoff sources,
      ‖frequencyVec k‖ ≤ ‖frequencyVec q‖ := by
    intro q hq k hk
    exact (Finset.mem_filter.mp hk).2.trans (houtput q hq)
  have hb := incomingEnergyRate_absorb (lowSources cutoff sources) receivers outputs omega (eta t)
    hlow nu hnu
  have ha := le_abs_self (incomingEnergyRate (lowSources cutoff sources) receivers outputs omega (eta t))
  linarith

/-- The source/output ordering follows from the actual pancake shell,
while receivers may belong to any sector or shell. -/
theorem pancake_output_above_cutoff {N : ℕ} (hN : 2 ≤ N) (cutoff : ℝ)
    (hcutoff : cutoff ≤ (N : ℝ) ^ 2) (outputs : Finset Wavevector)
    (hmode : ∀ q ∈ outputs, InOrientedSquarePancakeConeAnnulus identityFrame N q) :
    ∀ q ∈ outputs, cutoff ≤ ‖frequencyVec q‖ := by
  intro q hq
  exact hcutoff.trans (pancake_frequency_bounds hN q (hmode q hq)).2.2.1

/-- Integrate the actual full-receiver equation with its high-source term
still present.  All rate-integrability requirements are explicit. -/
theorem integrated_lowSource_absorption
    (cutoff : ℝ) (sources receivers outputs : Finset Wavevector)
    (omega eta : ℝ → FourierVelocity) (nu T : ℝ) (hnu : 0 < nu) (hT : 0 ≤ T)
    (houtput : ∀ q ∈ outputs, cutoff ≤ ‖frequencyVec q‖)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ outputs, ∀ i,
      HasDerivAt (fun tau ↦ eta tau q i)
        (finiteUnitTorusVorticityRHS sources receivers (omega t) (eta t) nu q i) t)
    (hi : IntervalIntegrable (fun t ↦ incomingEnergyRate sources receivers outputs (omega t) (eta t) -
      2 * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs (eta t)) MeasureTheory.volume 0 T)
    (hD : IntervalIntegrable (fun t ↦ misalignedDissipation outputs (eta t)) MeasureTheory.volume 0 T)
    (hF : IntervalIntegrable (fun t ↦
      incomingEnergyRate (highSources cutoff sources) receivers outputs (omega t) (eta t) +
        lowSourceCost nu (lowSources cutoff sources) receivers (omega t) (eta t)) MeasureTheory.volume 0 T) :
    misalignedEnergy outputs (eta T) + nu * (2 * Real.pi) ^ 2 *
      (∫ t in (0 : ℝ)..T, misalignedDissipation outputs (eta t)) ≤
        misalignedEnergy outputs (eta 0) + ∫ t in (0 : ℝ)..T,
          (incomingEnergyRate (highSources cutoff sources) receivers outputs (omega t) (eta t) +
            lowSourceCost nu (lowSources cutoff sources) receivers (omega t) (eta t)) := by
  apply integrated_energy_inequality _ _ _ _ _ _ hT
    (fun t ht ↦ hasDerivAt_misalignedEnergy_fullReceiver sources receivers outputs (omega t) eta nu t (he t ht))
    hi hD hF
  intro t ht
  have h := misalignedEnergy_deriv_lowSource_absorption cutoff sources receivers outputs (omega t)
    houtput eta nu t hnu (he t ht)
  rw [(hasDerivAt_misalignedEnergy_fullReceiver sources receivers outputs (omega t) eta nu t (he t ht)).deriv] at h
  exact h

/-- A fixed source set has a horizon-uniform low-source cost whenever
physical kinetic energy and time-integrated receiver enstrophy have their
displayed bounds.  These energy bounds are inputs, not solution-existence
or kinetic-energy theorems asserted by this lemma. -/
theorem lowSourceCost_integral_le_of_energy_bounds
    (sources receivers : Finset Wavevector) (omega eta : ℝ → FourierVelocity)
    (nu T U B : ℝ) (hnu : 0 < nu) (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hkinetic : ∀ t ∈ Set.Icc (0 : ℝ) T, sourceKineticEnergy sources (omega t) ≤ U)
    (hC : IntervalIntegrable (fun t ↦ lowSourceCost nu sources receivers (omega t) (eta t))
      MeasureTheory.volume 0 T)
    (hE : IntervalIntegrable (fun t ↦ fullEnergy receivers (eta t)) MeasureTheory.volume 0 T)
    (hbudget : (∫ t in (0 : ℝ)..T, fullEnergy receivers (eta t)) ≤ B) :
    (∫ t in (0 : ℝ)..T, lowSourceCost nu sources receivers (omega t) (eta t)) ≤
      36 * (sources.card : ℝ) / nu * U * B := by
  have hc : 0 ≤ 36 * (sources.card : ℝ) / nu := by positivity
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) T,
      lowSourceCost nu sources receivers (omega t) (eta t) ≤
        (36 * (sources.card : ℝ) / nu * U) * fullEnergy receivers (eta t) := by
    intro t ht
    exact (lowSourceCost_le_kinetic nu hnu sources receivers (omega t) (eta t)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hkinetic t ht) hc) (fullEnergy_nonneg _ _))
  have hm := intervalIntegral.integral_mono_on hT hC (hE.const_mul _) hb
  rw [intervalIntegral.integral_const_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left hbudget (mul_nonneg hc hU))

/-- The usual kinetic/enstrophy normalization gives an explicit bound
independent of the time horizon, conditional on those energy estimates. -/
theorem lowSourceCost_integral_le_of_kinetic_dissipation
    (sources receivers : Finset Wavevector) (omega eta : ℝ → FourierVelocity)
    (nu T U : ℝ) (hnu : 0 < nu) (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hkinetic : ∀ t ∈ Set.Icc (0 : ℝ) T, sourceKineticEnergy sources (omega t) ≤ U)
    (hC : IntervalIntegrable (fun t ↦ lowSourceCost nu sources receivers (omega t) (eta t))
      MeasureTheory.volume 0 T)
    (hE : IntervalIntegrable (fun t ↦ fullEnergy receivers (eta t)) MeasureTheory.volume 0 T)
    (hbudget : 2 * nu * (∫ t in (0 : ℝ)..T, fullEnergy receivers (eta t)) ≤ U) :
    (∫ t in (0 : ℝ)..T, lowSourceCost nu sources receivers (omega t) (eta t)) ≤
      18 * (sources.card : ℝ) * U ^ 2 / nu ^ 2 := by
  have hh : (∫ t in (0 : ℝ)..T, fullEnergy receivers (eta t)) ≤ U / (2 * nu) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * nu)).mpr
    nlinarith
  have h := lowSourceCost_integral_le_of_energy_bounds sources receivers omega eta nu T U
    (U / (2 * nu)) hnu hT hU hkinetic hC hE hh
  have he : 36 * (sources.card : ℝ) / nu * U * (U / (2 * nu)) =
      18 * (sources.card : ℝ) * U ^ 2 / nu ^ 2 := by ring
  exact h.trans_eq he

/-- An explicit containing cube for all integer modes below a fixed
natural frequency cutoff, independent of the ambient retained support. -/
def sourceCube (L : ℕ) : Finset Wavevector :=
  ((Finset.Icc (-(L : ℤ)) (L : ℤ)).product
    ((Finset.Icc (-(L : ℤ)) (L : ℤ)).product (Finset.Icc (-(L : ℤ)) (L : ℤ)))).image
      latticeToWavevector

theorem lowSources_subset_sourceCube (L : ℕ) (sources : Finset Wavevector) :
    lowSources (L : ℝ) sources ⊆ sourceCube L := by
  intro k hk
  have hfreq := (Finset.mem_filter.mp hk).2
  have hcoord (i : Fin 3) : -(L : ℤ) ≤ k i ∧ k i ≤ (L : ℤ) := by
    have h := (norm_frequency_apply_le k i).trans hfreq
    have hn : ‖(k i : ℂ)‖ = |(k i : ℝ)| := by norm_cast
    rw [hn, abs_le] at h
    exact_mod_cast h
  apply Finset.mem_image.mpr
  refine ⟨(k 0, k 1, k 2), ?_, ?_⟩
  · change (k 0, k 1, k 2) ∈
      (Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ
        ((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ)))
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨hcoord 0, hcoord 1, hcoord 2⟩
  · ext i
    fin_cases i <;> rfl

theorem sourceCube_card_le (L : ℕ) : (sourceCube L).card ≤ (2 * L + 1) ^ 3 := by
  have hcard : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ ((Finset.Icc (-(L : ℤ)) (L : ℤ)).product
        ((Finset.Icc (-(L : ℤ)) (L : ℤ)).product (Finset.Icc (-(L : ℤ)) (L : ℤ)))).card :=
      Finset.card_image_le
    _ = _ := by
      change ((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ
        ((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ)))).card = _
      rw [Finset.card_product, Finset.card_product, hcard]
      ring

theorem lowSources_card_le (L : ℕ) (sources : Finset Wavevector) :
    (lowSources (L : ℝ) sources).card ≤ (2 * L + 1) ^ 3 :=
  (Finset.card_le_card (lowSources_subset_sourceCube L sources)).trans (sourceCube_card_le L)

/-- The conditional low-source time budget is uniform in the ambient
Galerkin cutoff and receiver sector.  Its chosen source cutoff stays fixed. -/
theorem lowSourceCost_integral_le_fixed_cutoff
    (L : ℕ) (sources receivers : Finset Wavevector) (omega eta : ℝ → FourierVelocity)
    (nu T U : ℝ) (hnu : 0 < nu) (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hkinetic : ∀ t ∈ Set.Icc (0 : ℝ) T,
      sourceKineticEnergy (lowSources (L : ℝ) sources) (omega t) ≤ U)
    (hC : IntervalIntegrable (fun t ↦
      lowSourceCost nu (lowSources (L : ℝ) sources) receivers (omega t) (eta t)) MeasureTheory.volume 0 T)
    (hE : IntervalIntegrable (fun t ↦ fullEnergy receivers (eta t)) MeasureTheory.volume 0 T)
    (hbudget : 2 * nu * (∫ t in (0 : ℝ)..T, fullEnergy receivers (eta t)) ≤ U) :
    (∫ t in (0 : ℝ)..T,
      lowSourceCost nu (lowSources (L : ℝ) sources) receivers (omega t) (eta t)) ≤
        18 * (2 * (L : ℝ) + 1) ^ 3 * U ^ 2 / nu ^ 2 := by
  have h := lowSourceCost_integral_le_of_kinetic_dissipation
    (lowSources (L : ℝ) sources) receivers omega eta nu T U hnu hT hU hkinetic hC hE hbudget
  have hcard : ((lowSources (L : ℝ) sources).card : ℝ) ≤ (2 * (L : ℝ) + 1) ^ 3 := by
    exact_mod_cast lowSources_card_le L sources
  exact h.trans (by gcongr)

end Mettapedia.FluidDynamics.NavierStokes.PancakeIncomingLowSourceEnergy
