import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierAxialLeraySource

/-!
# Internal renewal of a cellular Fourier parent

Two transverse, genuinely three-dimensional modes feed a planar cellular
parent through the complete pressure-projected Navier--Stokes nonlinearity.
Changing one hidden phase reverses the transfer, with equal initial energy.

The finite support describes only the initial datum. The source uses the
existing infinite coefficient equation, with all outputs permitted; no
closed finite-mode evolution or external force is introduced. The explicit
derivative calculation is instantaneous, not a recurrent-history bound.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.CellularParentRenewal

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit
  PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
  PancakeLowPressureBudget InfiniteFilteredEquation PancakeCoefficientLimitEquation
  PancakeFrequencyProjectorCommutator PancakeSignedTransportEnergy PancakeBlockReality
  PancakeFilteredStrainDynamics PancakeSobolevFiberEnvelope

def parentP : Wavevector := ![1, 2, 0]
def parentQ : Wavevector := ![2, 1, 0]
def parentR : Wavevector := ![1, -2, 0]
def verticalMode : Wavevector := ![1, 0, 0]
def hiddenK : Wavevector := ![1, 1, 1]
def hiddenL : Wavevector := ![0, -1, 1]

def support : Finset Wavevector :=
  {parentP, -parentP, parentQ, -parentQ, parentR, -parentR,
    verticalMode, -verticalMode, hiddenK, -hiddenK, hiddenL, -hiddenL}

def pv : VelocityCoefficient := Complex.I • ![-1 / 5, 1 / 10, 0]
def qv : VelocityCoefficient := Complex.I • ![-9 / 100, 9 / 50, 0]
def rv : VelocityCoefficient := Complex.I • ![4 / 25, 2 / 25, 0]
def vv : VelocityCoefficient := -Complex.I • ![0, 0, 1]
def kv (ε : ℝ) : VelocityCoefficient := ((ε : ℂ) / 2) • ![1, -1, 0]
def lv (ε σ : ℝ) : VelocityCoefficient := ((σ : ℂ) * (ε : ℂ) / 2) • ![1, 1, 1]

/-- Real Fourier datum; `σ = ±1` changes one hidden cosine phase. -/
def velocity (ε σ : ℝ) : FourierVelocity := fun k ↦
  if k = parentP then pv else if k = -parentP then -pv
  else if k = parentQ then qv else if k = -parentQ then -qv
  else if k = parentR then rv else if k = -parentR then -rv
  else if k = verticalMode then vv else if k = -verticalMode then -vv
  else if k = hiddenK ∨ k = -hiddenK then kv ε
  else if k = hiddenL ∨ k = -hiddenL then lv ε σ else 0

theorem support_symmetric (k : Wavevector) : -k ∈ support ↔ k ∈ support := by
  simp only [support, Finset.mem_insert, Finset.mem_singleton, neg_eq_iff_eq_neg, neg_neg]
  tauto

theorem velocity_supported (ε σ : ℝ) (k : Wavevector) (hk : k ∉ support) :
    velocity ε σ k = 0 := by
  simp only [support, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  simp [velocity, hk]

theorem support_nonzero (k : Wavevector) (hk : k ∈ support) : k ≠ 0 := by
  intro h
  exact (by decide : (0 : Wavevector) ∉ support) (h ▸ hk)

theorem velocity_transverse (ε σ : ℝ) (k : Wavevector) :
    modeDot k (velocity ε σ k) = 0 := by
  by_cases hk : k ∈ support
  · simp only [support, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [velocity, parentP, parentQ, parentR, verticalMode, hiddenK, hiddenL,
        pv, qv, rv, vv, kv, lv, modeDot, Fin.sum_univ_three, Matrix.cons_val_two,
        ite_apply, funext_iff, Fin.forall_fin_succ] <;> ring
  · simp [velocity_supported ε σ k hk, modeDot]

theorem velocity_reality (ε σ : ℝ) (k : Wavevector) :
    velocity ε σ (-k) = fun i ↦ conj (velocity ε σ k i) := by
  by_cases hk : k ∈ support
  · simp only [support, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      ext i <;> fin_cases i <;>
      norm_num [velocity, parentP, parentQ, parentR, verticalMode, hiddenK, hiddenL,
        pv, qv, rv, vv, kv, lv, Matrix.cons_val_two, ite_apply,
        funext_iff, Fin.forall_fin_succ, map_ofNat]
  · rw [velocity_supported ε σ k hk,
      velocity_supported ε σ (-k) (fun h ↦ hk ((support_symmetric k).mp h))]
    ext i
    simp

/-- Only the two hidden interactions reach this receiving parent. -/
theorem parent_pairs : interactionPairs support parentP =
    {(hiddenK, -hiddenL), (-hiddenL, hiddenK)} := by decide

theorem negative_parent_pairs : interactionPairs support (-parentP) =
    {(-hiddenK, hiddenL), (hiddenL, -hiddenK)} := by decide

private theorem velocity_hiddenK (ε σ : ℝ) : velocity ε σ hiddenK = kv ε := by
  norm_num [velocity, parentP, parentQ, parentR, verticalMode, hiddenK,
    hiddenL, funext_iff, Fin.forall_fin_succ]

private theorem velocity_negative_hiddenK (ε σ : ℝ) : velocity ε σ (-hiddenK) = kv ε := by
  norm_num [velocity, parentP, parentQ, parentR, verticalMode, hiddenK,
    hiddenL, funext_iff, Fin.forall_fin_succ]

private theorem velocity_hiddenL (ε σ : ℝ) : velocity ε σ hiddenL = lv ε σ := by
  norm_num [velocity, parentP, parentQ, parentR, verticalMode, hiddenK,
    hiddenL, funext_iff, Fin.forall_fin_succ]

private theorem velocity_negative_hiddenL (ε σ : ℝ) : velocity ε σ (-hiddenL) = lv ε σ := by
  norm_num [velocity, parentP, parentQ, parentR, verticalMode, hiddenK,
    hiddenL, funext_iff, Fin.forall_fin_succ]

theorem parent_source (ε σ : ℝ) :
    projectedNonlinearity support (velocity ε σ) parentP =
      (Complex.I * (σ : ℂ) * (ε : ℂ) ^ 2) • ![-4 / 5, 2 / 5, 1 / 4] := by
  rw [projectedNonlinearity, convectionConvolution_eq_pairSum, parent_pairs]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [orderedConvection, velocity_hiddenK, velocity_negative_hiddenL]
  ext i
  fin_cases i <;>
    norm_num [parentP, hiddenK, hiddenL, kv, lv, lerayMode, modeSquare, modeDot,
      Fin.sum_univ_three, Matrix.cons_val_two, ite_apply,
      funext_iff, Fin.forall_fin_succ] <;> ring

theorem negative_parent_source (ε σ : ℝ) :
    projectedNonlinearity support (velocity ε σ) (-parentP) =
      (-Complex.I * (σ : ℂ) * (ε : ℂ) ^ 2) • ![-4 / 5, 2 / 5, 1 / 4] := by
  rw [projectedNonlinearity, convectionConvolution_eq_pairSum, negative_parent_pairs]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [orderedConvection, velocity_negative_hiddenK, velocity_hiddenL]
  ext i
  fin_cases i <;>
    norm_num [parentP, hiddenK, hiddenL, kv, lv, lerayMode, modeSquare, modeDot,
      Fin.sum_univ_three, Matrix.cons_val_two, ite_apply,
      funext_iff, Fin.forall_fin_succ] <;> ring

/-- This is the all-input infinite equation at every output, not a
projection of the dynamics onto the twelve initial modes. -/
theorem actual_source (ε σ ν : ℝ) (q : Wavevector) :
    infiniteVelocityRHS ν (velocity ε σ) q =
      (2 * (Real.pi : ℂ)) • projectedNonlinearity support (velocity ε σ) q +
        unitTorusViscousVorticityCoeff ν (velocity ε σ) q := by
  have hn : ∀ k ∈ support, frequencyVec k ≠ 0 :=
    fun k hk ↦ frequencyVec_ne_zero (support_nonzero k hk)
  have ht : ∀ k ∈ support, modeDot k (velocity ε σ k) = 0 :=
    fun k _ ↦ velocity_transverse ε σ k
  rw [infiniteVelocityRHS_eq_finite support _ (velocity_supported ε σ) hn ht,
    velocityRHS_eq_projectedNonlinearity support _ hn ht]

theorem parent_work (ε σ : ℝ) :
    (coefficientHermitian (velocity ε σ parentP)
      (projectedNonlinearity support (velocity ε σ) parentP)).re = σ * ε ^ 2 / 5 := by
  rw [parent_source]
  norm_num [velocity, pv, parentP, coefficientHermitian,
    Fin.sum_univ_three, Matrix.cons_val_two, ite_apply,
    funext_iff, Fin.forall_fin_succ, Complex.mul_re, Complex.mul_im, pow_two]
  ring

theorem negative_parent_work (ε σ : ℝ) :
    (coefficientHermitian (velocity ε σ (-parentP))
      (projectedNonlinearity support (velocity ε σ) (-parentP))).re = σ * ε ^ 2 / 5 := by
  rw [negative_parent_source]
  norm_num [velocity, pv, parentP, coefficientHermitian,
    Fin.sum_univ_three, Matrix.cons_val_two, ite_apply,
    funext_iff, Fin.forall_fin_succ, Complex.mul_re, Complex.mul_im, pow_two]
  ring

def parentPair : Finset Wavevector := {parentP, -parentP}

theorem summable_full_fiber (ε σ : ℝ) (q : Wavevector) (i : Fin 3) :
    Summable (fun k ↦ outputFiber q (velocity ε σ) k i) :=
  summable_of_ne_finset_zero (s := support)
    (fun k hk ↦ by simp [outputFiber, velocity_supported ε σ k hk, modeDot])

/-- The receiving plane wave has no autonomous convection at this output. -/
theorem filtered_parent_convection_zero (ε σ : ℝ) :
    infiniteConvection (filteredVelocity (sharpFilter parentPair) (velocity ε σ)) parentP = 0 := by
  have hs : ∀ k, k ∉ parentPair →
      filteredVelocity (sharpFilter parentPair) (velocity ε σ) k = 0 := by
    intro k hk
    simp [filteredVelocity, sharpFilter, hk]
  have ht : ∀ k ∈ parentPair, modeDot k
      (filteredVelocity (sharpFilter parentPair) (velocity ε σ) k) = 0 := by
    intro k _
    simp [filteredVelocity, modeDot_smul, velocity_transverse]
  have hc : infiniteConvection
      (filteredVelocity (sharpFilter parentPair) (velocity ε σ)) parentP =
      convectionConvolution parentPair
        (filteredVelocity (sharpFilter parentPair) (velocity ε σ)) parentP := by
    ext i
    exact PancakeConvectionFiberIdentity.tsum_outputFiber_eq_convectionConvolution
      parentPair _ hs ht parentP i
  rw [hc, convectionConvolution_eq_pairSum,
    show interactionPairs parentPair parentP = ∅ by decide]
  simp

/-- The apparent force on the observed parent is precisely the compatible
all-input subgrid force, including its pressure correction. -/
theorem actual_subgrid_force (ε σ : ℝ) :
    subgridForce (sharpFilter parentPair) (velocity ε σ) parentP =
      (2 * (Real.pi : ℂ)) •
        ((Complex.I * (σ : ℂ) * (ε : ℂ) ^ 2) • ![-4 / 5, 2 / 5, 1 / 4]) := by
  have h := filtered_infiniteConvection (sharpFilter parentPair) (velocity ε σ) 1
    (norm_sharpFilter_le_one parentPair) parentP (summable_full_fiber ε σ parentP)
  have hh : sharpFilter parentPair parentP = 1 := by simp [sharpFilter, parentPair]
  rw [hh, one_smul, filtered_parent_convection_zero, zero_add] at h
  have hc : infiniteConvection (velocity ε σ) parentP =
      convectionConvolution support (velocity ε σ) parentP := by
    ext i
    exact PancakeConvectionFiberIdentity.tsum_outputFiber_eq_convectionConvolution
      support _ (velocity_supported ε σ) (fun k _ ↦ velocity_transverse ε σ k) parentP i
  rw [subgridForce, ← h, hc]
  rw [← parent_source]
  rw [projectedNonlinearity, lerayMode_smul, smul_smul]
  congr 1
  simp [unitTorusDerivativePhase]

/-- Normalized nonlinear energy transfer into both conjugate receivers. -/
theorem parent_nonlinear_energy_rate (ε σ : ℝ) :
    nonlinearEnergyRate support parentPair (velocity ε σ) = 4 / 5 * σ * ε ^ 2 := by
  unfold nonlinearEnergyRate parentPair
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, parent_work, negative_parent_work]
  ring

theorem parent_pair_energy (ε σ : ℝ) :
    fourierEnergy parentPair (velocity ε σ) = 1 / 10 := by
  norm_num [fourierEnergy, parentPair, velocity, pv, parentP, coefficientEnergy,
    Complex.normSq_apply, Fin.sum_univ_three, Matrix.cons_val_two, ite_apply,
    funext_iff, Fin.forall_fin_succ]

/-- Reversing the hidden phase leaves the full datum's energy unchanged. -/
theorem initial_energy (ε σ : ℝ) :
    fourierEnergy support (velocity ε σ) =
      449 / 200 + ε ^ 2 * (1 + 3 / 2 * σ ^ 2) := by
  norm_num [fourierEnergy, support, velocity, parentP, parentQ, parentR,
    verticalMode, hiddenK, hiddenL, pv, qv, rv, vv, kv, lv, coefficientEnergy,
    Complex.normSq_apply, Fin.sum_univ_three, Matrix.cons_val_two, ite_apply,
    funext_iff, Fin.forall_fin_succ, Complex.mul_re, Complex.mul_im, pow_two]
  ring

theorem phase_energy_equal (ε : ℝ) :
    fourierEnergy support (velocity ε 1) = fourierEnergy support (velocity ε (-1)) := by
  rw [initial_energy, initial_energy]
  norm_num

/-- The receiving gain is internal: the complete unforced vector field
still has its exact kinetic-energy dissipation identity. Newly generated
outputs have zero initial velocity, not suppressed evolution. -/
theorem actual_kinetic_balance (ε σ ν : ℝ) :
    2 * (∑ q ∈ support, (coefficientHermitian (velocity ε σ q)
      (infiniteVelocityRHS ν (velocity ε σ) q)).re) =
      -2 * ν * PancakeViscousMisalignmentAbsorption.fullEnergy support
        (fourierCurl (velocity ε σ)) := by
  have hn : ∀ k ∈ support, frequencyVec k ≠ 0 :=
    fun k hk ↦ frequencyVec_ne_zero (support_nonzero k hk)
  have ht : ∀ k ∈ support, modeDot k (velocity ε σ k) = 0 :=
    fun k _ ↦ velocity_transverse ε σ k
  have hr : ∀ k, velocity ε σ (-k) = coefficientConjugate (velocity ε σ k) :=
    velocity_reality ε σ
  have hh : ∀ q, infiniteVelocityRHS ν (velocity ε σ) q =
      velocityRHS support (velocity ε σ) ν q :=
    infiniteVelocityRHS_eq_finite support _ (velocity_supported ε σ) hn ht ν
  simp only [hh]
  exact velocityRHS_energy_balance support _ ν support_symmetric hr ht

/-- Physical unit-torus energy rate, including viscosity and the exact
positive `2π` nonlinear normalization. -/
theorem actual_parent_energy_rate (ε σ ν : ℝ) :
    2 * (∑ q ∈ parentPair, (coefficientHermitian (velocity ε σ q)
      (infiniteVelocityRHS ν (velocity ε σ) q)).re) =
      8 / 5 * Real.pi * σ * ε ^ 2 - 4 * ν * Real.pi ^ 2 := by
  unfold parentPair
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    actual_source, actual_source, parent_source, negative_parent_source]
  norm_num [velocity, pv, parentP, coefficientHermitian,
    unitTorusViscousVorticityCoeff, unitTorusDerivativePhase, modeSquare,
    Fin.sum_univ_three, Matrix.cons_val_two, ite_apply,
    funext_iff, Fin.forall_fin_succ, Complex.mul_re, Complex.mul_im, pow_two]
  ring

/-- For the period-`2π` viscosity `1/100`, rescaling to the unit torus
gives viscosity `1/(200π)`. The receiving energy strictly increases. -/
theorem forward_parent_rate :
    2 * (∑ q ∈ parentPair, (coefficientHermitian (velocity (1 / 5) 1 q)
      (infiniteVelocityRHS (1 / (200 * Real.pi)) (velocity (1 / 5) 1) q)).re) =
      11 * Real.pi / 250 := by
  rw [actual_parent_energy_rate]
  field_simp [Real.pi_ne_zero]
  ring

theorem reversed_parent_rate :
    2 * (∑ q ∈ parentPair, (coefficientHermitian (velocity (1 / 5) (-1) q)
      (infiniteVelocityRHS (1 / (200 * Real.pi)) (velocity (1 / 5) (-1)) q)).re) =
      -21 * Real.pi / 250 := by
  rw [actual_parent_energy_rate]
  field_simp [Real.pi_ne_zero]
  ring

theorem phase_changes_receiving_growth :
    0 < 2 * (∑ q ∈ parentPair, (coefficientHermitian (velocity (1 / 5) 1 q)
      (infiniteVelocityRHS (1 / (200 * Real.pi)) (velocity (1 / 5) 1) q)).re) ∧
    2 * (∑ q ∈ parentPair, (coefficientHermitian (velocity (1 / 5) (-1) q)
      (infiniteVelocityRHS (1 / (200 * Real.pi)) (velocity (1 / 5) (-1)) q)).re) < 0 := by
  rw [forward_parent_rate, reversed_parent_rate]
  constructor <;> nlinarith [Real.pi_pos]

/-- Any differentiable coefficient path obeying the actual NS equation at
this datum inherits the physical receiving-pair energy rate. This is a
derivative consumer, not an existence theorem for such paths. -/
theorem hasDerivAt_parent_energy (ε σ ν t : ℝ) (u : ℝ → FourierVelocity)
    (hi : u t = velocity ε σ)
    (he : ∀ q ∈ parentPair, ∀ i,
      HasDerivAt (fun s ↦ u s q i) (infiniteVelocityRHS ν (u t) q i) t) :
    HasDerivAt (fun s ↦ fourierEnergy parentPair (u s))
      (8 / 5 * Real.pi * σ * ε ^ 2 - 4 * ν * Real.pi ^ 2) t := by
  have h := HasDerivAt.fun_sum (fun q hq ↦ hasDerivAt_coefficientEnergy
    (fun s ↦ u s q) (infiniteVelocityRHS ν (u t) q) t (he q hq))
  have hh : HasDerivAt (fun s ↦ fourierEnergy parentPair (u s))
      (2 * ∑ q ∈ parentPair, (coefficientHermitian (u t q)
        (infiniteVelocityRHS ν (u t) q)).re) t := by
    simpa only [fourierEnergy, Finset.mul_sum] using h
  rw [hi, actual_parent_energy_rate] at hh
  exact hh

end Mettapedia.FluidDynamics.NavierStokes.CellularParentRenewal
