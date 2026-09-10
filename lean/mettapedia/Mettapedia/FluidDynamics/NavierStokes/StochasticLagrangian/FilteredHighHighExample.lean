import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFilteredEquation

/-!
# A real, transverse high-high interaction feeding a retained mode

The retained velocity is zero, but the projected nonlinear forcing of its
unit-frequency mode is nonzero. The four input modes have squared lengths
five and two. Thus neither zero mean nor exact removal of the input modes
by a static filter justifies discarding their quadratic feedback.

This is an instantaneous finite Fourier example, not a blowup solution or
a counterexample to unforced global regularity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredHighHighExample

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeCoefficientLimitEquation PancakeSobolevFiberEnvelope
open PancakeFilteredStrainDynamics InfiniteFilteredEquation
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
open PancakeIncomingLowSourceEnergy

def output : Wavevector := ![1, 0, 0]
def firstInput : Wavevector := ![2, 1, 0]
def secondInput : Wavevector := ![-1, -1, 0]
def firstAmplitude : VelocityCoefficient := ![1, -2, 0]
def secondAmplitude : VelocityCoefficient := ![0, 0, 1]

def inputModes : Finset Wavevector := {firstInput, -firstInput, secondInput, -secondInput}
def retainedModes : Finset Wavevector := {output, -output}

def velocity (k : Wavevector) : VelocityCoefficient :=
  if k = firstInput ∨ k = -firstInput then firstAmplitude
  else if k = secondInput ∨ k = -secondInput then secondAmplitude else 0

theorem velocity_support (k : Wavevector) (hk : k ∉ inputModes) : velocity k = 0 := by
  simp only [inputModes, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  simp [velocity, hk]

theorem velocity_transverse (k : Wavevector) : modeDot k (velocity k) = 0 := by
  unfold velocity
  split_ifs with h h
  · rcases h with rfl | rfl <;>
      norm_num [modeDot, firstInput, firstAmplitude, Fin.sum_univ_succ]
  · rcases h with rfl | rfl <;>
      norm_num [modeDot, secondInput, secondAmplitude, Fin.sum_univ_succ]
  · simp [modeDot]

theorem velocity_reality (k : Wavevector) : velocity (-k) = coefficientConjugate (velocity k) := by
  have hf : (-k = firstInput ∨ -k = -firstInput) ↔ (k = firstInput ∨ k = -firstInput) := by
    simp [neg_eq_iff_eq_neg, or_comm]
  have hs : (-k = secondInput ∨ -k = -secondInput) ↔
      (k = secondInput ∨ k = -secondInput) := by
    simp [neg_eq_iff_eq_neg, or_comm]
  simp only [velocity, hf, hs]
  split_ifs <;> ext i <;> fin_cases i <;>
    norm_num [coefficientConjugate, firstAmplitude, secondAmplitude, map_ofNat]

theorem velocity_zero : velocity 0 = 0 := by
  norm_num [velocity, firstInput, secondInput, funext_iff, Fin.forall_fin_succ]

theorem filtered_velocity_zero : filteredVelocity (sharpFilter retainedModes) velocity = 0 := by
  funext k
  by_cases hk : k ∈ retainedModes
  · simp only [retainedModes, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;>
      norm_num [filteredVelocity, velocity, output, firstInput, secondInput,
        funext_iff, Fin.forall_fin_succ]
  · simp [filteredVelocity, sharpFilter, hk]

theorem infiniteConvection_output : infiniteConvection velocity output = secondAmplitude := by
  have hfin : infiniteConvection velocity output =
      convectionConvolution inputModes velocity output := by
    ext i
    exact PancakeConvectionFiberIdentity.tsum_outputFiber_eq_convectionConvolution
      inputModes velocity velocity_support (fun k _ ↦ velocity_transverse k) output i
  rw [hfin]
  ext i
  fin_cases i <;>
    norm_num [convectionConvolution, inputModes, orderedConvection, velocity, output,
      firstInput, secondInput, firstAmplitude, secondAmplitude, modeDot,
      Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ, Matrix.cons_val_two]

theorem input_frequencies : modeSquare firstInput = 5 ∧ modeSquare secondInput = 2 ∧
    modeSquare output = 1 := by
  norm_num [modeSquare, firstInput, secondInput, output, Fin.sum_univ_succ]

theorem summable_outputFiber (q : Wavevector) (i : Fin 3) :
    Summable (fun k ↦ outputFiber q velocity k i) :=
  summable_of_ne_finset_zero (s := inputModes)
    (fun k hk ↦ by simp [outputFiber, velocity_support k hk, modeDot])

theorem subgridConvection_output :
    InfiniteFilteredEquation.subgridConvection (sharpFilter retainedModes) velocity output =
      secondAmplitude := by
  have h := filtered_infiniteConvection (sharpFilter retainedModes) velocity 1
    (norm_sharpFilter_le_one retainedModes) output (summable_outputFiber output)
  have hc : infiniteConvection 0 output = 0 := by
    ext i
    simp [infiniteConvection, outputFiber, modeDot]
  rw [filtered_velocity_zero, hc, zero_add, infiniteConvection_output] at h
  simpa [sharpFilter, retainedModes] using h.symm

/-- Pressure projection does not eliminate this feedback. -/
theorem subgridForce_output :
    subgridForce (sharpFilter retainedModes) velocity output =
      (-unitTorusDerivativePhase) • secondAmplitude := by
  rw [subgridForce, subgridConvection_output]
  ext i
  fin_cases i <;>
    norm_num [lerayMode, modeSquare, modeDot, output, secondAmplitude, Fin.sum_univ_succ]

theorem subgridForce_output_ne_zero :
    subgridForce (sharpFilter retainedModes) velocity output ≠ 0 := by
  intro h
  rw [subgridForce_output] at h
  have hz := congrFun h 2
  have hp : unitTorusDerivativePhase = 0 := by
    simpa [secondAmplitude, Matrix.cons_val_two] using hz
  have hn := norm_derivativePhase
  rw [hp, norm_zero] at hn
  nlinarith [Real.pi_pos]

/-- A single checked witness rules out autonomous evolution after filtering:
zero resolved velocity does not imply zero resolved nonlinear forcing. -/
theorem exists_nonzero_feedback_from_unresolved_velocity :
    ∃ u : FourierVelocity,
      (∀ k, u (-k) = coefficientConjugate (u k)) ∧
      (∀ k, modeDot k (u k) = 0) ∧ u 0 = 0 ∧
      filteredVelocity (sharpFilter retainedModes) u = 0 ∧
      subgridForce (sharpFilter retainedModes) u output ≠ 0 :=
  ⟨velocity, velocity_reality, velocity_transverse, velocity_zero,
    filtered_velocity_zero, subgridForce_output_ne_zero⟩

end Mettapedia.FluidDynamics.NavierStokes.FilteredHighHighExample
