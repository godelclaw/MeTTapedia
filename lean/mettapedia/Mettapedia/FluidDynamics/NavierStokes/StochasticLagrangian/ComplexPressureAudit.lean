import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PhysicalPressurePair
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierLocalizationDivergence
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressurePairOutputStability

/-! Regression tests for phases, cancellation, and actual cutoff divergence. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ComplexPressureAudit

open scoped BigOperators RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeFiniteFourierLocalization
open FourierPressureCommutator FourierPressureTraceSymbol PressureTiltSymbol
open ComplexTransverseMatrix ComplexPressurePair ComplexPressureMisalignment
open FourierLocalizationDivergence FourierResolventSmoothing FourierEllipticProductEnergy

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)

@[simp] private theorem vector_last {α : Type*} (a b c : α) : ![a, b, c] (2 : Fin 3) = c := rfl

@[simp] private theorem patch_frequency_add :
    (![0, 0, 1] : Wavevector) + ![1, 0, 0] = ![1, 0, 1] := by
  ext i
  fin_cases i <;> rfl

@[simp] private theorem patch_fiber :
    ({(![0, 0, 1], ![1, 0, 0])} : Finset (Wavevector × Wavevector)).filter
      (fun pk ↦ pk.1 + pk.2 = ![1, 0, 1]) = {(![0, 0, 1], ![1, 0, 0])} := by
  apply Finset.filter_eq_self.mpr
  intro pk hpk
  simp only [Finset.mem_singleton] at hpk
  subst pk
  exact patch_frequency_add

example (e : R3) (k : Wavevector) (w v : VelocityCoefficient) : tiltPair e k (-k) w v = 0 := by
  have hz : realFrequency (0 : Wavevector) = 0 := by ext i; simp [realFrequency]
  simp [tiltPair, complexTiltSymbol, hz, tiltSymbol_zero, complexifyVector, coefficientVec]
  exact Or.inr rfl

example (e : R3) (p : Wavevector) (w v : VelocityCoefficient) : tiltPair e 0 p w v = 0 := by
  simp [tiltPair, tracePair, complexBiotSavartAmp, modeDot, modeSquare]

/-- Two imaginary input phases reverse the pressure-pair sign. -/
example (e : R3) (k p : Wavevector) (w v : VelocityCoefficient) :
    tiltPair e k p (Complex.I • w) (Complex.I • v) = -tiltPair e k p w v := by
  rw [tiltPair_smul_left, tiltPair_smul_right, smul_smul, Complex.I_mul_I, neg_one_smul]

/-- A non-real amplitude is preserved, not replaced by its real part. -/
example : tracePair ![1, 0, 1] ![-1, 1, 0]
    (Complex.I • ![-1, 0, 1]) ![0, 0, 1] = -Complex.I / 2 := by
  norm_num [tracePair, complexBiotSavartAmp, modeDot, modeSquare, coefficientCross,
    wavevectorCoefficient, Fin.sum_univ_three]
  ring

/-- An aligned transverse input becomes longitudinal after a genuine scalar cutoff. -/
example :
    modeDot (![1, 0, 0] : Wavevector) (![0, 0, Complex.I] : VelocityCoefficient) = 0 ∧
    modeDot (![1, 0, 1] : Wavevector)
      (finiteCutoffConvolutionCoeff {![0, 0, 1]} {![1, 0, 0]}
        (fun _ ↦ 1) (fun _ ↦ ![0, 0, Complex.I]) ![1, 0, 1]) = Complex.I := by
  norm_num [finiteCutoffConvolutionCoeff, modeDot, Fin.sum_univ_three]

/-- The fixed-line projection detects no transverse error in that same input. -/
example : transverse (WithLp.toLp 2 ![0, 0, 1] : R3)
    (coefficientVec ![0, 0, Complex.I]) = 0 := by
  ext i
  fin_cases i <;> simp [transverse, pairing, complexifyVector, coefficientVec, Fin.sum_univ_three]

/-- The derivative-energy bound is attained by a one-mode cutoff and field. -/
example :
    (∑ q ∈ finiteCutoffOutputModes {![0, 0, 1]} {![1, 0, 0]},
      ‖modeDot q (finiteCutoffConvolutionCoeff {![0, 0, 1]} {![1, 0, 0]}
        (fun _ ↦ 1) (fun _ ↦ ![0, 0, (1 : ℂ)]) q)‖ ^ 2) =
      coordinateEnergy {![0, 0, 1]} (fun _ ↦ (1 : ℂ)) := by
  norm_num [finiteCutoffOutputModes, finiteCutoffConvolutionCoeff, coordinateEnergy_eq,
    modeDot, realFrequency, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

end Mettapedia.FluidDynamics.NavierStokes.ComplexPressureAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairOutputStability.tracePair_eq_output_dots
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairOutputStability.norm_tracePair_mul_frequencies_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairOutputStability.norm_tracePair_mul_frequency_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairOutputStability.norm_complexTiltSymbol_sub_mul_frequency_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairOutputStability.norm_output_symbol_change_mul_frequency_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressurePair.norm_realCoefficient
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressurePair.norm_frequencyVec_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressurePair.modeSquare_eq_real
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressurePair.modeDot_realCoefficient
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressurePair.coefficientCross_realCoefficient
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressurePair.tracePair_real
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressurePair.tiltPair_real
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressurePair.norm_tiltPair_coherent_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressurePair.norm_tracePair_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressurePair.norm_tiltPair_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressurePair.physical_tracePair_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierLocalizationDivergence.modeDot_finiteCutoffConvolutionCoeff
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierLocalizationDivergence.modeDot_localized_of_divergenceFree
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierLocalizationDivergence.transverse_localized
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierLocalizationDivergence.sum_norm_divergence_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierLocalizationDivergence.sum_normalized_divergence_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressureConvolution.localizationDefect_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressureConvolution.sum_norm_pairConvolution_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressureConvolution.localizationDefect_eq_of_divergenceFree
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressureConvolution.summable_tracePair
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressurePair.tracePair_fourierCurl
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressurePair.pressureHessian_trace_eq_pairSum
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressurePair.pressureHessian_tilt_eq_pairConvolution
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressurePair.sum_pressureHessian_tilt_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressurePair.modeDot_infiniteConvection
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressurePair.traceAmplitude_eq_tsum_pairs
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressurePair.traceAmplitude_eq_tsum_pairs_of_moment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressurePair.summable_norm_fourierCurl
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressurePair.tiltCoefficient_eq_tsum_pairs
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressureMisalignment.coefficient_decomposition
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressureMisalignment.modeDot_transverseCoefficient
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressureMisalignment.longitudinal_mul_amplitude_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressureMisalignment.tiltPair_add_left
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressureMisalignment.tiltPair_add_right
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressureMisalignment.tiltPair_smul_left
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressureMisalignment.tiltPair_smul_right
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressureMisalignment.tiltPair_decomposition
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressureMisalignment.norm_tiltPair_le_misalignment_add_divergence
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexPressureMisalignment.norm_tiltPair_le_misalignment
