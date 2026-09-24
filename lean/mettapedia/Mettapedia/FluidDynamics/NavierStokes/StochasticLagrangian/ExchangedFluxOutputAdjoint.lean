import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicTensorFourierFrame
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxAdjointGeometry

/-!
# Frequency-resolved bounds for the actual coefficient adjoints

The nonlinear slots act on the Fourier output coefficient of the test,
not on its global norm. Vectorization supplies a Hilbert coefficient
space; its finite-dimensional constants are independent of frequencies.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxOutputAdjoint

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy
open PeriodicGradientFluxTriple ExchangedFluxModeDynamics ExchangedFluxModeEnvelope
open ExchangedFluxAdjoint ExchangedFluxAdjointGeometry PeriodicTensorFourierFrame

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "H" => Mettapedia.Analysis.UnitTorusGradientProjection.TensorL2
  (Fin 3) (EuclideanSpace ℝ (Fin 3))
local notation "Tensor" => Fin 3 → VelocityCoefficient

def tensorToVecCLM : Tensor →L[ℂ] TensorCoefficientSpace :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 × Fin 3 ↦ ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun p ↦
      (ContinuousLinearMap.proj p.2 : VelocityCoefficient →L[ℂ] ℂ).comp
        (ContinuousLinearMap.proj p.1 : Tensor →L[ℂ] VelocityCoefficient)))

theorem tensorOfVec_tensorToVec (a : Tensor) : tensorOfVecCLM (tensorToVecCLM a) = a := by
  ext j i
  rfl

theorem norm_tensorToVec_le (a : Tensor) : ‖tensorToVecCLM a‖ ≤ 3 * ‖a‖ := by
  have h : ‖tensorToVecCLM a‖ ^ 2 ≤ 9 * ‖a‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _p : Fin 3 × Fin 3, ‖a‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm (a p.1) p.2).trans
          (norm_le_pi_norm a p.1)) 2
      _ = _ := by norm_num
  nlinarith [norm_nonneg (tensorToVecCLM a), norm_nonneg a]

def outerVectorSlot (u : FourierVelocity) (p : TripleIndex) : C3 →L[ℝ] TensorCoefficientSpace :=
  (tensorToVecCLM.comp (outerTensorCLM u p)).restrictScalars ℝ

def leftVectorSlot (u : FourierVelocity) (p : TripleIndex) : C3 →L[ℝ] TensorCoefficientSpace :=
  (tensorToVecCLM.comp (leftTensorCLM u p)).restrictScalars ℝ

theorem outerSlot_eq_synthesis_comp (u : FourierVelocity) (p : TripleIndex) :
    outerSlot u p = (synthesis (tripleFrequency p)).comp (outerVectorSlot u p) := by
  apply ContinuousLinearMap.ext
  intro a
  change tensorModeCLM (tripleFrequency p) ((outerTensorCLM u p) a) =
    tensorModeCLM (tripleFrequency p) (tensorOfVecCLM (tensorToVecCLM ((outerTensorCLM u p) a)))
  rw [tensorOfVec_tensorToVec]

theorem leftSlot_eq_synthesis_comp (u : FourierVelocity) (p : TripleIndex) :
    leftSlot u p = (synthesis (tripleFrequency p)).comp (leftVectorSlot u p) := by
  apply ContinuousLinearMap.ext
  intro a
  change tensorModeCLM (tripleFrequency p) ((leftTensorCLM u p) a) =
    tensorModeCLM (tripleFrequency p) (tensorOfVecCLM (tensorToVecCLM ((leftTensorCLM u p) a)))
  rw [tensorOfVec_tensorToVec]

theorem outerTest_eq_outputCoefficient (u : FourierVelocity) (F : H) (p : TripleIndex) :
    outerTest u F p = (outerVectorSlot u p).adjoint (outputCoefficient F (tripleFrequency p)) := by
  rw [outerTest, outerSlot_eq_synthesis_comp, ContinuousLinearMap.adjoint_comp]
  rfl

theorem leftTest_eq_outputCoefficient (u : FourierVelocity) (F : H) (p : TripleIndex) :
    leftTest u F p = (leftVectorSlot u p).adjoint (outputCoefficient F (tripleFrequency p)) := by
  rw [leftTest, leftSlot_eq_synthesis_comp, ContinuousLinearMap.adjoint_comp]
  rfl

theorem norm_outerVectorSlot_le (u : FourierVelocity) (p : TripleIndex) :
    ‖outerVectorSlot u p‖ ≤ (3 / 2 : ℝ) * ‖curlCoefficientCLM p.1‖ *
      ‖differenceCLM p (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2))‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun a ↦ ?_)
  have h : ‖outerTensorCLM u p a‖ ≤ (1 / 2 : ℝ) * (‖curlCoefficientCLM p.1‖ * ‖a‖) *
      ‖differenceCLM p (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2))‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    change ‖(1 / 2 : ℂ) • (((curlCoefficientCLM p.1) a j) •
      differenceCLM p (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2)))‖ ≤ _
    simp only [norm_smul]
    norm_num
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right ((norm_le_pi_norm _ _).trans
        ((curlCoefficientCLM p.1).le_opNorm a)) (norm_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq (by ring)
  exact (norm_tensorToVec_le ((outerTensorCLM u p) a)).trans
    ((mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by ring))

theorem norm_leftVectorSlot_le (u : FourierVelocity) (p : TripleIndex) :
    ‖leftVectorSlot u p‖ ≤ 3 * (‖differenceCLM p‖ * ‖curlCoefficientCLM p.2.1‖) *
      ‖fourierCurl u p.1‖ * ‖fourierCurl u p.2.2‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun a ↦ ?_)
  have hc : ‖coefficientCross ((curlCoefficientCLM p.2.1) a) (fourierCurl u p.2.2)‖ ≤
      2 * (‖curlCoefficientCLM p.2.1‖ * ‖a‖) * ‖fourierCurl u p.2.2‖ := by
    exact (norm_coefficientCross_le _ _).trans (by gcongr; exact (curlCoefficientCLM p.2.1).le_opNorm a)
  have hd := ((differenceCLM p).le_opNorm _).trans (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
  have h : ‖leftTensorCLM u p a‖ ≤ (‖differenceCLM p‖ * ‖curlCoefficientCLM p.2.1‖) *
      ‖fourierCurl u p.1‖ * ‖fourierCurl u p.2.2‖ * ‖a‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    change ‖((1 / 2 : ℂ) * fourierCurl u p.1 j) •
      differenceCLM p (coefficientCross ((curlCoefficientCLM p.2.1) a) (fourierCurl u p.2.2))‖ ≤ _
    simp only [norm_smul, norm_mul]
    norm_num
    calc
      _ ≤ ((1 / 2 : ℝ) * ‖fourierCurl u p.1‖) *
          (‖differenceCLM p‖ * (2 * (‖curlCoefficientCLM p.2.1‖ * ‖a‖) * ‖fourierCurl u p.2.2‖)) := by
        gcongr
        · exact norm_le_pi_norm _ _
      _ = _ := by ring
  exact (norm_tensorToVec_le ((leftTensorCLM u p) a)).trans
    ((mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by ring))

theorem norm_outerTest_le_output (u : FourierVelocity) (F : H) (p : TripleIndex) :
    ‖outerTest u F p‖ ≤ ((3 / 2 : ℝ) * ‖curlCoefficientCLM p.1‖ *
      ‖differenceCLM p (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2))‖) *
      ‖outputCoefficient F (tripleFrequency p)‖ := by
  rw [outerTest_eq_outputCoefficient]
  have h := ((outerVectorSlot u p).adjoint).le_opNorm (outputCoefficient F (tripleFrequency p))
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans (mul_le_mul_of_nonneg_right (norm_outerVectorSlot_le u p) (norm_nonneg _))

theorem norm_leftTest_le_output (u : FourierVelocity) (F : H) (p : TripleIndex) :
    ‖leftTest u F p‖ ≤ (3 * (‖differenceCLM p‖ * ‖curlCoefficientCLM p.2.1‖) *
      ‖fourierCurl u p.1‖ * ‖fourierCurl u p.2.2‖) * ‖outputCoefficient F (tripleFrequency p)‖ := by
  rw [leftTest_eq_outputCoefficient]
  have h := ((leftVectorSlot u p).adjoint).le_opNorm (outputCoefficient F (tripleFrequency p))
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans (mul_le_mul_of_nonneg_right (norm_leftVectorSlot_le u p) (norm_nonneg _))

/-- The pair-frequency derivative gain survives the output-frequency resolution. -/
theorem norm_leftTest_le_pair_output (u : FourierVelocity) (F : H) (p : TripleIndex)
    (hl : p.2.1 ≠ 0) (hm : p.2.2 ≠ 0) :
    ‖leftTest u F p‖ ≤ (36 * (2 * Real.pi) * ‖frequencyVec (p.2.1 + p.2.2)‖ *
      ‖fourierCurl u p.1‖ * ‖fourierCurl u p.2.2‖) * ‖outputCoefficient F (tripleFrequency p)‖ := by
  apply (norm_leftTest_le_output u F p).trans
  have h := mul_le_mul_of_nonneg_left (norm_difference_mul_curl_le_pair_frequency p hl hm)
    (by norm_num : (0 : ℝ) ≤ 3)
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)).trans_eq (by ring)

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxOutputAdjoint
