import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ComplexPressureMisalignment
import Mettapedia.Analysis.FiniteTwoChannelConvolutionEnergy

/-! # Complex pressure convolution with both localization error channels -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ComplexPressureConvolution

open scoped BigOperators
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator ComplexTransverseMatrix
open ComplexPressurePair ComplexPressureMisalignment
open Mettapedia.Analysis.FiniteConvolutionEnergy

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)

def pairConvolution (e : R3) (P K : Finset Wavevector) (w v : FourierVelocity) (q : Wavevector) : C3 :=
  ∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, tiltPair e pk.1 pk.2 (w pk.1) (v pk.2)

def localizationDefect (e : R3) (k : Wavevector) (w : VelocityCoefficient) : ℝ :=
  ‖transverse e (coefficientVec w)‖ + ‖modeDot k w‖ / (2 * ‖frequencyVec k‖)

theorem localizationDefect_nonneg (e : R3) (k : Wavevector) (w : VelocityCoefficient) :
    0 ≤ localizationDefect e k w := by unfold localizationDefect; positivity

theorem sum_norm_pairConvolution_sq_le (e : R3) (he : ‖e‖ = 1)
    (P K Q : Finset Wavevector) (w v : FourierVelocity)
    (hQ : ∀ p ∈ P, ∀ k ∈ K, p + k ∈ Q) :
    (∑ q ∈ Q, ‖pairConvolution e P K w v q‖ ^ 2) ≤
      8 * (∑ p ∈ P, localizationDefect e p (w p)) ^ 2 * (∑ k ∈ K, ‖coefficientVec (v k)‖ ^ 2) +
        8 * (∑ p ∈ P, ‖coefficientVec (w p)‖) ^ 2 * (∑ k ∈ K, localizationDefect e k (v k) ^ 2) := by
  have h := sum_norm_sq_le_two_channels P K Q
    (fun p ↦ 2 * localizationDefect e p (w p)) (fun p ↦ 2 * ‖coefficientVec (w p)‖)
    (fun k ↦ ‖coefficientVec (v k)‖) (fun k ↦ localizationDefect e k (v k))
    (fun p k ↦ tiltPair e p k (w p) (v k))
    (fun p _ ↦ mul_nonneg (by norm_num) (localizationDefect_nonneg e p (w p)))
    (fun _ _ ↦ by positivity) (fun _ _ ↦ norm_nonneg _)
    (fun k _ ↦ localizationDefect_nonneg e k (v k))
    (fun p _ k _ ↦ by
      have h := norm_tiltPair_le_misalignment_add_divergence e he p k (w p) (v k)
      unfold localizationDefect
      simp only [div_eq_mul_inv, mul_inv_rev] at h ⊢
      norm_num only at h ⊢
      nlinarith only [h]) hQ
  simp only [← Finset.mul_sum] at h
  unfold pairConvolution
  nlinarith only [h]

theorem localizationDefect_eq_of_divergenceFree (e : R3) (k : Wavevector) (w : VelocityCoefficient)
    (hw : modeDot k w = 0) : localizationDefect e k w = ‖transverse e (coefficientVec w)‖ := by
  simp [localizationDefect, hw]

theorem summable_tracePair (w v : FourierVelocity)
    (hw : Summable (fun k ↦ ‖coefficientVec (w k)‖))
    (hv : Summable (fun k ↦ ‖coefficientVec (v k)‖)) (q : Wavevector) :
    Summable (fun k ↦ tracePair k (q - k) (w k) (v (q - k))) := by
  apply (hw.mul_right (∑' p, ‖coefficientVec (v p)‖)).of_norm_bounded
  intro k
  exact (norm_tracePair_le k (q - k) (w k) (v (q - k))).trans
    (mul_le_mul_of_nonneg_left (hv.le_tsum (q - k) (fun _ _ ↦ norm_nonneg _)) (norm_nonneg _))

end Mettapedia.FluidDynamics.NavierStokes.ComplexPressureConvolution
