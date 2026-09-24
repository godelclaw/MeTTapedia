import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInteractionTruncationTail
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeDiscardedNonlinearLimit

/-!
# Exhaustion with the zero mode excluded

For mean-zero velocity, a curl interaction vanishes when either input or
its output is zero. Removing those identically zero terms from the
majorant makes the consistency estimate compatible with retained sets
that omit zero. No zero-frequency tail is left artificially unpaid.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeZeroSafeInteractionTail

open Filter
open scoped Topology
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeFrequencyProjectorCommutator PancakeCurlOutputTail
open PancakeZeroModeCurlBridge PancakeDiscardedNonlinearLimit PancakeInteractionTruncationTail
open PancakeGalerkinKineticEnergy

def nonzeroMajorant (H : Wavevector × Wavevector → ℝ) (p : Wavevector × Wavevector) : ℝ :=
  if p.1 = 0 ∨ p.2 = 0 ∨ p.1 + p.2 = 0 then 0 else H p

theorem nonzeroMajorant_nonneg (H : Wavevector × Wavevector → ℝ) (hH : ∀ p, 0 ≤ H p)
    (p : Wavevector × Wavevector) : 0 ≤ nonzeroMajorant H p := by
  unfold nonzeroMajorant
  split_ifs <;> simp_all

theorem summable_nonzeroMajorant (H : Wavevector × Wavevector → ℝ)
    (hH : ∀ p, 0 ≤ H p) (hSum : Summable H) : Summable (nonzeroMajorant H) := by
  apply hSum.of_norm_bounded
  intro p
  unfold nonzeroMajorant
  split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hH p), hH p]

theorem interactionTail_erase_zero (H : Wavevector × Wavevector → ℝ) (M : Finset Wavevector) :
    interactionTail (nonzeroMajorant H) (M.erase 0) = interactionTail (nonzeroMajorant H) M := by
  apply tsum_congr
  intro p
  by_cases hk : p.1 = 0 <;> by_cases hl : p.2 = 0 <;> by_cases hq : p.1 + p.2 = 0 <;>
    simp [nonzeroMajorant, mem_retainedPairs, Finset.mem_erase, hk, hl, hq]

theorem tendsto_interactionTail_erase_zero (H : Wavevector × Wavevector → ℝ)
    (hH : ∀ p, 0 ≤ H p) (hSum : Summable H) :
    Tendsto (fun M : Finset Wavevector ↦ interactionTail (nonzeroMajorant H) (M.erase 0)) atTop (𝓝 0) := by
  simp_rw [interactionTail_erase_zero]
  exact tendsto_interactionTail _ (nonzeroMajorant_nonneg H hH) (summable_nonzeroMajorant H hH hSum)

theorem curlPair_zero_of_zero_frequency (u : FourierVelocity) (hzero : u 0 = 0)
    (p : Wavevector × Wavevector) (hp : p.1 = 0 ∨ p.2 = 0 ∨ p.1 + p.2 = 0) :
    curlPair u (fourierCurl u) p = 0 := by
  rcases hp with hk | hl | hq
  · simp [curlPair, hk, hzero, coefficientCross]
  · simp [curlPair, hl, fourierCurl_zero, coefficientCross]
  · unfold curlPair
    rw [hq]
    simp [wavevectorCoefficient, coefficientCross]

theorem norm_velocityCurlPair_le_nonzeroMajorant (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (u : FourierVelocity) (hzero : u 0 = 0) (hu : ∀ k, fourierMoment 2 u k ≤ g k)
    (p : Wavevector × Wavevector) :
    ‖coefficientVec (curlPair u (fourierCurl u) p)‖ ≤ nonzeroMajorant (velocityCurlMajorant g) p := by
  unfold nonzeroMajorant
  split_ifs with hp
  · rw [curlPair_zero_of_zero_frequency u hzero p hp]
    simp [coefficientVec]
  · exact norm_velocityCurlPair_le_envelope g hg u hu p

end Mettapedia.FluidDynamics.NavierStokes.PancakeZeroSafeInteractionTail
