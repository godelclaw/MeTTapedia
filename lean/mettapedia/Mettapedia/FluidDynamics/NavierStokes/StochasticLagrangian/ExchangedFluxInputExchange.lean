import Mettapedia.Analysis.BalancedResolventStability
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxSevenInputExpansion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicTensorFourierWeight

/-!
# High-input exchange with the actual coefficient mismatch retained

Exchanging a convection input and a variation input preserves the output
frequency and total heat damping. If their sum is small, the two kernel
shifts nearly cancel. The complete convection/curl/flux tests remain
distinct; no favorable sign or smallness of their difference is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxInputExchange

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PeriodicGradientFluxTriple
open PancakeSobolevFiberEnvelope PancakePeriodicVorticityEquation
open FourierVorticityPairDynamics FourierStretchingInteractionDynamics
open FourierHeatFlow FourierHeatCommutatorKernel FourierHeatCommutatorEnergy FourierHeatCommutatorReflection
open ExchangedFluxModeDynamics ExchangedFluxAdjoint ExchangedFluxSevenInputHeat
open PeriodicTensorFourierWeight

def outputFrequency (k l m n : Wavevector) : Wavevector := k + l + m + n

theorem outputFrequency_exchange (k l m n : Wavevector) :
    outputFrequency k l m n = outputFrequency k m l n := by unfold outputFrequency; abel

/-- Actual real Fourier modes can interact only at equal or opposite total outputs. -/
theorem interactionTest_eq_zero (inner : Bool) (u : FourierVelocity)
    (k l m n : Wavevector) (p : TripleIndex)
    (hp : outputFrequency k l m n ≠ tripleFrequency p)
    (hn : outputFrequency k l m n ≠ -tripleFrequency p) :
    interactionTest inner u k l m n p = 0 := by
  have ho : tripleFrequency (k + l, (m, n)) = outputFrequency k l m n := by
    simp [tripleFrequency, outputFrequency, add_assoc]
  have hi : tripleFrequency (m, (k + l, n)) = outputFrequency k l m n := by
    simp [tripleFrequency, outputFrequency, add_comm, add_left_comm]
  cases inner
  · change ⟪tensorModeCLM _ _, tensorModeCLM _ _⟫ = 0
    exact inner_tensorMode_eq_zero _ _ _ _ (ho ▸ hp) (ho ▸ hn)
  · change ⟪tensorModeCLM _ _, tensorModeCLM _ _⟫ = 0
    exact inner_tensorMode_eq_zero _ _ _ _ (hi ▸ hp) (hi ▸ hn)

theorem outputShift_add_right (ν : ℝ) (k l m : Wavevector) :
    outputShift ν k l + outputShift ν k m = outputShift ν k (l + m) := by
  simp only [outputShift, rateDefect_eq_frequency_contraction, Pi.add_apply, Int.cast_add,
    mul_add, Finset.sum_add_distrib]
  ring

theorem norm_high_pair_le (k l m n : Wavevector) :
    ‖frequencyVec (l + m)‖ ≤
      ‖frequencyVec (outputFrequency k l m n)‖ + ‖frequencyVec k‖ + ‖frequencyVec n‖ := by
  have he : l + m = outputFrequency k l m n - k - n := by unfold outputFrequency; abel
  rw [he, frequencyVec_sub, frequencyVec_sub]
  exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)

theorem abs_shift_sum_le {ν : ℝ} (hν : 0 ≤ ν) (k l m n : Wavevector) :
    |outputShift ν k l + outputShift ν k m| ≤
      (2 * ν * (2 * Real.pi) ^ 2 * ‖frequencyVec k‖) *
        (‖frequencyVec (outputFrequency k l m n)‖ + ‖frequencyVec k‖ + ‖frequencyVec n‖) := by
  rw [outputShift_add_right, outputShift, abs_neg]
  exact (abs_rateDefect_le hν k (l + m)).trans
    (mul_le_mul_of_nonneg_left (norm_high_pair_le k l m n) (by positivity))

theorem modeDot_add_frequency (k l : Wavevector) (v : VelocityCoefficient) :
    modeDot (k + l) v = modeDot k v + modeDot l v := by
  simp only [modeDot, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

/-- Incompressibility makes the two transport factors nearly opposite, not equal. -/
theorem transportFactor_exchange (u : FourierVelocity) (k l m n : Wavevector)
    (hk : modeDot k (u k) = 0) :
    modeDot (k + l) (u k) + modeDot (k + m) (u k) =
      modeDot (outputFrequency k l m n - n) (u k) := by
  have he : outputFrequency k l m n - n = k + l + m := by unfold outputFrequency; abel
  rw [he]
  simp only [modeDot_add_frequency, hk, zero_add]

theorem convectionAtom_eq_transportFactor (u : FourierVelocity) (k l : Wavevector) :
    convectionAtom u k l = modeDot (k + l) (u k) •
      lerayMode (k + l) ((-unitTorusDerivativePhase) • u l) := by
  unfold convectionAtom outputFiber
  rw [add_sub_cancel_left]
  change lerayMode (k + l) ((-unitTorusDerivativePhase) •
    (modeDot (k + l) (u k) • u l)) = _
  rw [smul_comm]
  exact (lerayLinear (k + l)).map_smul _ _

/-- The complete coefficient pair, including the potentially large difference channel. -/
theorem abs_integrated_exchange_le (inner : Bool) {ν : ℝ} (hν : 0 ≤ ν)
    (u : FourierVelocity) (k l m n : Wavevector) (p : TripleIndex)
    (hc : 0 < remainingDamping ν m n p) (hc' : 0 < remainingDamping ν l n p)
    (hl : 0 < ‖frequencyVec l‖)
    (hkl : ‖frequencyVec k‖ ≤ ‖frequencyVec l‖ / 4)
    (hkm : ‖frequencyVec k‖ ≤ ‖frequencyVec m‖ / 4) :
    let a := totalDamping ν k l m n p
    let r := ‖frequencyVec k‖ / ‖frequencyVec l‖
    let x := interactionTest inner u k l m n p
    let y := interactionTest inner u k m l n p
    |(∫ σ : ℝ in Set.Ioi 0, heatInteraction inner ν σ u k l m n p) +
      (∫ σ : ℝ in Set.Ioi 0, heatInteraction inner ν σ u k m l n p)| ≤
      (8 * r ^ 2 / a) * |x + y| + (4 * r / a) * |x - y| +
        (4 * |outputShift ν k l + outputShift ν k m| / a ^ 2) * |y| := by
  dsimp only
  rw [integral_heatInteraction_eq_defect inner hν u k l m n p hc,
    integral_heatInteraction_eq_defect inner hν u k m l n p hc',
    ← totalDamping_exchange ν k l m n p]
  have ha : 0 < totalDamping ν k l m n p := by
    rw [← centerRate_eq_totalDamping]
    exact centerRate_pos hν hc k l
  have hd := abs_outputShift_le_relative_centerRate hν hc.le k l hl
  rw [centerRate_eq_totalDamping] at hd
  have he := abs_outputShift_le_half_centerRate_of_separated hν hc'.le k m hkm
  rw [centerRate_eq_totalDamping, ← totalDamping_exchange ν k l m n p] at he
  have hrh : 2 * ‖frequencyVec k‖ / ‖frequencyVec l‖ ≤ 1 / 2 :=
    (div_le_iff₀ hl).mpr (by linarith)
  exact (BalancedResolvent.abs_near_reflected_pair_le ha (by positivity) hrh hd he
    (interactionTest inner u k l m n p) (interactionTest inner u k m l n p)).trans_eq (by ring)

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxInputExchange
