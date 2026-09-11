import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.NormalizedPressureTrace
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressurePairOutputStability

/-!
# Complete one-input variation of the complex pressure-tilt kernel

The input trace costs 4 and the output-direction change costs 8. Their
sum gives a frequency-uniform bound including shifted input zero and
cancelling output frequencies. No cone or buffer hypothesis is used.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressurePairInputStability

open PeriodicFourierTriad PancakeFrequencyProjectorCommutator
open ComplexPressurePair FourierPressureCommutator FourierPressureTraceSymbol PressureTiltSymbol
open NormalizedPressureTrace PressurePairOutputStability

local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem tiltPair_sub_decomposition (e : R3) (k l p : Wavevector) (w v : VelocityCoefficient) :
    tiltPair e k p w v - tiltPair e l p w v =
      (tracePair k p w v - tracePair l p w v) • complexTiltSymbol e (l + p) +
      tracePair k p w v • (complexTiltSymbol e (k + p) - complexTiltSymbol e (l + p)) := by
  simp only [tiltPair, sub_smul, smul_sub]
  abel

theorem norm_tiltPair_sub_left_mul_frequency_le (e : R3) (he : ‖e‖ = 1)
    (k l p : Wavevector) (w v : VelocityCoefficient) :
    ‖tiltPair e k p w v - tiltPair e l p w v‖ * ‖frequencyVec k‖ ≤
      12 * ‖frequencyVec (k - l)‖ * ‖coefficientVec w‖ * ‖coefficientVec v‖ := by
  have hs : ‖complexTiltSymbol e (l + p)‖ ≤ 1 := by
    rw [complexTiltSymbol, norm_complexifyVector]
    exact norm_tiltSymbol_le_one e _ he
  have hfirst : ‖(tracePair k p w v - tracePair l p w v) • complexTiltSymbol e (l + p)‖ * ‖frequencyVec k‖ ≤
      4 * ‖frequencyVec (k - l)‖ * ‖coefficientVec w‖ * ‖coefficientVec v‖ := by
    rw [norm_smul]
    calc
      _ ≤ ‖tracePair k p w v - tracePair l p w v‖ * ‖frequencyVec k‖ := by
        have h := mul_le_mul_of_nonneg_left hs (norm_nonneg (tracePair k p w v - tracePair l p w v))
        simpa only [mul_one] using mul_le_mul_of_nonneg_right h (norm_nonneg (frequencyVec k))
      _ ≤ _ := norm_tracePair_sub_mul_frequency_le k l p w v
  have hsecond := norm_output_symbol_change_mul_frequency_le e he k p (l + p) w v
  rw [show k + p - (l + p) = k - l by abel] at hsecond
  rw [tiltPair_sub_decomposition]
  have hn := mul_le_mul_of_nonneg_right (norm_add_le
    ((tracePair k p w v - tracePair l p w v) • complexTiltSymbol e (l + p))
    (tracePair k p w v • (complexTiltSymbol e (k + p) - complexTiltSymbol e (l + p)))) (norm_nonneg (frequencyVec k))
  nlinarith only [hn, hfirst, hsecond]

theorem tracePair_swap (k p : Wavevector) (w v : VelocityCoefficient) : tracePair p k v w = tracePair k p w v := by
  unfold tracePair
  ring

theorem tiltPair_swap (e : R3) (k p : Wavevector) (w v : VelocityCoefficient) : tiltPair e p k v w = tiltPair e k p w v := by
  rw [tiltPair, tracePair_swap, add_comm]
  rfl

theorem norm_tiltPair_sub_right_mul_frequency_le (e : R3) (he : ‖e‖ = 1)
    (k p r : Wavevector) (w v : VelocityCoefficient) :
    ‖tiltPair e k p w v - tiltPair e k r w v‖ * ‖frequencyVec p‖ ≤
      12 * ‖frequencyVec (p - r)‖ * ‖coefficientVec w‖ * ‖coefficientVec v‖ := by
  have h := norm_tiltPair_sub_left_mul_frequency_le e he p r k v w
  rw [tiltPair_swap e k p w v, tiltPair_swap e k r w v] at h
  nlinarith only [h]

end Mettapedia.FluidDynamics.NavierStokes.PressurePairInputStability
