import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ComplexPressurePair

/-!
# Output-symbol stability after pressure-pair cancellation

The trace numerator vanishes quadratically with the output frequency for
arbitrary complex amplitudes. This compensates the apparent singularity
in the pressure-tilt symbol's variation. The result controls the output
symbol part of a bilinear localization commutator; variation of the
input Biot--Savart symbols is a separate term.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressurePairOutputStability

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator PancakePeriodicComplexStretch
open PancakeFourierPressureStrain PancakeSignedTransportEnergy PancakeLowPressureBudget
open PancakeSameSectorDissipation ComplexPressurePair FourierPressureCommutator FourierPressureTraceSymbol
open PressureTiltSymbol

theorem tracePair_eq_output_dots (k p : Wavevector) (w v : VelocityCoefficient) :
    tracePair k p w v =
      modeDot (k + p) (complexBiotSavartAmp k w) *
        modeDot (k + p) (complexBiotSavartAmp p v) := by
  simp only [tracePair, modeDot_add_wavevector, modeDot_complexBiotSavartAmp_self, zero_add, add_zero]

theorem norm_tracePair_mul_frequencies_le (k p : Wavevector) (w v : VelocityCoefficient) :
    ‖tracePair k p w v‖ * ‖frequencyVec k‖ * ‖frequencyVec p‖ ≤
      ‖frequencyVec (k + p)‖ ^ 2 * ‖coefficientVec w‖ * ‖coefficientVec v‖ := by
  have hd : ‖tracePair k p w v‖ ≤
      ‖frequencyVec (k + p)‖ ^ 2 * ‖coefficientVec (complexBiotSavartAmp k w)‖ *
        ‖coefficientVec (complexBiotSavartAmp p v)‖ := by
    rw [tracePair_eq_output_dots, norm_mul]
    have h := mul_le_mul (norm_modeDot_le (k + p) (complexBiotSavartAmp k w))
      (norm_modeDot_le (k + p) (complexBiotSavartAmp p v)) (norm_nonneg _) (by positivity)
    nlinarith only [h]
  calc
    _ ≤ (‖frequencyVec (k + p)‖ ^ 2 * ‖coefficientVec (complexBiotSavartAmp k w)‖ *
        ‖coefficientVec (complexBiotSavartAmp p v)‖) * ‖frequencyVec k‖ * ‖frequencyVec p‖ := by gcongr
    _ = ‖frequencyVec (k + p)‖ ^ 2 *
        ((‖frequencyVec k‖ * ‖coefficientVec (complexBiotSavartAmp k w)‖) *
        (‖frequencyVec p‖ * ‖coefficientVec (complexBiotSavartAmp p v)‖)) := by ring
    _ ≤ _ := by
      have h := mul_le_mul (frequency_mul_norm_biot_le k w) (frequency_mul_norm_biot_le p v)
        (by positivity) (norm_nonneg _)
      nlinarith only [mul_le_mul_of_nonneg_left h (sq_nonneg ‖frequencyVec (k + p)‖)]

theorem norm_tracePair_mul_frequency_le (k p : Wavevector) (w v : VelocityCoefficient) :
    ‖tracePair k p w v‖ * ‖frequencyVec k‖ ≤
      2 * ‖frequencyVec (k + p)‖ * ‖coefficientVec w‖ * ‖coefficientVec v‖ := by
  have hbase := norm_tracePair_le k p w v
  have hquad := norm_tracePair_mul_frequencies_le k p w v
  have htriangle : ‖frequencyVec k‖ ≤ ‖frequencyVec (k + p)‖ + ‖frequencyVec p‖ := by
    have hk : frequencyVec k = frequencyVec (k + p) - frequencyVec p := by
      rw [← frequencyVec_sub, add_sub_cancel_right]
    conv_lhs => rw [hk]
    exact norm_sub_le _ _
  by_cases hp : frequencyVec p = 0
  · rw [hp, norm_zero, add_zero] at htriangle
    have h := mul_le_mul hbase htriangle (norm_nonneg _) (by positivity)
    nlinarith only [h, mul_nonneg (norm_nonneg (frequencyVec (k + p)))
      (mul_nonneg (norm_nonneg (coefficientVec w)) (norm_nonneg (coefficientVec v)))]
  have hpn := norm_pos_iff.mpr hp
  rcases le_total ‖frequencyVec (k + p)‖ ‖frequencyVec p‖ with hqp | hpq
  · have h : ‖tracePair k p w v‖ * ‖frequencyVec k‖ ≤
        ‖frequencyVec (k + p)‖ * ‖coefficientVec w‖ * ‖coefficientVec v‖ := by
      apply le_of_mul_le_mul_right (a := ‖frequencyVec p‖) ?_ hpn
      have hb := mul_le_mul_of_nonneg_right hqp
        (show 0 ≤ ‖frequencyVec (k + p)‖ * ‖coefficientVec w‖ * ‖coefficientVec v‖ by positivity)
      nlinarith only [hquad, hb]
    nlinarith only [h, mul_nonneg (norm_nonneg (frequencyVec (k + p)))
      (mul_nonneg (norm_nonneg (coefficientVec w)) (norm_nonneg (coefficientVec v)))]
  · have hk : ‖frequencyVec k‖ ≤ 2 * ‖frequencyVec (k + p)‖ := by linarith
    have h := mul_le_mul hbase hk (norm_nonneg _) (by positivity)
    nlinarith only [h]

theorem norm_complexTiltSymbol_sub_mul_frequency_le
    (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1) (q r : Wavevector) :
    ‖complexTiltSymbol e q - complexTiltSymbol e r‖ * ‖frequencyVec q‖ ≤
      4 * ‖frequencyVec (q - r)‖ := by
  rw [complexTiltSymbol, complexTiltSymbol, ← complexifyVector_sub, norm_complexifyVector,
    norm_frequencyVec_eq]
  by_cases hq : realFrequency q = 0
  · rw [hq, norm_zero, mul_zero]
    positivity
  have h := norm_tiltSymbol_sub_le e (realFrequency q) (realFrequency r) he hq
  have hn := norm_pos_iff.mpr hq
  have hid : ‖realFrequency q - realFrequency r‖ = ‖frequencyVec (q - r)‖ := by
    rw [frequencyVec_sub]
    exact (norm_complexifyVector (realFrequency q - realFrequency r)).symm.trans
      (congrArg norm (complexifyVector_sub _ _))
  rw [hid] at h
  exact (le_div_iff₀ hn).mp h

/-- No exclusion of zero or nearly cancelling output frequencies. The
source frequency multiplies the bound, leaving an inverse source scale
when that scale is positive. -/
theorem norm_output_symbol_change_mul_frequency_le
    (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1)
    (k p r : Wavevector) (w v : VelocityCoefficient) :
    ‖tracePair k p w v • (complexTiltSymbol e (k + p) - complexTiltSymbol e r)‖ * ‖frequencyVec k‖ ≤
      8 * ‖frequencyVec (k + p - r)‖ * ‖coefficientVec w‖ * ‖coefficientVec v‖ := by
  rw [norm_smul]
  have h1 := mul_le_mul_of_nonneg_left (norm_tracePair_mul_frequency_le k p w v)
    (norm_nonneg (complexTiltSymbol e (k + p) - complexTiltSymbol e r))
  have h2 := mul_le_mul_of_nonneg_right (norm_complexTiltSymbol_sub_mul_frequency_le e he (k + p) r)
    (show 0 ≤ 2 * ‖coefficientVec w‖ * ‖coefficientVec v‖ by positivity)
  nlinarith only [h1, h2]

end Mettapedia.FluidDynamics.NavierStokes.PressurePairOutputStability
