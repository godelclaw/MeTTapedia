import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ComplexPressurePair
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ComplexTransverseMatrix

/-!
# Pressure depletion for arbitrary complex vorticity amplitudes

The estimate has the same constant as its real counterpart. Coherence is
measured by the actual orthogonal projection off a real unit line; no
reality, phase alignment, input cone, or output-frequency exclusion is
required. Normalized divergence defects are retained for localized inputs.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ComplexPressureMisalignment

open scoped RealInnerProductSpace BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeComplexMisalignmentExpansion
open FourierPressureCommutator FourierPressureTraceSymbol ComplexTransverseMatrix
open ComplexPressurePair PancakeLowPressureBudget

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def transverseCoefficient (e : R3) (w : VelocityCoefficient) : VelocityCoefficient :=
  WithLp.ofLp (transverse e (coefficientVec w))

theorem coefficient_decomposition (e : R3) (w : VelocityCoefficient) :
    w = pairing e (coefficientVec w) • realCoefficient e + transverseCoefficient e w := by
  ext i
  simp [transverseCoefficient, transverse, complexifyVector, coefficientVec, realCoefficient]

theorem modeDot_transverseCoefficient (e : R3) (k : Wavevector) (w : VelocityCoefficient) :
    modeDot k (transverseCoefficient e w) = modeDot k w -
      pairing e (coefficientVec w) * (⟪realFrequency k, e⟫ : ℝ) := by
  change modeDot k (w - pairing e (coefficientVec w) • realCoefficient e) = _
  rw [modeDot_sub, modeDot_smul, modeDot_realCoefficient]

theorem longitudinal_mul_amplitude_le (e : R3) (k : Wavevector) (w : VelocityCoefficient) :
    |⟪realFrequency k, e⟫| / ‖frequencyVec k‖ * ‖pairing e (coefficientVec w)‖ ≤
      ‖transverse e (coefficientVec w)‖ + ‖modeDot k w‖ / ‖frequencyVec k‖ := by
  by_cases hk : frequencyVec k = 0
  · simp only [hk, norm_zero, div_zero, zero_mul, add_zero]
    exact norm_nonneg _
  have hkn := norm_pos_iff.mpr hk
  have hid : pairing e (coefficientVec w) * (⟪realFrequency k, e⟫ : ℝ) =
      modeDot k w - modeDot k (transverseCoefficient e w) := by
    rw [modeDot_transverseCoefficient, sub_sub_cancel]
  have ht := norm_sub_le (modeDot k w) (modeDot k (transverseCoefficient e w))
  rw [← hid, norm_mul, Complex.norm_real, Real.norm_eq_abs] at ht
  have hd := norm_modeDot_le k (transverseCoefficient e w)
  change ‖modeDot k (transverseCoefficient e w)‖ ≤
    ‖frequencyVec k‖ * ‖transverse e (coefficientVec w)‖ at hd
  apply le_of_mul_le_mul_left (a := ‖frequencyVec k‖) ?_ hkn
  calc
    _ = ‖pairing e (coefficientVec w)‖ * |⟪realFrequency k, e⟫| := by field_simp
    _ ≤ ‖modeDot k w‖ + ‖frequencyVec k‖ * ‖transverse e (coefficientVec w)‖ := by linarith
    _ = _ := by field_simp; ring

theorem tiltPair_add_left (e : R3) (k p : Wavevector) (w z v : VelocityCoefficient) :
    tiltPair e k p (w + z) v = tiltPair e k p w v + tiltPair e k p z v := by
  simp only [tiltPair, tracePair, complexBiotSavartAmp_add, modeDot, Pi.add_apply,
    mul_add, Finset.sum_add_distrib, add_mul, add_smul]

theorem tiltPair_add_right (e : R3) (k p : Wavevector) (w v z : VelocityCoefficient) :
    tiltPair e k p w (v + z) = tiltPair e k p w v + tiltPair e k p w z := by
  simp only [tiltPair, tracePair, complexBiotSavartAmp_add, modeDot, Pi.add_apply,
    mul_add, Finset.sum_add_distrib, add_smul]

theorem tiltPair_smul_left (a : ℂ) (e : R3) (k p : Wavevector) (w v : VelocityCoefficient) :
    tiltPair e k p (a • w) v = a • tiltPair e k p w v := by
  simp only [tiltPair, tracePair, complexBiotSavartAmp_smul, modeDot_smul, smul_smul, mul_assoc]

theorem tiltPair_smul_right (a : ℂ) (e : R3) (k p : Wavevector) (w v : VelocityCoefficient) :
    tiltPair e k p w (a • v) = a • tiltPair e k p w v := by
  simp only [tiltPair, tracePair, complexBiotSavartAmp_smul, modeDot_smul, smul_smul]
  congr 1
  ring

theorem tiltPair_decomposition (e : R3) (k p : Wavevector) (w v : VelocityCoefficient) :
    tiltPair e k p w v =
      (pairing e (coefficientVec w) * pairing e (coefficientVec v)) •
        tiltPair e k p (realCoefficient e) (realCoefficient e) +
      pairing e (coefficientVec w) • tiltPair e k p (realCoefficient e) (transverseCoefficient e v) +
      tiltPair e k p (transverseCoefficient e w) v := by
  conv_lhs => rw [coefficient_decomposition e w, tiltPair_add_left, tiltPair_smul_left]
  conv_lhs => arg 1; arg 2; rw [coefficient_decomposition e v, tiltPair_add_right, tiltPair_smul_right]
  rw [smul_add, smul_smul]

theorem norm_tiltPair_le_misalignment_add_divergence
    (e : R3) (he : ‖e‖ = 1) (k p : Wavevector) (w v : VelocityCoefficient) :
    ‖tiltPair e k p w v‖ ≤
      2 * (‖transverse e (coefficientVec w)‖ * ‖coefficientVec v‖ +
        ‖coefficientVec w‖ * ‖transverse e (coefficientVec v)‖) +
      ‖modeDot k w‖ / ‖frequencyVec k‖ * ‖coefficientVec v‖ +
      ‖coefficientVec w‖ * (‖modeDot p v‖ / ‖frequencyVec p‖) := by
  have ha := norm_pairing_le e (coefficientVec w) he
  have hb := norm_pairing_le e (coefficientVec v) he
  have hka := longitudinal_mul_amplitude_le e k w
  have hpb := longitudinal_mul_amplitude_le e p v
  have hcoh := mul_le_mul_of_nonneg_left (norm_tiltPair_coherent_le e he k p)
    (mul_nonneg (norm_nonneg (pairing e (coefficientVec w))) (norm_nonneg (pairing e (coefficientVec v))))
  have hA := mul_le_mul_of_nonneg_right hka (norm_nonneg (pairing e (coefficientVec v)))
  have hB := mul_le_mul_of_nonneg_right hpb (norm_nonneg (pairing e (coefficientVec w)))
  have hAv := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ ‖transverse e (coefficientVec w)‖ + ‖modeDot k w‖ / ‖frequencyVec k‖ by positivity)
  have hBw := mul_le_mul_of_nonneg_left ha
    (show 0 ≤ ‖transverse e (coefficientVec v)‖ + ‖modeDot p v‖ / ‖frequencyVec p‖ by positivity)
  have hfirst : ‖(pairing e (coefficientVec w) * pairing e (coefficientVec v)) •
        tiltPair e k p (realCoefficient e) (realCoefficient e)‖ ≤
      (‖transverse e (coefficientVec w)‖ + ‖modeDot k w‖ / ‖frequencyVec k‖) * ‖coefficientVec v‖ +
        ‖coefficientVec w‖ * (‖transverse e (coefficientVec v)‖ + ‖modeDot p v‖ / ‖frequencyVec p‖) := by
    rw [norm_smul, norm_mul]
    nlinarith only [hcoh, hA, hB, hAv, hBw]
  have hsecond : ‖pairing e (coefficientVec w) •
      tiltPair e k p (realCoefficient e) (transverseCoefficient e v)‖ ≤
      ‖coefficientVec w‖ * ‖transverse e (coefficientVec v)‖ := by
    rw [norm_smul]
    have h := norm_tiltPair_le e he k p (realCoefficient e) (transverseCoefficient e v)
    rw [norm_realCoefficient, he, one_mul] at h
    exact mul_le_mul ha h (norm_nonneg _) (norm_nonneg _)
  have hthird := norm_tiltPair_le e he k p (transverseCoefficient e w) v
  change ‖tiltPair e k p (transverseCoefficient e w) v‖ ≤
    ‖transverse e (coefficientVec w)‖ * ‖coefficientVec v‖ at hthird
  rw [tiltPair_decomposition]
  have hnorm := (norm_add_le
    ((pairing e (coefficientVec w) * pairing e (coefficientVec v)) •
      tiltPair e k p (realCoefficient e) (realCoefficient e) +
      pairing e (coefficientVec w) • tiltPair e k p (realCoefficient e) (transverseCoefficient e v))
    (tiltPair e k p (transverseCoefficient e w) v)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  nlinarith only [hnorm, hfirst, hsecond, hthird]

theorem norm_tiltPair_le_misalignment
    (e : R3) (he : ‖e‖ = 1) (k p : Wavevector) (w v : VelocityCoefficient)
    (hw : modeDot k w = 0) (hv : modeDot p v = 0) :
    ‖tiltPair e k p w v‖ ≤
      2 * (‖transverse e (coefficientVec w)‖ * ‖coefficientVec v‖ +
        ‖coefficientVec w‖ * ‖transverse e (coefficientVec v)‖) := by
  simpa only [hw, hv, norm_zero, zero_div, zero_mul, mul_zero, add_zero] using
    norm_tiltPair_le_misalignment_add_divergence e he k p w v

end Mettapedia.FluidDynamics.NavierStokes.ComplexPressureMisalignment
