import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LongitudinalInviscidFluxFourier

/-!
# Exchange cancellation in the actual vorticity stretching pair

Curl and incompressibility identify each ordered stretching interaction
with a Leray projection of the vorticity cross product. Exchanging the
inputs yields the difference of their Leray projections. This is an
identity for the actual velocity coefficients, not independent fields.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LerayStretchExchange

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakePeriodicVorticityEquation

theorem lerayMode_sub (k : Wavevector) (a b : VelocityCoefficient) :
    lerayMode k (a - b) = lerayMode k a - lerayMode k b := by
  by_cases hk : modeSquare k = 0
  · simp [lerayMode, hk]
  · ext i
    simp [lerayMode, hk, modeDot_sub]
    ring

theorem lerayMode_of_transverse (k : Wavevector) (a : VelocityCoefficient)
    (ha : modeDot k a = 0) : lerayMode k a = a := by
  simp [lerayMode, ha]

theorem lerayMode_wavevector (k : Wavevector) :
    lerayMode k (wavevectorCoefficient k) = 0 := by
  by_cases hk : k = 0
  · subst k
    ext i
    simp [lerayMode, modeSquare, wavevectorCoefficient]
  · have hs := modeSquare_ne_zero_of_frequencyVec_ne_zero (frequencyVec_ne_zero hk)
    have hd : modeDot k (wavevectorCoefficient k) = modeSquare k := rfl
    ext i
    simp [lerayMode, hs, hd, wavevectorCoefficient]

theorem lerayMode_neg (k : Wavevector) (a : VelocityCoefficient) :
    lerayMode k (-a) = -lerayMode k a := by
  simpa only [neg_one_smul] using lerayMode_smul k (-1) a

/-- No inverse vorticity amplitude or nonzero frequency hypothesis is needed. -/
theorem stretch_pair_eq_leray_cross (u : FourierVelocity) (m : Wavevector)
    (a : VelocityCoefficient) (hu : modeDot m (u m) = 0) :
    (unitTorusDerivativePhase * modeDot m a) • u m =
      -lerayMode m (coefficientCross a (fourierCurl u m)) := by
  have hc := cross_cross_eq_smul_sub_smul' a (wavevectorCoefficient m) (u m)
  change coefficientCross a (coefficientCross (wavevectorCoefficient m) (u m)) =
    coefficientDot a (u m) • wavevectorCoefficient m - modeDot m a • u m at hc
  rw [fourierCurl, coefficientCross_smul_right, hc, lerayMode_smul, lerayMode_sub,
    lerayMode_smul, lerayMode_smul, lerayMode_wavevector, lerayMode_of_transverse m _ hu,
    smul_zero, zero_sub, smul_neg, neg_neg, smul_smul]

theorem stretch_pair_add_exchange (u : FourierVelocity) (l m : Wavevector)
    (hl : modeDot l (u l) = 0) (hm : modeDot m (u m) = 0) :
    (unitTorusDerivativePhase * modeDot m (fourierCurl u l)) • u m +
      (unitTorusDerivativePhase * modeDot l (fourierCurl u m)) • u l =
    lerayMode l (coefficientCross (fourierCurl u l) (fourierCurl u m)) -
      lerayMode m (coefficientCross (fourierCurl u l) (fourierCurl u m)) := by
  rw [stretch_pair_eq_leray_cross u m _ hm, stretch_pair_eq_leray_cross u l _ hl]
  have hc : coefficientCross (fourierCurl u m) (fourierCurl u l) =
      -coefficientCross (fourierCurl u l) (fourierCurl u m) :=
    (cross_anticomm _ _).symm
  rw [hc, lerayMode_neg]
  abel

theorem lerayMode_neg_frequency (k : Wavevector) (a : VelocityCoefficient) :
    lerayMode (-k) a = lerayMode k a := by
  have hs : modeSquare (-k) = modeSquare k := by simp [modeSquare]
  have hd : modeDot (-k) a = -modeDot k a := by
    simp [modeDot, Finset.sum_neg_distrib]
  by_cases hk : modeSquare k = 0
  · simp [lerayMode, hs, hk]
  · ext i
    simp [lerayMode, hs, hk, hd]

theorem coefficientVec_lerayMode (k : Wavevector) (a : VelocityCoefficient) :
    coefficientVec (lerayMode k a) =
      coefficientVec a - orthogonalLineProjector (frequencyVec k) (coefficientVec a) := by
  rw [orthogonalLineProjector_frequencyVec_apply]
  by_cases hk : modeSquare k = 0
  · simp [lerayMode, hk]
  · ext i
    simp [coefficientVec, frequencyVec, wavevectorCoefficient, lerayMode, hk,
      PiLp.sub_apply, PiLp.smul_apply]
    ring

/-- Nearly opposite inputs yield a small projector difference. -/
theorem norm_lerayMode_sub_le_output (k l : Wavevector) (a : VelocityCoefficient)
    (hk : k ≠ 0) (hl : l ≠ 0) :
    ‖coefficientVec (lerayMode k a - lerayMode l a)‖ ≤
      4 * ‖frequencyVec (k + l)‖ / ‖frequencyVec k‖ * ‖coefficientVec a‖ := by
  have he : coefficientVec (lerayMode k a - lerayMode l a) =
      -(orthogonalLineProjector (frequencyVec k) -
        orthogonalLineProjector (frequencyVec (-l))) (coefficientVec a) := by
    change coefficientVec (lerayMode k a) - coefficientVec (lerayMode l a) = _
    rw [← lerayMode_neg_frequency l a, coefficientVec_lerayMode, coefficientVec_lerayMode]
    simp only [sub_apply]
    abel
  rw [he, norm_neg]
  have h := norm_orthogonalLineProjector_sub_le (frequencyVec k) (frequencyVec (-l))
    (frequencyVec_ne_zero hk) (frequencyVec_ne_zero (neg_ne_zero.mpr hl))
  have hf : frequencyVec k - frequencyVec (-l) = frequencyVec (k + l) := by
    rw [← frequencyVec_sub, sub_neg_eq_add]
  rw [hf] at h
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

theorem norm_stretch_pair_add_exchange_le (u : FourierVelocity) (l m : Wavevector)
    (hl0 : l ≠ 0) (hm0 : m ≠ 0)
    (hl : modeDot l (u l) = 0) (hm : modeDot m (u m) = 0) :
    ‖coefficientVec
      ((unitTorusDerivativePhase * modeDot m (fourierCurl u l)) • u m +
       (unitTorusDerivativePhase * modeDot l (fourierCurl u m)) • u l)‖ ≤
      4 * ‖frequencyVec (l + m)‖ / ‖frequencyVec l‖ *
        ‖coefficientVec (coefficientCross (fourierCurl u l) (fourierCurl u m))‖ := by
  rw [stretch_pair_add_exchange u l m hl hm]
  exact norm_lerayMode_sub_le_output l m _ hl0 hm0

theorem norm_lerayMode_sub_le_output_max (k l : Wavevector) (a : VelocityCoefficient)
    (hk : k ≠ 0) (hl : l ≠ 0) :
    ‖coefficientVec (lerayMode k a - lerayMode l a)‖ ≤
      4 * ‖frequencyVec (k + l)‖ /
        max ‖frequencyVec k‖ ‖frequencyVec l‖ * ‖coefficientVec a‖ := by
  by_cases h : ‖frequencyVec k‖ ≤ ‖frequencyVec l‖
  · rw [max_eq_right h]
    have he : ‖coefficientVec (lerayMode k a - lerayMode l a)‖ =
        ‖coefficientVec (lerayMode l a - lerayMode k a)‖ := by
      change ‖coefficientVec (lerayMode k a) - coefficientVec (lerayMode l a)‖ =
        ‖coefficientVec (lerayMode l a) - coefficientVec (lerayMode k a)‖
      exact norm_sub_rev _ _
    rw [he, add_comm k l]
    exact norm_lerayMode_sub_le_output l k a hl hk
  · rw [max_eq_left (le_of_not_ge h)]
    exact norm_lerayMode_sub_le_output k l a hk hl

end Mettapedia.FluidDynamics.NavierStokes.LerayStretchExchange
