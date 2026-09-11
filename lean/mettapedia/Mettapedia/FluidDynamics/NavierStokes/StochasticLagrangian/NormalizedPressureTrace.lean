import Mettapedia.Analysis.NormalizationStability
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ComplexPressurePair
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLowTouchEnergy
import Mettapedia.Analysis.FiniteSumEnergy

/-!
# The pressure trace as a polynomial in normalized input directions

The exact complex pressure trace is homogeneous of degree zero in each
input frequency. Its normalized polynomial has a Lipschitz estimate on
the unit ball, including the zero normalized direction.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.NormalizedPressureTrace

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeLowTouchEnergy ComplexPressurePair
open Mettapedia.Analysis NormedSpace

theorem norm_coefficientDot_le_product (u v : VelocityCoefficient) :
    ‖coefficientDot u v‖ ≤ ‖coefficientVec u‖ * ‖coefficientVec v‖ := by
  have h : ‖coefficientDot u v‖ ^ 2 ≤ ‖coefficientVec u‖ ^ 2 * ‖coefficientVec v‖ ^ 2 := by
    simpa only [coefficientDot, coefficientVec, EuclideanSpace.norm_sq_eq, PiLp.toLp_apply,
      smul_eq_mul] using Finset.norm_sum_smul_sq_le Finset.univ u v
  nlinarith only [h, norm_nonneg (coefficientDot u v),
    mul_nonneg (norm_nonneg (coefficientVec u)) (norm_nonneg (coefficientVec v))]

def triple (a b w : VelocityCoefficient) : ℂ := coefficientDot b (coefficientCross a w)

theorem norm_triple_le (a b w : VelocityCoefficient) :
    ‖triple a b w‖ ≤ ‖coefficientVec a‖ * ‖coefficientVec b‖ * ‖coefficientVec w‖ := by
  have h := (norm_coefficientDot_le_product b (coefficientCross a w)).trans
    (mul_le_mul_of_nonneg_left (norm_complex_cross_le a w) (norm_nonneg (coefficientVec b)))
  unfold triple
  nlinarith only [h]

theorem triple_sub_left (a a' b w : VelocityCoefficient) :
    triple (a - a') b w = triple a b w - triple a' b w := by
  simp [triple, coefficientDot, coefficientCross, Fin.sum_univ_three]
  ring

theorem triple_sub_right (a b b' w : VelocityCoefficient) :
    triple a (b - b') w = triple a b w - triple a b' w := by
  simp [triple, coefficientDot, coefficientCross, Fin.sum_univ_three]
  ring

theorem triple_smul_smul (r s : ℂ) (a b w : VelocityCoefficient) :
    triple (r • a) (s • b) w = (r * s) * triple a b w := by
  simp [triple, coefficientDot, coefficientCross, Fin.sum_univ_three]
  ring

def directionalTrace (a b w v : VelocityCoefficient) : ℂ := triple a b w * triple b a v

theorem directionalTrace_sub_left (a a' b w v : VelocityCoefficient) :
    directionalTrace a b w v - directionalTrace a' b w v =
      triple (a - a') b w * triple b a v + triple a' b w * triple b (a - a') v := by
  rw [triple_sub_left, triple_sub_right]
  unfold directionalTrace
  ring

theorem norm_directionalTrace_sub_le (a a' b w v : VelocityCoefficient)
    (ha : ‖coefficientVec a‖ ≤ 1) (ha' : ‖coefficientVec a'‖ ≤ 1) (hb : ‖coefficientVec b‖ ≤ 1) :
    ‖directionalTrace a b w v - directionalTrace a' b w v‖ ≤
      2 * ‖coefficientVec (a - a')‖ * ‖coefficientVec w‖ * ‖coefficientVec v‖ := by
  have h1 : ‖triple (a - a') b w‖ ≤ ‖coefficientVec (a - a')‖ * ‖coefficientVec w‖ := by
    have h := norm_triple_le (a - a') b w
    have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg (coefficientVec (a - a')))
    have hn := mul_le_mul_of_nonneg_right hm (norm_nonneg (coefficientVec w))
    nlinarith only [h, hn]
  have h2 : ‖triple b a v‖ ≤ ‖coefficientVec v‖ := by
    have h := norm_triple_le b a v
    have hn := mul_le_mul_of_nonneg_right (mul_le_mul hb ha (norm_nonneg _) zero_le_one) (norm_nonneg (coefficientVec v))
    nlinarith only [h, hn]
  have h3 : ‖triple a' b w‖ ≤ ‖coefficientVec w‖ := by
    have h := norm_triple_le a' b w
    have hn := mul_le_mul_of_nonneg_right (mul_le_mul ha' hb (norm_nonneg _) zero_le_one) (norm_nonneg (coefficientVec w))
    nlinarith only [h, hn]
  have h4 : ‖triple b (a - a') v‖ ≤ ‖coefficientVec (a - a')‖ * ‖coefficientVec v‖ := by
    have h := norm_triple_le b (a - a') v
    have hn := mul_le_mul_of_nonneg_right hb (show 0 ≤ ‖coefficientVec (a - a')‖ * ‖coefficientVec v‖ by positivity)
    nlinarith only [h, hn]
  rw [directionalTrace_sub_left]
  have hn := norm_add_le (triple (a - a') b w * triple b a v) (triple a' b w * triple b (a - a') v)
  rw [norm_mul, norm_mul] at hn
  have h12 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have h34 := mul_le_mul h3 h4 (norm_nonneg _) (norm_nonneg _)
  nlinarith only [hn, h12, h34]

def normalizedCoefficient (k : Wavevector) : VelocityCoefficient :=
  ((‖frequencyVec k‖ : ℂ)⁻¹) • wavevectorCoefficient k

theorem coefficientVec_normalizedCoefficient (k : Wavevector) :
    coefficientVec (normalizedCoefficient k) = normalize (frequencyVec k) := by
  simp only [normalizedCoefficient, NormedSpace.normalize, RCLike.real_smul_eq_coe_smul (K := ℂ),
    Complex.coe_algebraMap, Complex.ofReal_inv]
  rfl

theorem norm_normalizedCoefficient_le (k : Wavevector) : ‖coefficientVec (normalizedCoefficient k)‖ ≤ 1 := by
  rw [coefficientVec_normalizedCoefficient]
  exact norm_normalize_le_one _

theorem tracePair_eq_directionalTrace (k p : Wavevector) (w v : VelocityCoefficient) :
    tracePair k p w v = directionalTrace (normalizedCoefficient k) (normalizedCoefficient p) w v := by
  rw [directionalTrace]
  simp only [normalizedCoefficient, triple_smul_smul]
  simp only [tracePair, complexBiotSavartAmp, modeDot_smul, modeSquare_eq_norm_sq, Complex.ofReal_pow]
  change (1 / (‖frequencyVec k‖ : ℂ) ^ 2 * triple (wavevectorCoefficient k) (wavevectorCoefficient p) w) *
    (1 / (‖frequencyVec p‖ : ℂ) ^ 2 * triple (wavevectorCoefficient p) (wavevectorCoefficient k) v) = _
  ring

theorem norm_tracePair_sub_mul_frequency_le (k l p : Wavevector) (w v : VelocityCoefficient) :
    ‖tracePair k p w v - tracePair l p w v‖ * ‖frequencyVec k‖ ≤
      4 * ‖frequencyVec (k - l)‖ * ‖coefficientVec w‖ * ‖coefficientVec v‖ := by
  have h := norm_directionalTrace_sub_le (normalizedCoefficient k) (normalizedCoefficient l)
    (normalizedCoefficient p) w v (norm_normalizedCoefficient_le k)
    (norm_normalizedCoefficient_le l) (norm_normalizedCoefficient_le p)
  rw [← tracePair_eq_directionalTrace, ← tracePair_eq_directionalTrace] at h
  have hid : coefficientVec (normalizedCoefficient k - normalizedCoefficient l) =
      normalize (frequencyVec k) - normalize (frequencyVec l) := by
    rw [← coefficientVec_normalizedCoefficient, ← coefficientVec_normalizedCoefficient]
    rfl
  rw [hid] at h
  have hn := norm_normalize_sub_mul_norm_le (frequencyVec k) (frequencyVec l)
  rw [← frequencyVec_sub] at hn
  have h1 := mul_le_mul_of_nonneg_right h (norm_nonneg (frequencyVec k))
  have h2 := mul_le_mul_of_nonneg_right hn (show 0 ≤ 2 * ‖coefficientVec w‖ * ‖coefficientVec v‖ by positivity)
  nlinarith only [h1, h2]

end Mettapedia.FluidDynamics.NavierStokes.NormalizedPressureTrace
