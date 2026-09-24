import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PositiveStretchingSnapshot
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ResolvedProjectionCutoffLimit
import Mettapedia.Analysis.UnitTorusPositiveCoefficient

/-!
# Positive actual stretching and a nondecaying resolved remainder

Positivity of one finite Fourier convolution path suffices. The spatial
mean is linked to the actual reconstructed velocity, with every factor
of `2π` retained. This supplies an explicit witness against a remainder
bound that vanishes with oversized normalization; it is not a blowup
example and does not refute a nonzero time-integrated budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PositiveStretchingSnapshot

open MeasureTheory Mettapedia.Analysis.UnitTorusPositiveCoefficient
open PeriodicFourierTriad LocalVorticityEighthMoment InfiniteFilteredEquation
open FilteredCoherentProjectionBudget ResolvedProjectionCutoffLimit
open PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator FiniteInviscidSupport
open scoped Topology

local notation "T3" => UnitAddTorus (Fin 3)
local notation "A" => AddMonoidAlgebra ℝ Wavevector
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def normPolynomial : A :=
  (cosinePolynomial xMode + cosinePolynomial diagonalMode) *
      (cosinePolynomial xMode + cosinePolynomial diagonalMode) +
    cosinePolynomial diagonalMode * cosinePolynomial diagonalMode +
    cosinePolynomial yMode * cosinePolynomial yMode

def strainPolynomial : A :=
  (cosinePolynomial yMode * (cosinePolynomial xMode + cosinePolynomial diagonalMode)) *
    cosinePolynomial diagonalMode

def stretchingPolynomial : A := ((normPolynomial * normPolynomial) * normPolynomial) * strainPolynomial

theorem normPolynomial_nonnegative : HasNonnegativeCoefficients normPolynomial :=
  nonnegative_add (nonnegative_add
    (nonnegative_mul (nonnegative_add (cosine_nonnegative _) (cosine_nonnegative _))
      (nonnegative_add (cosine_nonnegative _) (cosine_nonnegative _)))
    (nonnegative_mul (cosine_nonnegative _) (cosine_nonnegative _)))
    (nonnegative_mul (cosine_nonnegative _) (cosine_nonnegative _))

theorem strainPolynomial_nonnegative : HasNonnegativeCoefficients strainPolynomial :=
  nonnegative_mul (nonnegative_mul (cosine_nonnegative _)
    (nonnegative_add (cosine_nonnegative _) (cosine_nonnegative _))) (cosine_nonnegative _)

theorem normPolynomial_zero_pos : 0 < normPolynomial 0 := by
  have h := mul_coeff_pos (cosine_nonnegative diagonalMode) (cosine_nonnegative diagonalMode)
    (cosine_coeff_pos diagonalMode) (cosine_neg_coeff_pos diagonalMode)
  simp only [add_neg_cancel] at h
  have h1 := nonnegative_mul
    (nonnegative_add (cosine_nonnegative xMode) (cosine_nonnegative diagonalMode))
    (nonnegative_add (cosine_nonnegative xMode) (cosine_nonnegative diagonalMode)) (0 : Wavevector)
  have h2 := nonnegative_mul (cosine_nonnegative yMode) (cosine_nonnegative yMode) (0 : Wavevector)
  change (0 : ℝ) < _ + _ + _
  linarith only [h, h1, h2]

theorem strainPolynomial_zero_pos : 0 < strainPolynomial 0 := by
  have hx : 0 < (cosinePolynomial xMode + cosinePolynomial diagonalMode) xMode :=
    add_pos_of_pos_of_nonneg (cosine_coeff_pos xMode) (cosine_nonnegative diagonalMode xMode)
  have h1 := mul_coeff_pos (cosine_nonnegative yMode)
    (nonnegative_add (cosine_nonnegative xMode) (cosine_nonnegative diagonalMode))
    (cosine_coeff_pos yMode) hx
  have hxy : yMode + xMode = diagonalMode := by ext i; fin_cases i <;> rfl
  rw [hxy] at h1
  have h2 := mul_coeff_pos
    (nonnegative_mul (cosine_nonnegative yMode)
      (nonnegative_add (cosine_nonnegative xMode) (cosine_nonnegative diagonalMode)))
    (cosine_nonnegative diagonalMode) h1 (cosine_neg_coeff_pos diagonalMode)
  simpa only [add_neg_cancel, strainPolynomial] using h2

theorem stretchingPolynomial_zero_pos : 0 < stretchingPolynomial 0 := by
  have h2 := mul_coeff_pos normPolynomial_nonnegative normPolynomial_nonnegative
    normPolynomial_zero_pos normPolynomial_zero_pos
  simp only [zero_add] at h2
  have h3 := mul_coeff_pos (nonnegative_mul normPolynomial_nonnegative normPolynomial_nonnegative)
    normPolynomial_nonnegative h2 normPolynomial_zero_pos
  simp only [zero_add] at h3
  simpa only [zero_add, stretchingPolynomial] using mul_coeff_pos
    (nonnegative_mul (nonnegative_mul normPolynomial_nonnegative normPolynomial_nonnegative)
      normPolynomial_nonnegative) strainPolynomial_nonnegative h3 strainPolynomial_zero_pos

theorem evaluate_stretchingPolynomial (x : T3) :
    (2 * Real.pi : ℂ) ^ 9 * evaluate stretchingPolynomial x =
      (stretchingDensity coefficients x : ℂ) := by
  rw [stretchingDensity_eq]
  simp only [stretchingPolynomial, normPolynomial, strainPolynomial, map_mul, map_add,
    ContinuousMap.mul_apply, ContinuousMap.add_apply, evaluate_cosine, cosine,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_ofNat]
  ring

theorem stretching_eq_zeroCoefficient :
    stretching coefficients = (2 * Real.pi) ^ 9 * stretchingPolynomial 0 := by
  have h := integral_evaluate stretchingPolynomial
  have hi := congrArg (fun z : ℂ ↦ (2 * Real.pi : ℂ) ^ 9 * z) h
  rw [← integral_const_mul] at hi
  simp_rw [evaluate_stretchingPolynomial] at hi
  rw [integral_complex_ofReal] at hi
  exact_mod_cast hi

theorem stretching_pos : 0 < stretching coefficients := by
  rw [stretching_eq_zeroCoefficient]
  exact mul_pos (pow_pos (by positivity) _) stretchingPolynomial_zero_pos

/-- Every constant fails for this one explicitly constructed finite field. -/
theorem no_decaying_remainder_bound (ν : ℝ) (hν : 0 < ν) :
    ¬ ∃ C : ℝ, ∀ᶠ R : ℝ in Filter.atTop,
      signedWorkRemainder ν R (resolvedModes modes) (sharpFilter (resolvedModes modes)) coefficients ≤
        C / FiniteBandProjectionAbsorption.normalization R :=
  no_decaying_resolved_upper_bound ν hν modes coefficients supported transverse reality stretching_pos

end Mettapedia.FluidDynamics.NavierStokes.PositiveStretchingSnapshot
