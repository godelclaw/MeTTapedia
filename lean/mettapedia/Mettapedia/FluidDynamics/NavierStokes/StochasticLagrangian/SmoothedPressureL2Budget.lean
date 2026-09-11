import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.WeightedPressureL2Replacement

/-!
# Smoothed pressure localization from L2-controlled spatial patches

The spatial-to-Fourier and resolvent errors are both charged explicitly.
This estimate requires neither pointwise coverage by Fourier polynomials
nor a bound for their second derivatives. The actual first-derivative
coefficient energy pays for smoothing and the elliptic commutator.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SmoothedPressureL2Budget

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakeAnisotropyDepletion SpectralTiltFreezing
open PancakeQuadraticFourierSupport FourierPressureTiltEnergy FourierPressureLocalization
open PressureTracePatchEnergy LocalPressureCommutator FourierEllipticProductEnergy
open LocalPressureEllipticBudget FourierResolventSmoothing PressurePatchSmoothing
open WeightedPressureL2Replacement Mettapedia.Analysis.QuadraticWeightStability

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {ι : Type*} [Fintype ι]

theorem approximationError_smooth_le (p : ι → C(T3, ℂ)) (c : ι → FourierCoeff (Fin 3))
    (epsilon : ℝ) (he : 0 ≤ epsilon) :
    approximationError p (fun i ↦ smoothCutoff epsilon (c i)) ≤
      2 * approximationError p c + epsilon / 2 * (∑ i, coordinateEnergy (c i).support (c i)) := by
  have hcell (i : ι) := integral_sub_sq_le volume
    (fourierPolynomial (smoothCutoff epsilon (c i))) (fourierPolynomial (c i)) (p i)
  simp_rw [norm_sub_rev (fourierPolynomial (smoothCutoff epsilon (c _)) _) (fourierPolynomial (c _) _)] at hcell
  have hbound (i : ι) := integral_error_sq_le epsilon he (c i)
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦
    show (∫ x : T3, ‖fourierPolynomial (smoothCutoff epsilon (c i)) x - p i x‖ ^ 2) ≤
      2 * (∫ x : T3, ‖fourierPolynomial (c i) x - p i x‖ ^ 2) +
        epsilon / 2 * coordinateEnergy (c i).support (c i) by
      linarith only [hcell i, hbound i])
  simpa only [approximationError, Finset.sum_add_distrib, ← Finset.mul_sum] using h

def derivativeCost (epsilon eta : ℝ) (chi : Wavevector → ℂ) (K : Finset Wavevector)
    (u : FourierVelocity) : ℝ :=
  1536 * potentialCoordinateBound chi K u ^ 2 +
    72 / epsilon * ‖potentialField chi K u‖ ^ 2 +
    2 * epsilon * ‖pressureField chi K u‖ ^ 2 +
    8 * epsilon * eta ^ 2 * ‖traceField chi K u‖ ^ 2

def replacementCost (eta : ℝ) (chi : Wavevector → ℂ) (K : Finset Wavevector)
    (u : FourierVelocity) : ℝ :=
  8 * ‖pressureField chi K u‖ ^ 2 + 32 * eta ^ 2 * ‖traceField chi K u‖ ^ 2

theorem derivativeCost_nonneg (epsilon eta : ℝ) (he : 0 ≤ epsilon)
    (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity) :
    0 ≤ derivativeCost epsilon eta chi K u := by
  unfold derivativeCost
  positivity

theorem replacementCost_nonneg (eta : ℝ) (chi : Wavevector → ℂ) (K : Finset Wavevector)
    (u : FourierVelocity) : 0 ≤ replacementCost eta chi K u := by
  unfold replacementCost
  positivity

theorem integral_weighted_tilt_le_smoothed (p : ι → C(T3, ℂ)) (c : ι → FourierCoeff (Fin 3))
    (a : T3 → ℝ) (ha : Continuous a) (han : ∀ x, 0 ≤ a x)
    (e : T3 → R3) (he : ∀ x, ‖e x‖ = 1)
    (hP : Continuous (fun x ↦ Real.sqrt (a x) • InnerProductSpace.rankOne ℝ (e x) (e x)))
    (f : ι → R3) (hf : ∀ i, ‖f i‖ = 1) (rho : ℝ)
    (hmass : ∀ x, (∑ i, ‖p i x‖ ^ 2) = a x)
    (hline : ∀ x, (∑ i, ‖p i x‖ ^ 2 * lineDistanceSq (e x) (f i)) ≤ rho ^ 2)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity)
    (hK : ∀ q, -q ∈ K ↔ q ∈ K) (eta : ℝ) (heta : 0 ≤ eta) :
    (∫ x : T3, a x *
      ‖lineRemainder (e x) (filteredPressureOperator chi K u x (e x))‖ ^ 2) ≤
        16 * eta ^ 2 * (∫ x : T3, a x * realPressureTrace chi K u x ^ 2) +
          8 * (∑ i, tiltTailTraceEnergy (smoothCutoff epsilon (c i)) chi K u (f i) eta) +
          derivativeCost epsilon eta chi K u * (∑ i, coordinateEnergy (c i).support (c i)) +
          replacementCost eta chi K u * approximationError p c +
          32 * rho ^ 2 * hessianEnergy chi K u := by
  have h := integral_weighted_tilt_le_with_tail p (fun i ↦ smoothCutoff epsilon (c i))
    a ha han e he hP f hf rho hmass hline chi K u hK eta heta
  have hc := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦
    tiltCommutatorEnergy_smooth_le epsilon hepsilon (c i) chi K u (f i) (hf i))
  simp only [← Finset.mul_sum] at hc
  have herr := mul_le_mul_of_nonneg_left (approximationError_smooth_le p c epsilon hepsilon.le)
    (show 0 ≤ 4 * ‖pressureField chi K u‖ ^ 2 + 16 * eta ^ 2 * ‖traceField chi K u‖ ^ 2 by positivity)
  unfold derivativeCost replacementCost
  simp only [div_eq_mul_inv] at hc ⊢
  nlinarith only [h, hc, herr]

end Mettapedia.FluidDynamics.NavierStokes.SmoothedPressureL2Budget
