import Mettapedia.Analysis.QuadraticWeightStability
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierResolventSmoothing
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPressureEllipticBudget

/-!
# Pressure localization after resolvent smoothing

Smoothing costs are measured against the actual continuous pressure fields.
The Hessian supremum controls the physical localization error, while the
potential and its gradient control the elliptic commutator. These norms
are not asserted to be uniform in the pressure truncation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressurePatchSmoothing

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization
open PancakeAnisotropyDepletion LocalPressureCommutator
open FourierPressureTiltEnergy FourierPressureHessianEnergy FourierPressurePatchEnergy
open PressureTracePatchEnergy FourierPressureLocalization FourierEllipticProductEnergy
open LocalPressureEllipticBudget FourierResolventSmoothing
open Mettapedia.Analysis.QuadraticWeightStability

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def pressureField (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity) :
    C(T3, R3 →L[ℝ] R3) :=
  ⟨filteredPressureOperator chi K u, continuous_filteredPressureOperator chi K u⟩

def traceField (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity) : C(T3, ℝ) :=
  ⟨realPressureTrace chi K u, continuous_realPressureTrace chi K u⟩

theorem transverse_sq_le (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity)
    (e : R3) (he : ‖e‖ = 1) (x : T3) :
    ‖lineRemainder e (filteredPressureOperator chi K u x e)‖ ^ 2 ≤ ‖pressureField chi K u‖ ^ 2 := by
  apply pow_le_pow_left₀ (norm_nonneg _)
  apply (norm_lineRemainder_le e _ he).trans
  have h := (filteredPressureOperator chi K u x).le_opNorm e
  rw [he, mul_one] at h
  exact h.trans ((pressureField chi K u).norm_coe_le_norm x)

theorem frozenPatchEnergy_le_smooth (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity)
    (hK : ∀ q, -q ∈ K ↔ q ∈ K) (e : R3) (he : ‖e‖ = 1) :
    frozenPatchEnergy c chi K u e ≤ 2 * frozenPatchEnergy (smoothCutoff epsilon c) chi K u e +
      epsilon / 2 * ‖pressureField chi K u‖ ^ 2 * coordinateEnergy c.support c := by
  have h := integral_mul_le volume (fourierPolynomial c) (fourierPolynomial (smoothCutoff epsilon c))
    (fun x ↦ ‖lineRemainder e (filteredPressureOperator chi K u x e)‖ ^ 2)
    ((continuous_transverse_pressure chi K u e).norm.pow 2) (fun _ ↦ sq_nonneg _)
    (‖pressureField chi K u‖ ^ 2) (transverse_sq_le chi K u e he)
  have herr := mul_le_mul_of_nonneg_left (integral_error_sq_le epsilon hepsilon c)
    (show 0 ≤ 2 * ‖pressureField chi K u‖ ^ 2 by positivity)
  have hpoly (b : FourierCoeff (Fin 3)) (x : T3) : ‖fourierPolynomial b x‖ ^ 2 = quadraticWeight b x :=
    (Complex.normSq_eq_norm_sq _).symm
  simp only [hpoly,
    integral_frozen_patch_eq _ chi K u _ hK] at h
  nlinarith only [h, herr]

theorem tracePatchEnergy_smooth_le (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity)
    (hK : ∀ q, -q ∈ K ↔ q ∈ K) :
    tracePatchEnergy (smoothCutoff epsilon c) chi K u ≤ 2 * tracePatchEnergy c chi K u +
      epsilon / 2 * ‖traceField chi K u‖ ^ 2 * coordinateEnergy c.support c := by
  have hb (x : T3) : realPressureTrace chi K u x ^ 2 ≤ ‖traceField chi K u‖ ^ 2 := by
    have h : ‖realPressureTrace chi K u x‖ ^ 2 ≤ ‖traceField chi K u‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ((traceField chi K u).norm_coe_le_norm x) 2
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have h := integral_mul_le volume (fourierPolynomial (smoothCutoff epsilon c)) (fourierPolynomial c)
    (fun x ↦ realPressureTrace chi K u x ^ 2) ((continuous_realPressureTrace chi K u).pow 2)
    (fun _ ↦ sq_nonneg _) (‖traceField chi K u‖ ^ 2) hb
  simp_rw [norm_sub_rev (fourierPolynomial (smoothCutoff epsilon c) _) (fourierPolynomial c _)] at h
  have herr := mul_le_mul_of_nonneg_left (integral_error_sq_le epsilon hepsilon c)
    (show 0 ≤ 2 * ‖traceField chi K u‖ ^ 2 by positivity)
  have hpoly (b : FourierCoeff (Fin 3)) (x : T3) : ‖fourierPolynomial b x‖ ^ 2 = quadraticWeight b x :=
    (Complex.normSq_eq_norm_sq _).symm
  simp only [hpoly,
    ← tracePatchEnergy_eq_integral _ chi K u hK] at h
  nlinarith only [h, herr]

theorem tiltCommutatorEnergy_smooth_le (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity)
    (e : R3) (he : ‖e‖ = 1) :
    tiltCommutatorEnergy (smoothCutoff epsilon c) chi K u e ≤
      (192 * potentialCoordinateBound chi K u ^ 2 + 9 / epsilon * ‖potentialField chi K u‖ ^ 2) *
        coordinateEnergy c.support c := by
  have h := tiltCommutatorEnergy_le_derivative_cost (smoothCutoff epsilon c) chi K u e he
  have hg := mul_le_mul_of_nonneg_left (coordinateEnergy_smooth_le epsilon hepsilon.le c)
    (show 0 ≤ 192 * potentialCoordinateBound chi K u ^ 2 by positivity)
  have hh := mul_le_mul_of_nonneg_left (secondCoordinateEnergy_smooth_le epsilon hepsilon c)
    (show 0 ≤ 36 * ‖potentialField chi K u‖ ^ 2 by positivity)
  calc
    _ ≤ 192 * potentialCoordinateBound chi K u ^ 2 * coordinateEnergy c.support c +
        36 * ‖potentialField chi K u‖ ^ 2 * (1 / (4 * epsilon) * coordinateEnergy c.support c) :=
      h.trans (add_le_add hg hh)
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PressurePatchSmoothing
