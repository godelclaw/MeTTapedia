import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteSpatialCurl
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Fourier coefficients of actual spatial derivatives

Haar translation invariance identifies the Fourier coefficient of a
translated continuous field. Differentiating that integral, with the
continuous derivative supplying its uniform bound, recovers the physical
Fourier derivative factor. The derivative identity is an ordinary
HasDerivAt hypothesis on the spatial field, not an assumed symbol law.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalFourierDerivative

open MeasureTheory Filter
open scoped Topology
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakeFourierTranslationCurve
open PancakeHaarTransportRate

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem norm_character (k : Wavevector) (x : T3) : ‖UnitAddTorus.mFourier k x‖ = 1 := by
  simp only [UnitAddTorus.mFourier, fourier_apply, ContinuousMap.coe_mk,
    norm_prod, Circle.norm_coe, Finset.prod_const_one]

theorem norm_fourierCoeff_le (f : C(T3, ℂ)) (k : Wavevector) :
    ‖UnitAddTorus.mFourierCoeff f k‖ ≤ ‖f‖ := by
  apply (norm_integral_le_of_norm_le_const (μ := (volume : Measure T3))
    (Filter.Eventually.of_forall (fun x : T3 ↦ show ‖UnitAddTorus.mFourier (-k) x • f x‖ ≤ ‖f‖ by
      rw [norm_smul, norm_character, one_mul]
      exact f.norm_coe_le_norm x))).trans_eq
  simp only [probReal_univ, mul_one]

theorem fourierCoeff_translation (f : C(T3, ℂ)) (k : Wavevector) (c : T3) :
    UnitAddTorus.mFourierCoeff (fun x ↦ f (x + c)) k =
      UnitAddTorus.mFourier k c * UnitAddTorus.mFourierCoeff f k := by
  have hp : UnitAddTorus.mFourier k c * UnitAddTorus.mFourier (-k) c = 1 := by
    rw [← UnitAddTorus.mFourier_add]
    simp [UnitAddTorus.mFourier]
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  rw [← integral_add_right_eq_self (fun x ↦ UnitAddTorus.mFourier (-k) x * f x) c,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [mFourier_space_add]
  calc
    _ = (UnitAddTorus.mFourier k c * UnitAddTorus.mFourier (-k) c) *
        (UnitAddTorus.mFourier (-k) x * f (x + c)) := by rw [hp, one_mul]
    _ = _ := by ring

theorem fourierCoeff_derivative (f g : C(T3, ℂ)) (j : Fin 3)
    (hd : ∀ x h, HasDerivAt (fun t ↦ f (x + coordinateShift j t)) (g (x + coordinateShift j h)) h)
    (k : Wavevector) :
    UnitAddTorus.mFourierCoeff g k =
      (unitTorusDerivativePhase * (k j : ℂ)) * UnitAddTorus.mFourierCoeff f k := by
  have hc (h : ℝ) : Continuous (fun x : T3 ↦ UnitAddTorus.mFourier (-k) x * f (x + coordinateShift j h)) := by
    fun_prop
  have hg : Continuous (fun x : T3 ↦ UnitAddTorus.mFourier (-k) x * g (x + coordinateShift j 0)) := by
    fun_prop
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure T3)) (s := Set.univ) (x₀ := (0 : ℝ))
    (F := fun h x ↦ UnitAddTorus.mFourier (-k) x * f (x + coordinateShift j h))
    (F' := fun h x ↦ UnitAddTorus.mFourier (-k) x * g (x + coordinateShift j h))
    (bound := fun _ : T3 ↦ ‖g‖) (by simp)
    (Eventually.of_forall (fun h ↦ (hc h).aestronglyMeasurable))
    ((hc 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hg.aestronglyMeasurable
    (Eventually.of_forall (fun x h _ ↦ by
      rw [norm_mul, norm_character, one_mul]
      exact g.norm_coe_le_norm _))
    (integrable_const _) (Eventually.of_forall (fun x h _ ↦ (hd x h).const_mul _))
  have he (h : ℝ) : (∫ x : T3, UnitAddTorus.mFourier (-k) x * f (x + coordinateShift j h)) =
      Complex.exp (unitTorusDerivativePhase * (k j : ℂ) * (h : ℂ)) * UnitAddTorus.mFourierCoeff f k := by
    rw [← mFourier_coordinateShift]
    exact fourierCoeff_translation f k (coordinateShift j h)
  have hp := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul
    (unitTorusDerivativePhase * (k j : ℂ))).cexp).mul_const (UnitAddTorus.mFourierCoeff f k)
  have hi := hint.2
  simp only [he, coordinateShift_zero, add_zero] at hi
  simpa only [id_eq, Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_one,
    mul_one, one_mul, UnitAddTorus.mFourierCoeff, smul_eq_mul] using hi.unique hp

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalFourierDerivative
