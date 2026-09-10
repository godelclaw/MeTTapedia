import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteFourierDerivative
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMappedFourierDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHaarTransportRate
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Uniform second differences of an infinite Fourier field

Two summable coordinate derivatives give a twice continuously
differentiable translation curve in the Banach space of continuous fields.
Its central differences therefore converge uniformly in space. Real
continuous linear images inherit the same constructed error bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.InfiniteFourierDiffusion

open scoped Topology ContDiff
open Filter PeriodicFourierTriad PancakeFourierTranslationCurve
open PancakeCentralDifferenceLimit PancakeWeakDiffusionLimit PancakeInfiniteFourierDerivative
open PancakeHaarTransportRate

local notation "T3" => UnitAddTorus (Fin 3)

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem continuous_fullTranslationCurve (a : Wavevector → E)
    (ha : Summable (fun q ↦ ‖a q‖)) (j : Fin 3) :
    Continuous (fullTranslationCurve id a j) := by
  refine continuous_tsum ?_ ha ?_
  · intro q
    have hc : Continuous (fun h : ℝ ↦
        Complex.exp (PancakePeriodicVorticityEquation.unitTorusDerivativePhase * (q j : ℂ) * (h : ℂ))) := by
      fun_prop
    exact hc.smul continuous_const
  · intro q h
    rw [norm_smul, norm_translationPhase, one_mul]
    exact norm_modeField_le q (a q)

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem fullTranslationCurve_zero (a : Wavevector → E)
    (ha : Summable (fun q ↦ ‖a q‖)) (j : Fin 3) :
    fullTranslationCurve id a j 0 = fullFourierField id a := by
  ext x
  simp only [fullTranslationCurve_apply id a ha, coordinateShift_zero, add_zero]

theorem deriv_fullTranslationCurve (a : Wavevector → E)
    (ha : Summable (fun q ↦ ‖a q‖)) (j : Fin 3)
    (hd : Summable (fun q ↦ ‖indexedDerivativeCoeff id j a q‖)) :
    deriv (fullTranslationCurve id a j) = fullTranslationCurve id (indexedDerivativeCoeff id j a) j :=
  funext (fun h ↦ (hasDerivAt_fullTranslationCurve id a ha j hd h).deriv)

theorem contDiff_fullTranslationCurve (a : Wavevector → E)
    (ha : Summable (fun q ↦ ‖a q‖)) (j : Fin 3)
    (hd : Summable (fun q ↦ ‖indexedDerivativeCoeff id j a q‖))
    (hdd : Summable (fun q ↦ ‖indexedDerivativeCoeff id j (indexedDerivativeCoeff id j a) q‖)) :
    ContDiff ℝ 2 (fullTranslationCurve id a j) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun h ↦ (hasDerivAt_fullTranslationCurve id a ha j hd h).differentiableAt, by simp, ?_⟩
  rw [deriv_fullTranslationCurve a ha j hd, contDiff_one_iff_deriv]
  refine ⟨fun h ↦ (hasDerivAt_fullTranslationCurve id _ hd j hdd h).differentiableAt, ?_⟩
  rw [deriv_fullTranslationCurve _ hd j hdd]
  exact continuous_fullTranslationCurve _ hdd j

def uniformError (a : Wavevector → E) (j : Fin 3) (C h : ℝ) : ℝ :=
  C * ‖centralDifference (fullTranslationCurve id a j) h -
    fullFourierField id (indexedDerivativeCoeff id j (indexedDerivativeCoeff id j a))‖

theorem uniformError_tendsto (a : Wavevector → E)
    (ha : Summable (fun q ↦ ‖a q‖)) (j : Fin 3)
    (hd : Summable (fun q ↦ ‖indexedDerivativeCoeff id j a q‖))
    (hdd : Summable (fun q ↦ ‖indexedDerivativeCoeff id j (indexedDerivativeCoeff id j a) q‖))
    (C : ℝ) : Tendsto (uniformError a j C) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  change Tendsto (fun h ↦ C * ‖centralDifference (fullTranslationCurve id a j) h -
    fullFourierField id (indexedDerivativeCoeff id j (indexedDerivativeCoeff id j a))‖)
    (𝓝[≠] (0 : ℝ)) (𝓝 0)
  have h := centralDifference_tendsto (fullTranslationCurve id a j)
    (contDiff_fullTranslationCurve a ha j hd hdd)
  rw [deriv_fullTranslationCurve a ha j hd, deriv_fullTranslationCurve _ hd j hdd,
    fullTranslationCurve_zero _ hdd j] at h
  simpa only [sub_self, norm_zero, mul_zero] using
    ((h.sub_const (fullFourierField id (indexedDerivativeCoeff id j
      (indexedDerivativeCoeff id j a)))).norm.const_mul C)

def mappedField (Q : E →L[ℝ] V) (a : Wavevector → E) (x : T3) : V := Q (fullFourierField id a x)

def mappedSecond (Q : E →L[ℝ] V) (a : Wavevector → E) (j : Fin 3) (x : T3) : V :=
  Q (fullFourierField id (indexedDerivativeCoeff id j (indexedDerivativeCoeff id j a)) x)

omit [IsScalarTower ℝ ℂ E] in
theorem centralDirection_mappedField (Q : E →L[ℝ] V) (a : Wavevector → E)
    (ha : Summable (fun q ↦ ‖a q‖)) (j : Fin 3) (h : ℝ) (x : T3) :
    centralDirection (mappedField Q a) (coordinateShift j h) h x =
      Q (centralDifference (fullTranslationCurve id a j) h x) := by
  simp only [centralDirection, mappedField, centralDifference, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, ContinuousMap.add_apply, fullTranslationCurve_apply id a ha,
    coordinateShift_zero, add_zero, coordinateShift_neg, map_smul, map_sub, map_add]
  module

omit [IsScalarTower ℝ ℂ E] in
theorem norm_mappedSecond_sub_central_le (Q : E →L[ℝ] V) (a : Wavevector → E)
    (ha : Summable (fun q ↦ ‖a q‖)) (j : Fin 3) (h : ℝ) (x : T3) :
    ‖mappedSecond Q a j x - centralDirection (mappedField Q a) (coordinateShift j h) h x‖ ≤
      uniformError a j ‖Q‖ h := by
  rw [centralDirection_mappedField Q a ha]
  unfold mappedSecond uniformError
  rw [← map_sub]
  apply (Q.le_opNorm _).trans
  have he := (centralDifference (fullTranslationCurve id a j) h -
    fullFourierField id (indexedDerivativeCoeff id j (indexedDerivativeCoeff id j a))).norm_coe_le_norm x
  rw [ContinuousMap.sub_apply, norm_sub_rev] at he
  exact mul_le_mul_of_nonneg_left he (norm_nonneg Q)

end Mettapedia.FluidDynamics.NavierStokes.InfiniteFourierDiffusion
