import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierTranslationCurve
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeWeakDiffusionLimit

/-!
# Real linear images of the uniform Fourier diffusion approximation

The finite Fourier construction survives real continuous linear maps,
including the real matrix-to-strain operator and real-part vorticity map.
The uniform error is constructed explicitly and proved to vanish.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeMappedFourierDiffusion

open scoped Topology
open Filter PeriodicFourierTriad PancakeFourierTranslationCurve
open PancakeCentralDifferenceLimit PancakeWeakDiffusionLimit

local notation "T3" => UnitAddTorus (Fin 3)

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

def mappedField (Q : E →L[ℝ] V) (modes : Finset Wavevector) (a : Wavevector → E) : T3 → V :=
  fun x ↦ Q (fourierField modes a x)

def mappedSecond (Q : E →L[ℝ] V) (modes : Finset Wavevector) (a : Wavevector → E)
    (j : Fin 3) : T3 → V := mappedField Q modes (derivativeCoeff j (derivativeCoeff j a))

def uniformError (modes : Finset Wavevector) (a : Wavevector → E) (j : Fin 3)
    (C h : ℝ) : ℝ :=
  C * ‖centralDifference (translationCurve modes a j) h -
    fourierField modes (derivativeCoeff j (derivativeCoeff j a))‖

omit [IsScalarTower ℝ ℂ E] in
theorem continuous_mappedField (Q : E →L[ℝ] V) (modes : Finset Wavevector) (a : Wavevector → E) :
    Continuous (mappedField Q modes a) := Q.continuous.comp (fourierField modes a).continuous

omit [IsScalarTower ℝ ℂ E] in
theorem centralDirection_mappedField (Q : E →L[ℝ] V) (modes : Finset Wavevector)
    (a : Wavevector → E) (j : Fin 3) (h : ℝ) (x : T3) :
    centralDirection (mappedField Q modes a) (coordinateShift j h) h x =
      Q (centralDifference (translationCurve modes a j) h x) := by
  simp only [centralDirection, mappedField, centralDifference, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, ContinuousMap.add_apply, translationCurve_apply,
    translationCurve_zero, coordinateShift_neg, map_smul, map_sub, map_add]
  module

theorem norm_mappedField_increment_le (Q : E →L[ℝ] V) (modes : Finset Wavevector)
    (a : Wavevector → E) (j : Fin 3) (C h : ℝ) (x : T3) (hC : 0 ≤ C)
    (hQ : ∀ v, ‖Q v‖ ≤ C * ‖v‖) :
    ‖mappedField Q modes a (x + coordinateShift j h) - mappedField Q modes a x‖ ≤
      (C * ∑ q ∈ modes, ‖derivativeCoeff j a q‖) * |h| := by
  have he := (translationCurve modes a j h - fourierField modes a).norm_coe_le_norm x
  have hm := norm_translationCurve_sub_zero_le modes a j h
  change ‖Q (fourierField modes a (x + coordinateShift j h)) - Q (fourierField modes a x)‖ ≤ _
  rw [← map_sub]
  apply (hQ _).trans
  have he' : ‖fourierField modes a (x + coordinateShift j h) - fourierField modes a x‖ ≤
      (∑ q ∈ modes, ‖derivativeCoeff j a q‖) * |h| := by
    simpa only [ContinuousMap.sub_apply, translationCurve_apply] using he.trans hm
  calc
    _ ≤ C * ((∑ q ∈ modes, ‖derivativeCoeff j a q‖) * |h|) :=
      mul_le_mul_of_nonneg_left he' hC
    _ = _ := by ring

omit [IsScalarTower ℝ ℂ E] in
theorem norm_mappedSecond_sub_central_le (Q : E →L[ℝ] V) (modes : Finset Wavevector)
    (a : Wavevector → E) (j : Fin 3) (C h : ℝ) (x : T3) (hC : 0 ≤ C)
    (hQ : ∀ v, ‖Q v‖ ≤ C * ‖v‖) :
    ‖mappedSecond Q modes a j x -
      centralDirection (mappedField Q modes a) (coordinateShift j h) h x‖ ≤
      uniformError modes a j C h := by
  rw [centralDirection_mappedField]
  unfold mappedSecond mappedField uniformError
  rw [← map_sub]
  apply (hQ _).trans
  have he := (centralDifference (translationCurve modes a j) h -
    fourierField modes (derivativeCoeff j (derivativeCoeff j a))).norm_coe_le_norm x
  rw [ContinuousMap.sub_apply, norm_sub_rev] at he
  exact mul_le_mul_of_nonneg_left he hC

theorem uniformError_tendsto (modes : Finset Wavevector) (a : Wavevector → E)
    (j : Fin 3) (C : ℝ) : Tendsto (uniformError modes a j C) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  unfold uniformError
  simpa only [mul_zero] using
    (centralDifference_uniform_error_tendsto modes a j).const_mul C

theorem hasDerivAt_mappedField_shift (Q : E →L[ℝ] V) (modes : Finset Wavevector)
    (a : Wavevector → E) (j : Fin 3) (h : ℝ) (x : T3) :
    HasDerivAt (fun t ↦ mappedField Q modes a (x + coordinateShift j t))
      (mappedField Q modes (derivativeCoeff j a) (x + coordinateShift j h)) h := by
  have he := (ContinuousMap.evalCLM (R := ℝ) (M := E) x).hasFDerivAt.comp_hasDerivAt h
    (hasDerivAt_translationCurve modes a j h)
  have hm := Q.hasFDerivAt.comp_hasDerivAt h he
  change HasDerivAt (fun t ↦ Q (translationCurve modes a j t x))
    (Q (translationCurve modes (derivativeCoeff j a) j h x)) h at hm
  simpa only [translationCurve_apply, mappedField] using hm

end Mettapedia.FluidDynamics.NavierStokes.PancakeMappedFourierDiffusion
