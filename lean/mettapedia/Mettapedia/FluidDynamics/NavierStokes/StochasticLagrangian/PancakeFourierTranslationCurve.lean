import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCentralDifferenceLimit
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierStrainGradient

/-!
# Uniform spatial central differences of actual finite Fourier fields

Translations form a smooth curve in the normed space of continuous fields.
Banach-valued Taylor expansion therefore gives a uniform spatial limit,
not merely pointwise convergence. The second-derivative coefficients are
constructed from the physical unit-torus Fourier derivative phase.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFourierTranslationCurve

open scoped Topology
open Filter PancakeCentralDifferenceLimit PeriodicFourierTriad PancakePeriodicVorticityEquation
open PancakeFourierMaterialPaths PancakeFourierStrainGradient

local notation "T3" => UnitAddTorus (Fin 3)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def modeField (q : Wavevector) (a : E) : C(T3, E) :=
  ⟨fun x ↦ UnitAddTorus.mFourier q x • a, by fun_prop⟩

def fourierField (modes : Finset Wavevector) (a : Wavevector → E) : C(T3, E) :=
  ∑ q ∈ modes, modeField q (a q)

def translationCurve (modes : Finset Wavevector) (a : Wavevector → E) (j : Fin 3)
    (h : ℝ) : C(T3, E) :=
  ∑ q ∈ modes, Complex.exp (unitTorusDerivativePhase * (q j : ℂ) * (h : ℂ)) • modeField q (a q)

def derivativeCoeff (j : Fin 3) (a : Wavevector → E) (q : Wavevector) : E :=
  (unitTorusDerivativePhase * (q j : ℂ)) • a q

def coordinateShift (j : Fin 3) (h : ℝ) : T3 := torusPoint (coordinateLine 0 j h)

theorem coordinateShift_neg (j : Fin 3) (h : ℝ) :
    coordinateShift j (-h) = -coordinateShift j h := by
  ext i
  by_cases hij : i = j <;> simp [coordinateShift, torusPoint, coordinateLine, hij]

theorem modeField_smul (q : Wavevector) (a : E) (c : ℂ) :
    modeField q (c • a) = c • modeField q a := by
  ext x
  simp [modeField, smul_smul, mul_comm]

theorem translationCurve_zero (modes : Finset Wavevector) (a : Wavevector → E) (j : Fin 3) :
    translationCurve modes a j 0 = fourierField modes a := by
  simp [translationCurve, fourierField]

theorem mFourier_space_add (q : Wavevector) (x y : T3) :
    UnitAddTorus.mFourier q (x + y) = UnitAddTorus.mFourier q x * UnitAddTorus.mFourier q y := by
  simp [UnitAddTorus.mFourier, Pi.add_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem mFourier_coordinateShift (q : Wavevector) (j : Fin 3) (h : ℝ) :
    UnitAddTorus.mFourier q (coordinateShift j h) =
      Complex.exp (unitTorusDerivativePhase * (q j : ℂ) * (h : ℂ)) := by
  rw [coordinateShift, mFourier_torusPoint]
  simp [realModeDot, coordinateLine, mul_ite]
  congr 1
  ring

theorem translationCurve_apply (modes : Finset Wavevector) (a : Wavevector → E)
    (j : Fin 3) (h : ℝ) (x : T3) :
    translationCurve modes a j h x = fourierField modes a (x + coordinateShift j h) := by
  simp only [translationCurve, fourierField, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    modeField, ContinuousMap.coe_mk, mFourier_space_add, mFourier_coordinateShift, smul_smul]
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_comm]

theorem norm_modeField_le (q : Wavevector) (a : E) : ‖modeField q a‖ ≤ ‖a‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg a)).mpr
  intro x
  change ‖UnitAddTorus.mFourier q x • a‖ ≤ _
  rw [norm_smul]
  have h := (UnitAddTorus.mFourier q).norm_coe_le_norm x
  rw [UnitAddTorus.mFourier_norm] at h
  nlinarith [norm_nonneg a]

theorem norm_translationPhase (q : Wavevector) (j : Fin 3) (h : ℝ) :
    ‖Complex.exp (unitTorusDerivativePhase * (q j : ℂ) * (h : ℂ))‖ = 1 := by
  simp [Complex.norm_exp, unitTorusDerivativePhase, Complex.mul_re, Complex.mul_im]

theorem norm_translationCurve_le (modes : Finset Wavevector) (a : Wavevector → E)
    (j : Fin 3) (h : ℝ) : ‖translationCurve modes a j h‖ ≤ ∑ q ∈ modes, ‖a q‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q _
  rw [norm_smul, norm_translationPhase, one_mul]
  exact norm_modeField_le q (a q)

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem contDiff_translationCurve (modes : Finset Wavevector) (a : Wavevector → E)
    (j : Fin 3) : ContDiff ℝ 2 (translationCurve modes a j) := by
  unfold translationCurve
  apply ContDiff.sum
  intro q _
  have hc : ContDiff ℝ 2 (fun h : ℝ ↦
      Complex.exp (unitTorusDerivativePhase * (q j : ℂ) * (h : ℂ))) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  exact hc.smul contDiff_const

theorem hasDerivAt_translationCurve (modes : Finset Wavevector) (a : Wavevector → E)
    (j : Fin 3) (h : ℝ) :
    HasDerivAt (translationCurve modes a j) (translationCurve modes (derivativeCoeff j a) j h) h := by
  have hc := HasDerivAt.fun_sum (u := modes) (fun q _ ↦
    (((hasDerivAt_id h).ofReal_comp.const_mul (unitTorusDerivativePhase * (q j : ℂ))).cexp).smul_const
      (modeField q (a q)))
  apply hc.congr_deriv
  simp only [id_eq, Complex.ofReal_one, mul_one, translationCurve, derivativeCoeff, modeField_smul, smul_smul]

theorem deriv_translationCurve (modes : Finset Wavevector) (a : Wavevector → E) (j : Fin 3) :
    deriv (translationCurve modes a j) = translationCurve modes (derivativeCoeff j a) j :=
  funext (fun h ↦ (hasDerivAt_translationCurve modes a j h).deriv)

theorem deriv2_translationCurve_zero (modes : Finset Wavevector) (a : Wavevector → E) (j : Fin 3) :
    deriv (deriv (translationCurve modes a j)) 0 =
      fourierField modes (derivativeCoeff j (derivativeCoeff j a)) := by
  rw [deriv_translationCurve, deriv_translationCurve, translationCurve_zero]

theorem norm_translationCurve_sub_zero_le (modes : Finset Wavevector) (a : Wavevector → E)
    (j : Fin 3) (h : ℝ) :
    ‖translationCurve modes a j h - fourierField modes a‖ ≤
      (∑ q ∈ modes, ‖derivativeCoeff j a q‖) * |h| := by
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ht : t ∈ Set.univ) ↦ (hasDerivAt_translationCurve modes a j t).hasDerivWithinAt)
    (fun t (_ht : t ∈ Set.univ) ↦ norm_translationCurve_le modes (derivativeCoeff j a) j t)
    convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ h)
  simpa only [translationCurve_zero, sub_zero, Real.norm_eq_abs] using hm

/-- Convergence in the continuous-field norm: spatially uniform. -/
theorem centralDifference_translationCurve_tendsto (modes : Finset Wavevector)
    (a : Wavevector → E) (j : Fin 3) :
    Tendsto (centralDifference (translationCurve modes a j)) (𝓝[≠] (0 : ℝ))
      (𝓝 (fourierField modes (derivativeCoeff j (derivativeCoeff j a)))) := by
  have h := centralDifference_tendsto (translationCurve modes a j) (contDiff_translationCurve modes a j)
  rwa [deriv2_translationCurve_zero] at h

theorem centralDifference_uniform_error_tendsto (modes : Finset Wavevector)
    (a : Wavevector → E) (j : Fin 3) :
    Tendsto (fun h ↦ ‖centralDifference (translationCurve modes a j) h -
      fourierField modes (derivativeCoeff j (derivativeCoeff j a))‖) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have h := (centralDifference_translationCurve_tendsto modes a j).sub_const
    (fourierField modes (derivativeCoeff j (derivativeCoeff j a)))
  simpa only [sub_self, norm_zero] using h.norm

end Mettapedia.FluidDynamics.NavierStokes.PancakeFourierTranslationCurve
