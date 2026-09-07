import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierTranslationCurve
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Differentiating an actual infinite Fourier field

The Fourier series is constructed in the Banach space of continuous
fields. Summability of the coefficient norms and derivative-coefficient
norms justifies differentiation of its translation curve in that space.
Evaluation then gives the actual coordinate derivative on the torus.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteFourierDerivative

open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakeFourierTranslationCurve

local notation "T3" => UnitAddTorus (Fin 3)

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def indexedDerivativeCoeff (freq : ι → Wavevector) (j : Fin 3) (a : ι → E) (q : ι) : E :=
  (unitTorusDerivativePhase * (freq q j : ℂ)) • a q

def fullFourierField (freq : ι → Wavevector) (a : ι → E) : C(T3, E) := ∑' q, modeField (freq q) (a q)

def fullTranslationCurve (freq : ι → Wavevector) (a : ι → E) (j : Fin 3) (h : ℝ) : C(T3, E) :=
  ∑' q, Complex.exp (unitTorusDerivativePhase * (freq q j : ℂ) * (h : ℂ)) • modeField (freq q) (a q)

theorem summable_modeField (freq : ι → Wavevector) (a : ι → E) (ha : Summable (fun q ↦ ‖a q‖)) :
    Summable (fun q ↦ modeField (freq q) (a q)) :=
  ha.of_norm_bounded (fun q ↦ norm_modeField_le (freq q) (a q))

theorem summable_translationModes (freq : ι → Wavevector) (a : ι → E) (ha : Summable (fun q ↦ ‖a q‖))
    (j : Fin 3) (h : ℝ) :
    Summable (fun q ↦ Complex.exp (unitTorusDerivativePhase * (freq q j : ℂ) * (h : ℂ)) • modeField (freq q) (a q)) := by
  apply ha.of_norm_bounded
  intro q
  rw [norm_smul, norm_translationPhase, one_mul]
  exact norm_modeField_le (freq q) (a q)

theorem fullFourierField_apply (freq : ι → Wavevector) (a : ι → E) (ha : Summable (fun q ↦ ‖a q‖)) (x : T3) :
    fullFourierField freq a x = ∑' q, UnitAddTorus.mFourier (freq q) x • a q :=
  (ContinuousMap.evalCLM (R := ℂ) (M := E) x).map_tsum (summable_modeField freq a ha)

theorem fullTranslationCurve_apply (freq : ι → Wavevector) (a : ι → E) (ha : Summable (fun q ↦ ‖a q‖))
    (j : Fin 3) (h : ℝ) (x : T3) :
    fullTranslationCurve freq a j h x = fullFourierField freq a (x + coordinateShift j h) := by
  change (ContinuousMap.evalCLM (R := ℂ) (M := E) x) (∑' q, _) = _
  rw [(ContinuousMap.evalCLM (R := ℂ) (M := E) x).map_tsum (summable_translationModes freq a ha j h),
    fullFourierField_apply freq a ha]
  apply tsum_congr
  intro q
  change Complex.exp (unitTorusDerivativePhase * (freq q j : ℂ) * (h : ℂ)) •
    (UnitAddTorus.mFourier (freq q) x • a q) = UnitAddTorus.mFourier (freq q) (x + coordinateShift j h) • a q
  rw [mFourier_space_add, mFourier_coordinateShift, smul_smul, mul_comm]

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem hasDerivAt_fullTranslationCurve (freq : ι → Wavevector) (a : ι → E)
    (ha : Summable (fun q ↦ ‖a q‖)) (j : Fin 3)
    (hd : Summable (fun q ↦ ‖indexedDerivativeCoeff freq j a q‖)) (h : ℝ) :
    HasDerivAt (fullTranslationCurve freq a j) (fullTranslationCurve freq (indexedDerivativeCoeff freq j a) j h) h := by
  have hterm (q : ι) (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ Complex.exp (unitTorusDerivativePhase * (freq q j : ℂ) * (s : ℂ)) • modeField (freq q) (a q))
        (Complex.exp (unitTorusDerivativePhase * (freq q j : ℂ) * (t : ℂ)) • modeField (freq q) (indexedDerivativeCoeff freq j a q)) t := by
    have hc := (((hasDerivAt_id t).ofReal_comp.const_mul (unitTorusDerivativePhase * (freq q j : ℂ))).cexp).smul_const
      (modeField (freq q) (a q))
    apply hc.congr_deriv
    simp only [id_eq, Complex.ofReal_one, mul_one, indexedDerivativeCoeff, modeField_smul, smul_smul]
  exact hasDerivAt_tsum hd hterm (fun q t ↦ by
    rw [norm_smul, norm_translationPhase, one_mul]
    exact norm_modeField_le (freq q) (indexedDerivativeCoeff freq j a q)) (summable_translationModes freq a ha j 0) h

theorem hasDerivAt_fullFourierField_shift (freq : ι → Wavevector) (a : ι → E)
    (ha : Summable (fun q ↦ ‖a q‖)) (j : Fin 3)
    (hd : Summable (fun q ↦ ‖indexedDerivativeCoeff freq j a q‖)) (h : ℝ) (x : T3) :
    HasDerivAt (fun t ↦ fullFourierField freq a (x + coordinateShift j t))
      (fullFourierField freq (indexedDerivativeCoeff freq j a) (x + coordinateShift j h)) h := by
  have he := (ContinuousMap.evalCLM (R := ℝ) (M := E) x).hasFDerivAt.comp_hasDerivAt h
    (hasDerivAt_fullTranslationCurve freq a ha j hd h)
  change HasDerivAt (fun t ↦ fullTranslationCurve freq a j t x)
    (fullTranslationCurve freq (indexedDerivativeCoeff freq j a) j h x) h at he
  simpa only [fullTranslationCurve_apply freq a ha, fullTranslationCurve_apply freq (indexedDerivativeCoeff freq j a) hd] using he

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteFourierDerivative
