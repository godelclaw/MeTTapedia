import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicWeakDerivative
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierCoordinateDerivatives

/-!
# Fourier coefficients of weak coordinate derivatives on the unit torus

Periodic integration by parts applies to a real locally Lipschitz field
and a smooth complex character. The derivative coefficient includes the
physical unit-torus phase. The scalar field need not be continuously
differentiable, so the result applies to spectral-cutoff patches at corners.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierWeakDerivative

open scoped BigOperators
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakeFourierMaterialPaths
open PancakeFourierTranslationCurve PancakeHaarTransportRate PancakePeriodicWeakDerivative
open FourierCoordinateDerivatives FourierEllipticProductCoefficients
open PancakeMisalignmentEnergyBridge
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_coordinateRate_mul_complex (f : T3 → ℝ) (g g' : T3 → ℂ) (j : Fin 3)
    (hf : Continuous f) (hg : Continuous g) (hg' : Continuous g')
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r)))
    (hgL : LocallyLipschitz (fun r : X3 ↦ g (torusPoint r)))
    (hd : ∀ x, HasDerivAt (fun h : ℝ ↦ g (x + coordinateShift j h)) (g' x) 0) :
    (∫ x : T3, (shiftRate f (coordinateShift j) x : ℂ) * g x) =
      -(∫ x : T3, (f x : ℂ) * g' x) := by
  have hdre (x : T3) : shiftRate (fun y ↦ (g y).re) (coordinateShift j) x = (g' x).re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hd x)).deriv
  have hdim (x : T3) : shiftRate (fun y ↦ (g y).im) (coordinateShift j) x = (g' x).im :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 (hd x)).deriv
  have hr := integral_coordinateRate_mul f (fun x ↦ (g x).re) j hf
    (Complex.continuous_re.comp hg) hfL (Complex.reCLM.lipschitz.locallyLipschitz.comp hgL)
  have hi := integral_coordinateRate_mul f (fun x ↦ (g x).im) j hf
    (Complex.continuous_im.comp hg) hfL (Complex.imCLM.lipschitz.locallyLipschitz.comp hgL)
  simp_rw [hdre] at hr
  simp_rw [hdim] at hi
  have hleft : Integrable (fun x : T3 ↦ (shiftRate f (coordinateShift j) x : ℂ) * g x) := by
    rw [← integrableOn_univ]
    exact (Complex.ofRealCLM.integrable_comp (integral_coordinateRate_zero f j hf hfL).1
      ).integrableOn.mul_continuousOn hg.continuousOn isCompact_univ
  have hright : Integrable (fun x : T3 ↦ (f x : ℂ) * g' x) :=
    ((Complex.continuous_ofReal.comp hf).mul hg').integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply Complex.ext
  · have hl : (∫ x : T3, (shiftRate f (coordinateShift j) x : ℂ) * g x).re =
        ∫ x : T3, ((shiftRate f (coordinateShift j) x : ℂ) * g x).re :=
      (Complex.reCLM.integral_comp_comm hleft).symm
    have hr' : (∫ x : T3, (f x : ℂ) * g' x).re = ∫ x : T3, ((f x : ℂ) * g' x).re :=
      (Complex.reCLM.integral_comp_comm hright).symm
    rw [hl, Complex.neg_re, hr']
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hr
  · have hl : (∫ x : T3, (shiftRate f (coordinateShift j) x : ℂ) * g x).im =
        ∫ x : T3, ((shiftRate f (coordinateShift j) x : ℂ) * g x).im :=
      (Complex.imCLM.integral_comp_comm hleft).symm
    have hi' : (∫ x : T3, (f x : ℂ) * g' x).im = ∫ x : T3, ((f x : ℂ) * g' x).im :=
      (Complex.imCLM.integral_comp_comm hright).symm
    rw [hl, Complex.neg_im, hi']
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using hi

theorem hasDerivAt_character_shift (q : Wavevector) (j : Fin 3) (x : T3) :
    HasDerivAt (fun h : ℝ ↦ UnitAddTorus.mFourier q (x + coordinateShift j h))
      (unitTorusDerivativePhase * (q j : ℂ) * UnitAddTorus.mFourier q x) 0 := by
  simpa only [finiteScalarFourierReconstruction, Finset.sum_singleton, coordinateMultiplier,
    mul_one, one_mul, coordinateShift_zero, add_zero, mul_assoc, mul_comm, mul_left_comm] using
    hasDerivAt_reconstruction_shift {q} (fun _ ↦ (1 : ℂ)) j x 0

theorem locallyLipschitz_character (q : Wavevector) :
    LocallyLipschitz (fun r : X3 ↦ UnitAddTorus.mFourier q (torusPoint r)) := by
  have h : ContDiff ℝ 1 (fun r : X3 ↦ UnitAddTorus.mFourier q (torusPoint r)) := by
    simp only [mFourier_torusPoint]
    have hdot : ContDiff ℝ 1 (realModeDot q) := by unfold realModeDot; fun_prop
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hdot)).cexp
  exact h.locallyLipschitz

theorem mFourierCoeff_coordinateRate (f : T3 → ℝ) (j : Fin 3)
    (hf : Continuous f) (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) (q : Wavevector) :
    UnitAddTorus.mFourierCoeff (fun x ↦ (shiftRate f (coordinateShift j) x : ℂ)) q =
      unitTorusDerivativePhase * (q j : ℂ) * UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) q := by
  have h := integral_coordinateRate_mul_complex f (UnitAddTorus.mFourier (-q))
    (fun x ↦ unitTorusDerivativePhase * ((-q) j : ℂ) * UnitAddTorus.mFourier (-q) x) j hf
    (UnitAddTorus.mFourier (-q)).continuous (continuous_const.mul (UnitAddTorus.mFourier (-q)).continuous)
    hfL (locallyLipschitz_character (-q)) (hasDerivAt_character_shift (-q) j)
  have hid (x : T3) : (f x : ℂ) *
      (unitTorusDerivativePhase * ((-q) j : ℂ) * UnitAddTorus.mFourier (-q) x) =
        -(unitTorusDerivativePhase * (q j : ℂ)) * (UnitAddTorus.mFourier (-q) x * (f x : ℂ)) := by
    simp only [Pi.neg_apply, Int.cast_neg]
    ring
  simp_rw [hid] at h
  rw [integral_const_mul, neg_mul, neg_neg] at h
  simpa only [UnitAddTorus.mFourierCoeff, smul_eq_mul, mul_comm (UnitAddTorus.mFourier (-q) _)] using h

end Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierWeakDerivative
