import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicFourierWeakDerivative
import Mettapedia.Analysis.UnitTorusFourierEnergy

/-!
# Derivative-energy contraction under finite Fourier restriction

A real periodic locally Lipschitz field has square-integrable coordinate
derivatives. Integration by parts and Bessel's inequality bound every
finite restriction of its actual Fourier coefficients by its physical
gradient energy. The unit-torus phase is retained explicitly.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierGradientEnergy

open scoped BigOperators
open MeasureTheory
open Mettapedia.Analysis.UnitTorusFourierEnergy Mettapedia.Analysis.FiniteMultiplierLocalization
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakeFourierMaterialPaths
open PancakeFourierTranslationCurve PancakeHaarTransportRate PancakePeriodicLipschitz
open PeriodicFourierWeakDerivative FourierEllipticProductCoefficients FourierEllipticProductEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def realFourierCoeff (f : T3 → ℝ) : Wavevector → ℂ :=
  UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ))

def gradientSquare (f : T3 → ℝ) (x : T3) : ℝ :=
  ∑ j : Fin 3, shiftRate f (coordinateShift j) x ^ 2

theorem memLp_coordinateRate (f : T3 → ℝ) (j : Fin 3)
    (hf : Continuous f) (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) :
    MemLp (shiftRate f (coordinateShift j)) 2 := by
  obtain ⟨C, hC⟩ := exists_uniform_coordinate_lipschitz f hfL
  apply MemLp.of_bound (measurable_shiftRate f _ hf (continuous_coordinateShift j)).aestronglyMeasurable C
  filter_upwards [] with x
  exact norm_deriv_le_of_lipschitzOn (Icc_mem_nhds (by norm_num) (by norm_num)) (hC j x)

theorem integrable_gradientSquare (f : T3 → ℝ)
    (hf : Continuous f) (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) :
    Integrable (gradientSquare f) :=
  integrable_finsetSum _ (fun j _ ↦ (memLp_coordinateRate f j hf hfL).integrable_sq)

theorem coordinateEnergy_le (f : T3 → ℝ) (j : Fin 3)
    (hf : Continuous f) (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r)))
    (P : Finset Wavevector) :
    ‖unitTorusDerivativePhase‖ ^ 2 * scalarEnergy P (coordinateMultiplier (realFourierCoeff f) j) ≤
      ∫ x : T3, shiftRate f (coordinateShift j) x ^ 2 := by
  have hm : MemLp (fun x : T3 ↦ (shiftRate f (coordinateShift j) x : ℂ)) 2 :=
    Complex.ofRealCLM.comp_memLp' (memLp_coordinateRate f j hf hfL)
  have h := sum_norm_mFourierCoeff_sq_le _ hm P
  simp_rw [mFourierCoeff_coordinateRate f j hf hfL, norm_mul, mul_pow] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  simpa only [scalarEnergy, coordinateMultiplier, realFourierCoeff, norm_mul, mul_pow,
    Finset.mul_sum, mul_assoc] using h

theorem gradientEnergy_le (f : T3 → ℝ)
    (hf : Continuous f) (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r)))
    (P : Finset Wavevector) :
    ‖unitTorusDerivativePhase‖ ^ 2 * coordinateEnergy P (realFourierCoeff f) ≤
      ∫ x : T3, gradientSquare f x := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
    coordinateEnergy_le f j hf hfL P)
  rw [← Finset.mul_sum, ← integral_finsetSum _
    (fun j _ ↦ (memLp_coordinateRate f j hf hfL).integrable_sq)] at h
  exact h

end Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierGradientEnergy
