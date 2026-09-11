import Mettapedia.Analysis.UnitTorusTranslationEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicFourierGradientEnergy

/-!
# Spatial translation controlled by actual weak gradient energy

The locally Lipschitz periodic field need not have an absolutely summable
Fourier series. Its actual almost-everywhere coordinate derivatives supply
the gradient budget used by the full Fourier translation theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicTranslationEnergy

open MeasureTheory
open PeriodicFourierTriad PancakeFourierMaterialPaths PeriodicFourierGradientEnergy
open FourierEllipticProductEnergy FourierEllipticProductCoefficients
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_translate_sub_sq_le (f : T3 → ℝ) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) (a : T3) :
    (∫ x : T3, (f (x + a) - f x) ^ 2) ≤ 3 * ‖a‖ ^ 2 * ∫ x : T3, gradientSquare f x := by
  have h := Mettapedia.Analysis.UnitTorusTranslationEnergy.integral_norm_translate_sub_sq_le
    (fun x ↦ (f x : ℂ)) (Complex.continuous_ofReal.comp hf)
    (∫ x : T3, gradientSquare f x) (fun P ↦ ?_) a
  · simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Fintype.card_fin, Nat.cast_ofNat] using h
  have he := gradientEnergy_le f hf hfL P
  rw [PancakeIncomingLowSourceEnergy.norm_derivativePhase] at he
  convert! he using 1
  simp only [coordinateEnergy, scalarEnergy, coordinateMultiplier, realFourierCoeff,
    norm_mul, mul_pow, Complex.norm_intCast, sq_abs, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem integral_sub_translate_sq_le (f : T3 → ℝ) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) (a : T3) :
    (∫ x : T3, (f x - f (x - a)) ^ 2) ≤ 3 * ‖a‖ ^ 2 * ∫ x : T3, gradientSquare f x := by
  have h := integral_translate_sub_sq_le f hf hfL (-a)
  have he (x : T3) : (f (x + -a) - f x) ^ 2 = (f x - f (x - a)) ^ 2 := by
    rw [sub_eq_add_neg x a]
    ring
  simpa only [he, norm_neg] using h

theorem sum_integral_sub_translate_sq_le {ι : Type*} [Fintype ι]
    (f : ι → T3 → ℝ) (hf : ∀ i, Continuous (f i))
    (hfL : ∀ i, LocallyLipschitz (fun r : X3 ↦ f i (torusPoint r))) (a : T3) :
    (∑ i, ∫ x : T3, (f i x - f i (x - a)) ^ 2) ≤
      3 * ‖a‖ ^ 2 * ∑ i, ∫ x : T3, gradientSquare (f i) x := by
  simpa only [Finset.mul_sum] using
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦
      integral_sub_translate_sq_le (f i) (hf i) (hfL i) a)

end Mettapedia.FluidDynamics.NavierStokes.PeriodicTranslationEnergy
