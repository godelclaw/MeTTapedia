import Mettapedia.Analysis.UnitTorusPolynomialEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ParallelHeatPolynomial

/-!
# Differential energy of finite Fourier polynomials

The coordinate derivative is the physical unit-torus derivative, with
the factor `2 pi`. Parseval gives a bound uniform in the support size.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPolynomialDifferential

open scoped Pointwise
open MeasureTheory Mettapedia.Analysis UnitTorusPolynomialEnergy
open PeriodicFourierTriad PancakeQuadraticFourierSupport FourierPolynomialRealAlgebra
open PancakePeriodicVorticityEquation PancakeFrequencyProjectorCommutator PancakeCurlOutputTail
open PancakeFourierTranslationCurve
open ParallelHeatFlow (derivativeCoeff derivativeCoeff_apply support_derivativeCoeff_subset)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem fourierPolynomial_eq_fourierField (a : FourierCoeff (Fin 3)) :
    fourierPolynomial a = fourierField a.support a := by
  ext x
  simp [fourierPolynomial_apply, fourierField, modeField, Finsupp.sum, mul_comm]

theorem fourierPolynomial_derivative_eq (a : FourierCoeff (Fin 3)) (j : Fin 3) :
    fourierPolynomial (ParallelHeatFlow.derivativeCoeff a j) =
      fourierField a.support (PancakeFourierTranslationCurve.derivativeCoeff j a) := by
  ext x
  rw [fourierPolynomial_eq_sum_of_support_subset _ a.support (support_derivativeCoeff_subset a j)]
  simp [fourierField, modeField, ParallelHeatFlow.derivativeCoeff_apply,
    PancakeFourierTranslationCurve.derivativeCoeff, mul_comm]

theorem hasDerivAt_fourierPolynomial_shift (a : FourierCoeff (Fin 3))
    (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ fourierPolynomial a (x + coordinateShift j t))
      (fourierPolynomial (ParallelHeatFlow.derivativeCoeff a j) (x + coordinateShift j h)) h := by
  have hd := ((ContinuousMap.evalCLM ℂ x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt h
    (hasDerivAt_translationCurve a.support a j h)
  change HasDerivAt (fun τ ↦ translationCurve a.support a j τ x)
    (translationCurve a.support (PancakeFourierTranslationCurve.derivativeCoeff j a) j h x) h at hd
  simpa only [translationCurve_apply, ← fourierPolynomial_eq_fourierField,
    ← fourierPolynomial_derivative_eq] using hd

def HasRadius (a : FourierCoeff (Fin 3)) (R : ℝ) : Prop :=
  ∀ q ∈ a.support, ‖frequencyVec q‖ ≤ R

theorem hasRadius_zero (R : ℝ) : HasRadius 0 R := by simp [HasRadius]

theorem hasRadius_add {a b : FourierCoeff (Fin 3)} {R : ℝ}
    (ha : HasRadius a R) (hb : HasRadius b R) : HasRadius (a + b) R := by
  intro q hq
  have h := Finsupp.support_add hq
  rcases Finset.mem_union.mp h with h | h
  · exact ha q h
  · exact hb q h

theorem hasRadius_sum {ι : Type*} (s : Finset ι) (a : ι → FourierCoeff (Fin 3)) (R : ℝ)
    (ha : ∀ i ∈ s, HasRadius (a i) R) : HasRadius (∑ i ∈ s, a i) R := by
  intro q hq
  obtain ⟨i, hi, hqi⟩ := Finsupp.mem_support_finsetSum q hq
  exact ha i hi q hqi

theorem hasRadius_product {a b : FourierCoeff (Fin 3)} {R S : ℝ}
    (ha : HasRadius a R) (hb : HasRadius b S) : HasRadius (productCoeff a b) (R + S) := by
  intro q hq
  have hs : (productCoeff a b).support ⊆ a.support + b.support :=
    AddMonoidAlgebra.support_mul (AddMonoidAlgebra.ofCoeff a) (AddMonoidAlgebra.ofCoeff b)
  obtain ⟨k, hk, l, hl, rfl⟩ := Finset.mem_add.mp (hs hq)
  rw [frequencyVec_add]
  exact (norm_add_le _ _).trans (add_le_add (ha k hk) (hb l hl))

theorem integral_fourierPolynomial_sq (a : FourierCoeff (Fin 3)) :
    (∫ x : T3, ‖fourierPolynomial a x‖ ^ 2) = ∑ q ∈ a.support, ‖a q‖ ^ 2 := by
  rw [fourierPolynomial_eq_polynomial]
  exact integral_norm_polynomial_sq _ _

theorem integral_gradient_sq_le (a : FourierCoeff (Fin 3)) (R : ℝ)
    (ha : HasRadius a R) :
    (∑ j : Fin 3, ∫ x : T3, ‖fourierPolynomial (ParallelHeatFlow.derivativeCoeff a j) x‖ ^ 2) ≤
      (2 * Real.pi * R) ^ 2 * ∫ x : T3, ‖fourierPolynomial a x‖ ^ 2 := by
  have he (j : Fin 3) : fourierPolynomial (ParallelHeatFlow.derivativeCoeff a j) =
      UnitTorusFourierUniqueness.polynomial a.support
        (fun q ↦ (unitTorusDerivativePhase * (q j : ℂ)) * a q) := by
    ext x
    rw [fourierPolynomial_eq_sum_of_support_subset _ a.support (support_derivativeCoeff_subset a j)]
    simp [UnitTorusFourierUniqueness.polynomial_apply, mul_comm]
  simp_rw [he]
  rw [fourierPolynomial_eq_polynomial]
  apply sum_integral_multiplier_sq_le
  intro q hq
  have hqR := pow_le_pow_left₀ (norm_nonneg _) (ha q hq) 2
  have heq : (∑ j : Fin 3, ‖unitTorusDerivativePhase * (q j : ℂ)‖ ^ 2) =
      (2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 := by
    simp only [norm_mul, mul_pow, ← Finset.mul_sum, norm_frequencyVec_sq]
    congr 1
    · simp [unitTorusDerivativePhase, Real.pi_pos.le, abs_of_nonneg, mul_pow]
    · simp [Complex.norm_intCast, sq_abs]
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hqR (sq_nonneg _)).trans_eq (by ring)

theorem hasRadius_smul {a : FourierCoeff (Fin 3)} {R : ℝ}
    (ha : HasRadius a R) (c : ℂ) : HasRadius (c • a) R := by
  intro q hq
  apply ha q
  apply Finsupp.mem_support_iff.mpr
  intro hz
  exact Finsupp.mem_support_iff.mp hq (by simp [hz])

theorem hasRadius_conjugateReflect {a : FourierCoeff (Fin 3)} {R : ℝ}
    (ha : HasRadius a R) : HasRadius (conjugateReflect a) R := by
  classical
  intro q hq
  have hs := conjugateReflect_support_subset a hq
  simp only [reflectedFrequencySet, Finset.mem_image] at hs
  obtain ⟨k, hk, rfl⟩ := hs
  have he : frequencyVec (-k) = -frequencyVec k := by
    ext i
    simp [frequencyVec, coefficientVec, PancakePeriodicComplexStretch.wavevectorCoefficient]
  simpa only [he, norm_neg] using ha k hk

theorem hasRadius_realPart {a : FourierCoeff (Fin 3)} {R : ℝ}
    (ha : HasRadius a R) : HasRadius (realPartCoeff a) R :=
  hasRadius_smul (hasRadius_add ha (hasRadius_conjugateReflect ha)) _

end Mettapedia.FluidDynamics.NavierStokes.FourierPolynomialDifferential
