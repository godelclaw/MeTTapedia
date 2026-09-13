import Mettapedia.Analysis.UnitTorusConvolutionEnergy
import Mettapedia.Analysis.UnitTorusFourierUniqueness

/-!
# Exact finite Fourier tests of signed periodic convolution

A polynomial test factor turns a spatial convolution pairing into a finite
sum of exact Fourier coefficients. Convergence of the kernel multipliers then
suffices for convergence of the pairing; no uniform pointwise kernel bound
or interchange with an infinite series is needed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusPolynomialPairing

open MeasureTheory UnitAddTorus UnitTorusFourierUniqueness UnitTorusConvolutionEnergy
open scoped BigOperators Topology
variable {d : Type*} [Fintype d]
local notation "T" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- This pairing is bilinear, not Hermitian; the second coefficient is at `-k`. -/
theorem integral_polynomial_mul (P : Finset (d → ℤ)) (a : (d → ℤ) → ℂ)
    (f : T → ℂ) (hf : Continuous f) :
    (∫ x : T, polynomial P a x * f x) = ∑ k ∈ P, a k * mFourierCoeff f (-k) := by
  simp only [polynomial_apply, smul_eq_mul, Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    simp_rw [mul_right_comm (mFourier k _) (a k)]
    rw [integral_mul_const]
    simp only [mFourierCoeff, neg_neg, smul_eq_mul]
    ring
  · intro k _
    exact (((mFourier k).continuous.mul continuous_const).mul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem integral_polynomial_mul_convolution (P : Finset (d → ℤ)) (a : (d → ℤ) → ℂ)
    (K f : T → ℂ) (hK : Continuous K) (hf : Continuous f) :
    (∫ x : T, polynomial P a x * convolution K f x) =
      ∑ k ∈ P, a k * (mFourierCoeff K (-k) * mFourierCoeff f (-k)) := by
  rw [integral_polynomial_mul P a _ (continuous_convolution K f hK hf)]
  simp_rw [mFourierCoeff_convolution K f hK hf]

theorem integral_polynomial_mul_convolution_polynomial
    (P Q : Finset (d → ℤ)) (a b : (d → ℤ) → ℂ) (K : T → ℂ) (hK : Continuous K) :
    (∫ x : T, polynomial P a x * convolution K (polynomial Q b) x) =
      ∑ k ∈ P, a k * (mFourierCoeff K (-k) * if -k ∈ Q then b (-k) else 0) := by
  rw [integral_polynomial_mul_convolution P a K _ hK (polynomial Q b).continuous]
  simp_rw [mFourierCoeff_polynomial]

theorem tendsto_integral_polynomial_mul_convolution
    (P : Finset (d → ℤ)) (a : (d → ℤ) → ℂ)
    (K : ℕ → T → ℂ) (hK : ∀ n, Continuous (K n))
    (f : T → ℂ) (hf : Continuous f) (m : (d → ℤ) → ℂ)
    (hm : ∀ k, Filter.Tendsto (fun n ↦ mFourierCoeff (K n) k) Filter.atTop (𝓝 (m k))) :
    Filter.Tendsto (fun n ↦ ∫ x : T, polynomial P a x * convolution (K n) f x)
      Filter.atTop (𝓝 (∑ k ∈ P, a k * (m (-k) * mFourierCoeff f (-k)))) := by
  simp_rw [integral_polynomial_mul_convolution P a _ _ (hK _) hf]
  exact tendsto_finsetSum _ fun k _ ↦ (hm (-k)).mul_const _ |>.const_mul _

end Mettapedia.Analysis.UnitTorusPolynomialPairing
