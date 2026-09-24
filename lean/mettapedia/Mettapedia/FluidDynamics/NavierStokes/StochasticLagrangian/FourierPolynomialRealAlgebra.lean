import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeQuadraticFourierSupport
import Mettapedia.Analysis.UnitTorusFourierUniqueness

/-!
# Real parts and products of the existing finite Fourier polynomials

Coefficient convolution is evaluated by the already constructed monoid-algebra
homomorphism. Taking a real part reflects and conjugates coefficients before
averaging. No reality assumption on the input coefficients is necessary.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPolynomialRealAlgebra

open scoped ComplexConjugate
open PancakeQuadraticFourierSupport Mettapedia.Analysis.UnitTorusFourierUniqueness
variable {d : Type*} [Fintype d]

theorem fourierPolynomial_eq_polynomial (a : FourierCoeff d) :
    fourierPolynomial a = polynomial a.support a := by
  ext x
  simp [fourierPolynomial_apply, polynomial_apply, Finsupp.sum, mul_comm]

theorem mFourierCoeff_fourierPolynomial (a : FourierCoeff d) (k : d → ℤ) :
    UnitAddTorus.mFourierCoeff (fourierPolynomial a) k = a k := by
  rw [fourierPolynomial_eq_polynomial, mFourierCoeff_polynomial]
  split_ifs with hk
  · rfl
  · have hz : a k = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hk
    exact hz.symm

@[simp] theorem fourierPolynomial_zero : fourierPolynomial (0 : FourierCoeff d) = 0 := by
  simp [fourierPolynomial]

theorem fourierPolynomial_add (a b : FourierCoeff d) :
    fourierPolynomial (a + b) = fourierPolynomial a + fourierPolynomial b := by
  simp only [← addMonoidAlgebraLift_eq_fourierPolynomial, AddMonoidAlgebra.ofCoeff_add, map_add]

theorem fourierPolynomial_smul (c : ℂ) (a : FourierCoeff d) :
    fourierPolynomial (c • a) = c • fourierPolynomial a := by
  simp only [← addMonoidAlgebraLift_eq_fourierPolynomial, AddMonoidAlgebra.ofCoeff_smul, map_smul]

theorem fourierPolynomial_neg (a : FourierCoeff d) :
    fourierPolynomial (-a) = -fourierPolynomial a := by
  simp only [← addMonoidAlgebraLift_eq_fourierPolynomial, AddMonoidAlgebra.ofCoeff_neg, map_neg]

/-- The actual collected coefficients of a pointwise product. -/
def productCoeff (a b : FourierCoeff d) : FourierCoeff d :=
  AddMonoidAlgebra.coeff (AddMonoidAlgebra.ofCoeff a * AddMonoidAlgebra.ofCoeff b)

theorem fourierPolynomial_productCoeff (a b : FourierCoeff d) :
    fourierPolynomial (productCoeff a b) = fourierPolynomial a * fourierPolynomial b :=
  fourierPolynomial_convolutionCoeff a b

/-- Coefficients of the real part, retained as a complex-valued polynomial. -/
def realPartCoeff (a : FourierCoeff d) : FourierCoeff d :=
  (1 / 2 : ℂ) • (a + conjugateReflect a)

theorem fourierPolynomial_realPartCoeff (a : FourierCoeff d) (x : UnitAddTorus d) :
    fourierPolynomial (realPartCoeff a) x = ((fourierPolynomial a x).re : ℂ) := by
  rw [realPartCoeff, fourierPolynomial_smul, fourierPolynomial_add]
  simp only [ContinuousMap.smul_apply, ContinuousMap.add_apply, smul_eq_mul,
    fourierPolynomial_conjugateReflect, Complex.re_eq_add_conj]
  ring

theorem fourierPolynomial_eq_sum_of_support_subset (a : FourierCoeff d)
    (P : Finset (d → ℤ)) (h : a.support ⊆ P) (x : UnitAddTorus d) :
    fourierPolynomial a x = ∑ k ∈ P, a k * UnitAddTorus.mFourier k x := by
  rw [fourierPolynomial_apply, Finsupp.sum_of_support_subset _ h
    (fun k z ↦ z * UnitAddTorus.mFourier k x) (fun _ _ ↦ zero_mul _)]

end Mettapedia.FluidDynamics.NavierStokes.FourierPolynomialRealAlgebra
