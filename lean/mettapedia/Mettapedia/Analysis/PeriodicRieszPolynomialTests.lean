import Mettapedia.Analysis.PeriodicRieszPolynomial

/-! Integrable Fourier uniqueness, support, and exact representative audit. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PeriodicRieszPolynomialTests

open MeasureTheory UnitAddTorus
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (f : UnitAddTorus (Fin 3) → ℂ) (hf : Integrable f)
    (h : ∀ k, mFourierCoeff f k = 0) : f =ᵐ[volume] 0 :=
  UnitTorusFourierL1Uniqueness.ae_eq_zero_of_mFourierCoeff_eq_zero hf h

example (x : UnitAddTorus (Fin 3)) : PeriodicRieszPolynomial.kernel 0 x = 0 := by simp

example (N : ℕ) (x : UnitAddTorus (Fin 3)) :
    PeriodicRieszPolynomial.kernel N (-x) = PeriodicRieszPolynomial.kernel N x := by simp

example (N : ℕ) (k : Fin 3 → ℤ) (hk : k ∉ AnnularRieszKernel.frequencySupport N) :
    AnnularRieszKernel.weight N (UnitTorusLattice.frequency k) = 0 :=
  AnnularRieszKernel.weight_frequency_eq_zero_of_not_mem N k hk

example (N : ℕ) :
    (∫ x : UnitAddTorus (Fin 3), ‖x‖ ^ 2 * ‖PeriodicRieszPolynomial.kernel N x‖) ≤
      PeriodicRieszOperator.secondMomentBound 3 := PeriodicRieszPolynomial.secondMoment_le N

#print axioms IntegralContinuousTest.ae_eq_zero_of_integral_mul_eq_zero
#print axioms UnitTorusFourierL1Uniqueness.ae_eq_zero_of_mFourierCoeff_eq_zero
#print axioms UnitTorusFourierL1Uniqueness.ae_eq_of_mFourierCoeff_eq
#print axioms UnitTorusFourierL1Uniqueness.ae_eq_polynomial
#print axioms AnnularRieszKernel.weight_eq_zero_of_le_norm
#print axioms AnnularRieszKernel.weight_frequency_eq_zero_of_not_mem
#print axioms PeriodicRieszPolynomial.entry_ae_eq
#print axioms PeriodicRieszPolynomial.continuous_kernel
#print axioms PeriodicRieszPolynomial.kernel_ae_eq
#print axioms PeriodicRieszPolynomial.kernel_sub_ae_eq
#print axioms PeriodicRieszPolynomial.kernel_neg
#print axioms PeriodicRieszPolynomial.integral_pair_eq
#print axioms PeriodicRieszPolynomial.integrable_kernel
#print axioms PeriodicRieszPolynomial.integrable_secondMoment
#print axioms PeriodicRieszPolynomial.secondMoment_le

end Mettapedia.Analysis.PeriodicRieszPolynomialTests
