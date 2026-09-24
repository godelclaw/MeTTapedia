import Mettapedia.Analysis.IntegralContinuousTest
import Mettapedia.Analysis.UnitTorusFourierUniqueness

/-!
# Fourier uniqueness and finite reconstruction for integrable torus fields

The Fourier coefficients determine an integrable scalar field almost everywhere.
In particular a finitely supported coefficient sequence gives a continuous
polynomial representative, without any initial `L²` or continuity hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusFourierL1Uniqueness

open MeasureTheory UnitAddTorus Set

variable {d : Type*} [Fintype d]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem ae_eq_zero_of_mFourierCoeff_eq_zero {f : UnitAddTorus d → ℂ}
    (hf : Integrable f) (h : ∀ k, mFourierCoeff f k = 0) : f =ᵐ[volume] 0 := by
  have hdense : Dense (Submodule.span ℂ (range (mFourier (d := d))) :
      Set C(UnitAddTorus d, ℂ)) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
      span_mFourier_closure_eq_top, Submodule.top_coe]
  have hp : IntegralContinuousTest.pairing hf = 0 := by
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨k, rfl⟩
    simpa only [IntegralContinuousTest.pairing_apply, mFourierCoeff,
      neg_neg, smul_eq_mul, zero_apply] using h (-k)
  apply IntegralContinuousTest.ae_eq_zero_of_integral_mul_eq_zero hf
  intro g
  exact congrArg (fun L : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ ↦ L g) hp

theorem ae_eq_of_mFourierCoeff_eq {f g : UnitAddTorus d → ℂ}
    (hf : Integrable f) (hg : Integrable g)
    (h : ∀ k, mFourierCoeff f k = mFourierCoeff g k) : f =ᵐ[volume] g := by
  have hz : (fun x ↦ f x - g x) =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_mFourierCoeff_eq_zero (hf.sub hg)
    intro k
    simp only [mFourierCoeff, Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [integral_sub (IntegralContinuousTest.integrable_mul hf (mFourier (-k)))
      (IntegralContinuousTest.integrable_mul hg (mFourier (-k)))]
    exact sub_eq_zero.mpr (h k)
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

theorem ae_eq_polynomial {f : UnitAddTorus d → ℂ} (hf : Integrable f)
    (P : Finset (d → ℤ)) (h : ∀ k ∉ P, mFourierCoeff f k = 0) :
    f =ᵐ[volume] UnitTorusFourierUniqueness.polynomial P (mFourierCoeff f) := by
  classical
  apply ae_eq_of_mFourierCoeff_eq hf (Continuous.integrable_of_hasCompactSupport
    (ContinuousMap.continuous _) (HasCompactSupport.of_compactSpace _))
  intro k
  rw [UnitTorusFourierUniqueness.mFourierCoeff_polynomial]
  split_ifs with hk
  · rfl
  · exact h k hk

end Mettapedia.Analysis.UnitTorusFourierL1Uniqueness
