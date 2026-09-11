import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Finite symbol kernels on a torus of arbitrary finite dimension

This generalizes the three-dimensional finite-symbol construction to
arbitrary complete complex normed targets, including bilinear operators
on the six-dimensional frequency-pair torus.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.FiniteTorusSymbolKernel

open MeasureTheory
open scoped BigOperators

variable {d E : Type*} [Fintype d] [NormedAddCommGroup E] [NormedSpace ℂ E]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_mFourier (k : d → ℤ) :
    (∫ x : UnitAddTorus d, UnitAddTorus.mFourier k x) = if k = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := d))) (0 : d → ℤ) k
  simpa only [ContinuousMap.inner_toLp, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, map_one, one_mul, mul_one, eq_comm] using h

def kernel (s : Finset (d → ℤ)) (symbol : (d → ℤ) → E) (x : UnitAddTorus d) : E :=
  ∑ k ∈ s, UnitAddTorus.mFourier k x • symbol k

theorem continuous_kernel (s : Finset (d → ℤ)) (symbol : (d → ℤ) → E) :
    Continuous (kernel s symbol) := by
  unfold kernel
  fun_prop

theorem integrable_kernel (s : Finset (d → ℤ)) (symbol : (d → ℤ) → E) :
    Integrable (kernel s symbol) :=
  (continuous_kernel s symbol).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem mFourierCoeff_kernel [CompleteSpace E] (s : Finset (d → ℤ)) (symbol : (d → ℤ) → E)
    (l : d → ℤ) : UnitAddTorus.mFourierCoeff (kernel s symbol) l =
      if l ∈ s then symbol l else 0 := by
  classical
  unfold UnitAddTorus.mFourierCoeff kernel
  simp_rw [Finset.smul_sum, smul_smul, ← UnitAddTorus.mFourier_add]
  rw [integral_finsetSum s]
  · simp_rw [integral_smul_const, integral_mFourier]
    by_cases hl : l ∈ s
    · rw [if_pos hl, Finset.sum_eq_single l]
      · simp only [neg_add_cancel, if_pos, one_smul]
      · intro k hk hne
        have hz : -l + k ≠ 0 := by
          intro h
          exact hne (by simpa only [neg_add_eq_zero, eq_comm] using h)
        rw [if_neg hz, zero_smul]
      · exact fun hnot ↦ (hnot hl).elim
    · rw [if_neg hl]
      apply Finset.sum_eq_zero
      intro k hk
      have hz : -l + k ≠ 0 := by
        intro h
        have he : l = k := by simpa only [neg_add_eq_zero] using h
        exact hl (he ▸ hk)
      rw [if_neg hz, zero_smul]
  · intro k _
    have h : Integrable (fun x : UnitAddTorus d ↦ UnitAddTorus.mFourier (-l + k) x) :=
      (UnitAddTorus.mFourier (-l + k)).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact h.smul_const (symbol k)

theorem norm_kernel_le (s : Finset (d → ℤ)) (symbol : (d → ℤ) → E) (x : UnitAddTorus d) :
    ‖kernel s symbol x‖ ≤ ∑ k ∈ s, ‖symbol k‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ ↦ ?_))
  simp only [norm_smul, UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one, one_mul, le_rfl]

end Mettapedia.Analysis.FiniteTorusSymbolKernel
