import Mettapedia.Analysis.UnitTorusContinuousFourier
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Adjoint pairing for finite Fourier filters

The input fields need not have finite Fourier support. Moving a scalar
Fourier filter between the two legs of an integrated inner product
conjugates its symbol at the same frequency. Neither a symmetric mode
set nor a real-valued symbol is required.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusFiniteFilter

open MeasureTheory UnitAddTorus
open scoped ComplexConjugate InnerProductSpace

variable {d E : Type*} [Fintype d]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def finiteFilter (P : Finset (d → ℤ)) (χ : (d → ℤ) → ℂ)
    (f : UnitAddTorus d → E) (x : UnitAddTorus d) : E :=
  ∑ q ∈ P, mFourier q x • (χ q • mFourierCoeff f q)

omit [CompleteSpace E] in
theorem continuous_finiteFilter (P : Finset (d → ℤ)) (χ : (d → ℤ) → ℂ)
    (f : UnitAddTorus d → E) : Continuous (finiteFilter P χ f) := by
  unfold finiteFilter
  exact continuous_finsetSum P (fun q _ ↦ (mFourier q).continuous.smul continuous_const)

omit [CompleteSpace E] in
@[simp] theorem finiteFilter_empty (χ : (d → ℤ) → ℂ) (f : UnitAddTorus d → E)
    (x : UnitAddTorus d) : finiteFilter ∅ χ f x = 0 := by simp [finiteFilter]

theorem finiteFilter_monomial (P : Finset (d → ℤ)) (χ : (d → ℤ) → ℂ)
    (q : d → ℤ) (c : E) (x : UnitAddTorus d) :
    finiteFilter P χ (fun y ↦ mFourier q y • c) x =
      if q ∈ P then mFourier q x • (χ q • c) else 0 := by
  classical
  simp only [finiteFilter, UnitTorusContinuousFourier.mFourierCoeff_monomial]
  by_cases hq : q ∈ P
  · rw [if_pos hq, Finset.sum_eq_single q]
    · simp
    · intro b _ hb
      simp [hb]
    · exact fun h ↦ (h hq).elim
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro b hb
    have hne : b ≠ q := fun h ↦ hq (h ▸ hb)
    simp [hne]

theorem integral_inner_monomial (f : UnitAddTorus d → E) (hf : Continuous f)
    (q : d → ℤ) (c : E) :
    (∫ x : UnitAddTorus d, ⟪f x, mFourier q x • c⟫_ℂ) =
      ⟪mFourierCoeff f q, c⟫_ℂ := by
  have hi : Integrable (fun x : UnitAddTorus d ↦ mFourier (-q) x • f x) :=
    ((mFourier (-q)).continuous.smul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := (innerSL ℂ c).integral_comp_comm hi
  simp only [innerSL_apply_apply] at h
  calc
    _ = ∫ x : UnitAddTorus d, conj (⟪c, mFourier (-q) x • f x⟫_ℂ) := by
      congr 1
      funext x
      simp only [inner_smul_right, map_mul, mFourier_neg,
        starRingEnd_self_apply, inner_conj_symm]
    _ = conj (∫ x : UnitAddTorus d, ⟪c, mFourier (-q) x • f x⟫_ℂ) := integral_conj
    _ = _ := by rw [h]; exact inner_conj_symm _ _

theorem integral_inner_finiteFilter (P : Finset (d → ℤ)) (χ : (d → ℤ) → ℂ)
    (f g : UnitAddTorus d → E) (hf : Continuous f) :
    (∫ x : UnitAddTorus d, ⟪f x, finiteFilter P χ g x⟫_ℂ) =
      ∑ q ∈ P, χ q * ⟪mFourierCoeff f q, mFourierCoeff g q⟫_ℂ := by
  simp only [finiteFilter, inner_sum]
  rw [integral_finsetSum P (fun q _ ↦
    (hf.inner ((mFourier q).continuous.smul continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_inner_monomial f hf, inner_smul_right]

theorem integral_inner_finiteFilter_eq_adjoint (P : Finset (d → ℤ))
    (χ : (d → ℤ) → ℂ) (f g : UnitAddTorus d → E)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ x : UnitAddTorus d, ⟪f x, finiteFilter P χ g x⟫_ℂ) =
      ∫ x : UnitAddTorus d, ⟪finiteFilter P (fun q ↦ conj (χ q)) f x, g x⟫_ℂ := by
  rw [integral_inner_finiteFilter P χ f g hf]
  conv_rhs => arg 2; ext x; rw [← inner_conj_symm]
  rw [integral_conj, integral_inner_finiteFilter P _ g f hg]
  simp only [map_sum, map_mul, starRingEnd_self_apply, inner_conj_symm]

end Mettapedia.Analysis.UnitTorusFiniteFilter
