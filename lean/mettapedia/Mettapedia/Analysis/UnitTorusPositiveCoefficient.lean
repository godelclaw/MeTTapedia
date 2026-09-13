import Mettapedia.Analysis.FiniteTorusSymbolKernel
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Positive Fourier coefficients and positive spatial means

Real coefficient convolution preserves coefficientwise nonnegativity.
A single positive convolution path certifies a positive coefficient,
without expanding the other terms. Evaluation on a unit torus identifies
the zero coefficient with the spatial mean. Nonnegative coefficients do
not assert that the function is pointwise nonnegative.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusPositiveCoefficient

open MeasureTheory
open scoped ComplexConjugate
variable {d : Type*}
local notation "A" => AddMonoidAlgebra ℝ (d → ℤ)
local notation "T" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def HasNonnegativeCoefficients (a : A) : Prop := ∀ q, 0 ≤ a q

theorem nonnegative_single (q : d → ℤ) (c : ℝ) (hc : 0 ≤ c) :
    HasNonnegativeCoefficients (AddMonoidAlgebra.single q c) := by
  classical
  intro k
  simp only [AddMonoidAlgebra.single_apply]
  split_ifs <;> positivity

theorem nonnegative_add {a b : A}
    (ha : HasNonnegativeCoefficients a) (hb : HasNonnegativeCoefficients b) :
    HasNonnegativeCoefficients (a + b) := fun q ↦ add_nonneg (ha q) (hb q)

theorem nonnegative_mul {a b : A}
    (ha : HasNonnegativeCoefficients a) (hb : HasNonnegativeCoefficients b) :
    HasNonnegativeCoefficients (a * b) := by
  intro q
  rw [AddMonoidAlgebra.mul_apply_left]
  exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (ha k) (hb (-k + q))

/-- One convolution path is a lower bound when every path has nonnegative weight. -/
theorem mul_coeff_le {a b : A}
    (ha : HasNonnegativeCoefficients a) (hb : HasNonnegativeCoefficients b)
    (k l : d → ℤ) : a k * b l ≤ (a * b) (k + l) := by
  classical
  rw [AddMonoidAlgebra.mul_apply_left]
  simp only [Finsupp.sum]
  by_cases hk : k ∈ a.support
  · simpa only [neg_add_cancel_left] using
      (Finset.single_le_sum (s := a.support)
        (fun j _ ↦ mul_nonneg (ha j) (hb (-j + (k + l)))) hk)
  · have hz : a k = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hk
    rw [hz, zero_mul]
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (ha j) (hb (-j + (k + l)))

theorem mul_coeff_pos {a b : A}
    (ha : HasNonnegativeCoefficients a) (hb : HasNonnegativeCoefficients b)
    {k l : d → ℤ} (hk : 0 < a k) (hl : 0 < b l) : 0 < (a * b) (k + l) :=
  lt_of_lt_of_le (mul_pos hk hl) (mul_coeff_le ha hb k l)

variable [Fintype d]

def characterHom : Multiplicative (d → ℤ) →* C(T, ℂ) where
  toFun q := UnitAddTorus.mFourier q.toAdd
  map_one' := UnitAddTorus.mFourier_zero
  map_mul' q r := by ext x; exact UnitAddTorus.mFourier_add

def evaluate : A →ₐ[ℝ] C(T, ℂ) :=
  AddMonoidAlgebra.lift ℝ C(T, ℂ) (d → ℤ) characterHom

theorem evaluate_single (q : d → ℤ) (c : ℝ) (x : T) :
    evaluate (AddMonoidAlgebra.single q c) x = (c : ℂ) * UnitAddTorus.mFourier q x := by
  simp [evaluate, AddMonoidAlgebra.lift_single, characterHom, Algebra.smul_def]

theorem integral_evaluate (a : A) : (∫ x : T, evaluate a x) = (a 0 : ℂ) := by
  classical
  have he (x : T) : evaluate a x =
      ∑ q ∈ a.support, (a q : ℂ) * UnitAddTorus.mFourier q x := by
    simp [evaluate, AddMonoidAlgebra.lift_apply, characterHom, Finsupp.sum,
      Algebra.smul_def, ContinuousMap.sum_apply]
  simp_rw [he]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, FiniteTorusSymbolKernel.integral_mFourier]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro q _ hq
      simp [hq]
    · intro h
      have hz : a 0 = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using h
      simp [hz]
  · intro q _
    exact ((UnitAddTorus.mFourier q).continuous.const_mul (a q : ℂ)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

def cosinePolynomial (q : d → ℤ) : A :=
  AddMonoidAlgebra.single q (1 / 2) + AddMonoidAlgebra.single (-q) (1 / 2)

omit [Fintype d] in
theorem cosine_nonnegative (q : d → ℤ) : HasNonnegativeCoefficients (cosinePolynomial q) :=
  nonnegative_add (nonnegative_single _ _ (by norm_num)) (nonnegative_single _ _ (by norm_num))

theorem cosine_coeff_pos (q : d → ℤ) : 0 < cosinePolynomial q q := by
  classical
  change 0 < AddMonoidAlgebra.single q (1 / 2 : ℝ) q +
    AddMonoidAlgebra.single (-q) (1 / 2 : ℝ) q
  simp only [AddMonoidAlgebra.single_apply]
  split_ifs <;> norm_num

theorem cosine_neg_coeff_pos (q : d → ℤ) : 0 < cosinePolynomial q (-q) := by
  classical
  change 0 < AddMonoidAlgebra.single q (1 / 2 : ℝ) (-q) +
    AddMonoidAlgebra.single (-q) (1 / 2 : ℝ) (-q)
  simp only [AddMonoidAlgebra.single_apply]
  split_ifs <;> norm_num

theorem evaluate_cosine (q : d → ℤ) (x : T) :
    evaluate (cosinePolynomial q) x = ((UnitAddTorus.mFourier q x).re : ℂ) := by
  rw [cosinePolynomial, map_add]
  simp only [ContinuousMap.add_apply, evaluate_single, UnitAddTorus.mFourier_neg]
  rw [Complex.re_eq_add_conj]
  push_cast
  ring

end Mettapedia.Analysis.UnitTorusPositiveCoefficient
