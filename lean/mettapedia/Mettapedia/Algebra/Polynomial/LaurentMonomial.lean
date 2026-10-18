import Mathlib

/-!
# Finite Laurent monomial substitution

Integer exponent tables describe monomial maps on any commutative group.
Substitution composes those tables; an integer right inverse supplies an
explicit inverse-value normalization without extracting roots.
-/

namespace Mettapedia.Algebra.Polynomial.LaurentMonomial

/-- A finite multiplicative monomial with integer exponents. -/
def monomial {G ι : Type*} [CommGroup G] [Fintype ι]
    (a : ι → G) (exponent : ι → ℤ) : G :=
  ∏ i, a i ^ exponent i

private theorem zpow_sum_finset {G ι : Type*} [CommGroup G]
    (a : G) (exponent : ι → ℤ) (s : Finset ι) :
    a ^ (∑ i ∈ s, exponent i) = ∏ i ∈ s, a ^ exponent i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add]

private theorem zpow_sum_univ {G ι : Type*} [CommGroup G] [Fintype ι]
    (a : G) (exponent : ι → ℤ) :
    a ^ (∑ i, exponent i) = ∏ i, a ^ exponent i := by
  simpa using zpow_sum_finset a exponent Finset.univ

/-- Substitution of finite monomials composes their integer exponent tables. -/
theorem monomial_monomial {G ι κ : Type*} [CommGroup G]
    [Fintype ι] [Fintype κ]
    (a : κ → G) (table : ι → κ → ℤ) (row : ι → ℤ) :
    monomial (fun i => monomial a (table i)) row =
      monomial a (fun k => ∑ i, row i * table i k) := by
  classical
  simp only [monomial]
  calc
    (∏ i, (∏ k, a k ^ table i k) ^ row i) =
        ∏ i, ∏ k, (a k ^ table i k) ^ row i := by
          apply Finset.prod_congr rfl
          intro i _
          exact (Finset.prod_zpow
            (fun k => a k ^ table i k) Finset.univ (row i)).symm
    _ = ∏ k, ∏ i, (a k ^ table i k) ^ row i := Finset.prod_comm
    _ = ∏ k, a k ^ (∑ i, row i * table i k) := by
          apply Finset.prod_congr rfl
          intro k _
          rw [zpow_sum_univ]
          apply Finset.prod_congr rfl
          intro i _
          rw [mul_comm, zpow_mul]

/-- Adding exponent vectors multiplies their monomial values. -/
theorem monomial_add {G ι : Type*} [CommGroup G] [Fintype ι]
    (a : ι → G) (left right : ι → ℤ) :
    monomial a (fun i => left i + right i) =
      monomial a left * monomial a right := by
  classical
  simp [monomial, zpow_add, Finset.prod_mul_distrib]

/-- If `rightInverse` is an integer right inverse for the exponent rows, then
the monomials with its negated columns scale every selected value by exactly
its inverse.  No roots or divisibility assumptions enter the construction. -/
theorem monomial_of_neg_rightInverse {G ι κ : Type*} [CommGroup G]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (a : κ → G) (rightInverse : ι → κ → ℤ) (row : κ → ι → ℤ)
    (hRight : ∀ k l,
      ∑ i, row k i * rightInverse i l = if k = l then 1 else 0)
    (k : κ) :
    monomial
        (fun i => monomial a (fun l => -rightInverse i l))
        (row k) = (a k)⁻¹ := by
  rw [monomial_monomial]
  unfold monomial
  have hexponent : ∀ l, (∑ i, row k i * -rightInverse i l) =
      if l = k then -1 else 0 := by
    intro l
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib, hRight]
    by_cases h : k = l
    · subst l
      simp
    · simp [h, Ne.symm h]
  simp_rw [hexponent]
  simp [zpow_neg]

end Mettapedia.Algebra.Polynomial.LaurentMonomial
