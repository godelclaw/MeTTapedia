import Mettapedia.Algebra.Order.Infinitesimal.LevelSeries

/-!
# Finite denotations are closed under ring operations, not inversion

`LevelField` is a field: every nonzero element has an inverse.  The executable
representation is a *finite* list of terms, and this file proves that the
finiteness is a real restriction rather than an accident of the encoding:

`Om - 1` is nonzero, so it is invertible in the field, but **no level series
denotes its inverse**.  The inverse is `Ω⁻¹ + Ω⁻² + Ω⁻³ + ⋯`, and no finite
list has that value.

The argument is elementary and needs neither the order nor infinite sums.  Put
a series in canonical form and look at its two extreme levels.  Multiplying by
`Ω - 1` moves each term to two places, one level lower and the same level
negated.  At the *highest* level nothing arrives from above, so the product's
coefficient there is minus the original's: nonzero.  At one below the *lowest*
level nothing arrives from below, so the product's coefficient there is the
original's: also nonzero.  A product equal to `1` has a nonzero coefficient
only at level `0`, so the highest level must be `0` and the lowest must be `1`
— and the lowest cannot exceed the highest.

This is the fact behind treating the fragment as an exact *numeric family*
rather than as a numeric foundation: division by a single term is exact and
stays inside the representation (`divideByTerm`), while general inversion
leaves it.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order.Infinitesimal

open HahnSeries LevelSeries

/-- `Ω - 1`, as data. -/
def omegaSubOne : LevelSeries := [(-1, 1), (0, -1)]

@[simp] theorem toHahn_omegaSubOne :
    toHahn omegaSubOne = single (-1 : ℤ) (1 : ℚ) + single (0 : ℤ) (-1 : ℚ) := by
  simp [omegaSubOne, toHahn]

theorem toLevelField_omegaSubOne : toLevelField omegaSubOne = Om - 1 := by
  simpa only [toLevelField, Om, toLex_add, single_neg, toLex_neg, single_zero_one, toLex_one,
    sub_eq_add_neg] using congrArg toLex toHahn_omegaSubOne

/-! ## The two extreme levels of a canonical series -/

/-- The last stored term is the highest nonzero coefficient of a canonical list. -/
theorem exists_top_level {l : LevelSeries} (nonempty : l ≠ []) (sorted : Sorted l) (nonzero : NoZero l) :
    ∃ m : ℤ, (∀ t ∈ l, t.1 ≤ m) ∧ (toHahn l).coeff m ≠ 0 := by
  have member := List.getLast_mem nonempty
  refine ⟨(l.getLast nonempty).1, ?_, ?_⟩
  · intro t occurs
    have weak : l.Pairwise (fun t u => t.1 ≤ u.1) :=
      ((sorted_iff_pairwise l).mp sorted).imp (fun h => h.le)
    exact weak.rel_getLast_of_rel_getLast_getLast occurs le_rfl
  · rw [coeff_toHahn_of_mem sorted member]
    exact nonzero _ member

/-- **And a bottom level, where it also does not vanish** — namely the head. -/
theorem exists_bottom_level : ∀ {l : LevelSeries}, l ≠ [] → Sorted l → NoZero l →
    ∃ n : ℤ, (∀ t ∈ l, n ≤ t.1) ∧ (toHahn l).coeff n ≠ 0
  | [], h, _, _ => absurd rfl h
  | (i, a) :: rest, _, hs, hz => by
      refine ⟨i, ?_, ?_⟩
      · simpa using fun t member => (hs.1 t member).le
      · rw [coeff_toHahn_head hs]
        exact hz (i, a) List.mem_cons_self

/-! ## What multiplying by `Ω - 1` does at the extremes -/

/-- Multiplication by `Ω - 1` is the difference of two coefficient shifts. -/
theorem coeff_mul_omegaSubOne (q : LevelSeries) (j : ℤ) :
    (toHahn (mul q omegaSubOne)).coeff j = (toHahn q).coeff (j + 1) - (toHahn q).coeff j := by
  simp [toHahn_mul, toHahn_omegaSubOne, mul_add, coeff_add, coeff_mul_single,
    sub_eq_add_neg]

/-- Above the raw support, the upper coefficient is just its own negation. -/
theorem coeff_mul_omegaSubOne_at_upper {m : ℤ} {q : LevelSeries}
    (bound : ∀ t ∈ q, t.1 ≤ m) :
    (toHahn (mul q omegaSubOne)).coeff m = - (toHahn q).coeff m := by
  rw [coeff_mul_omegaSubOne, coeff_toHahn_of_not_levels
    (fun t member => by have := bound t member; omega), zero_sub]

/-- Below the raw support, only the shifted bottom coefficient contributes. -/
theorem coeff_mul_omegaSubOne_at_lower {n : ℤ} {q : LevelSeries}
    (bound : ∀ t ∈ q, n ≤ t.1) :
    (toHahn (mul q omegaSubOne)).coeff (n - 1) = (toHahn q).coeff n := by
  rw [coeff_mul_omegaSubOne, sub_add_cancel, coeff_toHahn_of_not_levels
    (j := n - 1) (l := q) (fun t member => by have := bound t member; omega), sub_zero]

/-! ## `Ω - 1` has no inverse in the representation -/

/-- A series whose product with `Ω - 1` is `1` would have to have its top level
at `0` and its bottom level at `1`. -/
theorem toHahn_mul_omegaSubOne_ne_one (q : LevelSeries) :
    toHahn (mul q omegaSubOne) ≠ 1 := by
  intro product
  have normalizedProduct : toHahn (mul (norm q) omegaSubOne) = 1 := by
    simpa only [toHahn_mul, toHahn_norm] using product
  obtain ⟨sorted, nonzero⟩ := normalized_norm q
  by_cases empty : norm q = []
  · simp [empty, mul] at normalizedProduct
  obtain ⟨upper, upperBound, upperNonzero⟩ := exists_top_level empty sorted nonzero
  obtain ⟨lower, lowerBound, lowerNonzero⟩ := exists_bottom_level empty sorted nonzero
  have upperZero : upper = 0 := by
    by_contra other
    have coefficient := congrArg (fun value => value.coeff upper) normalizedProduct
    rw [coeff_mul_omegaSubOne_at_upper upperBound] at coefficient
    exact upperNonzero (by simpa [other] using coefficient)
  have lowerOne : lower = 1 := by
    by_contra other
    have coefficient := congrArg (fun value => value.coeff (lower - 1)) normalizedProduct
    rw [coeff_mul_omegaSubOne_at_lower lowerBound] at coefficient
    exact lowerNonzero (by simpa [show lower - 1 ≠ 0 by omega] using coefficient)
  obtain ⟨term, member⟩ := List.exists_mem_of_ne_nil _ empty
  have := lowerBound term member
  have := upperBound term member
  omega

/-- **The representation is not closed under inversion.**  `Ω - 1` is nonzero,
hence invertible in `LevelField`, but no level series denotes its inverse. -/
theorem no_levelSeries_inverts_omegaSubOne (q : LevelSeries) :
    toLevelField (mul q omegaSubOne) ≠ 1 :=
  fun equal => toHahn_mul_omegaSubOne_ne_one q (toLex.injective equal)

/-- The same, stated against the field element rather than the list: no finite
representation has `(Ω - 1)⁻¹` as its value. -/
theorem toLevelField_ne_inv_omegaSubOne (q : LevelSeries) :
    toLevelField q ≠ (Om - 1)⁻¹ := by
  intro inverse
  apply no_levelSeries_inverts_omegaSubOne q
  have greater : (1 : LevelField) < Om := by simpa [ofRat] using ofRat_lt_Om 1
  change toLex (toHahn (mul q omegaSubOne)) = 1
  rw [toHahn_mul]
  change toLevelField q * toLevelField omegaSubOne = 1
  rw [toLevelField_omegaSubOne, inverse, inv_mul_cancel₀ (sub_ne_zero.mpr greater.ne')]

/-! ## The positive side: division by a single term stays inside

Nonzero monomials invert within the finite fragment. General finite
expressions need not, as `Ω - 1` demonstrates. -/

theorem omega_inverts : toLevelField (mul omega omegaInv) = 1 :=
  toLevelField_mul_omega_omegaInv

end Mettapedia.Algebra.Order.Infinitesimal
