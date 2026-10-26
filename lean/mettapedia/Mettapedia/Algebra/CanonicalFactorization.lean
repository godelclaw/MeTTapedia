import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mettapedia.Algebra.ActionFold

/-!
# Canonical factors and ordered observations

Factor sets retain irreducible multiplicities and distinguish zero from one.
They classify associates, so they forget multiplication order and unit
representatives. Prefix products retain the execution positions separately.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.CanonicalFactorization

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

/-- Mathlib's mutually inverse factor and product maps, in multiplicative notation. -/
noncomputable def factorSetEquiv [Nontrivial R] :
    Associates R ≃* Multiplicative (Associates.FactorSet R) where
  toFun a := Multiplicative.ofAdd a.factors
  invFun s := (Multiplicative.toAdd s).prod
  left_inv := Associates.factors_prod
  right_inv := Associates.prod_factors
  map_mul' := Associates.factors_mul

theorem factors_dvd_iff (a b : Associates R) : a.factors ≤ b.factors ↔ a ∣ b := Associates.factors_le

/-- Observing a product is summing its factor sets, including the absorbing zero case. -/
theorem factors_prod [Nontrivial R] (xs : List R) :
    (Associates.mk xs.prod).factors = (xs.map (fun x => (Associates.mk x).factors)).sum := by
  induction xs with
  | nil => exact Associates.prod_factors (0 : Associates.FactorSet R)
  | cons x xs ih => simp [List.prod_cons, ← Associates.mk_mul_mk, Associates.factors_mul, ih]

/-- Every prefix square commutes, while repeated execution positions are retained. -/
theorem factors_scanl (xs : List R) (initial : R) :
    ((xs.scanl (· * ·) initial).map (fun x => (Associates.mk x).factors)) =
      (xs.map (fun x => (Associates.mk x).factors)).scanl (· + ·) (Associates.mk initial).factors := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih => simp [List.scanl_cons, ← Associates.mk_mul_mk, Associates.factors_mul, ih]

/-- Normalized representatives and factor sets agree after projecting to associates. -/
theorem normalized_factors_agree [NormalizationMonoid R] (a : R) :
    (UniqueFactorizationMonoid.normalizedFactors a).map Associates.mk =
      (Associates.factors' a).map Subtype.val := by
  rw [Associates.map_subtype_coe_factors']
  simp [UniqueFactorizationMonoid.normalizedFactors, Multiset.map_map, Associates.mk_normalize]

/-- The multiset alone loses zero; the factor-set observation retains it. -/
theorem zero_one_separated [Nontrivial R] [NormalizationMonoid R] :
    UniqueFactorizationMonoid.normalizedFactors (0 : R) = UniqueFactorizationMonoid.normalizedFactors 1 ∧
    (Associates.mk (0 : R)).factors ≠ (Associates.mk (1 : R)).factors :=
  ⟨by simp, fun equal => zero_ne_one ((factorSetEquiv (R := R)).injective equal)⟩

/-- Unit-associated integer representatives have the same canonical factors. -/
theorem signs_forgotten :
    (2 : ℤ) ≠ -2 ∧ (Associates.mk (2 : ℤ)).factors = (Associates.mk (-2 : ℤ)).factors := by
  exact ⟨by norm_num, congrArg (fun a : Associates ℤ => a.factors)
    (Associates.mk_eq_mk_iff_associated.mpr ⟨-1, by norm_num⟩)⟩

/-- Equal endpoint observations do not identify the supplied ordered prefixes. -/
theorem order_forgotten :
    (Associates.mk ([2,3] : List ℤ).prod).factors = (Associates.mk ([3,2] : List ℤ).prod).factors ∧
    ([2,3] : List ℤ).scanl (· * ·) 1 ≠ ([3,2] : List ℤ).scanl (· * ·) 1 :=
  ⟨rfl, by decide⟩

/-- Squaring an irreducible retains two occurrences, even though its support is unchanged. -/
theorem duplicate_retained [NormalizationMonoid R] {p : R} (hp : Irreducible p) :
    UniqueFactorizationMonoid.normalizedFactors (p*p) = {normalize p, normalize p} := by
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hp.ne_zero hp.ne_zero,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hp]
  rfl

end Mettapedia.Algebra.CanonicalFactorization
