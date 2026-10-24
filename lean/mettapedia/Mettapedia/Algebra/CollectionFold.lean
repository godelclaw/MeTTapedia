import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Dedup

/-!
# Finite collection folds and their binary algebras

A singleton-preserving operation on finite lists that respects flattening
determines a monoid. Its value on every list is the product in that monoid,
and every monoid supplies such an operation. Thus arbitrary variadic arities
are fixed by the binary operation and the empty value, rather than inferred
from finitely many tests at arity two or three.

## The Boom hierarchy

Lists, bags and sets are the free monoid, the free commutative monoid and the
free idempotent commutative monoid. The forgetful maps `List → Multiset →
Finset` are homomorphisms and commute with `map` and `filter`.

* A fold over a list consumes bags exactly when it is invariant under
  permutation, and sets exactly when it is also invariant under repetition
  (`Model.factorsThroughBag_iff`, `Model.factorsThroughSet_iff`); the
  descended folds are homomorphisms out of the free structures
  (`Model.bagFold_add`, `Model.setFold_union`).
* For a generator into a monoid, the fold factors through bags exactly when
  the generator's values commute, and through sets exactly when they also are
  idempotent (`Boom.foldList_factors_bag_iff`,
  `Boom.foldList_factors_set_iff`). The three folds are the unique
  homomorphisms extending the generator (`Boom.foldList_unique`,
  `Boom.foldBag_unique`, `Boom.foldSet_unique`).
* `map` keeps the kind. On bags it keeps the size; on sets it merges values
  identified by the function, so the size is kept exactly when the function is
  injective on the set (`Boom.setMap_card_eq_iff`). Mapping a set as a bag and
  then forgetting multiplicity is mapping it as a set (`Boom.setMap_eq_support`).
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.CollectionFold

universe u
variable {A : Type u}

structure Model (A : Type u) where
  fold : List A → A
  singleton : ∀ value, fold [value] = value
  flatten : ∀ pieces : List (List A), fold pieces.flatten = fold (pieces.map fold)

@[ext] theorem Model.ext {first second : Model A}
    (equal : first.fold = second.fold) : first = second := by
  cases first
  cases second
  cases equal
  rfl

def ofMonoid [Monoid A] : Model A where
  fold := List.prod
  singleton := by intro value; simp
  flatten := by intro pieces; exact List.prod_flatten

namespace Model

variable (algebra : Model A)

theorem fold_append (left right : List A) :
    algebra.fold (left ++ right) = algebra.fold [algebra.fold left, algebra.fold right] := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil,
    List.map_cons, List.map_nil] using algebra.flatten [left, right]

theorem fold_cons (value : A) (rest : List A) :
    algebra.fold (value :: rest) = algebra.fold [value, algebra.fold rest] := by
  simpa only [List.singleton_append, algebra.singleton] using algebra.fold_append [value] rest

theorem fold_left_unit (value : A) :
    algebra.fold [algebra.fold [], value] = value := by
  simpa only [List.nil_append, algebra.singleton] using (algebra.fold_append [] [value]).symm

theorem fold_right_unit (value : A) :
    algebra.fold [value, algebra.fold []] = value := by
  simpa only [List.append_nil, algebra.singleton] using (algebra.fold_append [value] []).symm

theorem fold_associative (first second third : A) :
    algebra.fold [algebra.fold [first, second], third] =
      algebra.fold [first, algebra.fold [second, third]] := by
  calc
    _ = algebra.fold ([first, second] ++ [third]) := by
      rw [algebra.fold_append, algebra.singleton]
    _ = _ := algebra.fold_cons first [second, third]

/-- The binary multiplication and unit are derived from the actual fold. -/
@[instance_reducible] def monoid : Monoid A where
  one := algebra.fold []
  mul first second := algebra.fold [first, second]
  one_mul := algebra.fold_left_unit
  mul_one := algebra.fold_right_unit
  mul_assoc := algebra.fold_associative

theorem fold_eq_prod (values : List A) :
    letI := algebra.monoid
    algebra.fold values = values.prod := by
  let _ := algebra.monoid
  induction values with
  | nil => rfl
  | cons value rest ih =>
    rw [List.prod_cons, ← ih]
    exact algebra.fold_cons value rest

/-- Reconstructing all arities from the extracted binary algebra returns
the entire original operation. -/
theorem ofMonoid_monoid : @ofMonoid A algebra.monoid = algebra := by
  apply Model.ext
  funext values
  exact (algebra.fold_eq_prod values).symm

def PermutationInvariant : Prop :=
  ∀ left right : List A, left.Perm right → algebra.fold left = algebra.fold right

theorem permutationInvariant_iff : algebra.PermutationInvariant ↔
    ∀ first second, algebra.fold [first, second] = algebra.fold [second, first] := by
  constructor
  · intro invariant first second
    exact invariant _ _ (List.Perm.swap _ _ [])
  · intro commutes left right permutation
    let _ : CommMonoid A := { algebra.monoid with mul_comm := commutes }
    rw [algebra.fold_eq_prod left, algebra.fold_eq_prod right]
    exact permutation.prod_eq

end Model

/-- Binary application is preserved by the finite-list realization. -/
theorem ofMonoid_binary [Monoid A] (first second : A) :
    (ofMonoid (A := A)).fold [first, second] = first * second := by
  simp [ofMonoid]

theorem ofMonoid_empty [Monoid A] : (ofMonoid (A := A)).fold [] = 1 := rfl

private theorem prod_absorb_of_mem [CommMonoid A]
    (idempotent : ∀ value : A, value * value = value)
    {value : A} {values : List A} (member : value ∈ values) :
    value * values.prod = values.prod := by
  induction values with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · rw [List.prod_cons, ← mul_assoc, idempotent]
    · rw [List.prod_cons, mul_left_comm, ih later]

private theorem prod_dedup [CommMonoid A] [DecidableEq A]
    (idempotent : ∀ value : A, value * value = value) (values : List A) :
    values.dedup.prod = values.prod := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
    by_cases member : head ∈ rest
    · rw [List.dedup_cons_of_mem member, ih, List.prod_cons,
        prod_absorb_of_mem idempotent member]
    · rw [List.dedup_cons_of_notMem member, List.prod_cons, List.prod_cons, ih]

theorem prod_eq_of_members [CommMonoid A]
    (idempotent : ∀ value : A, value * value = value)
    {left right : List A} (same : ∀ value, value ∈ left ↔ value ∈ right) :
    left.prod = right.prod := by
  classical
  have permuted : left.dedup.Perm right.dedup :=
    (List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)).mpr
      (fun value => by simpa only [List.mem_dedup] using same value)
  rw [← prod_dedup idempotent left, ← prod_dedup idempotent right]
  exact permuted.prod_eq

namespace Model

variable (algebra : Model A)

def MembershipInvariant : Prop :=
  ∀ left right : List A, (∀ value, value ∈ left ↔ value ∈ right) →
    algebra.fold left = algebra.fold right

/-- Exactly the commutative idempotent binary algebras permit set-valued
folds. Bag permutation alone never licenses erasing multiplicities. -/
theorem membershipInvariant_iff : algebra.MembershipInvariant ↔
    algebra.PermutationInvariant ∧ ∀ value, algebra.fold [value, value] = value := by
  constructor
  · intro invariant
    refine ⟨fun left right permuted => invariant left right (fun _ => permuted.mem_iff), ?_⟩
    intro value
    calc
      algebra.fold [value, value] = algebra.fold [value] := invariant _ _ (by simp)
      _ = value := algebra.singleton value
  · rintro ⟨permutation, idempotent⟩ left right same
    let _ : CommMonoid A :=
      { algebra.monoid with mul_comm := algebra.permutationInvariant_iff.mp permutation }
    rw [algebra.fold_eq_prod left, algebra.fold_eq_prod right]
    exact prod_eq_of_members idempotent same

/-! ### Consuming bags and sets -/

/-- A permutation-invariant fold, read on bags. -/
def bagFold (invariant : algebra.PermutationInvariant) : Multiset A → A :=
  Quot.lift algebra.fold (fun _ _ permuted => invariant _ _ permuted)

@[simp] theorem bagFold_coe (invariant : algebra.PermutationInvariant) (values : List A) :
    algebra.bagFold invariant values = algebra.fold values := rfl

/-- A fold consumes bags, i.e. it is a function of the bag of its arguments,
exactly when it is invariant under permutation. -/
theorem factorsThroughBag_iff :
    (∃ consume : Multiset A → A, ∀ values : List A, algebra.fold values = consume values) ↔
      algebra.PermutationInvariant := by
  constructor
  · rintro ⟨consume, factors⟩ left right permuted
    rw [factors, factors, Multiset.coe_eq_coe.mpr permuted]
  · intro invariant
    exact ⟨algebra.bagFold invariant, fun _ => rfl⟩

theorem bagFold_unique (invariant : algebra.PermutationInvariant)
    (consume : Multiset A → A) (factors : ∀ values : List A, consume values = algebra.fold values) :
    consume = algebra.bagFold invariant := by
  funext values
  induction values using Quot.ind with
  | mk values => exact factors values

/-- The bag fold is a homomorphism out of the free commutative monoid. -/
theorem bagFold_add (invariant : algebra.PermutationInvariant) (left right : Multiset A) :
    algebra.bagFold invariant (left + right) =
      algebra.fold [algebra.bagFold invariant left, algebra.bagFold invariant right] := by
  obtain ⟨left, rfl⟩ := Quot.exists_rep left
  obtain ⟨right, rfl⟩ := Quot.exists_rep right
  exact algebra.fold_append left right

theorem bagFold_singleton (invariant : algebra.PermutationInvariant) (value : A) :
    algebra.bagFold invariant {value} = value :=
  algebra.singleton value

/-- A membership-invariant fold, read on sets through any enumeration. -/
noncomputable def setFold (_invariant : algebra.MembershipInvariant) (values : Finset A) : A :=
  algebra.fold values.toList

theorem setFold_toFinset [DecidableEq A] (invariant : algebra.MembershipInvariant)
    (values : List A) : algebra.setFold invariant values.toFinset = algebra.fold values :=
  invariant _ _ (fun value => by simp)

/-- A fold consumes sets exactly when it is invariant under permutation and
repetition, i.e. when it depends only on which values occur. -/
theorem factorsThroughSet_iff [DecidableEq A] :
    (∃ consume : Finset A → A, ∀ values : List A, algebra.fold values = consume values.toFinset) ↔
      algebra.MembershipInvariant := by
  constructor
  · rintro ⟨consume, factors⟩ left right same
    rw [factors, factors]
    congr 1
    ext value
    simpa using same value
  · intro invariant
    exact ⟨algebra.setFold invariant, fun values => (algebra.setFold_toFinset invariant values).symm⟩

theorem setFold_unique [DecidableEq A] (invariant : algebra.MembershipInvariant)
    (consume : Finset A → A)
    (factors : ∀ values : List A, consume values.toFinset = algebra.fold values) :
    consume = algebra.setFold invariant := by
  funext values
  rw [← Finset.toList_toFinset values, factors, setFold_toFinset]

/-- The set fold is a homomorphism out of the free idempotent commutative
monoid. -/
theorem setFold_union [DecidableEq A] (invariant : algebra.MembershipInvariant)
    (left right : Finset A) :
    algebra.setFold invariant (left ∪ right) =
      algebra.fold [algebra.setFold invariant left, algebra.setFold invariant right] := by
  unfold setFold
  rw [← algebra.fold_append]
  exact invariant _ _ (fun value => by simp)

theorem setFold_singleton (invariant : algebra.MembershipInvariant) (value : A) :
    algebra.setFold invariant {value} = value := by
  simpa [setFold] using algebra.singleton value

/-- Reading a set as the bag of its distinct elements gives the same value. -/
theorem setFold_eq_bagFold (invariant : algebra.MembershipInvariant) (values : Finset A) :
    algebra.setFold invariant values =
      algebra.bagFold ((algebra.membershipInvariant_iff.mp invariant).1) values.val := by
  conv_rhs => rw [← Finset.coe_toList values]
  rfl

end Model

/-! ## Universal folds of the free list, bag and set structures -/

namespace Boom

variable {α β M : Type*}

/-- The fold out of the free monoid determined by a generator. -/
def foldList [Monoid M] (generator : α → M) (values : List α) : M :=
  (values.map generator).prod

/-- The fold out of the free commutative monoid determined by a generator. -/
def foldBag [CommMonoid M] (generator : α → M) (values : Multiset α) : M :=
  (values.map generator).prod

/-- The fold out of the free idempotent commutative monoid. -/
def foldSet [CommMonoid M] (generator : α → M) (values : Finset α) : M :=
  values.prod generator

section Laws

variable (generator : α → M)

@[simp] theorem foldList_nil [Monoid M] : foldList generator [] = 1 := rfl

@[simp] theorem foldList_singleton [Monoid M] (value : α) :
    foldList generator [value] = generator value := by
  simp [foldList]

theorem foldList_append [Monoid M] (left right : List α) :
    foldList generator (left ++ right) = foldList generator left * foldList generator right := by
  simp [foldList, List.prod_append]

@[simp] theorem foldBag_zero [CommMonoid M] : foldBag generator 0 = 1 := by
  simp [foldBag]

@[simp] theorem foldBag_singleton [CommMonoid M] (value : α) :
    foldBag generator {value} = generator value := by
  simp [foldBag]

theorem foldBag_add [CommMonoid M] (left right : Multiset α) :
    foldBag generator (left + right) = foldBag generator left * foldBag generator right := by
  simp [foldBag, Multiset.prod_add]

/-- The bag fold restricted along the forgetful map is the list fold. -/
@[simp] theorem foldBag_coe [CommMonoid M] (values : List α) :
    foldBag generator values = foldList generator values := by
  simp [foldBag, foldList]

@[simp] theorem foldSet_empty [CommMonoid M] : foldSet generator ∅ = 1 := by
  simp [foldSet]

@[simp] theorem foldSet_singleton [CommMonoid M] (value : α) :
    foldSet generator {value} = generator value := by
  simp [foldSet]

/-- An idempotent value absorbs a smaller product into a larger one. -/
theorem prod_absorb_subset [CommMonoid M] [DecidableEq α]
    (idempotent : ∀ value, IsIdempotentElem (generator value))
    {small large : Finset α} (contained : small ⊆ large) :
    large.prod generator * small.prod generator = large.prod generator := by
  rw [← Finset.union_sdiff_of_subset contained,
    Finset.prod_union Finset.disjoint_sdiff, mul_comm, ← mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun value _ => idempotent value)

theorem foldSet_union [CommMonoid M] [DecidableEq α]
    (idempotent : ∀ value, IsIdempotentElem (generator value)) (left right : Finset α) :
    foldSet generator (left ∪ right) = foldSet generator left * foldSet generator right := by
  unfold foldSet
  rw [← Finset.prod_union_inter, prod_absorb_subset generator idempotent
    (Finset.inter_subset_left.trans Finset.subset_union_left)]

/-- With idempotent generator values, the set fold restricted along the
forgetful map is the bag fold. -/
theorem foldSet_toFinset [CommMonoid M] [DecidableEq α]
    (idempotent : ∀ value, IsIdempotentElem (generator value)) (values : Multiset α) :
    foldSet generator values.toFinset = foldBag generator values := by
  unfold foldSet foldBag
  rw [Finset.prod_multiset_map_count]
  refine Finset.prod_congr rfl (fun value member => ?_)
  obtain ⟨count, hcount⟩ : ∃ count, values.count value = count + 1 :=
    Nat.exists_eq_succ_of_ne_zero
      (Multiset.count_ne_zero.mpr (Multiset.mem_toFinset.mp member))
  rw [hcount, (idempotent value).pow_succ_eq]

end Laws

/-! ### Uniqueness: each fold is the homomorphism extending its generator -/

theorem foldList_unique [Monoid M] (generator : α → M) (fold : List α → M)
    (nil : fold [] = 1) (append : ∀ left right, fold (left ++ right) = fold left * fold right)
    (singleton : ∀ value, fold [value] = generator value) :
    fold = foldList generator := by
  funext values
  induction values with
  | nil => exact nil
  | cons head tail ih =>
    rw [← List.singleton_append, append, ih, singleton, foldList_append, foldList_singleton]

theorem foldBag_unique [CommMonoid M] (generator : α → M) (fold : Multiset α → M)
    (zero : fold 0 = 1) (add : ∀ left right, fold (left + right) = fold left * fold right)
    (singleton : ∀ value, fold {value} = generator value) :
    fold = foldBag generator := by
  funext values
  induction values using Multiset.induction_on with
  | empty => simpa using zero
  | cons head tail ih =>
    rw [← Multiset.singleton_add, add, ih, singleton, foldBag_add, foldBag_singleton]

theorem foldSet_unique [CommMonoid M] [DecidableEq α] (generator : α → M)
    (fold : Finset α → M) (empty : fold ∅ = 1)
    (union : ∀ left right, fold (left ∪ right) = fold left * fold right)
    (singleton : ∀ value, fold {value} = generator value) :
    fold = foldSet generator := by
  funext values
  induction values using Finset.induction_on with
  | empty => simpa using empty
  | insert head tail fresh ih =>
    rw [Finset.insert_eq, union, ih, singleton, ← Finset.insert_eq]
    simp [foldSet, Finset.prod_insert fresh]

/-! ### Exact conditions for consuming bags and sets -/

/-- A list fold depends only on the bag exactly when the generator's values
commute pairwise. -/
theorem foldList_factors_bag_iff [Monoid M] (generator : α → M) :
    (∃ consume : Multiset α → M, ∀ values : List α,
        foldList generator values = consume values) ↔
      ∀ first second, Commute (generator first) (generator second) := by
  constructor
  · rintro ⟨consume, factors⟩ first second
    have swapped := factors [first, second]
    rw [show ((([first, second] : List α)) : Multiset α) = ([second, first] : List α) from
      Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ []), ← factors] at swapped
    show generator first * generator second = generator second * generator first
    simpa [foldList] using swapped
  · intro commute
    refine ⟨Quot.lift (foldList generator) ?_, fun _ => rfl⟩
    intro left right permuted
    exact (permuted.map generator).prod_eq'
      (List.pairwise_map.mpr (List.pairwise_of_forall (fun first second => commute first second)))

/-- A commutative list fold depends only on the set of values exactly when
every generator value is idempotent. -/
theorem foldList_factors_set_iff [CommMonoid M] [DecidableEq α] (generator : α → M) :
    (∃ consume : Finset α → M, ∀ values : List α,
        foldList generator values = consume values.toFinset) ↔
      ∀ value, IsIdempotentElem (generator value) := by
  constructor
  · rintro ⟨consume, factors⟩ value
    have repeated := factors [value, value]
    rw [show ([value, value] : List α).toFinset = ([value] : List α).toFinset by simp,
      ← factors] at repeated
    simpa [foldList, IsIdempotentElem] using repeated
  · intro idempotent
    refine ⟨foldSet generator, fun values => ?_⟩
    rw [← foldBag_coe, ← foldSet_toFinset generator idempotent]
    rfl

/-! ## Forgetting order and multiplicity: naturality of map and filter -/

/-- Mapping commutes with forgetting order and with forgetting multiplicity. -/
theorem map_natural [DecidableEq α] [DecidableEq β] (function : α → β) (values : List α) :
    ((values.map function : List β) : Multiset β) = (values : Multiset α).map function ∧
      ((values : Multiset α).map function).toFinset =
        (values : Multiset α).toFinset.image function :=
  ⟨Multiset.map_coe function values |>.symm, Multiset.toFinset_map function _⟩

/-- Filtering commutes with forgetting order and with forgetting multiplicity. -/
theorem filter_natural [DecidableEq α] (keep : α → Prop) [DecidablePred keep]
    (values : List α) :
    ((values.filter (fun value => decide (keep value)) : List α) : Multiset α) =
        (values : Multiset α).filter keep ∧
      ((values : Multiset α).filter keep).toFinset = (values : Multiset α).toFinset.filter keep :=
  ⟨(Multiset.filter_coe keep values).symm, Multiset.toFinset_filter _ keep⟩

/-- Mapping a bag keeps its size: values identified by the function keep
their separate occurrences. -/
theorem bagMap_card (function : α → β) (values : Multiset α) :
    (values.map function).card = values.card :=
  Multiset.card_map function values

/-- Mapping a set merges the values the function identifies, so it keeps the
size exactly when the function is injective on the set. -/
theorem setMap_card_eq_iff [DecidableEq β] (function : α → β) (values : Finset α) :
    (values.image function).card = values.card ↔ Set.InjOn function values :=
  Finset.card_image_iff

/-- Mapping a set as a bag and then forgetting multiplicity is mapping it as
a set; the intermediate bag is duplicate-free exactly for injective maps. -/
theorem setMap_eq_support [DecidableEq β] (function : α → β) (values : Finset α) :
    values.image function = (values.val.map function).toFinset ∧
      ((values.val.map function).Nodup ↔ Set.InjOn function values) :=
  ⟨rfl, Multiset.nodup_map_iff_inj_on values.nodup⟩

end Boom

/-! ## Controls -/

namespace Controls

open Boom

/-- A noncommutative fold does not consume bags: the free monoid on two
letters separates the two orders. -/
theorem freeMonoid_fold_not_bag :
    ¬ ∃ consume : Multiset Bool → FreeMonoid Bool, ∀ values : List Bool,
        foldList FreeMonoid.of values = consume values := by
  rw [foldList_factors_bag_iff]
  intro commute
  have := (commute true false).eq
  have lists := congrArg FreeMonoid.toList this
  simp at lists

/-- Addition of naturals consumes bags but not sets: repetition counts. -/
theorem nat_sum_bag_not_set :
    (∃ consume : Multiset ℕ → Multiplicative ℕ, ∀ values : List ℕ,
        foldList Multiplicative.ofAdd values = consume values) ∧
      ¬ ∃ consume : Finset ℕ → Multiplicative ℕ, ∀ values : List ℕ,
        foldList Multiplicative.ofAdd values = consume values.toFinset := by
  refine ⟨(foldList_factors_bag_iff _).mpr (fun _ _ => Commute.all _ _), ?_⟩
  rw [foldList_factors_set_iff]
  intro idempotent
  have := idempotent 1
  simp [IsIdempotentElem, ← ofAdd_add] at this

/-- Natural numbers under maximum, with unit zero: a commutative idempotent
monoid. -/
def MaxNat : Type := ℕ

instance : CommMonoid MaxNat where
  mul first second := (max first second : ℕ)
  one := (0 : ℕ)
  mul_assoc first second third := max_assoc (α := ℕ) first second third
  one_mul value := max_eq_right (Nat.zero_le (value : ℕ))
  mul_one value := max_eq_left (Nat.zero_le (value : ℕ))
  mul_comm first second := max_comm (α := ℕ) first second

/-- A natural number read in the maximum monoid. -/
def MaxNat.of (value : ℕ) : MaxNat := value

/-- Maximum consumes sets: it is commutative and idempotent. -/
theorem max_consumes_sets :
    ∃ consume : Finset ℕ → MaxNat, ∀ values : List ℕ,
      foldList MaxNat.of values = consume values.toFinset := by
  rw [foldList_factors_set_iff]
  intro value
  exact max_self (α := ℕ) value

/-- Mapping by a constant: the bag keeps both occurrences, the set merges
them. -/
theorem constant_map_bag_vs_set :
    (({1, 2} : Multiset ℕ).map (fun _ => (0 : ℕ))) = {0, 0} ∧
      (({1, 2} : Finset ℕ).image (fun _ => (0 : ℕ))) = {0} ∧
      ¬ Set.InjOn (fun _ : ℕ => (0 : ℕ)) (({1, 2} : Finset ℕ) : Set ℕ) := by
  refine ⟨by simp, by decide, ?_⟩
  intro injective
  have := injective (by simp : (1 : ℕ) ∈ (({1, 2} : Finset ℕ) : Set ℕ))
    (by simp : (2 : ℕ) ∈ (({1, 2} : Finset ℕ) : Set ℕ)) rfl
  omega

end Controls

end Mettapedia.Algebra.CollectionFold
