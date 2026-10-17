import Mettapedia.Languages.MeTTa.MeTTaZeroAnswerAlgebra
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.Order.Kleene
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Matrix.Mul

/-!
# One annotation algebra for spaces and answers

A space is a finitely supported map from keys to annotations in an algebra
`K` (`Space K Key = Key →₀ K`); answers are annotated in the same algebra
(`Ans K X = X →₀ K`).  Booleans give sets of facts and sets of answers, the
natural numbers give bags, other semirings give provenance, cost or evidence.
This is the annotated-relation semantics of Green, Karvounarakis and Tannen
(*Provenance semirings*, PODS 2007) used at two layers at once.

## Answers

`pure` and `bind` (`(A >>= f) y = ∑ₓ A x * f x y`) satisfy the three monad
laws over every semiring (`pure_bind`, `bind_pure`, `bind_assoc`).  Choice
(`+`) and scaling by an annotation are algebraic operations in the sense of
Plotkin and Power: bind distributes over them in its first argument
(`add_bind`, `smul_bind`), and it is additive in the continuation
(`bind_add_right`).  The answer monad is **commutative**, so two independent
choices may be bound in either order, exactly when the annotations commute:
`bind_comm` over a commutative semiring, and a two-by-two matrix semiring
separates the two orders (`Controls.bind_not_comm_matrix`).

A semiring homomorphism changes the annotation and is a monad morphism
(`mapK_pure`, `mapK_bind`).  **MeTTa Zero's multiset answers are the case
`K = ℕ`**: `Multiset.toFinsupp` carries multiset `bind` to weighted bind
(`toFinsupp_bind`), and the support map `ℕ → Presence` is the set quotient,
which is a monad morphism and is not injective
(`supportOfCount_not_injective`).

## Readouts and the capabilities they need

* **Possibility** (the support of an answer) composes as a union,
  `(A >>= f).support = ⋃_{x ∈ A.support} (f x).support`, when annotations
  are canonically ordered and have no zero divisors (`support_bind`).  A
  zero divisor breaks it: in `ℕ × ℕ`, an answer supported only positively
  bound to one supported only negatively has empty support
  (`Controls.support_bind_fails_with_zero_divisors`).  The coordinatewise
  product of positive and negative evidence counts has exactly this zero
  divisor.

## Spaces and the capabilities they need

Merging spaces needs only addition.  Mathlib's instances already make the
other operations capability-gated: `S ⊓ T` exists when `K` is a meet
semilattice, `S - T` when `K` has an ordered truncated subtraction (a monus),
and pointwise product (`S * T`, a natural join of two spaces over one key
type) when `K` has a multiplication with zero.

* **Subtraction cannot undo merging when merging is idempotent**
  (`no_cancellative_sub_of_idempotent`, and for spaces
  `no_space_sub_undoes_merge`): sets have set difference, but
  `(S ∪ T) \ T = S` fails, so a retraction of facts needs counts or event
  identity.  Over `ℕ` it holds (`nat_merge_sub_cancel`).
* **Joins distribute over monus over `ℕ`** (`nat_join_tsub`) **but not over
  `ℝ≥0∞`** (`Controls.ennreal_join_tsub_fails`, at `⊤`).  Distributivity of a
  join over difference is therefore a separate capability, as Amsterdamer,
  Deutch and Tannen observe for provenance with difference.
* **Saturation needs idempotent merging.**  Re-deriving a delta is a fixed
  point exactly when merging it again changes nothing: over an idempotent
  semiring it never changes anything (`idem_rederive_fixed`); over `ℕ` a
  fixed point admits only the empty delta (`nat_rederive_fixed_iff`), so a
  propagation rule that keeps deriving its conclusion never quiesces on bags
  without a record of which matches have fired.

`Presence` is the two-element idempotent commutative semiring of set-valued
spaces (`+` is "or", `*` is "and").
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra

open scoped ENNReal

universe u v w

/-- A space annotated in `K`: finitely many keys carry a nonzero annotation. -/
abbrev Space (K : Type u) [Zero K] (Key : Type v) : Type (max v u) := Key →₀ K

/-- Answers annotated in the same algebra as spaces. -/
abbrev Ans (K : Type u) [Zero K] (X : Type v) : Type (max v u) := X →₀ K

/-! ## The weighted answer monad -/

namespace Ans

variable {K : Type u} {X Y Z : Type*}

section Semiring

variable [Semiring K]

/-- One answer, annotated by `1`. -/
noncomputable def pure (x : X) : Ans K X := Finsupp.single x 1

/-- Weighted bind: `(A >>= f) y = ∑ₓ A x * f x y`. -/
noncomputable def bind (A : Ans K X) (f : X → Ans K Y) : Ans K Y :=
  A.sum fun x a => a • f x

theorem single_bind (x : X) (a : K) (f : X → Ans K Y) :
    bind (Finsupp.single x a) f = a • f x :=
  Finsupp.sum_single_index (zero_smul K (f x))

@[simp] theorem pure_bind (x : X) (f : X → Ans K Y) : bind (pure x) f = f x := by
  rw [pure, single_bind, one_smul]

@[simp] theorem bind_pure (A : Ans K X) : bind A pure = A := by
  unfold bind pure
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  exact Finsupp.sum_single A

@[simp] theorem zero_bind (f : X → Ans K Y) : bind (0 : Ans K X) f = 0 :=
  Finsupp.sum_zero_index

/-- Choice is an algebraic operation: bind distributes over it. -/
theorem add_bind (A B : Ans K X) (f : X → Ans K Y) :
    bind (A + B) f = bind A f + bind B f :=
  Finsupp.sum_add_index' (fun _ => zero_smul K _) (fun _ _ _ => add_smul _ _ _)

/-- Scaling by an annotation is an algebraic operation. -/
theorem smul_bind (c : K) (A : Ans K X) (f : X → Ans K Y) :
    bind (c • A) f = c • bind A f := by
  induction A using Finsupp.induction_linear with
  | zero => simp
  | add A B hA hB => rw [smul_add, add_bind, add_bind, hA, hB, smul_add]
  | single x a => rw [Finsupp.smul_single, single_bind, single_bind, smul_eq_mul, mul_smul]

@[simp] theorem bind_zero_right (A : Ans K X) : bind A (fun _ => (0 : Ans K Y)) = 0 := by
  simp [bind]

/-- Bind is additive in the continuation. -/
theorem bind_add_right (A : Ans K X) (f g : X → Ans K Y) :
    bind A (fun x => f x + g x) = bind A f + bind A g := by
  unfold bind
  simp only [smul_add]
  exact Finsupp.sum_add

theorem bind_apply (A : Ans K X) (f : X → Ans K Y) (y : Y) :
    bind A f y = A.sum fun x a => a * f x y := by
  unfold bind
  rw [Finsupp.sum_apply]
  rfl

/-- **Associativity** of weighted bind. -/
theorem bind_assoc (A : Ans K X) (f : X → Ans K Y) (g : Y → Ans K Z) :
    bind (bind A f) g = bind A (fun x => bind (f x) g) := by
  induction A using Finsupp.induction_linear with
  | zero => simp
  | add A B hA hB => rw [add_bind, add_bind, hA, hB, add_bind]
  | single x a => rw [single_bind, smul_bind, single_bind]

/-- Mapping answers is binding to annotated singletons. -/
noncomputable def map (h : X → Y) (A : Ans K X) : Ans K Y := bind A (fun x => pure (h x))

theorem map_eq_mapDomain (h : X → Y) (A : Ans K X) : map h A = Finsupp.mapDomain h A := by
  induction A using Finsupp.induction_linear with
  | zero => simp [map]
  | add A B hA hB => rw [map, add_bind, ← map, ← map, hA, hB, Finsupp.mapDomain_add]
  | single x a =>
      rw [map, single_bind, Finsupp.mapDomain_single, pure, Finsupp.smul_single, smul_eq_mul,
        mul_one]

end Semiring

section CommSemiring

variable [CommSemiring K]

theorem bind_smul_right (A : Ans K X) (c : K) (f : X → Ans K Y) :
    bind A (fun x => c • f x) = c • bind A f := by
  unfold bind
  rw [Finsupp.smul_sum]
  congr 1
  funext x a
  rw [smul_comm]

/-- **The weighted answer monad is commutative** over a commutative
semiring: independent choices may be bound in either order. -/
theorem bind_comm (A : Ans K X) (B : Ans K Y) (f : X → Y → Ans K Z) :
    bind A (fun x => bind B (f x)) = bind B (fun y => bind A (fun x => f x y)) := by
  induction A using Finsupp.induction_linear with
  | zero => simp
  | add A₁ A₂ h₁ h₂ =>
      rw [add_bind, h₁, h₂]
      simp only [add_bind]
      rw [bind_add_right]
  | single x a =>
      rw [single_bind]
      simp only [single_bind]
      rw [bind_smul_right]

end CommSemiring

/-! ### Change of annotation -/

section ChangeOfAnnotation

variable [Semiring K] {L : Type*} [Semiring L]

/-- Change the annotation along a semiring homomorphism. -/
noncomputable def mapK (φ : K →+* L) (A : Ans K X) : Ans L X :=
  Finsupp.mapRange φ φ.map_zero A

@[simp] theorem mapK_apply (φ : K →+* L) (A : Ans K X) (x : X) : mapK φ A x = φ (A x) := rfl

theorem mapK_single (φ : K →+* L) (x : X) (a : K) :
    mapK φ (Finsupp.single x a) = Finsupp.single x (φ a) :=
  Finsupp.mapRange_single

@[simp] theorem mapK_pure (φ : K →+* L) (x : X) : mapK φ (pure x : Ans K X) = pure x := by
  rw [pure, mapK_single, map_one, pure]

theorem mapK_add (φ : K →+* L) (A B : Ans K X) : mapK φ (A + B) = mapK φ A + mapK φ B :=
  Finsupp.mapRange_add (map_add φ) A B

theorem mapK_smul (φ : K →+* L) (c : K) (A : Ans K X) : mapK φ (c • A) = φ c • mapK φ A := by
  ext x
  simp [mapK]

/-- **A semiring homomorphism is a monad morphism** of weighted answers. -/
theorem mapK_bind (φ : K →+* L) (A : Ans K X) (f : X → Ans K Y) :
    mapK φ (bind A f) = bind (mapK φ A) (fun x => mapK φ (f x)) := by
  induction A using Finsupp.induction_linear with
  | zero => simp [mapK, bind]
  | add A B hA hB => rw [add_bind, mapK_add, hA, hB, mapK_add, add_bind]
  | single x a => rw [single_bind, mapK_smul, mapK_single, single_bind]

end ChangeOfAnnotation

/-! ### Possibility -/

section Possibility

variable [Semiring K] [PartialOrder K] [CanonicallyOrderedAdd K] [NoZeroDivisors K]

/-- **Possibility composes as a union** over canonically ordered annotations
without zero divisors. -/
theorem support_bind [DecidableEq Y] (A : Ans K X) (f : X → Ans K Y) :
    (bind A f).support = A.support.biUnion fun x => (f x).support := by
  ext y
  simp only [Finsupp.mem_support_iff, Finset.mem_biUnion, bind_apply, Finsupp.sum, ne_eq]
  rw [Finset.sum_eq_zero_iff]
  simp only [not_forall, Finsupp.mem_support_iff, mul_eq_zero, not_or, exists_prop]
  exact ⟨fun ⟨x, _, hx, hf⟩ => ⟨x, hx, hf⟩, fun ⟨x, hx, hf⟩ => ⟨x, hx, hx, hf⟩⟩

end Possibility

end Ans

/-! ## Multiset answers are the case `K = ℕ` -/

section NatAnswers

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

theorem toFinsupp_pure (x : X) : Multiset.toFinsupp ({x} : Multiset X) = Ans.pure x :=
  Multiset.toFinsupp_singleton x

/-- **Multiset bind is weighted bind over `ℕ`**: MeTTa Zero's answer monad
is the natural-number instance. -/
theorem toFinsupp_bind (m : Multiset X) (f : X → Multiset Y) :
    Multiset.toFinsupp (m.bind f) =
      Ans.bind (Multiset.toFinsupp m) (fun x => Multiset.toFinsupp (f x)) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
      rw [Multiset.cons_bind, Multiset.toFinsupp_add, ih,
        show x ::ₘ m = {x} + m from rfl, Multiset.toFinsupp_add, Ans.add_bind,
        Multiset.toFinsupp_singleton, Ans.single_bind, one_smul]

/-- The query answers of MeTTa Zero, read as weighted answers, are the count
of each answer occurrence. -/
theorem toFinsupp_apply_count (m : Multiset X) (x : X) :
    Multiset.toFinsupp m x = m.count x := by
  rw [Multiset.toFinsupp_apply]

end NatAnswers

/-! ## Presence: the annotation semiring of sets -/

/-- Presence or absence of a fact: the two-element semiring where `+` is
"or" and `*` is "and". -/
structure Presence where
  /-- Whether the fact is present. -/
  present : Bool
  deriving DecidableEq, Repr

namespace Presence

@[ext] theorem ext' {a b : Presence} (h : a.present = b.present) : a = b := by
  cases a; cases b; simp_all

instance : Zero Presence := ⟨⟨false⟩⟩
instance : One Presence := ⟨⟨true⟩⟩
instance : Add Presence := ⟨fun a b => ⟨a.present || b.present⟩⟩
instance : Mul Presence := ⟨fun a b => ⟨a.present && b.present⟩⟩

@[simp] theorem zero_present : (0 : Presence).present = false := rfl
@[simp] theorem one_present : (1 : Presence).present = true := rfl
@[simp] theorem add_present (a b : Presence) : (a + b).present = (a.present || b.present) := rfl
@[simp] theorem mul_present (a b : Presence) : (a * b).present = (a.present && b.present) := rfl

instance : CommSemiring Presence where
  add_assoc a b c := by ext; simp [Bool.or_assoc]
  zero_add a := by ext; simp
  add_zero a := by ext; simp
  add_comm a b := by ext; simp [Bool.or_comm]
  left_distrib a b c := by ext; simp [Bool.and_or_distrib_left]
  right_distrib a b c := by ext; simp [Bool.and_or_distrib_right]
  zero_mul a := by ext; simp
  mul_zero a := by ext; simp
  mul_assoc a b c := by ext; simp [Bool.and_assoc]
  one_mul a := by ext; simp
  mul_one a := by ext; simp
  mul_comm a b := by ext; simp [Bool.and_comm]
  nsmul := nsmulRec
  npow := npowRec

/-- Merging presence is idempotent. -/
theorem add_self (a : Presence) : a + a = a := by ext; simp

theorem ne_zero_iff (a : Presence) : a ≠ 0 ↔ a.present = true := by
  constructor
  · intro h
    by_contra hp
    exact h (by ext; simpa using hp)
  · intro h e
    rw [e] at h
    simp at h

end Presence

/-- The set quotient of counts: a count is present when it is nonzero. -/
def supportOfCount : ℕ →+* Presence where
  toFun n := ⟨decide (n ≠ 0)⟩
  map_one' := by ext; simp
  map_mul' m n := by ext; simp
  map_zero' := by ext; simp
  map_add' m n := by
    ext
    simp only [Presence.add_present, ne_eq, Nat.add_eq_zero_iff, not_and_or]
    cases decide (m = 0) <;> cases decide (n = 0) <;> simp_all

/-- **The set quotient forgets multiplicity**: one answer and two answers
have the same presence. -/
theorem supportOfCount_not_injective {X : Type*} (x : X) :
    Ans.mapK supportOfCount (Ans.pure x : Ans ℕ X) =
        Ans.mapK supportOfCount (Finsupp.single x 2 : Ans ℕ X) ∧
      (Ans.pure x : Ans ℕ X) ≠ Finsupp.single x 2 := by
  refine ⟨?_, ?_⟩
  · rw [Ans.pure, Ans.mapK_single, Ans.mapK_single]
    congr 1
  · intro h
    have := congrArg (fun A : Ans ℕ X => A x) h
    simp [Ans.pure] at this

/-! ## Space capabilities -/

section SpaceCapabilities

variable {Key : Type*}

/-- **Over an idempotent merge, no subtraction undoes merging.** -/
theorem no_cancellative_sub_of_idempotent {K : Type*} [AddZeroClass K] [One K]
    (idempotent : ∀ a : K, a + a = a) (nontrivial : (1 : K) ≠ 0) (sub : K → K → K) :
    ¬ ∀ a b : K, sub (a + b) b = a := by
  intro cancel
  have once := cancel 1 1
  have none := cancel 0 1
  rw [idempotent] at once
  rw [zero_add] at none
  exact nontrivial (once.symm.trans none)

/-- The same failure for spaces: no operation on idempotently annotated spaces
recovers `S` from `S + T` and `T`. -/
theorem no_space_sub_undoes_merge {K : Type*} [AddCommMonoid K] [One K]
    (idempotent : ∀ a : K, a + a = a) (nontrivial : (1 : K) ≠ 0) (key : Key)
    (sub : Space K Key → Space K Key → Space K Key) :
    ¬ ∀ S T : Space K Key, sub (S + T) T = S := by
  intro cancel
  have once := cancel (Finsupp.single key 1) (Finsupp.single key 1)
  have none := cancel 0 (Finsupp.single key 1)
  rw [← Finsupp.single_add, idempotent] at once
  rw [zero_add] at none
  have := congrArg (fun S : Space K Key => S key) (once.symm.trans none)
  simp at this
  exact nontrivial this

/-- Over `ℕ`, monus undoes merging. -/
theorem nat_merge_sub_cancel (S T : Space ℕ Key) : (S + T) - T = S :=
  add_tsub_cancel_right S T

/-- Over `ℕ`, a join distributes over monus. -/
theorem nat_join_tsub (S T U : Space ℕ Key) : S * (T - U) = S * T - S * U := by
  ext k
  simp [Finsupp.mul_apply, Finsupp.tsub_apply, Nat.mul_sub]

/-- Over an idempotent semiring, merging a derived delta a second time is a
fixed point. -/
theorem idem_rederive_fixed {K : Type*} [IdemSemiring K] (S Δ : Space K Key) :
    S + Δ + Δ = S + Δ := by
  rw [add_assoc]
  congr 1
  ext k
  exact add_idem (Δ k)

/-- Over `ℕ`, re-deriving is a fixed point only for the empty delta. -/
theorem nat_rederive_fixed_iff (S Δ : Space ℕ Key) : S + Δ = S ↔ Δ = 0 :=
  add_eq_left

end SpaceCapabilities

/-! ## Controls -/

namespace Controls

/-- `(1, 0) * (0, 1) = 0` in `ℕ × ℕ`: a zero divisor. -/
theorem pair_zero_divisor : ((1, 0) : ℕ × ℕ) * (0, 1) = 0 := rfl

/-- **Possibility is not compositional with zero divisors**: an answer
supported positively, bound to one supported negatively, has empty
support. -/
theorem support_bind_fails_with_zero_divisors :
    (Ans.bind (Finsupp.single () ((1, 0) : ℕ × ℕ))
        (fun _ => (Finsupp.single () ((0, 1) : ℕ × ℕ)))).support = ∅ ∧
      (Finsupp.single () ((1, 0) : ℕ × ℕ)).support = {()} ∧
      (Finsupp.single () ((0, 1) : ℕ × ℕ)).support = {()} := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Ans.single_bind, Finsupp.smul_single, smul_eq_mul, pair_zero_divisor,
      Finsupp.single_zero, Finsupp.support_zero]
  · rw [Finsupp.support_single _ (by decide)]
  · rw [Finsupp.support_single _ (by decide)]

/-- Two noncommuting annotations. -/
def upper : Matrix (Fin 2) (Fin 2) ℕ := !![0, 1; 0, 0]

/-- Two noncommuting annotations. -/
def lower : Matrix (Fin 2) (Fin 2) ℕ := !![0, 0; 1, 0]

theorem upper_mul_lower_ne : upper * lower ≠ lower * upper := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [upper, lower, Matrix.mul_apply, Fin.sum_univ_two] at this

/-- **Without commutative annotations the answer monad is not commutative.** -/
theorem bind_not_comm_matrix :
    Ans.bind (Finsupp.single () upper)
        (fun _ => Ans.bind (Finsupp.single () lower) (fun _ => Ans.pure ())) ≠
      Ans.bind (Finsupp.single () lower)
        (fun _ => Ans.bind (Finsupp.single () upper) (fun _ => Ans.pure ())) := by
  intro h
  simp only [Ans.single_bind, Ans.pure, Finsupp.smul_single, smul_eq_mul, mul_one] at h
  have := congrArg (fun A : Ans (Matrix (Fin 2) (Fin 2) ℕ) Unit => A ()) h
  simp only [Finsupp.single_eq_same] at this
  exact upper_mul_lower_ne this

/-- **Join does not distribute over monus in `ℝ≥0∞`**, at `⊤`. -/
theorem ennreal_join_tsub_fails :
    ∃ S T U : Space ℝ≥0∞ Unit, S * (T - U) ≠ S * T - S * U := by
  refine ⟨Finsupp.single () ⊤, Finsupp.single () 2, Finsupp.single () 1, ?_⟩
  intro h
  have := congrArg (fun S : Space ℝ≥0∞ Unit => S ()) h
  simp only [Finsupp.mul_apply, Finsupp.tsub_apply, Finsupp.single_eq_same] at this
  have two_sub_one : (2 : ℝ≥0∞) - 1 = 1 := by
    rw [← one_add_one_eq_two, ENNReal.add_sub_cancel_right ENNReal.one_ne_top]
  rw [two_sub_one, mul_one, ENNReal.top_mul (by norm_num : (2 : ℝ≥0∞) ≠ 0), tsub_self] at this
  exact ENNReal.top_ne_zero this

/-- Over `ℕ` bags, re-deriving a nonempty delta is never a fixed point. -/
theorem nat_propagation_not_fixed :
    (Finsupp.single () 1 : Space ℕ Unit) + Finsupp.single () 1 ≠ Finsupp.single () 1 := by
  rw [Ne, nat_rederive_fixed_iff]
  simp

/-- Over presence, re-deriving is a fixed point. -/
theorem presence_propagation_fixed :
    (Finsupp.single () (1 : Presence) : Space Presence Unit) + Finsupp.single () 1 =
      Finsupp.single () 1 := by
  rw [← Finsupp.single_add, Presence.add_self]

end Controls

end Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
