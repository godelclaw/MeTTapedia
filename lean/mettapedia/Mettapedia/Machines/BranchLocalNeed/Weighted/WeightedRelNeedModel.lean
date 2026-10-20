import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Multiset.Basic
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSpec

/-!
# Weighted Relational Semantics of Call-Time Choice: Comonoids, Parameter Semirings, and Collapse

This module constructs the weighted relational model (`Rel_S`) over a commutative
semiring `S` and develops the comonoid structures that distinguish:
1. **Eager evaluation (`seq`):** diagonal comonoid on ground value webs `A`, where
   copying is `a ↦ (a, a)` and discarding is `a ↦ 1`.
2. **Call-time choice (`need`):** the affine-sharing comonoid on the pointed web
   `NeedWeb A = Option A` (`none` = never forced, `some a` = forced at least once
   with memoized value `a`), where weakening is `none ↦ 1, some a ↦ 0` and
   contraction maps `some a` to `(some a, some a) + (some a, none) + (none, some a)`.
3. **Run-time choice (`delay`, `quote`):** finite sequence webs `List A` (developed
   with bounded fuel and adequacy in `StressAndCommitments.lean`).

We also establish:
* **Failure of the Seely isomorphism** for `NeedWeb`:
  `card (NeedWeb (A ⊕ B)) < card (NeedWeb A × NeedWeb B)` for nonempty `A, B`.
* **Recursive comonoid lifting** `liftNeedComonoid` for arbitrary value webs `V`
  that already carry a comonoid (supporting cells inside data values and nested cells).
* **The 3-state ordered comonoid** `OrderedNeedWeb A = unused | first a | cached a`
  for noncommutative weights and event traces (`emit`), where the producer's
  effect is paid chronologically at the *first* (leftmost) force site and
  subsequent forces read `cached a` with unit weight.
* **Stratified `collapse`:** proof that `collapse` is not monotone in `Rel_ℕ`,
  that unstratified recursion through `collapse` has no fixed point, that
  stage-stratified `collapse` is compositional on need-closed computations, and
  that open `collapse` distinguishes pre-forced (`cached`) from inside-forced
  (`first`) cells.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.Weighted

open scoped BigOperators

/-! ## 1. Weighted Relations over a Commutative Semiring -/

/-- A weighted relation between webs `A` and `B` over a semiring `S`. -/
abbrev WRel (S : Type*) (A B : Type*) := A → B → S

/-- A weighted state (or answer distribution/multiset) over web `A`. -/
abbrev WState (S : Type*) (A : Type*) := A → S

namespace WRel

variable {S : Type*} [CommSemiring S]

/-- Identity weighted relation on a web with decidable equality. -/
def id (A : Type*) [DecidableEq A] : WRel S A A :=
  fun a₁ a₂ => if a₁ = a₂ then 1 else 0

/-- Relational composition in `Rel_S` over a finite intermediate web `B`. -/
def comp {A B C : Type*} [Fintype B] (R : WRel S A B) (T : WRel S B C) : WRel S A C :=
  fun a c => ∑ b : B, R a b * T b c

/-- Action of a weighted relation on a weighted state. -/
def applyState {A B : Type*} [Fintype A] (w : WState S A) (R : WRel S A B) : WState S B :=
  fun b => ∑ a : A, w a * R a b

/-- Tensor product of weighted relations on product webs. -/
def tensor {A₁ B₁ A₂ B₂ : Type*} (R₁ : WRel S A₁ B₁) (R₂ : WRel S A₂ B₂) :
    WRel S (A₁ × A₂) (B₁ × B₂) :=
  fun p q => R₁ p.1 q.1 * R₂ p.2 q.2

/-- Pointwise sum of weighted relations (`choose`). -/
def add {A B : Type*} (R₁ R₂ : WRel S A B) : WRel S A B :=
  fun a b => R₁ a b + R₂ a b

/-- Zero weighted relation (`fail`). -/
def zero (A B : Type*) : WRel S A B :=
  fun _ _ => 0

@[simp]
theorem comp_id_right {A B : Type*} [Fintype B] [DecidableEq B] (R : WRel S A B) :
    comp R (id B) = R := by
  funext a b
  simp [comp, id]

@[simp]
theorem comp_id_left {A B : Type*} [Fintype A] [DecidableEq A] (R : WRel S A B) :
    comp (id A) R = R := by
  funext a b
  simp [comp, id]

theorem comp_assoc {A B C D : Type*} [Fintype B] [Fintype C]
    (R : WRel S A B) (T : WRel S B C) (U : WRel S C D) :
    comp (comp R T) U = comp R (comp T U) := by
  funext a d
  simp only [comp, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_assoc]

end WRel

/-! ## 2. Comonoids in `Rel_S` -/

/-- A comonoid structure on a finite web `W` in `Rel_S`:
weakening `counit : W → S` and contraction `comult : W → W × W → S`
satisfying left counitality, right counitality, and coassociativity. -/
structure WebComonoid (S : Type*) [CommSemiring S] (W : Type*) [Fintype W] [DecidableEq W] where
  counit : W → S
  comult : W → (W × W) → S
  left_counit : ∀ w w₂ : W, (∑ w₁ : W, comult w (w₁, w₂) * counit w₁) =
    if w = w₂ then 1 else 0
  right_counit : ∀ w w₁ : W, (∑ w₂ : W, comult w (w₁, w₂) * counit w₂) =
    if w = w₁ then 1 else 0
  coassoc : ∀ w w₁ w₂ w₃ : W,
    (∑ u : W, comult w (u, w₃) * comult u (w₁, w₂)) =
      (∑ v : W, comult w (w₁, v) * comult v (w₂, w₃))

/-- A cocommutative comonoid on a finite web `W` in `Rel_S`. -/
structure SymWebComonoid (S : Type*) [CommSemiring S] (W : Type*) [Fintype W] [DecidableEq W]
    extends WebComonoid S W where
  cocomm : ∀ w w₁ w₂ : W, comult w (w₁, w₂) = comult w (w₂, w₁)

/-- Helper lemma decomposing a finite sum over `Option A` into `none` and `some a`. -/
@[simp]
theorem sum_option {S : Type*} [AddCommMonoid S] {A : Type*} [Fintype A]
    (f : Option A → S) :
    (∑ u : Option A, f u) = f none + ∑ a : A, f (some a) :=
  Fintype.sum_option f

/-- Helper lemma decomposing a finite sum over `W₁ × W₂` into nested sums. -/
theorem sum_prod {S : Type*} [AddCommMonoid S] {W₁ W₂ : Type*} [Fintype W₁] [Fintype W₂]
    (f : W₁ × W₂ → S) :
    (∑ p : W₁ × W₂, f p) = ∑ x₁ : W₁, ∑ x₂ : W₂, f (x₁, x₂) :=
  Fintype.sum_prod_type f

/-! ### 2a. Ground (Eager Value) Diagonal Comonoid -/

section GroundComonoid

variable {S : Type*} [CommSemiring S] {A : Type*} [Fintype A] [DecidableEq A]

/-- Ground value weakening: every value can be discarded with weight `1`. -/
def groundCounit : A → S := fun _ => 1

/-- Ground value contraction: diagonal duplication `a ↦ (a, a)`. -/
def groundComult : A → (A × A) → S :=
  fun a p => if p.1 = a ∧ p.2 = a then 1 else 0

/-- Ground value types carry a symmetric comonoid structure via diagonal duplication. -/
def groundSymComonoid : SymWebComonoid S A where
  counit := groundCounit
  comult := groundComult
  left_counit := by
    intro a a₂
    simp only [groundComult, groundCounit, mul_one]
    have h : (∑ w₁ : A, if w₁ = a ∧ a₂ = a then (1 : S) else 0) =
        ∑ w₁ : A, if w₁ = a then (if a = a₂ then (1 : S) else 0) else 0 := by
      refine Finset.sum_congr rfl fun w₁ _ => ?_
      by_cases h1 : w₁ = a <;> by_cases h2 : a = a₂ <;> simp_all [eq_comm]
    rw [h, Finset.sum_ite_eq' Finset.univ a]
    simp
  right_counit := by
    intro a a₁
    simp only [groundComult, groundCounit, mul_one]
    have h : (∑ w₂ : A, if a₁ = a ∧ w₂ = a then (1 : S) else 0) =
        ∑ w₂ : A, if w₂ = a then (if a = a₁ then (1 : S) else 0) else 0 := by
      refine Finset.sum_congr rfl fun w₂ _ => ?_
      by_cases h1 : a = a₁ <;> by_cases h2 : w₂ = a <;> simp_all [eq_comm]
    rw [h, Finset.sum_ite_eq' Finset.univ a]
    simp
  coassoc := by
    intro a a₁ a₂ a₃
    have lhs_eq : (∑ u : A, groundComult a (u, a₃) * groundComult u (a₁, a₂) : S) =
        if a₁ = a ∧ a₂ = a ∧ a₃ = a then 1 else 0 := by
      have h : (∑ u : A, groundComult a (u, a₃) * groundComult u (a₁, a₂) : S) =
          ∑ u : A, if u = a then (if a₁ = a ∧ a₂ = a ∧ a₃ = a then (1 : S) else 0) else 0 := by
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hu : u = a
        · subst hu
          by_cases h1 : a₁ = u <;> by_cases h2 : a₂ = u <;> by_cases h3 : a₃ = u <;>
            simp [groundComult, h1, h2, h3]
        · simp [groundComult, hu]
      rw [h, Finset.sum_ite_eq' Finset.univ a]
      simp
    have rhs_eq : (∑ v : A, groundComult a (a₁, v) * groundComult v (a₂, a₃) : S) =
        if a₁ = a ∧ a₂ = a ∧ a₃ = a then 1 else 0 := by
      have h : (∑ v : A, groundComult a (a₁, v) * groundComult v (a₂, a₃) : S) =
          ∑ v : A, if v = a then (if a₁ = a ∧ a₂ = a ∧ a₃ = a then (1 : S) else 0) else 0 := by
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hv : v = a
        · subst hv
          by_cases h1 : a₁ = v <;> by_cases h2 : a₂ = v <;> by_cases h3 : a₃ = v <;>
            simp [groundComult, h1, h2, h3]
        · simp [groundComult, hv]
      rw [h, Finset.sum_ite_eq' Finset.univ a]
      simp
    rw [lhs_eq, rhs_eq]
  cocomm := by
    intro a a₁ a₂
    simp only [groundComult]
    by_cases h1 : a₁ = a <;> by_cases h2 : a₂ = a <;> simp [h1, h2]

end GroundComonoid

/-! ### 2b. The Affine-Sharing (`NeedWeb`) Comonoid -/

/-- The web of a memoized `need` cell over value web `A`:
`none` (`*`) means "never forced"; `some a` means "forced at least once, caching `a`". -/
abbrev NeedWeb (A : Type*) := Option A

section NeedComonoid

variable {S : Type*} [CommSemiring S] {A : Type*} [Fintype A] [DecidableEq A]

/-- Weakening on `NeedWeb A`: `none ↦ 1` (an unused cell is never forced) and `some a ↦ 0`. -/
def needCounit : NeedWeb A → S
  | none => 1
  | some _ => 0

/-- Contraction on `NeedWeb A`:
* `none` splits only as `(none, none)`.
* `some a` splits into the three nonempty usage patterns
  `(some a, some a)`, `(some a, none)`, and `(none, some a)`. -/
def needComult : NeedWeb A → (NeedWeb A × NeedWeb A) → S
  | none, (none, none) => 1
  | some a, (some a₁, some a₂) => if a₁ = a ∧ a₂ = a then 1 else 0
  | some a, (some a₁, none) => if a₁ = a then 1 else 0
  | some a, (none, some a₂) => if a₂ = a then 1 else 0
  | _, _ => 0

omit [Fintype A] in
theorem needComult_cocomm (u u₁ u₂ : NeedWeb A) :
    (needComult u (u₁, u₂) : S) = needComult u (u₂, u₁) := by
  cases u with
  | none =>
      cases u₁ <;> cases u₂ <;> rfl
  | some a =>
      cases u₁ with
      | none =>
          cases u₂ <;> rfl
      | some a₁ =>
          cases u₂ with
          | none => rfl
          | some a₂ =>
              simp only [needComult]
              by_cases h1 : a₁ = a <;> by_cases h2 : a₂ = a <;> simp [h1, h2]

theorem needComult_left_counit (u u₂ : NeedWeb A) :
    (∑ u₁ : NeedWeb A, needComult u (u₁, u₂) * needCounit u₁ : S) =
      if u = u₂ then 1 else 0 := by
  rw [sum_option]
  have hsome : (∑ a₁ : A, needComult u (some a₁, u₂) * needCounit (some a₁) : S) = 0 := by
    refine Finset.sum_eq_zero fun a₁ _ => ?_
    simp [needCounit]
  rw [hsome, add_zero]
  cases u with
  | none =>
      cases u₂ <;> simp [needComult, needCounit]
  | some a =>
      cases u₂ with
      | none => simp [needComult, needCounit]
      | some a₂ =>
          simp only [needComult, needCounit, mul_one, Option.some.injEq]
          by_cases h : a = a₂
          · subst h; simp
          · have hne : a₂ ≠ a := Ne.symm h
            simp [h, hne]

theorem needComult_right_counit (u u₁ : NeedWeb A) :
    (∑ u₂ : NeedWeb A, needComult u (u₁, u₂) * needCounit u₂ : S) =
      if u = u₁ then 1 else 0 := by
  have hswap : (∑ u₂ : NeedWeb A, needComult u (u₁, u₂) * needCounit u₂ : S) =
      ∑ u₂ : NeedWeb A, needComult u (u₂, u₁) * needCounit u₂ := by
    refine Finset.sum_congr rfl fun u₂ _ => ?_
    rw [needComult_cocomm]
  rw [hswap]
  exact needComult_left_counit u u₁

/-- Explicit characterization of the ternary contraction on `NeedWeb A`:
`some a` splits into `(u₁, u₂, u₃)` with weight `1` iff every `uᵢ ∈ {none, some a}`
and at least one `uᵢ = some a`. -/
def needTernary (u u₁ u₂ u₃ : NeedWeb A) : S :=
  match u with
  | none => if u₁ = none ∧ u₂ = none ∧ u₃ = none then 1 else 0
  | some a =>
      if (u₁ = none ∨ u₁ = some a) ∧
         (u₂ = none ∨ u₂ = some a) ∧
         (u₃ = none ∨ u₃ = some a) ∧
         (u₁ = some a ∨ u₂ = some a ∨ u₃ = some a)
      then 1 else 0

theorem needComult_coassoc_lhs (u u₁ u₂ u₃ : NeedWeb A) :
    (∑ w : NeedWeb A, needComult u (w, u₃) * needComult w (u₁, u₂) : S) =
      needTernary u u₁ u₂ u₃ := by
  rw [sum_option]
  cases u with
  | none =>
      have hsome : (∑ a : A, needComult (none : NeedWeb A) (some a, u₃) *
          needComult (some a) (u₁, u₂) : S) = 0 := by
        refine Finset.sum_eq_zero fun a _ => ?_
        cases u₃ <;> simp [needComult]
      rw [hsome, add_zero]
      cases u₁ <;> cases u₂ <;> cases u₃ <;> simp [needComult, needTernary]
  | some a =>
      have hsome : (∑ x : A, needComult (some a) (some x, u₃) *
          needComult (some x) (u₁, u₂) : S) =
          needComult (some a) (some a, u₃) * needComult (some a) (u₁, u₂) := by
        have hrew : (∑ x : A, needComult (some a) (some x, u₃) *
            needComult (some x) (u₁, u₂) : S) =
            ∑ x : A, if x = a then
              needComult (some a) (some a, u₃) * needComult (some a) (u₁, u₂) else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : x = a
          · subst hx; simp
          · cases u₃ <;> simp [needComult, hx]
        rw [hrew, Finset.sum_ite_eq' Finset.univ a]
        simp
      rw [hsome]
      cases u₁ with
      | none =>
          cases u₂ with
          | none =>
              cases u₃ with
              | none => simp [needComult, needTernary]
              | some a₃ =>
                  by_cases h3 : a₃ = a <;> simp [needComult, needTernary, h3]
          | some a₂ =>
              cases u₃ with
              | none =>
                  by_cases h2 : a₂ = a <;> simp [needComult, needTernary, h2]
              | some a₃ =>
                  by_cases h2 : a₂ = a <;> by_cases h3 : a₃ = a <;>
                    simp [needComult, needTernary, h2, h3]
      | some a₁ =>
          cases u₂ with
          | none =>
              cases u₃ with
              | none =>
                  by_cases h1 : a₁ = a <;> simp [needComult, needTernary, h1]
              | some a₃ =>
                  by_cases h1 : a₁ = a <;> by_cases h3 : a₃ = a <;>
                    simp [needComult, needTernary, h1, h3]
          | some a₂ =>
              cases u₃ with
              | none =>
                  by_cases h1 : a₁ = a <;> by_cases h2 : a₂ = a <;>
                    simp [needComult, needTernary, h1, h2]
              | some a₃ =>
                  by_cases h1 : a₁ = a <;> by_cases h2 : a₂ = a <;> by_cases h3 : a₃ = a <;>
                    simp [needComult, needTernary, h1, h2, h3]

theorem needComult_coassoc (u u₁ u₂ u₃ : NeedWeb A) :
    (∑ w : NeedWeb A, needComult u (w, u₃) * needComult w (u₁, u₂) : S) =
      (∑ v : NeedWeb A, needComult u (u₁, v) * needComult v (u₂, u₃) : S) := by
  have rhs_swap :
      (∑ v : NeedWeb A, needComult u (u₁, v) * needComult v (u₂, u₃) : S) =
        ∑ v : NeedWeb A, needComult u (v, u₁) * needComult v (u₂, u₃) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [needComult_cocomm u u₁ v]
  rw [needComult_coassoc_lhs, rhs_swap, needComult_coassoc_lhs]
  cases u with
  | none =>
      cases u₁ <;> cases u₂ <;> cases u₃ <;> simp [needTernary]
  | some a =>
      simp only [needTernary]
      by_cases h1n : u₁ = none <;>
      by_cases h2n : u₂ = none <;>
      by_cases h3n : u₃ = none <;>
      by_cases h1s : u₁ = some a <;>
      by_cases h2s : u₂ = some a <;>
      by_cases h3s : u₃ = some a <;>
      simp [h1n, h2n, h3n, h1s, h2s, h3s]

/-- The affine-sharing comonoid on `NeedWeb A = Option A`. -/
def needSymComonoid : SymWebComonoid S (NeedWeb A) where
  counit := needCounit
  comult := needComult
  left_counit := needComult_left_counit
  right_counit := needComult_right_counit
  coassoc := needComult_coassoc
  cocomm := needComult_cocomm

/-- Composition with a `need` binder in `Rel_S`:
given a producer state `w : WState S A` and a body relation `body : WRel S (NeedWeb A) B`,
`bindNeed w body b = (∑ a, w a * body (some a) b) + body none b`. -/
def bindNeed {B : Type*} (w : WState S A) (body : WRel S (NeedWeb A) B) : WState S B :=
  fun b => (∑ a : A, w a * body (some a) b) + body none b

/-- Forcing a `need` cell in `Rel_S` extracts `a` from `some a` and rejects `none`. -/
def forceNeedRel : WRel S (NeedWeb A) A
  | none, _ => 0
  | some a₁, a₂ => if a₁ = a₂ then 1 else 0

/-- Positive law: forcing a fresh `need` cell once reproduces the producer's exact weights. -/
theorem bindNeed_forceNeedRel (w : WState S A) :
    bindNeed w forceNeedRel = w := by
  funext a
  simp [bindNeed, forceNeedRel]

omit [DecidableEq A] in
/-- Positive law: discarding a `need` cell (`needCounit`) ignores the producer's weights
and always yields weight `1`. -/
theorem bindNeed_discard (w : WState S A) :
    (∑ u : NeedWeb A, (match u with | none => 1 | some a => w a) * needCounit u : S) = 1 := by
  rw [sum_option]
  simp [needCounit]

/-- Positive law: forcing a `need` cell twice and pairing the results yields the
diagonal distribution `(a, a)` with weight `w a` (call-time choice). -/
theorem bindNeed_double_diagonal (w : WState S A) (a₁ a₂ : A) :
    bindNeed w (fun u (p : A × A) =>
      ∑ u₁ : NeedWeb A, ∑ u₂ : NeedWeb A,
        needComult u (u₁, u₂) * forceNeedRel u₁ p.1 * forceNeedRel u₂ p.2) (a₁, a₂) =
      if a₁ = a₂ then w a₁ else 0 := by
  simp only [bindNeed]
  have hnone :
      (∑ u₁ : NeedWeb A, ∑ u₂ : NeedWeb A,
        needComult (none : NeedWeb A) (u₁, u₂) * forceNeedRel u₁ a₁ * forceNeedRel u₂ a₂ : S) = 0 := by
    rw [sum_option]
    simp [needComult, forceNeedRel]
  rw [hnone, add_zero]
  have hbody : ∀ a : A,
      (∑ u₁ : NeedWeb A, ∑ u₂ : NeedWeb A,
        needComult (some a) (u₁, u₂) * forceNeedRel u₁ a₁ * forceNeedRel u₂ a₂ : S) =
        if a₁ = a ∧ a₂ = a then 1 else 0 := by
    intro a
    rw [sum_option]
    have hnone1 : (∑ u₂ : NeedWeb A,
        needComult (some a) (none, u₂) * forceNeedRel (none : NeedWeb A) a₁ * forceNeedRel u₂ a₂ : S) = 0 := by
      simp [forceNeedRel]
    rw [hnone1, zero_add]
    have h1 : (∑ x : A, ∑ u₂ : NeedWeb A,
        needComult (some a) (some x, u₂) * forceNeedRel (some x) a₁ *
          forceNeedRel u₂ a₂ : S) =
        ∑ u₂ : NeedWeb A, needComult (some a) (some a₁, u₂) * forceNeedRel u₂ a₂ := by
      have hrew : (∑ x : A, ∑ u₂ : NeedWeb A,
          needComult (some a) (some x, u₂) * forceNeedRel (some x) a₁ *
            forceNeedRel u₂ a₂ : S) =
          ∑ x : A, if x = a₁ then
            (∑ u₂ : NeedWeb A, needComult (some a) (some a₁, u₂) * forceNeedRel u₂ a₂) else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : x = a₁
        · subst hx; simp [forceNeedRel]
        · simp [forceNeedRel, hx]
      rw [hrew, Finset.sum_ite_eq' Finset.univ a₁]
      simp
    rw [h1, sum_option]
    simp [forceNeedRel, needComult]
  simp only [hbody]
  have hsum : (∑ a : A, w a * (if a₁ = a ∧ a₂ = a then (1 : S) else 0)) =
      ∑ a : A, if a = a₁ then (if a₁ = a₂ then w a₁ else 0) else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha1 : a = a₁
    · subst ha1
      by_cases ha2 : a₂ = a <;> simp [ha2, eq_comm]
    · have hne : a₁ ≠ a := Ne.symm ha1
      simp [ha1, hne]
  rw [hsum, Finset.sum_ite_eq' Finset.univ a₁]
  simp

end NeedComonoid

/-! ## 3. Failure of the Seely Isomorphism for `NeedWeb` -/

section NoSeely

/-- `NeedWeb (A ⊕ B)` has cardinality `1 + |A| + |B|`, whereas
`NeedWeb A × NeedWeb B` has cardinality `(1 + |A|) * (1 + |B|) = 1 + |A| + |B| + |A| * |B|`.
Whenever `A` and `B` are nonempty, the two webs do not even have the same cardinality. -/
theorem needWeb_no_seely_card (A B : Type*) [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    Fintype.card (NeedWeb (A ⊕ B)) < Fintype.card (NeedWeb A × NeedWeb B) := by
  have hA : 0 < Fintype.card A := Fintype.card_pos
  have hB : 0 < Fintype.card B := Fintype.card_pos
  simp only [NeedWeb, Fintype.card_option, Fintype.card_sum, Fintype.card_prod]
  have hmul : 0 < Fintype.card A * Fintype.card B := Nat.mul_pos hA hB
  rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- Concrete witness: for `A = Unit` and `B = Unit`, `NeedWeb (Unit ⊕ Unit)` has 3 elements,
while `NeedWeb Unit × NeedWeb Unit` has 4 elements (the pair `(some (), some ())` simultaneously
forces both cells, which has no counterpart in `NeedWeb (Unit ⊕ Unit)`). -/
theorem needWeb_unit_cards :
    Fintype.card (NeedWeb (Unit ⊕ Unit)) = 3 ∧
      Fintype.card (NeedWeb Unit × NeedWeb Unit) = 4 := by
  decide

/-- Genuine Seely non-isomorphism theorem: for any nonempty finite webs `A` and `B`,
there is no equivalence (bijection) between `NeedWeb (A ⊕ B)` and `NeedWeb A × NeedWeb B`. -/
theorem needWeb_no_seely_equiv (A B : Type*) [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    IsEmpty (NeedWeb (A ⊕ B) ≃ NeedWeb A × NeedWeb B) := by
  refine ⟨fun e => ?_⟩
  have hcard : Fintype.card (NeedWeb (A ⊕ B)) = Fintype.card (NeedWeb A × NeedWeb B) :=
    Fintype.card_congr e
  have hlt := needWeb_no_seely_card A B
  omega

end NoSeely

/-! ## 4. Recursive Comonoid Lifting and Tensor Products (Task 5b: Cells in Data & Nested Cells) -/

section RecursiveComonoid

variable {S : Type*} [CommSemiring S]

/-- Tensor product of two web comonoids in `Rel_S`: models pairs and multi-field
constructors containing memoized cells or thunks, as well as multi-variable contexts. -/
def tensorWebComonoid {W₁ W₂ : Type*} [Fintype W₁] [Fintype W₂]
    [DecidableEq W₁] [DecidableEq W₂]
    (C₁ : WebComonoid S W₁) (C₂ : WebComonoid S W₂) : WebComonoid S (W₁ × W₂) where
  counit p := C₁.counit p.1 * C₂.counit p.2
  comult p q := C₁.comult p.1 (q.1.1, q.2.1) * C₂.comult p.2 (q.1.2, q.2.2)
  left_counit := by
    intro ⟨w₁, w₂⟩ ⟨u₁, u₂⟩
    rw [sum_prod]
    have h : (∑ x₁ : W₁, ∑ x₂ : W₂,
        C₁.comult w₁ (x₁, u₁) * C₂.comult w₂ (x₂, u₂) * (C₁.counit x₁ * C₂.counit x₂)) =
        (∑ x₁ : W₁, C₁.comult w₁ (x₁, u₁) * C₁.counit x₁) *
          (∑ x₂ : W₂, C₂.comult w₂ (x₂, u₂) * C₂.counit x₂) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x₂ _ => ?_
      exact mul_mul_mul_comm _ _ _ _
    rw [h, C₁.left_counit, C₂.left_counit]
    by_cases h1 : w₁ = u₁ <;> by_cases h2 : w₂ = u₂ <;> simp [Prod.ext_iff, h1, h2]
  right_counit := by
    intro ⟨w₁, w₂⟩ ⟨u₁, u₂⟩
    rw [sum_prod]
    have h : (∑ x₁ : W₁, ∑ x₂ : W₂,
        C₁.comult w₁ (u₁, x₁) * C₂.comult w₂ (u₂, x₂) * (C₁.counit x₁ * C₂.counit x₂)) =
        (∑ x₁ : W₁, C₁.comult w₁ (u₁, x₁) * C₁.counit x₁) *
          (∑ x₂ : W₂, C₂.comult w₂ (u₂, x₂) * C₂.counit x₂) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x₂ _ => ?_
      exact mul_mul_mul_comm _ _ _ _
    rw [h, C₁.right_counit, C₂.right_counit]
    by_cases h1 : w₁ = u₁ <;> by_cases h2 : w₂ = u₂ <;> simp [Prod.ext_iff, h1, h2]
  coassoc := by
    intro ⟨w₁, w₂⟩ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
    rw [sum_prod, sum_prod]
    have hlhs : (∑ u₁ : W₁, ∑ u₂ : W₂,
        C₁.comult w₁ (u₁, c₁) * C₂.comult w₂ (u₂, c₂) *
          (C₁.comult u₁ (a₁, b₁) * C₂.comult u₂ (a₂, b₂))) =
        (∑ u₁ : W₁, C₁.comult w₁ (u₁, c₁) * C₁.comult u₁ (a₁, b₁)) *
          (∑ u₂ : W₂, C₂.comult w₂ (u₂, c₂) * C₂.comult u₂ (a₂, b₂)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun u₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u₂ _ => ?_
      exact mul_mul_mul_comm _ _ _ _
    have hrhs : (∑ v₁ : W₁, ∑ v₂ : W₂,
        C₁.comult w₁ (a₁, v₁) * C₂.comult w₂ (a₂, v₂) *
          (C₁.comult v₁ (b₁, c₁) * C₂.comult v₂ (b₂, c₂))) =
        (∑ v₁ : W₁, C₁.comult w₁ (a₁, v₁) * C₁.comult v₁ (b₁, c₁)) *
          (∑ v₂ : W₂, C₂.comult w₂ (a₂, v₂) * C₂.comult v₂ (b₂, c₂)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun v₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v₂ _ => ?_
      exact mul_mul_mul_comm _ _ _ _
    rw [hlhs, hrhs, C₁.coassoc, C₂.coassoc]

/-- Recursive lifting of ANY `WebComonoid S V` to `NeedWeb V = Option V`:
when a memoized cell caches a value of type `V` that itself contains cells
(e.g., `S (.need ℓ)` or `Pair (.need ℓ₁) (.need ℓ₂)`), two forces of the outer cell
share the inner cell(s) via `C.comult`. -/
def liftNeedComult {V : Type*} [DecidableEq V] (comultV : V → V × V → S) :
    NeedWeb V → NeedWeb V × NeedWeb V → S
  | none, (none, none) => 1
  | some v, (some v₁, some v₂) => comultV v (v₁, v₂)
  | some v, (some v₁, none) => if v = v₁ then 1 else 0
  | some v, (none, some v₂) => if v = v₂ then 1 else 0
  | _, _ => 0

def liftNeedComonoid {V : Type*} [Fintype V] [DecidableEq V]
    (C : WebComonoid S V) : WebComonoid S (NeedWeb V) where
  counit := needCounit
  comult := liftNeedComult C.comult
  left_counit := by
    intro u u₂
    rw [sum_option]
    have hsome : (∑ v₁ : V, liftNeedComult C.comult u (some v₁, u₂) * needCounit (some v₁) : S) = 0 := by
      refine Finset.sum_eq_zero fun v₁ _ => ?_
      simp [needCounit]
    rw [hsome, add_zero]
    cases u with
    | none =>
        cases u₂ <;> simp [liftNeedComult, needCounit]
    | some v =>
        cases u₂ with
        | none => simp [liftNeedComult, needCounit]
        | some v₂ =>
            simp [liftNeedComult, needCounit]
  right_counit := by
    intro u u₁
    rw [sum_option]
    have hsome : (∑ v₂ : V, liftNeedComult C.comult u (u₁, some v₂) * needCounit (some v₂) : S) = 0 := by
      refine Finset.sum_eq_zero fun v₂ _ => ?_
      simp [needCounit]
    rw [hsome, add_zero]
    cases u with
    | none =>
        cases u₁ <;> simp [liftNeedComult, needCounit]
    | some v =>
        cases u₁ with
        | none => simp [liftNeedComult, needCounit]
        | some v₁ =>
            simp [liftNeedComult, needCounit]
  coassoc := by
    intro u u₁ u₂ u₃
    rw [sum_option, sum_option]
    cases u with
    | none =>
        have hl : (∑ x : V, liftNeedComult C.comult (none : NeedWeb V) (some x, u₃) *
            liftNeedComult C.comult (some x) (u₁, u₂) : S) = 0 := by
          refine Finset.sum_eq_zero fun x _ => ?_
          cases u₃ <;> simp [liftNeedComult]
        have hr : (∑ x : V, liftNeedComult C.comult (none : NeedWeb V) (u₁, some x) *
            liftNeedComult C.comult (some x) (u₂, u₃) : S) = 0 := by
          refine Finset.sum_eq_zero fun x _ => ?_
          cases u₁ <;> simp [liftNeedComult]
        rw [hl, hr, add_zero, add_zero]
        cases u₁ <;> cases u₂ <;> cases u₃ <;> simp [liftNeedComult]
    | some v =>
        cases u₁ with
        | none =>
            cases u₂ with
            | none =>
                cases u₃ with
                | none =>
                    simp [liftNeedComult]
                | some v₃ =>
                    simp [liftNeedComult]
            | some v₂ =>
                cases u₃ with
                | none =>
                    simp [liftNeedComult]
                | some v₃ =>
                    have hl : (∑ x : V, C.comult v (x, v₃) * (if x = v₂ then (1 : S) else 0)) =
                        C.comult v (v₂, v₃) := by simp
                    have hr : (∑ x : V, (if v = x then (1 : S) else 0) * C.comult x (v₂, v₃)) =
                        C.comult v (v₂, v₃) := by
                      have h : (∑ x : V, (if v = x then (1 : S) else 0) * C.comult x (v₂, v₃)) =
                          ∑ x : V, if x = v then C.comult v (v₂, v₃) else 0 := by
                        refine Finset.sum_congr rfl fun x _ => ?_
                        by_cases hx : x = v
                        · subst hx; simp
                        · have hne : v ≠ x := Ne.symm hx
                          simp [hx, hne]
                      rw [h, Finset.sum_ite_eq' Finset.univ v]; simp
                    simp only [liftNeedComult, mul_zero, zero_add]
                    rw [hl, hr]
        | some v₁ =>
            cases u₂ with
            | none =>
                cases u₃ with
                | none =>
                    have hl : (∑ x : V, (if v = x then (1 : S) else 0) *
                        (if x = v₁ then (1 : S) else 0)) = if v = v₁ then 1 else 0 := by
                      have h : (∑ x : V, (if v = x then (1 : S) else 0) *
                          (if x = v₁ then (1 : S) else 0)) =
                          ∑ x : V, if x = v then (if v = v₁ then (1 : S) else 0) else 0 := by
                        refine Finset.sum_congr rfl fun x _ => ?_
                        by_cases hx : x = v
                        · subst hx; simp
                        · have hne : v ≠ x := Ne.symm hx
                          simp [hx, hne]
                      rw [h, Finset.sum_ite_eq' Finset.univ v]; simp
                    simp only [liftNeedComult, mul_zero, zero_add, mul_one]
                    rw [hl]
                    simp
                | some v₃ =>
                    have hl : (∑ x : V, C.comult v (x, v₃) * (if x = v₁ then (1 : S) else 0)) =
                        C.comult v (v₁, v₃) := by simp
                    have hr : (∑ x : V, C.comult v (v₁, x) * (if x = v₃ then (1 : S) else 0)) =
                        C.comult v (v₁, v₃) := by simp
                    simp only [liftNeedComult, mul_zero, zero_add]
                    rw [hl, hr]
            | some v₂ =>
                cases u₃ with
                | none =>
                    have hl : (∑ x : V, (if v = x then (1 : S) else 0) * C.comult x (v₁, v₂)) =
                        C.comult v (v₁, v₂) := by
                      have h : (∑ x : V, (if v = x then (1 : S) else 0) * C.comult x (v₁, v₂)) =
                          ∑ x : V, if x = v then C.comult v (v₁, v₂) else 0 := by
                        refine Finset.sum_congr rfl fun x _ => ?_
                        by_cases hx : x = v
                        · subst hx; simp
                        · have hne : v ≠ x := Ne.symm hx
                          simp [hx, hne]
                      rw [h, Finset.sum_ite_eq' Finset.univ v]; simp
                    have hr : (∑ x : V, C.comult v (v₁, x) * (if x = v₂ then (1 : S) else 0)) =
                        C.comult v (v₁, v₂) := by simp
                    simp only [liftNeedComult, mul_zero, zero_add]
                    rw [hl, hr]
                | some v₃ =>
                    simp only [liftNeedComult, mul_zero, zero_add]
                    exact C.coassoc v v₁ v₂ v₃

end RecursiveComonoid

/-! ## 5. The 3-State Ordered Comonoid for Event Traces and Noncommutative Weights (Task 7i) -/

/-- When a semiring `S` is noncommutative, or when we observe `(value, event trace)`
pairs where `emit` order matters, a memoized cell's producer trace `τ` is emitted
at the **first** (leftmost) `force` in execution order, while all subsequent forces
read the cached value `a` with an empty trace.
`OrderedNeedWeb A` refines `NeedWeb A` into three states:
* `unused`: never forced in this subcomputation;
* `first a`: forced for the first time in this subcomputation (pays producer weight/trace);
* `cached a`: forced in this subcomputation after having already been forced earlier. -/
inductive OrderedNeedWeb (A : Type*) where
  | unused
  | first (value : A)
  | cached (value : A)
  deriving DecidableEq, Repr

namespace OrderedNeedWeb

variable {A : Type*}

/-- Collapse the chronological distinction between `first a` and `cached a` to `NeedWeb A`. -/
def toNeedWeb : OrderedNeedWeb A → NeedWeb A
  | .unused => none
  | .first a => some a
  | .cached a => some a

end OrderedNeedWeb

section OrderedNeedComonoid

variable {S : Type*} [Semiring S] {A : Type*} [Fintype A] [DecidableEq A]

/-- Weakening on `OrderedNeedWeb A`: only `unused` can be discarded. -/
def orderedNeedCounit : OrderedNeedWeb A → S
  | .unused => 1
  | .first _ => 0
  | .cached _ => 0

/-- Chronological (non-cocommutative) contraction on `OrderedNeedWeb A`:
* `unused` splits only as `(unused, unused)`.
* `first a` splits as `(first a, cached a)` (forced in both: left is first, right reads cache),
  `(first a, unused)` (forced only on left), or `(unused, first a)` (forced only on right).
* `cached a` splits as `(cached a, cached a)`, `(cached a, unused)`, or `(unused, cached a)`. -/
def orderedNeedComult : OrderedNeedWeb A → (OrderedNeedWeb A × OrderedNeedWeb A) → S
  | .unused, (.unused, .unused) => 1
  | .first a, (.first a₁, .cached a₂) => if a₁ = a ∧ a₂ = a then 1 else 0
  | .first a, (.first a₁, .unused) => if a₁ = a then 1 else 0
  | .first a, (.unused, .first a₂) => if a₂ = a then 1 else 0
  | .cached a, (.cached a₁, .cached a₂) => if a₁ = a ∧ a₂ = a then 1 else 0
  | .cached a, (.cached a₁, .unused) => if a₁ = a then 1 else 0
  | .cached a, (.unused, .cached a₂) => if a₂ = a then 1 else 0
  | _, _ => 0

/-- Sum over `OrderedNeedWeb A` defined directly via `unused`, `first a`, and `cached a`. -/
def sumOrderedNeed (f : OrderedNeedWeb A → S) : S :=
  f .unused + (∑ a : A, f (.first a)) + (∑ a : A, f (.cached a))

theorem orderedNeed_left_counit (u u₂ : OrderedNeedWeb A) :
    sumOrderedNeed (fun u₁ => orderedNeedComult u (u₁, u₂) * orderedNeedCounit u₁ : OrderedNeedWeb A → S) =
      if u = u₂ then 1 else 0 := by
  unfold sumOrderedNeed
  simp only [orderedNeedCounit, mul_zero, Finset.sum_const_zero, add_zero, mul_one]
  cases u with
  | unused =>
      cases u₂ <;> simp [orderedNeedComult]
  | first a =>
      cases u₂ with
      | unused => simp [orderedNeedComult]
      | first a₂ =>
          simp only [orderedNeedComult, OrderedNeedWeb.first.injEq]
          by_cases h : a = a₂
          · subst h; simp
          · have hne : a₂ ≠ a := Ne.symm h
            simp [h, hne]
      | cached a₂ => simp [orderedNeedComult]
  | cached a =>
      cases u₂ with
      | unused => simp [orderedNeedComult]
      | first a₂ => simp [orderedNeedComult]
      | cached a₂ =>
          simp only [orderedNeedComult, OrderedNeedWeb.cached.injEq]
          by_cases h : a = a₂
          · subst h; simp
          · have hne : a₂ ≠ a := Ne.symm h
            simp [h, hne]

theorem orderedNeed_right_counit (u u₁ : OrderedNeedWeb A) :
    sumOrderedNeed (fun u₂ => orderedNeedComult u (u₁, u₂) * orderedNeedCounit u₂ : OrderedNeedWeb A → S) =
      if u = u₁ then 1 else 0 := by
  unfold sumOrderedNeed
  simp only [orderedNeedCounit, mul_zero, Finset.sum_const_zero, add_zero, mul_one]
  cases u with
  | unused =>
      cases u₁ <;> simp [orderedNeedComult]
  | first a =>
      cases u₁ with
      | unused => simp [orderedNeedComult]
      | first a₁ =>
          simp only [orderedNeedComult, OrderedNeedWeb.first.injEq]
          by_cases h : a = a₁
          · subst h; simp
          · have hne : a₁ ≠ a := Ne.symm h
            simp [h, hne]
      | cached a₁ => simp [orderedNeedComult]
  | cached a =>
      cases u₁ with
      | unused => simp [orderedNeedComult]
      | first a₁ => simp [orderedNeedComult]
      | cached a₁ =>
          simp only [orderedNeedComult, OrderedNeedWeb.cached.injEq]
          by_cases h : a = a₁
          · subst h; simp
          · have hne : a₁ ≠ a := Ne.symm h
            simp [h, hne]

theorem orderedNeed_coassoc (u u₁ u₂ u₃ : OrderedNeedWeb A) :
    sumOrderedNeed (fun w => orderedNeedComult u (w, u₃) * orderedNeedComult w (u₁, u₂) : OrderedNeedWeb A → S) =
      sumOrderedNeed (fun v => orderedNeedComult u (u₁, v) * orderedNeedComult v (u₂, u₃) : OrderedNeedWeb A → S) := by
  unfold sumOrderedNeed
  cases u with
  | unused =>
      have hl1 : (∑ a : A, orderedNeedComult (.unused : OrderedNeedWeb A) (.first a, u₃) *
          orderedNeedComult (.first a) (u₁, u₂) : S) = 0 := by
        refine Finset.sum_eq_zero fun a _ => ?_
        cases u₃ <;> simp [orderedNeedComult]
      have hl2 : (∑ a : A, orderedNeedComult (.unused : OrderedNeedWeb A) (.cached a, u₃) *
          orderedNeedComult (.cached a) (u₁, u₂) : S) = 0 := by
        refine Finset.sum_eq_zero fun a _ => ?_
        cases u₃ <;> simp [orderedNeedComult]
      have hr1 : (∑ a : A, orderedNeedComult (.unused : OrderedNeedWeb A) (u₁, .first a) *
          orderedNeedComult (.first a) (u₂, u₃) : S) = 0 := by
        refine Finset.sum_eq_zero fun a _ => ?_
        cases u₁ <;> simp [orderedNeedComult]
      have hr2 : (∑ a : A, orderedNeedComult (.unused : OrderedNeedWeb A) (u₁, .cached a) *
          orderedNeedComult (.cached a) (u₂, u₃) : S) = 0 := by
        refine Finset.sum_eq_zero fun a _ => ?_
        cases u₁ <;> simp [orderedNeedComult]
      rw [hl1, hl2, hr1, hr2, add_zero, add_zero, add_zero, add_zero]
      cases u₁ <;> cases u₂ <;> cases u₃ <;> simp [orderedNeedComult]
  | first a =>
      have hl1 : (∑ x : A, orderedNeedComult (.first a) (.first x, u₃) *
          orderedNeedComult (.first x) (u₁, u₂) : S) =
          orderedNeedComult (.first a) (.first a, u₃) * orderedNeedComult (.first a) (u₁, u₂) := by
        have h : (∑ x : A, orderedNeedComult (.first a) (.first x, u₃) *
            orderedNeedComult (.first x) (u₁, u₂) : S) =
            ∑ x : A, if x = a then
              orderedNeedComult (.first a) (.first a, u₃) * orderedNeedComult (.first a) (u₁, u₂)
            else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : x = a
          · subst hx; simp
          · cases u₃ <;> simp [orderedNeedComult, hx]
        rw [h, Finset.sum_ite_eq' Finset.univ a]; simp
      have hl2 : (∑ x : A, orderedNeedComult (.first a) (.cached x, u₃) *
          orderedNeedComult (.cached x) (u₁, u₂) : S) = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        cases u₃ <;> simp [orderedNeedComult]
      have hr1 : (∑ x : A, orderedNeedComult (.first a) (u₁, .first x) *
          orderedNeedComult (.first x) (u₂, u₃) : S) =
          orderedNeedComult (.first a) (u₁, .first a) * orderedNeedComult (.first a) (u₂, u₃) := by
        have h : (∑ x : A, orderedNeedComult (.first a) (u₁, .first x) *
            orderedNeedComult (.first x) (u₂, u₃) : S) =
            ∑ x : A, if x = a then
              orderedNeedComult (.first a) (u₁, .first a) * orderedNeedComult (.first a) (u₂, u₃)
            else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : x = a
          · subst hx; simp
          · cases u₁ <;> simp [orderedNeedComult, hx]
        rw [h, Finset.sum_ite_eq' Finset.univ a]; simp
      have hr2 : (∑ x : A, orderedNeedComult (.first a) (u₁, .cached x) *
          orderedNeedComult (.cached x) (u₂, u₃) : S) =
          orderedNeedComult (.first a) (u₁, .cached a) * orderedNeedComult (.cached a) (u₂, u₃) := by
        have h : (∑ x : A, orderedNeedComult (.first a) (u₁, .cached x) *
            orderedNeedComult (.cached x) (u₂, u₃) : S) =
            ∑ x : A, if x = a then
              orderedNeedComult (.first a) (u₁, .cached a) * orderedNeedComult (.cached a) (u₂, u₃)
            else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : x = a
          · subst hx; simp
          · cases u₁ <;> simp [orderedNeedComult, hx]
        rw [h, Finset.sum_ite_eq' Finset.univ a]; simp
      rw [hl1, hl2, hr1, hr2, add_zero]
      cases u₁ with
      | unused =>
          cases u₂ with
          | unused =>
              cases u₃ with
              | unused => simp [orderedNeedComult]
              | first a₃ => by_cases h3 : a₃ = a <;> simp [orderedNeedComult, h3]
              | cached a₃ => simp [orderedNeedComult]
          | first a₂ =>
              cases u₃ with
              | unused => by_cases h2 : a₂ = a <;> simp [orderedNeedComult, h2]
              | first a₃ => simp [orderedNeedComult]
              | cached a₃ =>
                  by_cases h2 : a₂ = a <;> by_cases h3 : a₃ = a <;>
                    simp [orderedNeedComult, h2, h3]
          | cached a₂ =>
              cases u₃ <;> simp [orderedNeedComult]
      | first a₁ =>
          cases u₂ with
          | unused =>
              cases u₃ with
              | unused => by_cases h1 : a₁ = a <;> simp [orderedNeedComult, h1]
              | first a₃ => simp [orderedNeedComult]
              | cached a₃ =>
                  by_cases h1 : a₁ = a <;> by_cases h3 : a₃ = a <;>
                    simp [orderedNeedComult, h1, h3]
          | first a₂ =>
              cases u₃ <;> simp [orderedNeedComult]
          | cached a₂ =>
              cases u₃ with
              | unused =>
                  by_cases h1 : a₁ = a <;> by_cases h2 : a₂ = a <;>
                    simp [orderedNeedComult, h1, h2]
              | first a₃ => simp [orderedNeedComult]
              | cached a₃ =>
                  by_cases h1 : a₁ = a <;> by_cases h2 : a₂ = a <;> by_cases h3 : a₃ = a <;>
                    simp [orderedNeedComult, h1, h2, h3]
      | cached a₁ =>
          cases u₂ <;> cases u₃ <;> simp [orderedNeedComult]
  | cached a =>
      have hl1 : (∑ x : A, orderedNeedComult (.cached a) (.first x, u₃) *
          orderedNeedComult (.first x) (u₁, u₂) : S) = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        cases u₃ <;> simp [orderedNeedComult]
      have hl2 : (∑ x : A, orderedNeedComult (.cached a) (.cached x, u₃) *
          orderedNeedComult (.cached x) (u₁, u₂) : S) =
          orderedNeedComult (.cached a) (.cached a, u₃) * orderedNeedComult (.cached a) (u₁, u₂) := by
        have h : (∑ x : A, orderedNeedComult (.cached a) (.cached x, u₃) *
            orderedNeedComult (.cached x) (u₁, u₂) : S) =
            ∑ x : A, if x = a then
              orderedNeedComult (.cached a) (.cached a, u₃) * orderedNeedComult (.cached a) (u₁, u₂)
            else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : x = a
          · subst hx; simp
          · cases u₃ <;> simp [orderedNeedComult, hx]
        rw [h, Finset.sum_ite_eq' Finset.univ a]; simp
      have hr1 : (∑ x : A, orderedNeedComult (.cached a) (u₁, .first x) *
          orderedNeedComult (.first x) (u₂, u₃) : S) = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        cases u₁ <;> simp [orderedNeedComult]
      have hr2 : (∑ x : A, orderedNeedComult (.cached a) (u₁, .cached x) *
          orderedNeedComult (.cached x) (u₂, u₃) : S) =
          orderedNeedComult (.cached a) (u₁, .cached a) * orderedNeedComult (.cached a) (u₂, u₃) := by
        have h : (∑ x : A, orderedNeedComult (.cached a) (u₁, .cached x) *
            orderedNeedComult (.cached x) (u₂, u₃) : S) =
            ∑ x : A, if x = a then
              orderedNeedComult (.cached a) (u₁, .cached a) * orderedNeedComult (.cached a) (u₂, u₃)
            else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : x = a
          · subst hx; simp
          · cases u₁ <;> simp [orderedNeedComult, hx]
        rw [h, Finset.sum_ite_eq' Finset.univ a]; simp
      rw [hl1, hl2, hr1, hr2, add_zero, add_zero]
      cases u₁ with
      | unused =>
          cases u₂ with
          | unused =>
              cases u₃ with
              | unused => simp [orderedNeedComult]
              | first a₃ => simp [orderedNeedComult]
              | cached a₃ => by_cases h3 : a₃ = a <;> simp [orderedNeedComult, h3]
          | first a₂ =>
              cases u₃ <;> simp [orderedNeedComult]
          | cached a₂ =>
              cases u₃ with
              | unused => by_cases h2 : a₂ = a <;> simp [orderedNeedComult, h2]
              | first a₃ => simp [orderedNeedComult]
              | cached a₃ =>
                  by_cases h2 : a₂ = a <;> by_cases h3 : a₃ = a <;>
                    simp [orderedNeedComult, h2, h3]
      | first a₁ =>
          cases u₂ <;> cases u₃ <;> simp [orderedNeedComult]
      | cached a₁ =>
          cases u₂ with
          | unused =>
              cases u₃ with
              | unused => by_cases h1 : a₁ = a <;> simp [orderedNeedComult, h1]
              | first a₃ => simp [orderedNeedComult]
              | cached a₃ =>
                  by_cases h1 : a₁ = a <;> by_cases h3 : a₃ = a <;>
                    simp [orderedNeedComult, h1, h3]
          | first a₂ =>
              cases u₃ <;> simp [orderedNeedComult]
          | cached a₂ =>
              cases u₃ with
              | unused =>
                  by_cases h1 : a₁ = a <;> by_cases h2 : a₂ = a <;>
                    simp [orderedNeedComult, h1, h2]
              | first a₃ => simp [orderedNeedComult]
              | cached a₃ =>
                  by_cases h1 : a₁ = a <;> by_cases h2 : a₂ = a <;> by_cases h3 : a₃ = a <;>
                    simp [orderedNeedComult, h1, h2, h3]

omit [Fintype A] in
/-- Negative control: `orderedNeedComult` is NOT cocommutative when `A` is nonempty,
because `(first a, cached a)` has weight `1` (first use on left, cached use on right),
whereas `(cached a, first a)` has weight `0`. -/
theorem orderedNeedComult_not_cocomm (a : A) :
    orderedNeedComult (.first a) (.first a, .cached a) = (1 : Nat) ∧
      orderedNeedComult (.first a) (.cached a, .first a) = (0 : Nat) := by
  simp [orderedNeedComult]

/-- Exact characterization of where multiplication commutativity in `S` is needed
when collapsing `OrderedNeedWeb A` to `NeedWeb A`:
if `m₁` (with weight `w₁ : S`) does NOT force cell `c` (`unused`) and `m₂`
(with weight `w₂ : S`) DOES force cell `c` (`first a`, with producer weight `w_c : S`),
chronological evaluation multiplies `w₁ * (w_c * w₂)` whereas lexical `need`-binding
at `NeedWeb A` multiplies `w_c * (w₁ * w₂)`. In any `Semiring R`, these agree for all
`w₂` (in particular `w₂ = 1`) iff `w_c` and `w₁` commute. -/
theorem lexical_need_agrees_with_chronological_iff {R : Type*} [Semiring R]
    (w_c w₁ : R) :
    (∀ w₂ : R, w_c * (w₁ * w₂) = w₁ * (w_c * w₂)) ↔ w_c * w₁ = w₁ * w_c := by
  constructor
  · intro h
    have h1 := h 1
    simpa [mul_one] using h1
  · intro h w₂
    rw [← mul_assoc, h, mul_assoc]

end OrderedNeedComonoid

/-- Concrete non-commutative semiring of $2 \times 2$ upper-triangular matrices
$\begin{pmatrix} a & b \\ 0 & c \end{pmatrix}$ over `Nat`, witnessing that
`OrderedNeedComonoid` (`orderedNeed_left_counit`, `orderedNeed_right_counit`,
`orderedNeed_coassoc`) applies over genuinely non-commutative weight semirings. -/
structure UpperTri2Nat where
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq, Repr

namespace UpperTri2Nat

def zero : UpperTri2Nat := ⟨0, 0, 0⟩
def one : UpperTri2Nat := ⟨1, 0, 1⟩
def add (x y : UpperTri2Nat) : UpperTri2Nat := ⟨x.a + y.a, x.b + y.b, x.c + y.c⟩
def mul (x y : UpperTri2Nat) : UpperTri2Nat := ⟨x.a * y.a, x.a * y.b + x.b * y.c, x.c * y.c⟩
def nsmul (n : Nat) (x : UpperTri2Nat) : UpperTri2Nat := ⟨n * x.a, n * x.b, n * x.c⟩

instance : Semiring UpperTri2Nat where
  zero := zero
  one := one
  add := add
  mul := mul
  add_assoc x y z := by
    cases x; cases y; cases z
    change add (add _ _) _ = add _ (add _ _)
    dsimp [add]
    congr 1 <;> omega
  zero_add x := by
    cases x
    change add zero _ = _
    dsimp [add, zero]
    congr 1 <;> omega
  add_zero x := by
    cases x
    change add _ zero = _
    dsimp [add, zero]
  add_comm x y := by
    cases x; cases y
    change add _ _ = add _ _
    dsimp [add]
    congr 1 <;> omega
  nsmul := nsmul
  nsmul_zero x := by
    cases x
    change nsmul 0 _ = zero
    dsimp [nsmul, zero]
    congr 1 <;> omega
  nsmul_succ n x := by
    cases x
    change nsmul (n + 1) _ = add (nsmul n _) _
    dsimp [nsmul, add]
    congr 1 <;> rw [Nat.succ_mul]
  mul_assoc x y z := by
    cases x; cases y; cases z
    change mul (mul _ _) _ = mul _ (mul _ _)
    dsimp [mul]
    congr 1
    · exact Nat.mul_assoc _ _ _
    · rw [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.add_assoc]
    · exact Nat.mul_assoc _ _ _
  one_mul x := by
    cases x
    change mul one _ = _
    dsimp [mul, one]
    congr 1 <;> omega
  mul_one x := by
    cases x
    change mul _ one = _
    dsimp [mul, one]
    congr 1 <;> omega
  left_distrib x y z := by
    cases x; cases y; cases z
    change mul _ (add _ _) = add (mul _ _) (mul _ _)
    dsimp [mul, add]
    congr 1
    · exact Nat.left_distrib _ _ _
    · rw [Nat.left_distrib, Nat.left_distrib]; omega
    · exact Nat.left_distrib _ _ _
  right_distrib x y z := by
    cases x; cases y; cases z
    change mul (add _ _) _ = add (mul _ _) (mul _ _)
    dsimp [mul, add]
    congr 1
    · exact Nat.right_distrib _ _ _
    · rw [Nat.right_distrib, Nat.right_distrib]; omega
    · exact Nat.right_distrib _ _ _
  zero_mul x := by
    cases x
    change mul zero _ = zero
    dsimp [mul, zero]
    congr 1 <;> omega
  mul_zero x := by
    cases x
    change mul _ zero = zero
    dsimp [mul, zero]

/-- Explicit witness that multiplication in `UpperTri2Nat` is non-commutative, so
`lexical_need_agrees_with_chronological_iff` refutes collapsing `OrderedNeedWeb` to
`NeedWeb` over `UpperTri2Nat`. -/
theorem mul_not_comm :
    let m₁ : UpperTri2Nat := ⟨1, 1, 0⟩
    let m₂ : UpperTri2Nat := ⟨0, 1, 1⟩
    m₁ * m₂ ≠ m₂ * m₁ ∧
      ¬ (∀ w₂ : UpperTri2Nat, m₁ * (m₂ * w₂) = m₂ * (m₁ * w₂)) := by
  refine ⟨by decide, ?_⟩
  rw [lexical_need_agrees_with_chronological_iff]
  decide

/-- `orderedNeed_coassoc` instantiated directly over the non-commutative semiring `UpperTri2Nat`. -/
theorem orderedNeed_coassoc_noncomm {A : Type*} [Fintype A] [DecidableEq A]
    (u u₁ u₂ u₃ : OrderedNeedWeb A) :
    sumOrderedNeed (S := UpperTri2Nat)
      (fun w => orderedNeedComult u (w, u₃) * orderedNeedComult w (u₁, u₂)) =
    sumOrderedNeed (S := UpperTri2Nat)
      (fun v => orderedNeedComult u (u₁, v) * orderedNeedComult v (u₂, u₃)) :=
  orderedNeed_coassoc u u₁ u₂ u₃

end UpperTri2Nat

/-! ## 6. Semiring Parameters and Stratification of `collapse` (Task 7) -/

section CollapseStratification

/-- `collapse` reifies a finite-support answer multiset `WState Nat A` into a
deterministic computation returning a single `Multiset A` value:
each `a : A` occurs in the resulting multiset with multiplicity `w a`. -/
def collapseState {A : Type*} [Fintype A] (w : WState Nat A) : Multiset A :=
  Finset.univ.val.bind fun a => Multiset.replicate (w a) a

@[simp]
theorem count_collapseState {A : Type*} [Fintype A] [DecidableEq A]
    (w : WState Nat A) (a : A) :
    (collapseState w).count a = w a := by
  unfold collapseState
  rw [Multiset.count_bind]
  have hmap :
      (Finset.univ.val.map fun x => (Multiset.replicate (w x) x).count a) =
        Finset.univ.val.map fun x => if x = a then w x else 0 := by
    refine Multiset.map_congr rfl fun x _ => ?_
    rw [Multiset.count_replicate]
  rw [hmap]
  change (∑ x : A, if x = a then w x else 0) = w a
  simp

/-- Support finset of a quantitative state `w : WState Nat A` (the qualitative Boolean
image under `n ↦ decide (0 < n)`). -/
def supportFinset {A : Type*} [Fintype A] (w : WState Nat A) : Finset A :=
  Finset.univ.filter fun a => 0 < w a

theorem mem_supportFinset_iff {A : Type*} [Fintype A] [DecidableEq A]
    (w : WState Nat A) (a : A) :
    a ∈ supportFinset w ↔ a ∈ collapseState w := by
  rw [← Multiset.count_pos, count_collapseState]
  simp [supportFinset]

/-- The reified computation in `Rel_ℕ` on `Multiset A`: returns `collapseState w` once. -/
def collapseSem {A : Type*} [Fintype A] [DecidableEq A]
    (w : WState Nat A) : WState Nat (Multiset A) :=
  fun m => if m = collapseState w then 1 else 0

/-- Concrete states for `collapse` non-monotonicity:
`wSingleFalse = {false: 1, true: 0}` and `wCoin = {false: 1, true: 1}`. -/
def wSingleFalse : WState Nat Bool := fun b => if b = false then 1 else 0
def wCoin : WState Nat Bool := fun _ => 1

/-- Negative theorem (Task 7ii): `collapseSem` is NOT monotone with respect to the
pointwise order `w₁ ≤ w₂` on `WState Nat Bool`.
Specifically, `wSingleFalse ≤ wCoin` pointwise, yet
`collapseSem wSingleFalse (collapseState wSingleFalse) = 1` while
`collapseSem wCoin (collapseState wSingleFalse) = 0`. -/
theorem collapseSem_not_monotone :
    (∀ b : Bool, wSingleFalse b ≤ wCoin b) ∧
      ¬ (∀ m : Multiset Bool, collapseSem wSingleFalse m ≤ collapseSem wCoin m) := by
  refine ⟨?_, ?_⟩
  · intro b
    cases b <;> decide
  · intro hle
    have h := hle (collapseState wSingleFalse)
    have hw1 : collapseSem wSingleFalse (collapseState wSingleFalse) = 1 := by
      simp [collapseSem]
    have hneq : collapseState wSingleFalse ≠ collapseState wCoin := by
      intro heq
      have hc := congrArg (fun m : Multiset Bool => m.count true) heq
      rw [count_collapseState, count_collapseState] at hc
      change (0 : Nat) = 1 at hc
      omega
    have hw2 : collapseSem wCoin (collapseState wSingleFalse) = 0 := by
      simp [collapseSem, hneq]
    omega

/-- Unstratified recursion through `collapse`: a fixed-point equation
`w = step (collapseState w)` where `step m` returns `false` if `m = 0` (empty bag)
and `fail` (`0`) otherwise has NO fixed point in `WState Nat Bool`. -/
def unstratifiedCollapseStep (w : WState Nat Bool) : WState Nat Bool :=
  if collapseState w = 0 then wSingleFalse else (fun _ => 0)

theorem unstratified_collapse_no_fixpoint :
    ¬ ∃ w : WState Nat Bool, unstratifiedCollapseStep w = w := by
  rintro ⟨w, hw⟩
  by_cases hempty : collapseState w = 0
  · have hwf : w false = 1 := by
      have := congrFun hw false
      simpa [unstratifiedCollapseStep, wSingleFalse, hempty] using this.symm
    have hcount : (collapseState w).count false = 1 := by
      rw [count_collapseState, hwf]
    rw [hempty] at hcount
    simp at hcount
  · have hw0 : ∀ b, w b = 0 := by
      intro b
      have := congrFun hw b
      simpa [unstratifiedCollapseStep, hempty] using this.symm
    have hzero : collapseState w = 0 := by
      ext b
      rw [count_collapseState, hw0 b, Multiset.count_zero]
    exact hempty hzero

/-- Store-definedness web for `n` memoized cells over `A`: each cell slot is either
`none` (unforced) or `some a` (forced and committed to `a`). -/
abbrev StoreWeb (n : Nat) (A : Type*) := Fin n → NeedWeb A

/-- The definedness stratum of an `n`-cell store state is the number of committed cells.
Every first-force transition `none ↦ some a` strictly advances this stratum, bounding
the number of first-force transitions along any execution branch by `n`. -/
def definedStratum {n : Nat} {A : Type*} (σ : StoreWeb n A) : Nat :=
  (Finset.univ.filter fun i : Fin n => (σ i).isSome).card

theorem definedStratum_le {n : Nat} {A : Type*} (σ : StoreWeb n A) :
    definedStratum σ ≤ n := by
  unfold definedStratum
  simpa using Finset.card_le_univ (Finset.univ.filter fun i : Fin n => (σ i).isSome)

/-- Committing an unforced cell `σ i = none` to `some a` strictly increases
`definedStratum` by `1`. -/
theorem definedStratum_commit_succ {n : Nat} {A : Type*}
    (σ : StoreWeb n A) (i : Fin n) (a : A) (hUnforced : σ i = none) :
    definedStratum (Function.update σ i (some a)) = definedStratum σ + 1 := by
  unfold definedStratum
  have hmem : i ∉ Finset.univ.filter (fun j : Fin n => (σ j).isSome) := by
    simp [hUnforced]
  have hfilter :
      (Finset.univ.filter fun j : Fin n => (Function.update σ i (some a) j).isSome) =
        insert i (Finset.univ.filter fun j : Fin n => (σ j).isSome) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hj : j = i
    · subst hj
      simp [Function.update]
    · simp [Function.update, hj]
  rw [hfilter, Finset.card_insert_of_notMem hmem]

/-- Why collapsing only the value projection (forgetting the `NeedWeb` cell state)
is not compositional under a subsequent force:
two open computations `r₁, r₂ : WRel Nat (NeedWeb Bool) Bool`
* `r₁`: forces the cell (`forceNeedRel`),
* `r₂`: ignores the cell and flips a fresh coin (`needCounit u * 1`),
produce the **exact same** collapsed value multiset `{false, true}` when closed with
`bindNeed wCoin`, yet when sequenced with a second `forceNeedRel` via `needComult`,
`r₁` produces `{false, true}` (diagonal) whereas `r₂` produces `{false, false, true, true}`! -/
def rForceOnce : WRel Nat (NeedWeb Bool) Bool := forceNeedRel

def rFreshCoin : WRel Nat (NeedWeb Bool) Bool :=
  fun u _ => needCounit u

def seqWithForce (r : WRel Nat (NeedWeb Bool) Bool) :
    WRel Nat (NeedWeb Bool) (Bool × Bool) :=
  fun u p =>
    ∑ u₁ : NeedWeb Bool, ∑ u₂ : NeedWeb Bool,
      needComult u (u₁, u₂) * r u₁ p.1 * forceNeedRel u₂ p.2

theorem collapse_value_marginal_not_compositional :
    collapseState (bindNeed wCoin rForceOnce) =
      collapseState (bindNeed wCoin rFreshCoin) ∧
    collapseState (bindNeed wCoin (seqWithForce rForceOnce)) ≠
      collapseState (bindNeed wCoin (seqWithForce rFreshCoin)) := by
  refine ⟨?_, ?_⟩
  · ext b
    rw [count_collapseState, count_collapseState]
    cases b <;> decide
  · intro heq
    have hc := congrArg (fun m : Multiset (Bool × Bool) => m.count (false, true)) heq
    rw [count_collapseState, count_collapseState] at hc
    revert hc
    decide

end CollapseStratification

end Mettapedia.Machines.BranchLocalNeed.Weighted
