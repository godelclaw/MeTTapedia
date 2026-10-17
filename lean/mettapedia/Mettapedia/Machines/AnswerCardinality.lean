import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# Cardinality intervals for completed finite answer streams

The five intervals distinguish failure, one answer, at most one, at least one,
and arbitrary finite multiplicity. Relational choice adds multiplicities;
an exclusive branch takes an interval hull. Sequencing is list bind, whose
continuation can return a different list for each input occurrence.

These bounds do not prove termination, absence of exceptions, purity, or
boundness of an answer's variables. In particular, collection has one answer
only after its producer completes. Equal answer values remain occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AnswerCardinality

inductive Grade where
  | zero
  | one
  | optional
  | nonempty
  | any
  deriving DecidableEq, Repr

open Grade

def Allows : Grade → Nat → Prop
  | .zero, n => n = 0
  | .one, n => n = 1
  | .optional, n => n ≤ 1
  | .nonempty, n => 1 ≤ n
  | .any, _ => True

instance (a : Grade) (n : Nat) : Decidable (Allows a n) := by
  cases a <;> unfold Allows <;> infer_instance

def Refines (first second : Grade) : Prop :=
  ∀ n, Allows first n → Allows second n

/-- Classify a completed occurrence count in the existing interval domain.
This is not an estimate of an open producer's future answers. -/
def ofCount : Nat → Grade
  | 0 => .zero
  | 1 => .one
  | _ + 2 => .nonempty

theorem ofCount_sound (count : Nat) : Allows (ofCount count) count := by
  cases count with
  | zero => rfl
  | succ count => cases count <;> simp [ofCount, Allows]

def seq : Grade → Grade → Grade
  | .zero, _ | _, .zero => .zero
  | .one, b => b
  | a, .one => a
  | .optional, .optional => .optional
  | .nonempty, .nonempty => .nonempty
  | _, _ => .any

def choice : Grade → Grade → Grade
  | .zero, b => b
  | a, .zero => a
  | .one, _ | _, .one | .nonempty, _ | _, .nonempty => .nonempty
  | _, _ => .any

def join : Grade → Grade → Grade
  | .zero, .zero => .zero
  | .one, .one => .one
  | .zero, .one | .one, .zero => .optional
  | .optional, .zero | .zero, .optional => .optional
  | .optional, .one | .one, .optional => .optional
  | .optional, .optional => .optional
  | .one, .nonempty | .nonempty, .one => .nonempty
  | .nonempty, .nonempty => .nonempty
  | _, _ => .any

def once : Grade → Grade
  | .zero => .zero
  | .one | .nonempty => .one
  | .optional | .any => .optional

/-- An output constraint can remove every occurrence. It cannot preserve a
nonfailure guarantee merely because the unconstrained producer has one. -/
def constrained : Grade → Grade
  | .zero => .zero
  | .one | .optional => .optional
  | .nonempty | .any => .any

theorem filter_sound {A : Type*} (grade : Grade) (answers : List A)
    (accept : A → Bool) (bounded : Allows grade answers.length) :
    Allows (constrained grade) (answers.filter accept).length := by
  have upper := List.length_filter_le accept answers
  cases grade <;> simp_all [Allows, constrained]
  exact Nat.le_trans upper bounded

/-- The rule observer decides what an empty *matching family* means. It does
not decide what a matched rule with an empty body means. A normalizing observer
retains its supplied fallback value only when no rule applies. -/
inductive NoRulePolicy where
  | noAnswers
  | retainFallback
  deriving DecidableEq, Repr

def observeRuleBodies {A : Type*} (policy : NoRulePolicy) (fallback : A)
    (bodies : List (List A)) : List A :=
  match bodies with
  | [] => match policy with
    | .noAnswers => []
    | .retainFallback => [fallback]
  | _ :: _ => bodies.flatten

def ruleGrade (policy : NoRulePolicy) (grades : List Grade) : Grade :=
  match grades with
  | [] => match policy with
    | .noAnswers => .zero
    | .retainFallback => .one
  | first :: rest => choice first (rest.foldr choice .zero)

@[simp] theorem observeRuleBodies_matched {A : Type*} (policy : NoRulePolicy)
    (fallback : A) (first : List A) (rest : List (List A)) :
    observeRuleBodies policy fallback (first :: rest) = first ++ rest.flatten := rfl

/-- Explicit failure is not turned into an uninterpreted original value. -/
theorem matched_failure_stays_empty {A : Type*} (policy : NoRulePolicy) (fallback : A) :
    observeRuleBodies policy fallback [[]] = [] := rfl

theorem unmatched_policies_differ :
    observeRuleBodies .noAnswers (7 : Nat) [] = [] ∧
      observeRuleBodies .retainFallback 7 [] = [7] := ⟨rfl, rfl⟩

theorem choice_sound (a b : Grade) (n m : Nat)
    (left : Allows a n) (right : Allows b m) :
    Allows (choice a b) (n + m) := by
  cases a <;> cases b <;> simp_all [Allows, choice] <;> omega

/-- Physical rule alternatives add their answer bounds. A body's empty result
is still represented in the matching family and cannot trigger normalization. -/
theorem ruleGrade_sound {A : Type*} (policy : NoRulePolicy) (fallback : A)
    (grades : List Grade) (bodies : List (List A))
    (sound : List.Forall₂ (fun grade body => Allows grade body.length) grades bodies) :
    Allows (ruleGrade policy grades) (observeRuleBodies policy fallback bodies).length := by
  have fold_sound : ∀ (gs : List Grade) (bs : List (List A)),
      List.Forall₂ (fun grade body => Allows grade body.length) gs bs →
      Allows (gs.foldr choice .zero) bs.flatten.length := by
    intro gs bs paired
    induction paired with
    | nil => rfl
    | @cons grade body grades bodies bound _ rest =>
        simpa only [List.foldr_cons, List.flatten_cons, List.length_append] using
          choice_sound grade (grades.foldr choice .zero) body.length bodies.flatten.length bound rest
  cases sound with
  | nil => cases policy <;> rfl
  | cons bound tail =>
      exact fold_sound _ _ (.cons bound tail)

theorem seq_product_sound (a b : Grade) (n m : Nat)
    (left : Allows a n) (right : Allows b m) :
    Allows (seq a b) (n * m) := by
  cases a <;> cases b <;> simp_all [Allows, seq]
  · exact Nat.mul_le_mul left right
  · exact Nat.mul_pos left right

theorem join_left (a b : Grade) : Refines a (join a b) := by
  intro n h
  cases a <;> cases b <;> simp_all [Allows, join]

theorem join_right (a b : Grade) : Refines b (join a b) := by
  intro n h
  cases a <;> cases b <;> simp_all [Allows, join]

theorem once_sound (a : Grade) (n : Nat) (h : Allows a n) :
    Allows (once a) (min 1 n) := by
  cases a <;> simp_all [Allows, once]
  omega

private theorem flatMap_length_eq_zero {A B : Type*}
    (xs : List A) (f : A → List B)
    (h : ∀ x ∈ xs, (f x).length = 0) : (xs.flatMap f).length = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append]
      rw [h x (by simp), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem flatMap_length_eq_length {A B : Type*}
    (xs : List A) (f : A → List B)
    (h : ∀ x ∈ xs, (f x).length = 1) : (xs.flatMap f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [h x (by simp), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]
      omega

private theorem flatMap_length_le_length {A B : Type*}
    (xs : List A) (f : A → List B)
    (h : ∀ x ∈ xs, (f x).length ≤ 1) : (xs.flatMap f).length ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
      have head := h x (by simp)
      have tail := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega

private theorem length_le_flatMap_length {A B : Type*}
    (xs : List A) (f : A → List B)
    (h : ∀ x ∈ xs, 1 ≤ (f x).length) : xs.length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
      have head := h x (by simp)
      have tail := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega

/-- Continuation lengths need not be equal. The same interval must hold
for each input occurrence, in its corresponding binding environment. -/
theorem bind_sound {A B : Type*} (a b : Grade) (xs : List A) (f : A → List B)
    (input : Allows a xs.length)
    (continuation : ∀ x ∈ xs, Allows b (f x).length) :
    Allows (seq a b) (xs.flatMap f).length := by
  cases b with
  | zero =>
      have h := flatMap_length_eq_zero xs f continuation
      cases a <;> simp_all [Allows, seq]
  | one =>
      have h := flatMap_length_eq_length xs f continuation
      cases a <;> simp_all [Allows, seq]
  | optional =>
      have h := flatMap_length_le_length xs f continuation
      cases a <;> simp_all [Allows, seq]
      omega
  | nonempty =>
      have h := length_le_flatMap_length xs f continuation
      cases a <;> simp_all [Allows, seq]
      omega
  | any =>
      cases a <;> simp_all [Allows, seq]

theorem append_sound {A : Type*} (a b : Grade) (xs ys : List A)
    (left : Allows a xs.length) (right : Allows b ys.length) :
    Allows (choice a b) (xs ++ ys).length := by
  simpa using choice_sound a b xs.length ys.length left right

theorem take_one_sound {A : Type*} (a : Grade) (xs : List A)
    (h : Allows a xs.length) : Allows (once a) (xs.take 1).length := by
  simpa using once_sound a xs.length h

theorem collect_sound {A : Type*} (completed : List A) :
    Allows .one ([completed] : List (List A)).length := rfl

/-- This five-element abstraction distinguishes counts 0, 1 and at least 2.
These three probes therefore decide inclusion of intervals. -/
theorem refines_iff_probes (a b : Grade) :
    Refines a b ↔ ∀ n ∈ ([0, 1, 2] : List Nat), Allows a n → Allows b n := by
  constructor
  · exact fun h n _ => h n
  · intro h n hn
    have h0 := h 0 (by simp)
    have h1 := h 1 (by simp)
    have h2 := h 2 (by simp)
    cases a <;> cases b <;> simp_all [Allows]

/-- The hull is the least grade containing either branch. -/
theorem join_least (a b c : Grade) (left : Refines a c) (right : Refines b c) :
    Refines (join a b) c := by
  rw [refines_iff_probes] at left right ⊢
  have l0 := left 0 (by simp); have l1 := left 1 (by simp); have l2 := left 2 (by simp)
  have r0 := right 0 (by simp); have r1 := right 1 (by simp); have r2 := right 2 (by simp)
  cases a <;> cases b <;> cases c <;> simp_all [Allows, join]

/-- No more precise grade can describe every sum allowed by the inputs.
The lower bound is deliberately rounded to one rather than an exact sum. -/
theorem choice_least (a b c : Grade)
    (h : ∀ n m, Allows a n → Allows b m → Allows c (n + m)) :
    Refines (choice a b) c := by
  have h00 := h 0 0; have h01 := h 0 1; have h02 := h 0 2
  have h10 := h 1 0; have h11 := h 1 1; have h12 := h 1 2
  have h20 := h 2 0; have h21 := h 2 1; have h22 := h 2 2
  clear h
  rw [refines_iff_probes]
  cases a <;> cases b <;> cases c <;> simp_all [Allows, choice]

/-- Constant-length continuations already witness the precision limit of
the sequencing table; varying lengths remain sound by `bind_sound`. -/
theorem seq_least (a b c : Grade)
    (h : ∀ n m, Allows a n → Allows b m → Allows c (n * m)) :
    Refines (seq a b) c := by
  have h00 := h 0 0; have h01 := h 0 1; have h02 := h 0 2
  have h10 := h 1 0; have h11 := h 1 1; have h12 := h 1 2
  have h20 := h 2 0; have h21 := h 2 1; have h22 := h 2 2
  clear h
  rw [refines_iff_probes]
  cases a <;> cases b <;> cases c <;> simp_all [Allows, seq]

theorem once_least (a c : Grade)
    (h : ∀ n, Allows a n → Allows c (min 1 n)) : Refines (once a) c := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  clear h
  rw [refines_iff_probes]
  cases a <;> cases c <;> simp_all [Allows, once]

namespace Controls

theorem choice_is_not_exclusive_branching :
    choice .one .one = .nonempty ∧ join .one .one = .one := by decide

theorem duplicate_answers_still_count :
    Allows (choice .one .one) ([7, 7] : List Nat).length ∧
      ¬ Allows .one ([7, 7] : List Nat).length := by decide

theorem once_preserves_guaranteed_success :
    once .nonempty = .one ∧ once .any = .optional := by decide

theorem collection_of_failure_is_one_answer :
    Allows .zero ([] : List Nat).length ∧
      Allows .one ([[]] : List (List Nat)).length := by decide

theorem bind_needs_each_reachable_continuation :
    ¬ Allows (seq .one .one)
      (([true] : List Bool).flatMap (fun _ => ([] : List Nat))).length := by decide

end Controls
end Mettapedia.Machines.AnswerCardinality
