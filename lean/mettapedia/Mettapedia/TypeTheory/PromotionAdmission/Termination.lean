import Mettapedia.TypeTheory.PromotionAdmission.Unification
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Termination certificates, and a checked refutation of termination

A promoted rule list must terminate, and a justification does not show it. Termination is
established by a certificate that the kernel checks; one kind of non-termination is refuted
outright.

* **A reduction order** (`ReductionOrder`): a well-founded relation on terms, closed under
  argument positions, that contains every instance of every rule. Then every reduction is
  finite (`ReductionOrder.terminating`). This is the classical criterion of Manna and Ness.
* **A linear interpretation** (`LinearInterpretation`): each symbol `f` is read as
  `w_f + Σ (e_{f,i} + 1) · x_i`, so every coefficient is at least one and the reading is
  strictly monotone in each argument. A term's value is a linear form in the values of its
  variables (`value_linear`), so a rule is oriented for every valuation exactly when its
  constant drops and no variable's coefficient grows; `orients` checks this by computation and
  is sound (`orients_sound`). If every rule is oriented, every reduction is finite
  (`terminating_of_orients`). This is Lankford's method of polynomial interpretations, in its
  linear case.
* **A loop** (`loopSearch`): if the two sides of a rule unify, the rule rewrites an instance
  of its left side to itself, and no reduction from it is finite
  (`not_terminating_of_loopSearch`). The zero swap `x + 0 ↦ 0 + x` loops on `0 + 0`;
  commutativity loops on `x + x`.

No certificate can orient a looping rule (`no_certificate_of_loop`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PromotionAdmission

universe u v w

open Term Relation

variable {F : Type u} {V : Type v} {W : Type w}

/-- **Termination** of the steps of a rule list on terms over `W`: no infinite reduction. -/
def TerminatingAt (R : List (Rule F V)) (W : Type w) : Prop :=
  ∀ t : Term F W, Acc (fun target source => Step R source target) t

/-! ## Reduction orders -/

/-- A well-founded, argument-monotone relation containing every rule instance. -/
structure ReductionOrder (R : List (Rule F V)) (W : Type w) where
  gt : Term F W → Term F W → Prop
  wellFounded : ∀ t, Acc (fun target source => gt source target) t
  monotone : ∀ (f : F) (args : List (Term F W)) (i : ℕ) (h : i < args.length) (t' : Term F W),
    gt args[i] t' → gt (.app f args) (.app f (args.set i t'))
  orients : ∀ ρ ∈ R, ∀ σ : V → Term F W, gt (ρ.lhs.subst σ) (ρ.rhs.subst σ)

namespace ReductionOrder

variable {R : List (Rule F V)}

theorem step_gt (order : ReductionOrder R W) {s t : Term F W} (step : Step R s t) : order.gt s t := by
  induction step with
  | root mem σ => exact order.orients _ mem σ
  | arg f args i h _ ih => exact order.monotone f args i h _ ih

/-- **A reduction order compatible with the rules gives termination.** -/
theorem terminating (order : ReductionOrder R W) : TerminatingAt R W := by
  intro t
  have accessible := order.wellFounded t
  induction accessible with
  | intro t _ ih => exact Acc.intro t fun target step => ih target (order.step_gt step)

end ReductionOrder

/-! ## Linear interpretations -/

/-- A linear reading of the symbols: `f` is read as `weight f + Σ (extra f i + 1) · x_i`. -/
structure LinearInterpretation (F : Type u) where
  weight : F → ℕ
  extra : F → ℕ → ℕ

namespace LinearInterpretation

variable (I : LinearInterpretation F)

mutual
/-- The value of a term under a valuation of its variables. -/
def value (α : W → ℕ) : Term F W → ℕ
  | .var x => α x
  | .app f args => I.weight f + valueArgs α (I.extra f) 0 args
/-- The weighted values of the arguments from position `i` on, where `c i + 1` is the
coefficient of position `i`. -/
def valueArgs (α : W → ℕ) (c : ℕ → ℕ) (i : ℕ) : List (Term F W) → ℕ
  | [] => 0
  | a :: as => (c i + 1) * value α a + valueArgs α c (i + 1) as
end

@[simp] theorem value_var (α : W → ℕ) (x : W) : I.value α (.var x) = α x := by simp [value]

@[simp] theorem value_app (α : W → ℕ) (f : F) (args : List (Term F W)) :
    I.value α (.app f args) = I.weight f + I.valueArgs α (I.extra f) 0 args := by simp [value]

@[simp] theorem valueArgs_nil (α : W → ℕ) (c : ℕ → ℕ) (i : ℕ) :
    I.valueArgs α c i ([] : List (Term F W)) = 0 := by simp [valueArgs]

@[simp] theorem valueArgs_cons (α : W → ℕ) (c : ℕ → ℕ) (i : ℕ) (a : Term F W)
    (as : List (Term F W)) :
    I.valueArgs α c i (a :: as) = (c i + 1) * I.value α a + I.valueArgs α c (i + 1) as := by
  simp [valueArgs]

/-- **Strictly monotone in each argument.** -/
theorem valueArgs_set_lt (α : W → ℕ) (c : ℕ → ℕ) :
    ∀ (args : List (Term F W)) (i j : ℕ) (h : j < args.length) (t' : Term F W),
      I.value α t' < I.value α args[j] →
        I.valueArgs α c i (args.set j t') < I.valueArgs α c i args
  | [], _, _, h, _, _ => by simp at h
  | a :: as, i, 0, _, t', lt => by
      simp only [List.set_cons_zero, valueArgs_cons, List.getElem_cons_zero] at lt ⊢
      have : (c i + 1) * I.value α t' < (c i + 1) * I.value α a :=
        Nat.mul_lt_mul_of_pos_left lt (by omega)
      omega
  | a :: as, i, j + 1, h, t', lt => by
      simp only [List.set_cons_succ, valueArgs_cons]
      have := valueArgs_set_lt α c as (i + 1) j (by simpa using h) t' (by simpa using lt)
      omega

theorem value_subst (α : W → ℕ) {X : Type*} (σ : X → Term F W) :
    ∀ t : Term F X, I.value α (t.subst σ) = I.value (fun x => I.value α (σ x)) t := by
  intro t
  induction t using Term.induction' with
  | var x => simp
  | app f args ih =>
      simp only [subst_app, value_app]
      congr 1
      have list : ∀ (rest : List (Term F X)) (i : ℕ), (∀ a ∈ rest, a ∈ args) →
          I.valueArgs α (I.extra f) i (rest.map (Term.subst σ)) =
            I.valueArgs (fun x => I.value α (σ x)) (I.extra f) i rest := by
        intro rest
        induction rest with
        | nil => intro i _; simp
        | cons a as ihRest =>
            intro i sub
            simp only [List.map_cons, valueArgs_cons]
            rw [ih a (sub a (by simp)), ihRest (i + 1) (fun c hc => sub c (by simp [hc]))]
      exact list args 0 (fun a h => h)

/-- **Every step lowers the value**, under any valuation, when every rule is oriented for
every valuation. -/
theorem step_value_lt {R : List (Rule F V)}
    (oriented : ∀ ρ ∈ R, ∀ α : V → ℕ, I.value α ρ.rhs < I.value α ρ.lhs) (α : W → ℕ)
    {s t : Term F W} (step : Step R s t) : I.value α t < I.value α s := by
  induction step with
  | root mem σ =>
      rw [value_subst, value_subst]
      exact oriented _ mem _
  | arg f args i h _ ih =>
      simp only [value_app]
      have := I.valueArgs_set_lt α (I.extra f) args 0 i h _ ih
      omega

/-- The reduction order of a linear interpretation. -/
def reductionOrder {R : List (Rule F V)}
    (oriented : ∀ ρ ∈ R, ∀ α : V → ℕ, I.value α ρ.rhs < I.value α ρ.lhs) :
    ReductionOrder R W where
  gt s t := I.value (fun _ => 0) t < I.value (fun _ => 0) s
  wellFounded := fun t =>
    (InvImage.accessible (I.value (fun _ => 0)) (Nat.lt_wfRel.wf.apply _))
  monotone := by
    intro f args i h t' lt
    simp only [value_app]
    have := I.valueArgs_set_lt _ (I.extra f) args 0 i h t' lt
    omega
  orients := by
    intro ρ mem σ
    rw [value_subst, value_subst]
    exact oriented ρ mem _

section Coefficients

variable [DecidableEq V]

mutual
/-- The coefficient of the variable `x` in the linear form of a term. -/
def coeff (x : V) : Term F V → ℕ
  | .var y => if y = x then 1 else 0
  | .app f args => coeffArgs x (I.extra f) 0 args
/-- The weighted coefficients of `x` in the arguments from position `i` on. -/
def coeffArgs (x : V) (c : ℕ → ℕ) (i : ℕ) : List (Term F V) → ℕ
  | [] => 0
  | a :: as => (c i + 1) * coeff x a + coeffArgs x c (i + 1) as
end

/-- **The value of a term is a linear form** in the values of its variables. -/
theorem value_linear (α : V → ℕ) (S : Finset V) :
    ∀ t : Term F V, (∀ x ∈ t.vars, x ∈ S) →
      I.value α t = I.value (fun _ => 0) t + ∑ x ∈ S, I.coeff x t * α x := by
  intro t
  induction t using Term.induction' with
  | var y =>
      intro inS
      simp only [value_var, coeff]
      rw [Finset.sum_eq_single y]
      · simp
      · intro x _ ne; simp [Ne.symm ne]
      · intro notIn; exact absurd (inS y (by simp)) notIn
  | app f args ih =>
      intro inS
      simp only [value_app, coeff]
      have list : ∀ (rest : List (Term F V)) (i : ℕ), (∀ a ∈ rest, a ∈ args) →
          I.valueArgs α (I.extra f) i rest =
            I.valueArgs (fun _ => 0) (I.extra f) i rest +
              ∑ x ∈ S, I.coeffArgs x (I.extra f) i rest * α x := by
        intro rest
        induction rest with
        | nil => intro i _; simp [coeffArgs]
        | cons a as ihRest =>
            intro i sub
            simp only [valueArgs_cons, coeffArgs]
            rw [ih a (sub a (by simp)) (fun x hx => inS x (by simpa using ⟨a, sub a (by simp), hx⟩)),
              ihRest (i + 1) (fun c hc => sub c (by simp [hc]))]
            simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, mul_add]
            ring
      rw [list args 0 (fun a h => h)]
      ring

/-- **The orientation test**: the constant drops and no coefficient grows. -/
def orients (ρ : Rule F V) : Bool :=
  decide (I.value (fun _ => 0) ρ.rhs < I.value (fun _ => 0) ρ.lhs) &&
    (ρ.lhs.vars ++ ρ.rhs.vars).all fun x => decide (I.coeff x ρ.rhs ≤ I.coeff x ρ.lhs)

/-- **The orientation test is sound**: an oriented rule decreases under every valuation. -/
theorem orients_sound {ρ : Rule F V} (h : I.orients ρ = true) (α : V → ℕ) :
    I.value α ρ.rhs < I.value α ρ.lhs := by
  simp only [orients, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨constant, coefficients⟩ := h
  let S := (ρ.lhs.vars ++ ρ.rhs.vars).toFinset
  rw [I.value_linear α S ρ.lhs (fun x hx => by simp [S, hx]),
    I.value_linear α S ρ.rhs (fun x hx => by simp [S, hx])]
  have sums : ∑ x ∈ S, I.coeff x ρ.rhs * α x ≤ ∑ x ∈ S, I.coeff x ρ.lhs * α x :=
    Finset.sum_le_sum fun x hx =>
      Nat.mul_le_mul_right _ (coefficients x (by simpa [S] using hx))
  omega

/-- **Every rule oriented gives termination**, on terms over every variable type. -/
theorem terminating_of_orients {R : List (Rule F V)} (h : ∀ ρ ∈ R, I.orients ρ = true) :
    TerminatingAt R W :=
  (I.reductionOrder (W := W) fun ρ mem => I.orients_sound (h ρ mem)).terminating

end Coefficients

end LinearInterpretation

/-! ## A loop refutes termination -/

/-- The answer of the loop search. -/
inductive LoopAnswer where
  | found
  | none
  | outOfFuel
  deriving DecidableEq, Repr

section Loops

variable [DecidableEq F] [DecidableEq V]

/-- Search for a rule whose two sides unify. -/
def loopSearch (fuel : ℕ) : List (Rule F V) → LoopAnswer
  | [] => .none
  | ρ :: rest =>
      match unify fuel [(ρ.lhs, ρ.rhs)] with
      | .ok _ => .found
      | .fail => loopSearch fuel rest
      | .outOfFuel => .outOfFuel

omit [DecidableEq F] [DecidableEq V] in
theorem not_terminating_of_loop {R : List (Rule F V)} {ρ : Rule F V} (mem : ρ ∈ R)
    {θ : V → Term F V} (same : ρ.lhs.subst θ = ρ.rhs.subst θ) : ¬ TerminatingAt R V := by
  intro terminating
  have loop : Step R (ρ.lhs.subst θ) (ρ.lhs.subst θ) := by
    have := Step.root (W := V) mem θ
    rwa [← same] at this
  have claim : ∀ t, Acc (fun target source => Step R source target) t →
      t = ρ.lhs.subst θ → False := by
    intro t accessible
    induction accessible with
    | intro t _ ih => intro h; subst h; exact ih _ loop rfl
  exact claim _ (terminating _) rfl

theorem loopSearch_found {fuel : ℕ} :
    ∀ {R : List (Rule F V)}, loopSearch fuel R = .found →
      ∃ ρ ∈ R, ∃ θ : V → Term F V, ρ.lhs.subst θ = ρ.rhs.subst θ
  | [], h => by simp [loopSearch] at h
  | ρ :: rest, h => by
      simp only [loopSearch] at h
      split at h
      · rename_i θ hu
        have := unify_ok_unify hu _ (List.mem_singleton_self _)
        exact ⟨ρ, List.mem_cons_self, θ, this⟩
      · obtain ⟨ρ', mem, θ, same⟩ := loopSearch_found h
        exact ⟨ρ', List.mem_cons_of_mem _ mem, θ, same⟩
      · cases h

/-- **A rule whose sides unify refutes termination.** -/
theorem not_terminating_of_loopSearch {fuel : ℕ} {R : List (Rule F V)}
    (h : loopSearch fuel R = .found) : ¬ TerminatingAt R V := by
  obtain ⟨ρ, mem, θ, same⟩ := loopSearch_found h
  exact not_terminating_of_loop mem same

theorem loopSearch_mono {fuel fuel' : ℕ} (le : fuel ≤ fuel') :
    ∀ {R : List (Rule F V)}, loopSearch fuel R ≠ .outOfFuel →
      loopSearch fuel' R = loopSearch fuel R
  | [], _ => rfl
  | ρ :: rest, h => by
      simp only [loopSearch] at h ⊢
      cases hu : unify fuel [(ρ.lhs, ρ.rhs)] with
      | ok θ =>
          rw [unify_mono fuel _ fuel' le (by rw [hu]; exact fun h => by cases h), hu]
      | fail =>
          rw [unify_mono fuel _ fuel' le (by rw [hu]; exact fun h => by cases h), hu]
          rw [hu] at h
          exact loopSearch_mono le h
      | outOfFuel => rw [hu] at h; exact absurd rfl h

theorem loopSearch_none {fuel : ℕ} :
    ∀ {R : List (Rule F V)}, loopSearch fuel R = .none →
      ∀ ρ ∈ R, ∀ {W : Type w} (θ : V → Term F W), ρ.lhs.subst θ ≠ ρ.rhs.subst θ
  | [], _, ρ, mem => by simp at mem
  | ρ :: rest, h, ρ', mem => by
      intro θ same
      simp only [loopSearch] at h
      split at h
      · cases h
      · rename_i hu
        rcases List.mem_cons.mp mem with rfl | later
        · exact unify_fail _ _ hu θ (by simpa [Unifies] using same)
        · exact loopSearch_none h ρ' later θ same
      · cases h

omit [DecidableEq F] in
/-- **No certificate orients a looping rule.** -/
theorem no_certificate_of_loop {R : List (Rule F V)} {ρ : Rule F V} (mem : ρ ∈ R)
    {θ : V → Term F V} (same : ρ.lhs.subst θ = ρ.rhs.subst θ) (I : LinearInterpretation F) :
    ¬ ∀ ρ ∈ R, I.orients ρ = true :=
  fun oriented => not_terminating_of_loop mem same (I.terminating_of_orients oriented)

end Loops

end Mettapedia.TypeTheory.PromotionAdmission
