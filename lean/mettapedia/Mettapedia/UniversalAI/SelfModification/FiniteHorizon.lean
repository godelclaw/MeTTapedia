import Mettapedia.UniversalAI.SelfModification.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite Bellman evaluation

The environment supplies nonnegative real coefficients through `toReal`.
Probability language additionally requires finite, normalized rows: in particular,
an infinite `ENNReal` coefficient has real image zero. No normalization or utility
bound is needed for the finite algebraic laws below.
-/

namespace Mettapedia.UniversalAI.SelfModification

open BayesianAgents
open scoped BigOperators

/-- One complete interaction, without its policy-name record. -/
def nextHistory (h : History) (a : Action) (e : Percept) : History :=
  h ++ [HistElem.act a, HistElem.per e]

noncomputable def branchWeight (env : History → Percept → ENNReal)
    (h : History) (a : Action) (e : Percept) : ℝ :=
  (env (h ++ [HistElem.act a]) e).toReal

/-- Decision points exclude the pending-action histories accepted by `wellFormed`. -/
def DecisionHistory (h : History) : Prop := h.wellFormed ∧ h.length % 2 = 0

theorem DecisionHistory.next {h : History} (valid : DecisionHistory h)
    (a : Action) (e : Percept) : DecisionHistory (nextHistory h a e) := by
  have append_valid : ∀ (xs : History), DecisionHistory xs →
      (nextHistory xs a e).wellFormed := by
    intro xs
    induction xs using List.twoStepInduction with
    | nil => intro _; rfl
    | singleton x => intro v; have := v.2; simp at this
    | cons_cons x y rest ih₁ ih₂ =>
        intro v
        cases x <;> cases y <;> simp only [DecisionHistory, History.wellFormed,
          Bool.false_eq_true, false_and] at v
        obtain ⟨formed, even⟩ := v
        have shorter : rest.length % 2 = 0 := by
          simp only [List.length_cons] at even
          omega
        exact ih₁ ⟨formed, shorter⟩
  exact ⟨append_valid h valid, by simp [nextHistory, List.length_append, valid.2]⟩

structure FiniteValueData where
  envProb : History → Percept → ENNReal
  continuation : PolicyModAction → SelfModPolicy
  γ : DiscountFactor

noncomputable def finiteQ (data : FiniteValueData) (u : Utility)
    (h : History) (a : PolicyModAction) : ℕ → ℝ
  | 0 => 0
  | n+1 => if ¬h.wellFormed then 0 else
      ∑ e : Percept, branchWeight data.envProb h a.worldAction e *
        (u (nextHistory h a.worldAction e) + data.γ.val *
          finiteQ data u (nextHistory h a.worldAction e)
            (data.continuation a (nextHistory h a.worldAction e)) n)

@[simp] theorem finiteQ_zero (data : FiniteValueData) (u : Utility)
    (h : History) (a : PolicyModAction) : finiteQ data u h a 0 = 0 := rfl

/-- Without discount on the future, every positive horizon observes only the first reward. -/
theorem finiteQ_zero_discount (data : FiniteValueData) (u : Utility)
    (h : History) (a : PolicyModAction) (n : ℕ) (zero : data.γ.val = 0) :
    finiteQ data u h a (n+1) = finiteQ data u h a 1 := by
  simp [finiteQ, zero]

theorem finiteQ_nonneg (data : FiniteValueData) (u : Utility) (nonneg : ∀ h, 0 ≤ u h)
    (h : History) (a : PolicyModAction) (n : ℕ) : 0 ≤ finiteQ data u h a n := by
  induction n generalizing h a with
  | zero => rfl
  | succ n ih =>
      by_cases valid : h.wellFormed
      · simp only [finiteQ, valid, not_true_eq_false, ↓reduceIte]
        exact Finset.sum_nonneg fun e _ => mul_nonneg ENNReal.toReal_nonneg
          (add_nonneg (nonneg _) (mul_nonneg data.γ.nonneg (ih _ _)))
      · simp [finiteQ, valid]

theorem finiteQ_mono (data : FiniteValueData) (u v : Utility) (bound : ∀ h, u h ≤ v h)
    (h : History) (a : PolicyModAction) (n : ℕ) : finiteQ data u h a n ≤ finiteQ data v h a n := by
  induction n generalizing h a with
  | zero => rfl
  | succ n ih =>
      by_cases valid : h.wellFormed
      · simp only [finiteQ, valid, not_true_eq_false, ↓reduceIte]
        exact Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left
          (add_le_add (bound _) (mul_le_mul_of_nonneg_left (ih _ _) data.γ.nonneg))
          ENNReal.toReal_nonneg
      · simp [finiteQ, valid]

/-- The authored four-percept fold and the finite sum have the same value. -/
theorem sum_percepts {R : Type*} [AddCommMonoid R] (f : Percept → R) :
    (∑ e : Percept, f e) =
      [Percept.mk false false, .mk false true, .mk true false, .mk true true].foldl
        (fun total e => total + f e) 0 := by
  have all : (Finset.univ : Finset Percept) =
      {Percept.mk false false, .mk false true, .mk true false, .mk true true} := by
    ext e; rcases e with ⟨a,b⟩; cases a <;> cases b <;> simp
  simp [all, List.foldl, add_assoc]

/-- A probability interpretation needs these assumptions; raw weighted evaluation does not. -/
def ProbabilityRows (env : History → Percept → ENNReal) : Prop :=
  ∀ h a, DecisionHistory h →
    (∀ e, env (h ++ [HistElem.act a]) e ≠ ⊤) ∧
      ∑ e : Percept, env (h ++ [HistElem.act a]) e = 1

theorem ProbabilityRows.weights_sum {env : History → Percept → ENNReal}
    (rows : ProbabilityRows env) (h : History) (a : Action) (valid : DecisionHistory h) :
    ∑ e : Percept, branchWeight env h a e = 1 := by
  obtain ⟨finite, normalized⟩ := rows h a valid
  simpa only [branchWeight, normalized, ENNReal.toReal_one] using
    (ENNReal.toReal_sum (s := Finset.univ) (fun e _ => finite e)).symm

/-- The finite geometric return bound, including undiscounted finite horizons. -/
def returnBound (γ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => 1 + γ * returnBound γ n

theorem finiteQ_le_returnBound (data : FiniteValueData) (u : Utility)
    (upper : ∀ h, u h ≤ 1) (rows : ProbabilityRows data.envProb)
    (h : History) (valid : DecisionHistory h) (a : PolicyModAction) (n : ℕ) :
    finiteQ data u h a n ≤ returnBound data.γ.val n := by
  induction n generalizing h a with
  | zero => rfl
  | succ n ih =>
      simp only [finiteQ, valid.1, not_true_eq_false, ↓reduceIte]
      calc
        _ ≤ ∑ e : Percept, branchWeight data.envProb h a.worldAction e *
            (1 + data.γ.val * returnBound data.γ.val n) :=
          Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left
            (add_le_add (upper _) (mul_le_mul_of_nonneg_left
              (ih _ (valid.next _ _) _) data.γ.nonneg)) ENNReal.toReal_nonneg
        _ = returnBound data.γ.val (n+1) := by
          rw [← Finset.sum_mul, rows.weights_sum h a.worldAction valid, one_mul, returnBound]

end Mettapedia.UniversalAI.SelfModification
