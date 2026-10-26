import Mettapedia.UniversalAI.MultiAgent.Environment
import Mettapedia.UniversalAI.MultiAgent.Policy
import Mettapedia.UniversalAI.BayesianAgents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Multi-Agent Value Functions

This file defines value functions for multi-agent reinforcement learning.

## Main Definitions

* `playerValue`: Expected discounted reward for player i
* `playerQValue`: Expected value of taking action a for player i
* `bestResponseValue`: Maximum value player i can achieve

## References

- Leike, Taylor & Fallenstein (2016). "A Formal Solution to the Grain of Truth Problem"
- Shoham & Leyton-Brown (2008). "Multiagent Systems"

-/

namespace Mettapedia.UniversalAI.MultiAgent

open Mettapedia.UniversalAI.BayesianAgents
open BigOperators

/-! ## Weighted Average Bound Lemmas -/

/-- Weighted sum is bounded by the bound when weights sum to ≤ 1 and values are ≤ bound.
    This is the key lemma for bounding expected values. -/
theorem weighted_sum_le_bound {α : Type*} [Fintype α] (w : α → ℝ) (v : α → ℝ) (B : ℝ)
    (hw_nonneg : ∀ a, 0 ≤ w a) (hw_sum : ∑ a, w a ≤ 1)
    (hv_le : ∀ a, v a ≤ B) (hB_nonneg : 0 ≤ B) :
    ∑ a, w a * v a ≤ B := by
  calc
    _ ≤ ∑ a, w a * B := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (hv_le a) (hw_nonneg a)
    _ = (∑ a, w a) * B := (Finset.sum_mul ..).symm
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right hw_sum hB_nonneg
    _ = B := one_mul B

/-- The same upper bound holds for normalized nonnegative weights. -/
theorem weighted_sum_le_bound_eq_one {α : Type*} [Fintype α] (w : α → ℝ) (v : α → ℝ) (B : ℝ)
    (hw_nonneg : ∀ a, 0 ≤ w a) (hw_sum : ∑ a, w a = 1)
    (hv_le : ∀ a, v a ≤ B) (hB_nonneg : 0 ≤ B) :
    ∑ a, w a * v a ≤ B := by
  apply weighted_sum_le_bound w v B hw_nonneg (le_of_eq hw_sum) hv_le hB_nonneg

/-! ## ENNReal.toReal Helpers -/

/-- Convert ENNReal sum to Real sum when all terms are finite. -/
theorem ennreal_sum_toReal_eq {α : Type*} [Fintype α] (f : α → ENNReal)
    (hf_ne_top : ∀ a, f a ≠ ⊤) :
    (∑ a, f a).toReal = ∑ a, (f a).toReal := by
  exact ENNReal.toReal_sum (s := Finset.univ) (f := f) (fun a _ha => hf_ne_top a)

/-- Terms of a bounded sum are finite. -/
theorem ennreal_term_ne_top_of_sum_le {α : Type*} [Fintype α] (f : α → ENNReal)
    (hsum_le : ∑ a, f a ≤ 1) (a : α) : f a ≠ ⊤ := by
  exact ne_top_of_le_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hsum_le)
    (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ a))

/-- When ENNReal sum ≤ 1, the Real sum also ≤ 1. -/
theorem ennreal_sum_toReal_le_one {α : Type*} [Fintype α] (f : α → ENNReal)
    (hsum_le : ∑ a, f a ≤ 1) :
    ∑ a, (f a).toReal ≤ 1 := by
  rw [← ennreal_sum_toReal_eq f (ennreal_term_ne_top_of_sum_le f hsum_le)]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hsum_le)

/-- When ENNReal sum = 1, the Real sum also = 1. -/
theorem ennreal_sum_toReal_eq_one {α : Type*} [Fintype α] (f : α → ENNReal)
    (hsum_eq : ∑ a, f a = 1) :
    ∑ a, (f a).toReal = 1 := by
  rw [← ennreal_sum_toReal_eq f (ennreal_term_ne_top_of_sum_le f hsum_eq.le),
    hsum_eq, ENNReal.toReal_one]

/-! ## Helper: Joint action probability -/

/-- Probability that all agents choose the given joint action. -/
noncomputable def jointActionProb
    (π : MultiAgentPolicy n)
    (h : MultiAgentHistory n)
    (ja : JointAction n) : ENNReal :=
  ∏ j : Fin n, (π.agents j).policy (h.playerView j) (ja j)

/-- Joint action probabilities sum to 1.

    This follows from the fact that each agent's policy sums to 1,
    and the joint action probability is a product of independent policies.
    Uses Finset.sum_prod_piFinset: ∑ f ∈ piFinset s, ∏ i, g i (f i) = ∏ i, ∑ j ∈ s i, g i j
-/
theorem jointActionProb_sum_eq_one {n : ℕ} (π : MultiAgentPolicy n)
    (h : MultiAgentHistory n) (hw : h.wellFormed = true) :
    (∑ ja : JointAction n, jointActionProb π h ja) = 1 := by
  simp only [jointActionProb, JointAction]
  rw [← Fintype.piFinset_univ, Finset.sum_prod_piFinset]
  have each (j : Fin n) : (∑ a, (π.agents j).policy (h.playerView j) a) = 1 := by
    simpa only [tsum_fintype] using (π.agents j).policy_sum_one _
      (MultiAgentHistory.playerView_wellFormed j h hw)
  simp only [each, Finset.prod_const_one]

/-! ## Player Value Function -/

/-- Expected discounted reward for player i under joint policy π. -/
noncomputable def playerValue
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (horizon : ℕ) : ℝ :=
  match horizon with
  | 0 => 0
  | k + 1 =>
    ∑' (ja : JointAction n),
      ∑' (jp : JointPercept n),
        let actionProb := jointActionProb π h ja
        let envProb := μ.prob (h ++ [JointHistElem.act ja]) jp
        ((actionProb * envProb).toReal) *
        ((jp i).reward +
         γ.val * playerValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k)

/-- Player value is non-negative. -/
theorem playerValue_nonneg {n : ℕ} (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n) (γ : DiscountFactor)
    (i : Fin n) (h : MultiAgentHistory n) (horizon : ℕ) :
    0 ≤ playerValue μ π γ i h horizon := by
  induction horizon generalizing h with
  | zero => rfl
  | succ k ih =>
      exact tsum_nonneg fun ja => tsum_nonneg fun jp =>
        mul_nonneg ENNReal.toReal_nonneg
          (add_nonneg (Percept.reward_nonneg _) (mul_nonneg γ.nonneg (ih _)))

/-- Helper: The inner value term is bounded by (k+1). -/
private theorem playerValue_inner_bound {n : ℕ} (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n) (γ : DiscountFactor) (i : Fin n) (k : ℕ)
    (h : MultiAgentHistory n) (ja : JointAction n) (jp : JointPercept n)
    (ih : ∀ h', playerValue μ π γ i h' k ≤ k) :
    (jp i).reward + γ.val * playerValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k ≤ k + 1 := by
  calc
    _ ≤ 1 + γ.val * (k : ℝ) := add_le_add (Percept.reward_le_one _)
      (mul_le_mul_of_nonneg_left (ih _) γ.nonneg)
    _ ≤ k + 1 := by nlinarith [γ.le_one, Nat.cast_nonneg (α := ℝ) k]

/-- Player value is bounded by horizon.

    This is the multi-agent analogue of the single-agent `value_le` theorem.
    The proof uses:
    1. `jointActionProb_sum_eq_one`: joint action probabilities sum to 1
    2. `μ.prob_le_one`: environment probabilities sum to ≤ 1
    3. `Percept.reward_le_one`: rewards are in [0,1]
    4. `γ.le_one`: discount factor ≤ 1
    5. `endsWithPercept`: history ends with percept (or is empty) for extension
-/
theorem playerValue_le_horizon {n : ℕ} (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n) (γ : DiscountFactor)
    (i : Fin n) (h : MultiAgentHistory n)
    (hw : h.wellFormed = true) (hep : h.endsWithPercept = true) (horizon : ℕ) :
    playerValue μ π γ i h horizon ≤ horizon := by
  induction horizon generalizing h with
  | zero => simp [playerValue]
  | succ k ih =>
      simp only [playerValue, tsum_fintype, ENNReal.toReal_mul, mul_assoc]
      calc
        _ = ∑ ja, (jointActionProb π h ja).toReal *
            ∑ jp, (μ.prob (h ++ [JointHistElem.act ja]) jp).toReal *
              ((jp i).reward + γ.val *
                playerValue μ π γ i (h ++ [.act ja, .per jp]) k) := by
                  simp only [Finset.mul_sum]
        _ ≤ ∑ ja, (jointActionProb π h ja).toReal * ((k : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro ja _
          apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          apply weighted_sum_le_bound
          · exact fun _ => ENNReal.toReal_nonneg
          · apply ennreal_sum_toReal_le_one
            simpa only [tsum_fintype] using μ.prob_le_one _
              (MultiAgentHistory.wellFormed_append_act h ja hw hep)
          · intro jp
            have valid := MultiAgentHistory.wellFormed_append_act_per h ja jp hw hep
            calc
              _ ≤ 1 + γ.val * (k : ℝ) := add_le_add (Percept.reward_le_one _)
                (mul_le_mul_of_nonneg_left (ih _ valid.1 valid.2) γ.nonneg)
              _ ≤ k + 1 := by nlinarith [γ.le_one, Nat.cast_nonneg (α := ℝ) k]
          · positivity
        _ = ((k + 1 : ℕ) : ℝ) := by
          rw [← Finset.sum_mul, ennreal_sum_toReal_eq_one _ (jointActionProb_sum_eq_one π h hw)]
          simp

/-- Probability of other players' actions (excluding player i). -/
noncomputable def othersProb {n : ℕ}
    (π : MultiAgentPolicy n)
    (h : MultiAgentHistory n)
    (ja : JointAction n)
    (i : Fin n) : ENNReal :=
  Finset.prod (Finset.univ.erase i) fun j =>
    (π.agents j).policy (h.playerView j) (ja j)

/-- One forced action, with the supplied values of the actual successor histories.
The own-action guard retains each opponent configuration exactly once. -/
noncomputable def actionValueStep (μ : MultiAgentEnvironment n) (π : MultiAgentPolicy n)
    (γ : DiscountFactor) (i : Fin n) (h : MultiAgentHistory n) (action : Action)
    (continuation : MultiAgentHistory n → ℝ) : ℝ :=
  ∑' ja : JointAction n, if ja i = action then
    ∑' jp : JointPercept n, (othersProb π h ja i * μ.prob (h ++ [.act ja]) jp).toReal *
      ((jp i).reward + γ.val * continuation (h ++ [.act ja, .per jp]))
  else 0

/-- Only the other agents and the supplied successor observations matter. -/
theorem actionValueStep_congr (μ : MultiAgentEnvironment n) (π π' : MultiAgentPolicy n)
    (γ : DiscountFactor) (i : Fin n) (h : MultiAgentHistory n) (action : Action)
    (v v' : MultiAgentHistory n → ℝ)
    (others : ∀ j, j ≠ i → π.agents j = π'.agents j)
    (values : ∀ ja jp, v (h ++ [.act ja, .per jp]) = v' (h ++ [.act ja, .per jp])) :
    actionValueStep μ π γ i h action v = actionValueStep μ π' γ i h action v' := by
  have weights (ja : JointAction n) : othersProb π h ja i = othersProb π' h ja i :=
    Finset.prod_congr rfl fun j member => by rw [others j (Finset.mem_erase.mp member).1]
  simp only [actionValueStep, weights, values]

/-- Nonnegative transition weights make the continuation interpretation monotone. -/
theorem actionValueStep_mono (μ : MultiAgentEnvironment n) (π : MultiAgentPolicy n)
    (γ : DiscountFactor) (i : Fin n) (h : MultiAgentHistory n) (action : Action)
    (v v' : MultiAgentHistory n → ℝ)
    (values : ∀ ja jp, v (h ++ [.act ja, .per jp]) ≤ v' (h ++ [.act ja, .per jp])) :
    actionValueStep μ π γ i h action v ≤ actionValueStep μ π γ i h action v' := by
  simp only [actionValueStep, tsum_fintype]
  apply Finset.sum_le_sum
  intro ja _
  split_ifs
  · exact Finset.sum_le_sum fun jp _ => mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_left (values ja jp) γ.nonneg) _)
      ENNReal.toReal_nonneg
  · rfl

/-! ## Q-Value Function -/

/-- Expected value for player i when forcing action a, then following π. -/
noncomputable def playerQValue
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action)
    (horizon : ℕ) : ℝ :=
  match horizon with
  | 0 => 0
  | k + 1 =>
    -- Sum over all possible joint actions
    ∑' (ja : JointAction n),
      -- Check if player i takes the forced action
      if ja i = action then
        -- Compute probability of other players' actions
        let othersProb : ENNReal :=
          Finset.prod (Finset.univ.erase i) fun j =>
            (π.agents j).policy (h.playerView j) (ja j)
        ∑' (jp : JointPercept n),
          let envProb := μ.prob (h ++ [JointHistElem.act ja]) jp
          ((othersProb * envProb).toReal) *
          ((jp i).reward +
           γ.val * playerValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k)
      else
        0

/-! ## Full-history optimal continuation

These Bellman values optimize using the full joint history. They upper-bound
local-view policy values; attaining them needs an information-sufficiency proof.
`playerQValue` follows the fixed policy after its forced action, whereas
`bestResponseQValue` optimizes every remaining action.
-/

mutual
/-- Q-value when player i plays optimally in all future steps.
    Other players follow their policies π_j for j ≠ i. -/
noncomputable def bestResponseQValue
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action)
    (horizon : ℕ) : ℝ :=
  match horizon with
  | 0 => 0
  | k + 1 =>
    ∑' (ja : JointAction n),
      if ja i = action then
        let othersProb : ENNReal :=
          Finset.prod (Finset.univ.erase i) fun j =>
            (π.agents j).policy (h.playerView j) (ja j)
        ∑' (jp : JointPercept n),
          let envProb := μ.prob (h ++ [JointHistElem.act ja]) jp
          ((othersProb * envProb).toReal) *
          ((jp i).reward +
           γ.val * bestResponseValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k)
      else
        0

/-- The full-joint-history Bellman envelope with other agents fixed.
A local-view agent attains it only under a separate realization theorem. -/
noncomputable def bestResponseValue
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (horizon : ℕ) : ℝ :=
  ⨆ (action : Action), bestResponseQValue μ π γ i h action horizon
end

theorem playerQValue_succ (μ : MultiAgentEnvironment n) (π : MultiAgentPolicy n)
    (γ : DiscountFactor) (i : Fin n) (h : MultiAgentHistory n) (a : Action) (k : ℕ) :
    playerQValue μ π γ i h a (k+1) =
      actionValueStep μ π γ i h a (fun next => playerValue μ π γ i next k) := rfl

theorem bestResponseQValue_succ (μ : MultiAgentEnvironment n) (π : MultiAgentPolicy n)
    (γ : DiscountFactor) (i : Fin n) (h : MultiAgentHistory n) (a : Action) (k : ℕ) :
    bestResponseQValue μ π γ i h a (k+1) =
      actionValueStep μ π γ i h a (fun next => bestResponseValue μ π γ i next k) := by
  simp only [bestResponseQValue, actionValueStep, othersProb]

/-- At one step, there is no future policy choice to distinguish the two Q-values. -/
theorem playerQValue_one_eq_bestResponseQValue (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n) (γ : DiscountFactor) (i : Fin n) (h : MultiAgentHistory n) (a : Action) :
    playerQValue μ π γ i h a 1 = bestResponseQValue μ π γ i h a 1 := by
  simp only [playerQValue_succ, bestResponseQValue_succ, playerValue, bestResponseValue]
  simp only [bestResponseQValue, ciSup_const]

/-! ## One-Step Best Response Value (for comparison)

This is what we originally had - optimizing only the current action,
assuming player i follows π_i in future steps. Useful for some proofs. -/

/-- One-step best response: optimize current action only, then follow π_i.
    This equals ⨆_a playerQValue μ π γ i h a horizon. -/
noncomputable def oneStepBestResponseValue
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (horizon : ℕ) : ℝ :=
  ⨆ (action : Action), playerQValue μ π γ i h action horizon

/-- Weighted average is ≤ supremum for finite types with nonnegative weights summing to 1. -/
theorem weighted_avg_le_ciSup {α : Type*} [Fintype α] [Nonempty α]
    (w : α → ℝ) (x : α → ℝ)
    (hw_nonneg : ∀ a, 0 ≤ w a)
    (hw_sum : ∑ a, w a = 1) :
    ∑ a, w a * x a ≤ ⨆ a, x a := by
  have bounded := Set.Finite.bddAbove (Set.finite_range x)
  calc
    _ ≤ ∑ a, w a * (⨆ a, x a) := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (le_ciSup bounded a) (hw_nonneg a)
    _ = (⨆ a, x a) := by rw [← Finset.sum_mul, hw_sum, one_mul]

/-- Split jointActionProb into player i's probability and others' probability. -/
theorem jointActionProb_split {n : ℕ} (π : MultiAgentPolicy n)
    (h : MultiAgentHistory n) (ja : JointAction n) (i : Fin n) :
    jointActionProb π h ja =
    (π.agents i).policy (h.playerView i) (ja i) *
    Finset.prod (Finset.univ.erase i) fun j =>
      (π.agents j).policy (h.playerView j) (ja j) := by
  simp only [jointActionProb]
  -- Split the product at i: ∏ j, f j = f i * ∏ j ≠ i, f j
  conv_lhs => rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]

/-- othersProb is bounded by 1. -/
theorem othersProb_le_one {n : ℕ} (π : MultiAgentPolicy n)
    (h : MultiAgentHistory n) (ja : JointAction n) (i : Fin n)
    (hw : h.wellFormed = true) : othersProb π h ja i ≤ 1 := by
  simp only [othersProb]
  apply Finset.prod_le_one
  · intro j _; exact zero_le
  · intro j _hj
    have hpview := MultiAgentHistory.playerView_wellFormed j h hw
    have hsum : (∑ a : Action, (π.agents j).policy (h.playerView j) a) = 1 := by
      simpa [tsum_fintype] using (π.agents j).policy_sum_one (h.playerView j) hpview
    have hle : (π.agents j).policy (h.playerView j) (ja j) ≤
               ∑ a : Action, (π.agents j).policy (h.playerView j) a := by
      apply Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ _)
    simpa [hsum] using hle

/-- Sum over if-then-else: ∑ x, (if x = target then f x else 0) = f target -/
theorem sum_ite_eq_val {α β : Type*} [Fintype α] [AddCommMonoid β] [DecidableEq α]
    (f : α → β) (target : α) :
    ∑ x : α, (if x = target then f x else 0) = f target := by
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Fiber-wise decomposition: ∑_x f(x) = ∑_a ∑_x (if g(x) = a then f(x) else 0) -/
theorem sum_fiberwise {α β γ : Type*} [Fintype α] [Fintype β] [AddCommMonoid γ] [DecidableEq β]
    (f : α → γ) (g : α → β) :
    ∑ x : α, f x = ∑ b : β, ∑ x : α, (if g x = b then f x else 0) := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- Policy evaluation is the policy-weighted average of its forced-action values. -/
theorem playerValue_eq_weighted_qValue {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (horizon : ℕ) :
    playerValue μ π γ i h horizon =
    ∑ a : Action, ((π.agents i).policy (h.playerView i) a).toReal *
                  playerQValue μ π γ i h a horizon := by
  cases horizon with
  | zero => simp only [playerValue, playerQValue, mul_zero, Finset.sum_const_zero]
  | succ k =>
      simp only [playerValue, playerQValue, tsum_fintype]
      have factor (ja : JointAction n) : jointActionProb π h ja =
          (π.agents i).policy (h.playerView i) (ja i) * othersProb π h ja i :=
        jointActionProb_split π h ja i
      simp_rw [factor, mul_assoc, ENNReal.toReal_mul, mul_assoc, ← Finset.mul_sum]
      rw [sum_fiberwise _ (fun ja => ja i)]
      congr 1
      ext a
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ja _
      by_cases chosen : ja i = a
      · simp only [chosen, ↓reduceIte, othersProb]
      · simp only [chosen, ↓reduceIte, mul_zero]

/-- Averaging current actions cannot exceed their best Q-value. -/
theorem playerValue_le_oneStepBestResponseValue {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (horizon : ℕ) :
    playerValue μ π γ i h horizon ≤
    oneStepBestResponseValue μ π γ i h horizon := by
  rw [playerValue_eq_weighted_qValue]
  apply weighted_avg_le_ciSup _ _ (fun _ => ENNReal.toReal_nonneg)
  apply ennreal_sum_toReal_eq_one
  simpa only [tsum_fintype] using (π.agents i).policy_sum_one _
    (MultiAgentHistory.playerView_wellFormed i h hw)

/-- Following the fixed policy is bounded by optimizing each remaining decision. -/
theorem playerQValue_le_bestResponseQValue {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (hep : h.endsWithPercept = true)
    (action : Action)
    (horizon : ℕ) :
    playerQValue μ π γ i h action horizon ≤
    bestResponseQValue μ π γ i h action horizon := by
  induction horizon generalizing h action with
  | zero => simp [playerQValue, bestResponseQValue]
  | succ k ih =>
      rw [playerQValue_succ, bestResponseQValue_succ]
      apply actionValueStep_mono
      intro ja jp
      have valid := MultiAgentHistory.wellFormed_append_act_per h ja jp hw hep
      refine (playerValue_le_oneStepBestResponseValue μ π γ i _ valid.1 k).trans ?_
      simp only [oneStepBestResponseValue, bestResponseValue]
      apply ciSup_mono (Set.Finite.bddAbove (Set.finite_range _))
      exact fun a => ih _ valid.1 valid.2 a

/-- oneStepBestResponseValue ≤ bestResponseValue.

    One-step optimization is at most as good as optimizing at every step.
    This follows from playerQValue ≤ bestResponseQValue. -/
theorem oneStepBestResponseValue_le_bestResponseValue {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (hep : h.endsWithPercept = true)
    (horizon : ℕ) :
    oneStepBestResponseValue μ π γ i h horizon ≤
    bestResponseValue μ π γ i h horizon := by
  simp only [oneStepBestResponseValue, bestResponseValue]
  exact ciSup_mono (Set.Finite.bddAbove (Set.finite_range _)) fun a => playerQValue_le_bestResponseQValue μ π γ i h hw hep a horizon

/-- Best response value is at least as good as following the policy.

    This is the main inequality: playing optimally is at least as good as following any policy.
-/
theorem playerValue_le_bestResponseValue {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (hep : h.endsWithPercept = true)
    (horizon : ℕ) :
    playerValue μ π γ i h horizon ≤
    bestResponseValue μ π γ i h horizon := by
  calc playerValue μ π γ i h horizon
      ≤ oneStepBestResponseValue μ π γ i h horizon :=
        playerValue_le_oneStepBestResponseValue μ π γ i h hw horizon
    _ ≤ bestResponseValue μ π γ i h horizon :=
        oneStepBestResponseValue_le_bestResponseValue μ π γ i h hw hep horizon

end Mettapedia.UniversalAI.MultiAgent
