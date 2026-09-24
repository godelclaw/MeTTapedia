import Mathlib
import FeedbackSensitiveBatch

/-!
# Act, then observe: what a blind batch costs

`FeedbackSensitiveBatch` settles *whether* a continuation chosen before an
observation can be right for every outcome: exactly when the step is
observation-invariant.  This file measures *how often* it is wrong when the
outcome is uncertain.  That is the quantitative form of the claim that
batching dependent steps to save model calls produces unreliable behavior,
while an act-then-observe loop does not.

* `observed_success_eq_one`: choosing after the observation is always right.
* `blind_failure_ge_min`: if outcomes `a` and `b` need different
  continuations, every continuation fixed in advance is wrong with
  probability at least `min (μ a) (μ b)`.
* `blind_batch_success_eq_prod`, `blind_batch_of_sensitive_steps`: over a
  batch of independent blind steps the chances of being right multiply.  If
  each step is wrong with probability at least `ε`, the whole batch is right
  with probability at most `(1 - ε) ^ k`, while act-then-observe is right
  with probability one (`observed_batch_success_eq_one`).
* `five_step_blind_batch_is_right_less_than_a_third`: five such steps with
  `ε = 1/5` — the runtime's five-command envelope
  (`ToolLoopComparison.every_mode_retains_five_commands`) — are all right
  less than a third of the time.
* `observed_value_ge_blind_value`, `observed_value_gt_blind_value`: for any
  rewards, deciding after the observation is never worse in expectation than
  deciding before it, and is strictly better when two possible outcomes have
  different unique best continuations.  This is the one-step form of the
  standard fact that closed-loop policies dominate open-loop plans.
* `batched_absence_claim_is_right_only_when_truly_absent`: a search and an
  absence claim sent in one batch is right exactly as often as the item is
  truly absent; a search that failed silently is indistinguishable from
  absence to the precommitted claim.

None of this forbids batching.  An observation-invariant region loses
nothing (`precommitment_exists_iff_observation_invariant`) and saves model
calls.  The price computed here is paid only by steps whose right
continuation depends on a result not yet seen.
-/

namespace PettaClaw.ActThenObserve

open Finset PettaClaw.FeedbackSensitiveBatch

/-- A finite outcome distribution: nonnegative masses summing to one. -/
structure Dist (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

/-! ## One step -/

section OneStep

variable {Ω C : Type*} [Fintype Ω] [DecidableEq C]

/-- Probability that a continuation fixed before the observation is right. -/
noncomputable def blindSuccess (μ : Dist Ω)
    (required : RequiredContinuation Ω C) (fixed : C) : ℝ :=
  ∑ ω, if required ω = fixed then μ.mass ω else 0

/-- Probability that the continuation chosen after the observation is right. -/
noncomputable def observedSuccess (μ : Dist Ω)
    (required : RequiredContinuation Ω C) : ℝ :=
  ∑ ω, if observeThenChoose required ω = required ω then μ.mass ω else 0

theorem observed_success_eq_one (μ : Dist Ω)
    (required : RequiredContinuation Ω C) :
    observedSuccess μ required = 1 := by
  simp [observedSuccess, observe_then_choose_is_correct, μ.total]

theorem blind_success_nonneg (μ : Dist Ω)
    (required : RequiredContinuation Ω C) (fixed : C) :
    0 ≤ blindSuccess μ required fixed :=
  sum_nonneg fun ω _ => by
    split_ifs
    exacts [μ.nonneg ω, le_rfl]

/-- An outcome that the fixed continuation gets wrong costs its whole mass. -/
theorem blind_success_le_one_sub (μ : Dist Ω)
    (required : RequiredContinuation Ω C) (fixed : C) {x : Ω}
    (miss : required x ≠ fixed) :
    blindSuccess μ required fixed ≤ 1 - μ.mass x := by
  classical
  unfold blindSuccess
  calc ∑ ω, (if required ω = fixed then μ.mass ω else 0)
      = ∑ ω ∈ univ.erase x, (if required ω = fixed then μ.mass ω else 0) :=
        (sum_erase univ (f := fun ω => if required ω = fixed then μ.mass ω else 0)
          (a := x) (if_neg miss)).symm
    _ ≤ ∑ ω ∈ univ.erase x, μ.mass ω :=
        sum_le_sum fun ω _ => by
          split_ifs
          exacts [le_rfl, μ.nonneg ω]
    _ = ∑ ω, μ.mass ω - μ.mass x := sum_erase_eq_sub (mem_univ x)
    _ = 1 - μ.mass x := by rw [μ.total]

/-- A blind step is wrong with probability at least the smaller mass of any
two outcomes that need different continuations. -/
theorem blind_failure_ge_min (μ : Dist Ω)
    (required : RequiredContinuation Ω C) (fixed : C) {a b : Ω}
    (differ : required a ≠ required b) :
    min (μ.mass a) (μ.mass b) ≤ 1 - blindSuccess μ required fixed := by
  by_cases ha : required a = fixed
  · have hb : required b ≠ fixed := fun hb => differ (ha.trans hb.symm)
    have := blind_success_le_one_sub μ required fixed hb
    linarith [min_le_right (μ.mass a) (μ.mass b)]
  · have := blind_success_le_one_sub μ required fixed ha
    linarith [min_le_left (μ.mass a) (μ.mass b)]

end OneStep

/-! ## A batch of blind steps -/

section Batch

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Ω C : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (C i)]

/-- Probability that a batch whose continuations were all fixed before any
observation is right at every step, when step outcomes are independent. -/
noncomputable def blindBatchSuccess (μ : ∀ i, Dist (Ω i))
    (required : ∀ i, RequiredContinuation (Ω i) (C i))
    (fixed : ∀ i, C i) : ℝ :=
  ∑ ω : ∀ i, Ω i,
    if ∀ i, required i (ω i) = fixed i then ∏ i, (μ i).mass (ω i) else 0

/-- The same batch run act-then-observe: each continuation is chosen after its
step's observation. -/
noncomputable def observedBatchSuccess (μ : ∀ i, Dist (Ω i))
    (required : ∀ i, RequiredContinuation (Ω i) (C i)) : ℝ :=
  ∑ ω : ∀ i, Ω i,
    if ∀ i, observeThenChoose (required i) (ω i) = required i (ω i) then
      ∏ i, (μ i).mass (ω i)
    else 0

theorem observed_batch_success_eq_one (μ : ∀ i, Dist (Ω i))
    (required : ∀ i, RequiredContinuation (Ω i) (C i)) :
    observedBatchSuccess μ required = 1 := by
  simp only [observedBatchSuccess, observe_then_choose_is_correct,
    implies_true, if_true]
  rw [← Fintype.prod_sum]
  simp [Dist.total]

theorem blind_batch_success_eq_prod (μ : ∀ i, Dist (Ω i))
    (required : ∀ i, RequiredContinuation (Ω i) (C i))
    (fixed : ∀ i, C i) :
    blindBatchSuccess μ required fixed =
      ∏ i, blindSuccess (μ i) (required i) (fixed i) := by
  unfold blindBatchSuccess blindSuccess
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun ω _ => ?_
  rw [Fintype.prod_ite_zero]

theorem blind_batch_success_le_pow (μ : ∀ i, Dist (Ω i))
    (required : ∀ i, RequiredContinuation (Ω i) (C i))
    (fixed : ∀ i, C i) {ε : ℝ}
    (uncertain : ∀ i, ε ≤ 1 - blindSuccess (μ i) (required i) (fixed i)) :
    blindBatchSuccess μ required fixed ≤ (1 - ε) ^ Fintype.card ι := by
  rw [blind_batch_success_eq_prod, ← card_univ, ← prod_const]
  exact prod_le_prod (fun i _ => blind_success_nonneg _ _ _)
    (fun i _ => by linarith [uncertain i])

/-- If every step of a precommitted batch has two outcomes, each of mass at
least `ε`, that need different continuations, the batch is right at every
step with probability at most `(1 - ε) ^ k`. -/
theorem blind_batch_of_sensitive_steps (μ : ∀ i, Dist (Ω i))
    (required : ∀ i, RequiredContinuation (Ω i) (C i))
    (fixed : ∀ i, C i) {ε : ℝ} (a b : ∀ i, Ω i)
    (differ : ∀ i, required i (a i) ≠ required i (b i))
    (likely : ∀ i, ε ≤ min ((μ i).mass (a i)) ((μ i).mass (b i))) :
    blindBatchSuccess μ required fixed ≤ (1 - ε) ^ Fintype.card ι :=
  blind_batch_success_le_pow μ required fixed fun i =>
    (likely i).trans
      (blind_failure_ge_min (μ i) (required i) (fixed i) (differ i))

end Batch

/-- Five blind dependent steps, each with a one-in-five chance of the outcome
that needs a different continuation, are all right less than a third of the
time; act-then-observe is always right. -/
theorem five_step_blind_batch_is_right_less_than_a_third
    {Ω C : Fin 5 → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (C i)]
    (μ : ∀ i, Dist (Ω i))
    (required : ∀ i, RequiredContinuation (Ω i) (C i))
    (fixed : ∀ i, C i) (a b : ∀ i, Ω i)
    (differ : ∀ i, required i (a i) ≠ required i (b i))
    (likely : ∀ i, 1 / 5 ≤ min ((μ i).mass (a i)) ((μ i).mass (b i))) :
    blindBatchSuccess μ required fixed < 1 / 3 ∧
      observedBatchSuccess μ required = 1 := by
  refine ⟨?_, observed_batch_success_eq_one μ required⟩
  have h := blind_batch_of_sensitive_steps μ required fixed a b differ likely
  rw [Fintype.card_fin] at h
  exact lt_of_le_of_lt h (by norm_num)

/-! ## Expected value: closed loop dominates open loop -/

section Value

variable {Ω C : Type*} [Fintype Ω]

/-- Expected reward of a continuation fixed before the observation. -/
noncomputable def blindValue (μ : Dist Ω) (reward : Ω → C → ℝ)
    (fixed : C) : ℝ :=
  ∑ ω, μ.mass ω * reward ω fixed

/-- Expected reward of a policy that sees the observation first. -/
noncomputable def observedValue (μ : Dist Ω) (reward : Ω → C → ℝ)
    (policy : Ω → C) : ℝ :=
  ∑ ω, μ.mass ω * reward ω (policy ω)

/-- A policy is greedy when, after each observation, no continuation earns
more. -/
def Greedy (reward : Ω → C → ℝ) (policy : Ω → C) : Prop :=
  ∀ ω c, reward ω c ≤ reward ω (policy ω)

omit [Fintype Ω] in
theorem exists_greedy [Finite C] [Nonempty C] (reward : Ω → C → ℝ) :
    ∃ policy, Greedy reward policy :=
  ⟨fun ω => Classical.choose (Finite.exists_max (reward ω)),
    fun ω c => Classical.choose_spec (Finite.exists_max (reward ω)) c⟩

/-- Deciding after the observation is never worse in expectation than any
decision made before it. -/
theorem observed_value_ge_blind_value (μ : Dist Ω) (reward : Ω → C → ℝ)
    {policy : Ω → C} (greedy : Greedy reward policy) (fixed : C) :
    blindValue μ reward fixed ≤ observedValue μ reward policy :=
  sum_le_sum fun ω _ =>
    mul_le_mul_of_nonneg_left (greedy ω fixed) (μ.nonneg ω)

/-- It is strictly better when two outcomes of positive probability have
different unique best continuations. -/
theorem observed_value_gt_blind_value (μ : Dist Ω) (reward : Ω → C → ℝ)
    {policy : Ω → C} (greedy : Greedy reward policy) {a b : Ω}
    (pa : 0 < μ.mass a) (pb : 0 < μ.mass b)
    (uniqueA : ∀ c, c ≠ policy a → reward a c < reward a (policy a))
    (uniqueB : ∀ c, c ≠ policy b → reward b c < reward b (policy b))
    (differ : policy a ≠ policy b) (fixed : C) :
    blindValue μ reward fixed < observedValue μ reward policy := by
  apply sum_lt_sum fun ω _ =>
    mul_le_mul_of_nonneg_left (greedy ω fixed) (μ.nonneg ω)
  by_cases ha : fixed = policy a
  · have hb : fixed ≠ policy b := fun hb => differ (ha.symm.trans hb)
    exact ⟨b, mem_univ b, mul_lt_mul_of_pos_left (uniqueB fixed hb) pb⟩
  · exact ⟨a, mem_univ a, mul_lt_mul_of_pos_left (uniqueA fixed ha) pa⟩

/-- With the zero-one reward "right or wrong", expected blind value is the
blind success probability of the first section. -/
theorem blind_value_of_indicator [DecidableEq C] (μ : Dist Ω)
    (required : RequiredContinuation Ω C) (fixed : C) :
    blindValue μ (fun ω c => if required ω = c then 1 else 0) fixed =
      blindSuccess μ required fixed := by
  unfold blindValue blindSuccess
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : required ω = fixed <;> simp [h]

end Value

/-! ## Search, then claim absence -/

/-- What a search can return. A malformed pattern (for example `|` read
literally by a basic regular expression) returns nothing, just as a truly
absent item does. -/
inductive SearchOutcome where
  | found
  | silentlyBroken
  | trulyAbsent
deriving DecidableEq, Fintype

inductive SearchFollowup where
  | reportFound
  | runPositiveControl
  | claimAbsent
deriving DecidableEq

def requiredAfterSearch : RequiredContinuation SearchOutcome SearchFollowup
  | .found => .reportFound
  | .silentlyBroken => .runPositiveControl
  | .trulyAbsent => .claimAbsent

theorem search_then_claim_is_feedback_sensitive :
    FeedbackSensitive requiredAfterSearch :=
  ⟨.silentlyBroken, .trulyAbsent, by decide⟩

/-- An absence claim batched with its own search is right exactly as often as
the item is truly absent: every silently broken search becomes a confident
false claim. -/
theorem batched_absence_claim_is_right_only_when_truly_absent
    (μ : Dist SearchOutcome) :
    blindSuccess μ requiredAfterSearch .claimAbsent =
      μ.mass .trulyAbsent := by
  have huniv : (univ : Finset SearchOutcome) =
      {.found, .silentlyBroken, .trulyAbsent} := by decide
  simp [blindSuccess, huniv, requiredAfterSearch]

end PettaClaw.ActThenObserve

#print axioms PettaClaw.ActThenObserve.observed_success_eq_one
#print axioms PettaClaw.ActThenObserve.blind_failure_ge_min
#print axioms PettaClaw.ActThenObserve.observed_batch_success_eq_one
#print axioms PettaClaw.ActThenObserve.blind_batch_success_eq_prod
#print axioms PettaClaw.ActThenObserve.blind_batch_of_sensitive_steps
#print axioms PettaClaw.ActThenObserve.five_step_blind_batch_is_right_less_than_a_third
#print axioms PettaClaw.ActThenObserve.observed_value_ge_blind_value
#print axioms PettaClaw.ActThenObserve.observed_value_gt_blind_value
#print axioms PettaClaw.ActThenObserve.blind_value_of_indicator
#print axioms PettaClaw.ActThenObserve.search_then_claim_is_feedback_sensitive
#print axioms PettaClaw.ActThenObserve.batched_absence_claim_is_right_only_when_truly_absent
