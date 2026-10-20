import Mettapedia.PLN.Evidence.BinaryEvidence
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Real.Basic
import Mettapedia.ProbabilityTheory.FiniteEventMass


/-!
# Complete PLN: Exact Bayesian Inference in Logical Form

This file provides a "minimally complete" version of PLN that performs exact
Bayesian inference without independence assumptions. An AGI can smoothly switch
between the fast heuristic PLN and this complete version as needed.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     PLN INFERENCE SYSTEM                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   ┌─────────────────┐         ┌─────────────────┐              │
│   │   FAST PLN      │         │  COMPLETE PLN   │              │
│   │  (Heuristic)    │◄───────►│    (Exact)      │              │
│   │                 │  switch │                 │              │
│   │ • O(1) formulas │         │ • Full Bayes    │              │
│   │ • Independence  │         │ • No assumptions│              │
│   │ • Approximate   │         │ • Exact         │              │
│   └─────────────────┘         └─────────────────┘              │
│           │                           │                        │
│           └───────────┬───────────────┘                        │
│                       ▼                                        │
│              ┌─────────────────┐                               │
│              │  UNIFIED API    │                               │
│              │                 │                               │
│              │ deduction(A,B,C)│                               │
│              │ induction(A,B,C)│                               │
│              │ abduction(A,B,C)│                               │
│              └─────────────────┘                               │
└─────────────────────────────────────────────────────────────────┘
```

## When to Use Each Mode

| Situation | Use Fast PLN | Use Complete PLN |
|-----------|--------------|------------------|
| Many variables, need speed | ✓ | |
| Independence likely holds | ✓ | |
| Critical decision | | ✓ |
| Independence violated | | ✓ |
| Full joint available | | ✓ |
| Learning/calibration | | ✓ |

## Key Insight

Complete PLN = Bayesian inference expressed in PLN's logical notation.
The "completeness" comes from tracking full joint distributions rather
than just pairwise conditional probabilities.

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009)
- Pearl, "Probabilistic Reasoning in Intelligent Systems" (1988)
-/

namespace Mettapedia.PLN.Core.CompletePLN

open Mettapedia.PLN.Evidence
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation

/-! ## Part 1: Joint Probability Distribution

The key to completeness is tracking the full joint distribution P(A, B, C, ...).
From this, ALL conditional probabilities can be computed exactly.
-/

/-- A finite joint probability distribution over n binary propositions.

    For n propositions, there are 2^n possible worlds.
    Each world is a function from proposition index to Bool.
    The distribution assigns a probability to each world.
-/
structure JointDistribution (n : ℕ) where
  /-- Probability of each world (indexed by Fin (2^n)) -/
  prob : Fin (2^n) → ℝ
  /-- Probabilities are non-negative -/
  prob_nonneg : ∀ i, 0 ≤ prob i
  /-- Probabilities sum to 1 -/
  prob_sum_one : (Finset.univ.sum prob) = 1

/-- Convert a world index to a truth assignment for propositions -/
def worldToAssignment (n : ℕ) (world : Fin (2^n)) (prop : Fin n) : Bool :=
  (world.val / 2^prop.val) % 2 = 1

/-- Marginal probability P(prop_i = true) -/
noncomputable def marginalProb (J : JointDistribution n) (prop : Fin n) : ℝ :=
  Finset.univ.sum fun world =>
    if worldToAssignment n world prop then J.prob world else 0

/-- Joint probability P(prop_i = true ∧ prop_j = true) -/
noncomputable def jointProb2 (J : JointDistribution n) (i j : Fin n) : ℝ :=
  Finset.univ.sum fun world =>
    if worldToAssignment n world i ∧ worldToAssignment n world j
    then J.prob world else 0

/-- Conditional probability P(prop_i = true | prop_j = true)

    Returns 0 if P(prop_j) = 0 (undefined case).
-/
noncomputable def condProb (J : JointDistribution n) (i j : Fin n) : ℝ :=
  let pj := marginalProb J j
  if pj = 0 then 0 else jointProb2 J i j / pj

/-- Joint probability P(A ∧ B ∧ C) for three propositions -/
noncomputable def jointProb3 (J : JointDistribution n) (a b c : Fin n) : ℝ :=
  Finset.univ.sum fun world =>
    if worldToAssignment n world a ∧
       worldToAssignment n world b ∧
       worldToAssignment n world c
    then J.prob world else 0

/-- Conditional probability P(C | A ∧ B) -/
noncomputable def condProb2 (J : JointDistribution n) (c a b : Fin n) : ℝ :=
  let pab := jointProb2 J a b
  if pab = 0 then 0 else jointProb3 J a b c / pab

/-- Marginal probability P(prop_i = false) -/
noncomputable def marginalProbNeg (J : JointDistribution n) (prop : Fin n) : ℝ :=
  Finset.univ.sum fun world =>
    if ¬worldToAssignment n world prop then J.prob world else 0

/-- Joint probability P(prop_i = true ∧ prop_j = false) -/
noncomputable def jointProb2Neg (J : JointDistribution n) (i j : Fin n) : ℝ :=
  Finset.univ.sum fun world =>
    if worldToAssignment n world i ∧ ¬worldToAssignment n world j
    then J.prob world else 0

/-- Joint probability P(A ∧ ¬B ∧ C) -/
noncomputable def jointProb3Neg (J : JointDistribution n) (a b c : Fin n) : ℝ :=
  Finset.univ.sum fun world =>
    if worldToAssignment n world a ∧
       ¬worldToAssignment n world b ∧
       worldToAssignment n world c
    then J.prob world else 0

/-- Conditional probability P(C | ¬B)
    Returns 0 if P(¬B) = 0.
-/
noncomputable def condProbNeg (J : JointDistribution n) (c b : Fin n) : ℝ :=
  let pnb := marginalProbNeg J b
  if pnb = 0 then 0 else
    (Finset.univ.sum fun world =>
      if ¬worldToAssignment n world b ∧ worldToAssignment n world c
      then J.prob world else 0) / pnb

/-- Conditional probability P(C | A ∧ ¬B) -/
noncomputable def condProb2Neg (J : JointDistribution n) (c a b : Fin n) : ℝ :=
  let panb := jointProb2Neg J a b
  if panb = 0 then 0 else jointProb3Neg J a b c / panb

/-! ## Part 2: Complete PLN Inference Rules

These are the EXACT versions of PLN inference rules.
They compute true conditional probabilities without any assumptions.
-/

/-- COMPLETE Deduction: Exact P(C|A) via Law of Total Probability.

    P(C|A) = P(C|A,B) · P(B|A) + P(C|A,¬B) · P(¬B|A)

    This is EXACT - no independence assumptions needed.
    The complexity is in computing the joint probabilities.
-/
noncomputable def completeDeduction (J : JointDistribution n)
    (a b c : Fin n) : ℝ :=
  condProb J c a

/-- COMPLETE Induction: Exact P(C|A) given we know about B→A and B→C.

    Unlike fast PLN, this doesn't use Bayes inversion approximation.
    It directly computes P(C|A) from the joint distribution.
-/
noncomputable def completeInduction (J : JointDistribution n)
    (a b c : Fin n) : ℝ :=
  condProb J c a

/-- COMPLETE Abduction: Exact P(C|A) given we know about A→B and C→B.

    Unlike fast PLN, this doesn't use Bayes inversion approximation.
    It directly computes P(C|A) from the joint distribution.
-/
noncomputable def completeAbduction (J : JointDistribution n)
    (a b c : Fin n) : ℝ :=
  condProb J c a

/-! ## Part 3: Unified Inference Mode

An AGI can choose between fast and complete modes based on context.
-/

/-- Inference mode selector -/
inductive InferenceMode
  | fast      -- Use heuristic PLN formulas (O(1), approximate)
  | complete  -- Use exact Bayesian inference (O(2^n), exact)
  | adaptive  -- Automatically choose based on context
  deriving DecidableEq, Repr

/-- Context for deciding which mode to use -/
structure InferenceContext where
  /-- Number of propositions involved -/
  num_props : ℕ
  /-- Is this a critical decision? -/
  is_critical : Bool
  /-- Do we have the full joint distribution? -/
  has_joint : Bool
  /-- Are independence assumptions likely valid? -/
  independence_likely : Bool
  /-- Time budget (relative units) -/
  time_budget : ℕ

/-- Automatically select inference mode based on context -/
def selectMode (ctx : InferenceContext) : InferenceMode :=
  -- Use complete mode if:
  -- 1. It's a critical decision, OR
  -- 2. We have the joint AND independence is unlikely
  -- 3. Small enough to be tractable (≤ 10 props → 1024 worlds)
  if ctx.is_critical && ctx.num_props ≤ 10 then
    InferenceMode.complete
  else if ctx.has_joint && !ctx.independence_likely && ctx.num_props ≤ 10 then
    InferenceMode.complete
  else if ctx.time_budget < 10 then
    InferenceMode.fast
  else
    InferenceMode.fast

/-! ## Part 4: Hybrid Inference System

The unified API that dispatches to either fast or complete PLN.
-/

/-- Strength values for fast PLN (pairwise conditional probabilities) -/
structure FastPLNInputs where
  s_AB : ℝ  -- P(B|A)
  s_BC : ℝ  -- P(C|B)
  s_A : ℝ   -- P(A)
  s_B : ℝ   -- P(B)
  s_C : ℝ   -- P(C)

/-- Complete PLN inputs (joint distribution) -/
structure CompletePLNInputs (n : ℕ) where
  joint : JointDistribution n
  prop_A : Fin n
  prop_B : Fin n
  prop_C : Fin n

/-- Result of inference with provenance -/
structure InferenceResult where
  /-- The computed strength/probability -/
  strength : ℝ
  /-- Which mode was used -/
  mode_used : InferenceMode
  /-- Uncalibrated dispatcher score; neither PLN observation confidence nor
      a certified approximation-error bound. -/
  heuristicScore : ℝ
  /-- Was independence assumed? -/
  assumed_independence : Bool

/-- HYBRID Deduction: Dispatches to fast or complete based on mode.

    This is the main API for AGI systems. It:
    1. Accepts either fast inputs OR complete inputs
    2. Uses the specified mode (or auto-selects)
    3. Returns result with provenance
-/
noncomputable def hybridDeduction
    (mode : InferenceMode)
    (fast_inputs : Option FastPLNInputs)
    (complete_inputs : Option (Σ n, CompletePLNInputs n))
    (ctx : InferenceContext) : InferenceResult :=
  let actual_mode := match mode with
    | InferenceMode.adaptive => selectMode ctx
    | m => m
  match actual_mode with
  | InferenceMode.fast =>
    match fast_inputs with
    | some inputs =>
      { strength := plnDeductionStrength inputs.s_AB inputs.s_BC inputs.s_B inputs.s_C
        mode_used := InferenceMode.fast
        heuristicScore := 0.8  -- Dispatch heuristic; not calibrated observation confidence.
        assumed_independence := true }
    | none =>
      -- Fallback: can't compute without inputs
      { strength := 0.5
        mode_used := InferenceMode.fast
        heuristicScore := 0
        assumed_independence := true }
  | InferenceMode.complete =>
    match complete_inputs with
    | some ⟨n, inputs⟩ =>
      { strength := completeDeduction inputs.joint inputs.prop_A inputs.prop_B inputs.prop_C
        mode_used := InferenceMode.complete
        heuristicScore := 1.0  -- Dispatch heuristic; exactness is established separately.
        assumed_independence := false }
    | none =>
      -- Fallback to fast mode if no joint available
      match fast_inputs with
      | some inputs =>
        { strength := plnDeductionStrength inputs.s_AB inputs.s_BC inputs.s_B inputs.s_C
          mode_used := InferenceMode.fast
          heuristicScore := 0.8
          assumed_independence := true }
      | none =>
        { strength := 0.5
          mode_used := InferenceMode.fast
          heuristicScore := 0
          assumed_independence := true }
  | InferenceMode.adaptive =>
    -- Already handled above, this case shouldn't occur
    { strength := 0.5
      mode_used := InferenceMode.adaptive
      heuristicScore := 0
      assumed_independence := true }

/-! ## Part 5: Verification: Complete Mode Equals Exact Probability

Key theorem: When using complete mode, we get the TRUE conditional probability.
-/

/-- Complete deduction gives the exact conditional probability -/
theorem complete_deduction_exact (J : JointDistribution n) (a b c : Fin n) :
    completeDeduction J a b c = condProb J c a := by
  rfl

/-- Marginal probabilities are in [0, 1] -/
theorem marginal_prob_bounds (J : JointDistribution n) (prop : Fin n) :
    0 ≤ marginalProb J prop ∧ marginalProb J prop ≤ 1 := by
  constructor
  · -- Non-negativity
    unfold marginalProb
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact J.prob_nonneg i
    · linarith
  · -- Upper bound
    unfold marginalProb
    calc Finset.univ.sum (fun world => if worldToAssignment n world prop then J.prob world else 0)
        ≤ Finset.univ.sum J.prob := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs
          · exact le_refl _
          · exact J.prob_nonneg i
      _ = 1 := J.prob_sum_one

/-- Conditional probability is in [0, 1] when denominator is positive -/
theorem cond_prob_bounds (J : JointDistribution n) (i j : Fin n)
    (hj : 0 < marginalProb J j) :
    0 ≤ condProb J i j ∧ condProb J i j ≤ 1 := by
  unfold condProb
  simp only [hj.ne', ↓reduceIte]
  constructor
  · -- Non-negativity: jointProb2 ≥ 0 and marginalProb > 0
    apply div_nonneg
    · unfold jointProb2
      apply Finset.sum_nonneg
      intro k _
      split_ifs
      · exact J.prob_nonneg k
      · linarith
    · linarith
  · -- Upper bound: jointProb2 ≤ marginalProb j
    rw [div_le_one hj]
    unfold jointProb2 marginalProb
    apply Finset.sum_le_sum
    intro k _
    by_cases h1 : worldToAssignment n k i = true ∧ worldToAssignment n k j = true
    · -- Both true: if-then-else reduces to J.prob k on both sides
      simp only [h1, and_self, ↓reduceIte, le_refl]
    · -- Not both true: jointProb2 contribution is 0
      simp only [h1, ↓reduceIte]
      by_cases h2 : worldToAssignment n k j = true
      · -- j true but not both: 0 ≤ J.prob k
        simp only [h2, ↓reduceIte]
        exact J.prob_nonneg k
      · -- j false: 0 ≤ 0
        have h2' : worldToAssignment n k j = false := Bool.eq_false_iff.mpr h2
        simp only [h2', Bool.false_eq_true, ↓reduceIte]
        exact le_refl 0

/-- The conditional readout is in the unit interval, including its numerical
zero convention for an unsupported conditioning event. -/
theorem cond_prob_mem_unit (J : JointDistribution n) (i j : Fin n) :
    condProb J i j ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases positive : 0 < marginalProb J j
  · exact cond_prob_bounds J i j positive
  · have zero : marginalProb J j = 0 :=
      le_antisymm (le_of_not_gt positive) (marginal_prob_bounds J j).1
    simp [condProb, zero]

/-! ## Part 6: When Fast PLN Equals Complete PLN

The fast PLN formulas are EXACT when independence assumptions hold.
-/

/-- Independence condition: P(C|A,B) = P(C|B) -/
def hasPositiveIndependence (J : JointDistribution n) (a b c : Fin n) : Prop :=
  condProb2 J c a b = condProb J c b

/-- Independence condition: P(C|A,¬B) = P(C|¬B) -/
def hasNegativeIndependence (J : JointDistribution n) (a b c : Fin n) : Prop :=
  condProb2Neg J c a b = condProbNeg J c b

/-- A finite event mass is nonnegative. -/
theorem event_mass_nonneg (J : JointDistribution n) (event : Fin (2 ^ n) → Prop)
    [DecidablePred event] : 0 ≤ ∑ world, if event world then J.prob world else 0 := by
  exact Finset.sum_nonneg fun world _ => by split_ifs <;> simp_all [J.prob_nonneg]

/-- Event inclusion bounds finite event masses. -/
theorem event_mass_mono (J : JointDistribution n) (first second : Fin (2 ^ n) → Prop)
    [DecidablePred first] [DecidablePred second] (included : ∀ world, first world → second world) :
    (∑ world, if first world then J.prob world else 0) ≤
      ∑ world, if second world then J.prob world else 0 := by
  apply Finset.sum_le_sum
  intro world _
  by_cases left : first world
  · simp [left, included world left]
  · simp only [left, if_false]
    split_ifs <;> simp_all [J.prob_nonneg]

/-- A nonnegative submass divided by its carrier mass is in the unit interval,
including the zero-carrier convention of the existing query API. -/
theorem ratio_mem_unit {numerator denominator : ℝ}
    (nonnegative : 0 ≤ numerator) (bounded : numerator ≤ denominator) :
    numerator / denominator ∈ Set.Icc (0 : ℝ) 1 := by
  have den0 : 0 ≤ denominator := nonnegative.trans bounded
  by_cases zero : denominator = 0
  · simp [zero]
  · have positive : 0 < denominator := lt_of_le_of_ne den0 (Ne.symm zero)
    exact ⟨div_nonneg nonnegative den0, (div_le_one positive).mpr bounded⟩

theorem jointProb2_comm (J : JointDistribution n) (a b : Fin n) :
    jointProb2 J a b = jointProb2 J b a := by simp [jointProb2, and_comm]

/-- Reconstruct the joint mass from a conditional readout, including an empty
conditioning event. This does not assert that conditioning on it is defined. -/
theorem marginal_mul_condProb (J : JointDistribution n) (i j : Fin n) :
    marginalProb J j * condProb J i j = jointProb2 J j i := by
  rw [jointProb2_comm J j i]
  by_cases empty : marginalProb J j = 0
  · have nonnegative : 0 ≤ jointProb2 J i j := event_mass_nonneg J _
    have bounded : jointProb2 J i j ≤ marginalProb J j :=
      event_mass_mono J _ _ (fun _ h => h.2)
    have zero : jointProb2 J i j = 0 := by linarith
    simp [condProb, empty, zero]
  · simp only [condProb, empty, if_false]
    field_simp

theorem marginalProbNeg_eq_one_sub (J : JointDistribution n) (b : Fin n) :
    marginalProbNeg J b = 1 - marginalProb J b := by
  have complement := Mettapedia.ProbabilityTheory.FiniteEventMass.complement J.prob
    (worldToAssignment n · b)
  simpa [Mettapedia.ProbabilityTheory.FiniteEventMass.mass,
    marginalProb, marginalProbNeg, J.prob_sum_one] using complement

theorem marginal_partition (J : JointDistribution n) (a b : Fin n) :
    marginalProb J a = jointProb2 J a b + jointProb2Neg J a b := by
  unfold marginalProb jointProb2 jointProb2Neg
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro world _
  cases worldToAssignment n world a <;> cases worldToAssignment n world b <;> simp

/-- The complement-branch reference conditional is recoverable from the
ordinary deduction readouts. At a zero complement mass both conventions give
zero, so the algebraic identity still holds. -/
theorem condProbNeg_from_readouts (J : JointDistribution n) (c b : Fin n) :
    condProbNeg J c b =
      (marginalProb J c - marginalProb J b * condProb J c b) / (1 - marginalProb J b) := by
  rw [marginal_mul_condProb]
  have split := marginal_partition J c b
  rw [jointProb2_comm J c b] at split
  have numerator : marginalProb J c - jointProb2 J b c = jointProb2Neg J c b := by linarith
  rw [numerator, ← marginalProbNeg_eq_one_sub]
  unfold condProbNeg
  dsimp only
  split_ifs with empty
  · simp [empty]
  · simp only [jointProb2Neg, and_comm]

theorem joint_partition (J : JointDistribution n) (a b c : Fin n) :
    jointProb2 J a c = jointProb3 J a b c + jointProb3Neg J a b c := by
  unfold jointProb2 jointProb3 jointProb3Neg
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro world _
  cases worldToAssignment n world a <;> cases worldToAssignment n world b <;>
    cases worldToAssignment n world c <;> simp

theorem jointProb3_nonneg (J : JointDistribution n) (a b c : Fin n) :
    0 ≤ jointProb3 J a b c := event_mass_nonneg J _

theorem jointProb3_le_jointProb2 (J : JointDistribution n) (a b c : Fin n) :
    jointProb3 J a b c ≤ jointProb2 J a b :=
  event_mass_mono J _ _ (fun _ holds => ⟨holds.1, holds.2.1⟩)

theorem jointProb3Neg_nonneg (J : JointDistribution n) (a b c : Fin n) :
    0 ≤ jointProb3Neg J a b c := event_mass_nonneg J _

theorem jointProb3Neg_le_jointProb2Neg (J : JointDistribution n) (a b c : Fin n) :
    jointProb3Neg J a b c ≤ jointProb2Neg J a b :=
  event_mass_mono J _ _ (fun _ holds => ⟨holds.1, holds.2.1⟩)

/-- Multiplying by the branch mass remains valid for a zero-probability branch. -/
theorem condProb2_mul_joint (J : JointDistribution n) (a b c : Fin n) :
    condProb2 J c a b * jointProb2 J a b = jointProb3 J a b c := by
  by_cases zero : jointProb2 J a b = 0
  · have numerator : jointProb3 J a b c = 0 := by
      have bounded := jointProb3_le_jointProb2 J a b c
      rw [zero] at bounded
      exact le_antisymm bounded (jointProb3_nonneg J a b c)
    simp [condProb2, zero, numerator]
  · simp [condProb2, zero]

theorem condProb2Neg_mul_joint (J : JointDistribution n) (a b c : Fin n) :
    condProb2Neg J c a b * jointProb2Neg J a b = jointProb3Neg J a b c := by
  by_cases zero : jointProb2Neg J a b = 0
  · have numerator : jointProb3Neg J a b c = 0 := by
      have bounded := jointProb3Neg_le_jointProb2Neg J a b c
      rw [zero] at bounded
      exact le_antisymm bounded (jointProb3Neg_nonneg J a b c)
    simp [condProb2Neg, zero, numerator]
  · simp [condProb2Neg, zero]

theorem condProb2_mem_unit (J : JointDistribution n) (a b c : Fin n) :
    condProb2 J c a b ∈ Set.Icc (0 : ℝ) 1 := by
  unfold condProb2
  dsimp only
  split_ifs with zero
  · simp
  · exact ratio_mem_unit (jointProb3_nonneg J a b c) (jointProb3_le_jointProb2 J a b c)

theorem condProb2Neg_mem_unit (J : JointDistribution n) (a b c : Fin n) :
    condProb2Neg J c a b ∈ Set.Icc (0 : ℝ) 1 := by
  unfold condProb2Neg
  dsimp only
  split_ifs with zero
  · simp
  · exact ratio_mem_unit (jointProb3Neg_nonneg J a b c) (jointProb3Neg_le_jointProb2Neg J a b c)

/-- Total probability for a conditional query. Only the query's conditioning
mass must be nonzero; either internal branch may be empty. -/
theorem conditional_total_probability (J : JointDistribution n) (a b c : Fin n)
    (possible : marginalProb J a ≠ 0) :
    condProb J c a = condProb J b a * condProb2 J c a b +
      (1 - condProb J b a) * condProb2Neg J c a b := by
  have positiveBranch := condProb2_mul_joint J a b c
  have negativeBranch := condProb2Neg_mul_joint J a b c
  have split := marginal_partition J a b
  have joint := joint_partition J a b c
  simp only [condProb, possible, if_false]
  rw [jointProb2_comm J c a, jointProb2_comm J b a, joint]
  have complement : 1 - jointProb2 J a b / marginalProb J a =
      jointProb2Neg J a b / marginalProb J a := by
    field_simp
    linarith
  rw [complement]
  field_simp
  nlinarith [positiveBranch, negativeBranch]

/-- The branch-screening approximation expressed using the two actual branch
reference conditionals. -/
noncomputable def screeningDeduction (J : JointDistribution n) (a b c : Fin n) : ℝ :=
  condProb J b a * condProb J c b + (1 - condProb J b a) * condProbNeg J c b

/-- On coherent model readouts the branch formulation is exactly the existing
PLN deduction formula. This connects the error analysis to that actual API. -/
theorem screeningDeduction_eq_plnDeductionStrength (J : JointDistribution n) (a b c : Fin n) :
    screeningDeduction J a b c =
      plnDeductionStrength (condProb J b a) (condProb J c b)
        (marginalProb J b) (marginalProb J c) := by
  simp only [screeningDeduction, condProbNeg_from_readouts, plnDeductionStrength, mul_div_assoc]

/-- Both branch-screening equalities make the approximate query exact.
This theorem compares two independently defined computations. -/
theorem fast_equals_complete_under_independence
    (J : JointDistribution n) (a b c : Fin n)
    (h_pos : hasPositiveIndependence J a b c)
    (h_neg : hasNegativeIndependence J a b c)
    (h_marg_a : 0 < marginalProb J a) :
    plnDeductionStrength (condProb J b a) (condProb J c b)
      (marginalProb J b) (marginalProb J c) = completeDeduction J a b c := by
  rw [← screeningDeduction_eq_plnDeductionStrength]
  unfold screeningDeduction completeDeduction
  rw [conditional_total_probability J a b c h_marg_a.ne', h_pos, h_neg]

/-! ## Part 7: Practical API for AGI Systems

Simple functions that an AGI can call directly.
-/

/-- Quick check: should we use complete mode? -/
def shouldUseCompleteMode (ctx : InferenceContext) : Bool :=
  ctx.is_critical || (!ctx.independence_likely && ctx.has_joint && ctx.num_props ≤ 10)

/-- Estimate computational cost of complete mode -/
def estimateCompleteCost (num_props : ℕ) : ℕ :=
  2^num_props  -- O(2^n) worlds to consider

/-- Check if complete mode is tractable -/
def isCompleteTractable (num_props : ℕ) (max_cost : ℕ := 10000) : Bool :=
  estimateCompleteCost num_props ≤ max_cost

/-- Recommendation for an AGI system -/
structure ModeRecommendation where
  recommended_mode : InferenceMode
  reason : String
  estimated_cost : ℕ
  expected_accuracy : ℝ

/-- Get recommendation for which mode to use -/
def getRecommendation (ctx : InferenceContext) : ModeRecommendation :=
  if ctx.is_critical && isCompleteTractable ctx.num_props then
    { recommended_mode := InferenceMode.complete
      reason := "Critical decision with tractable joint distribution"
      estimated_cost := estimateCompleteCost ctx.num_props
      expected_accuracy := 1.0 }
  else if !ctx.independence_likely && ctx.has_joint && isCompleteTractable ctx.num_props then
    { recommended_mode := InferenceMode.complete
      reason := "Independence unlikely but joint available"
      estimated_cost := estimateCompleteCost ctx.num_props
      expected_accuracy := 1.0 }
  else if ctx.independence_likely then
    { recommended_mode := InferenceMode.fast
      reason := "Independence likely - fast mode appropriate"
      estimated_cost := 1
      expected_accuracy := 0.9 }
  else
    { recommended_mode := InferenceMode.fast
      reason := "Complete mode intractable, using fast approximation"
      estimated_cost := 1
      expected_accuracy := 0.7 }

/-! ## Summary

This file provides:

1. **JointDistribution**: Full joint probability tracking for exact inference

2. **Complete Inference Rules**:
   - `completeDeduction`: Exact P(C|A) from joint
   - `completeInduction`: Exact P(C|A) from joint
   - `completeAbduction`: Exact P(C|A) from joint

3. **Hybrid System**:
   - `InferenceMode`: fast | complete | adaptive
   - `hybridDeduction`: Unified API that dispatches appropriately
   - `InferenceResult`: Result with provenance and an uncalibrated dispatcher score

4. **Mode Selection**:
   - `selectMode`: Automatic mode selection based on context
   - `shouldUseCompleteMode`: Quick check
   - `getRecommendation`: Full recommendation with reasoning

5. **Correctness Theorems**:
   - `complete_deduction_exact`: Complete mode gives true probability
   - `fast_equals_complete_under_independence`: Fast = Complete when assumptions hold

## Usage Example for AGI

```
-- AGI receives inference request
let ctx := { num_props := 5, is_critical := true, has_joint := true,
             independence_likely := false, time_budget := 100 }

-- Get recommendation
let rec := getRecommendation ctx
-- rec.recommended_mode = complete
-- rec.reason = "Critical decision with tractable joint distribution"

-- Perform inference with appropriate mode
let result := hybridDeduction rec.recommended_mode fast_inputs complete_inputs ctx
-- result.strength = exact P(C|A)
-- result.heuristicScore = 1.0
-- result.assumed_independence = false
```

The AGI can seamlessly switch between modes based on:
- Criticality of the decision
- Availability of joint distribution
- Validity of independence assumptions
- Computational budget
-/

end Mettapedia.PLN.Core.CompletePLN
