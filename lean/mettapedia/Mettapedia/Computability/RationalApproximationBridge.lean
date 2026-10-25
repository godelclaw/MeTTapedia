import Mettapedia.Analysis.RationalApproximation
import Mettapedia.Computability.HutterComputabilityRational

/-!
# Effective producers and asynchronous interval refinement

Hutter's interface uses computable natural numerators with denominator `2^n`.
Forgetting that computability certificate gives analytic rational stages. A
converse requires a matching computable producer, including its nonnegative
dyadic profile; signed analytic data alone cannot provide one.

The refinement machine retains separate lower and upper stage counters. Its
interval observation is sound and nested along every execution. Width tends to
zero when both counters advance cofinally. Commuting updates have the same final
state without identifying their intermediate observations or event histories.
-/

namespace Mettapedia.Computability.RationalApproximationBridge

open Mettapedia.Analysis Filter Topology

noncomputable section

/-- The actual rational stage associated with Hutter's natural dyadic producer. -/
def dyadicRat (a n : ℕ) : ℚ := (a : ℚ) / (2 : ℚ) ^ n

@[simp] theorem cast_dyadicRat (a n : ℕ) :
    (dyadicRat a n : ℝ) = Hutter.dyadic a n := by
  simp [dyadicRat, Hutter.dyadic]

variable {α : Type*} {f : α → ℝ}

/-- Forget effectivity while retaining precisely the supplied dyadic stages. -/
noncomputable def lowerOfDyadic (a : α → ℕ → ℕ)
    (hm : ∀ x, Monotone (fun n => Hutter.dyadic (a x n) n))
    (ht : ∀ x, Tendsto (fun n => Hutter.dyadic (a x n) n) atTop (𝓝 (f x))) :
    LowerApproximation f where
  approx x n := dyadicRat (a x n) n
  monotone x m n h := (Rat.cast_le (K := ℝ)).1 (by simpa using hm x h)
  tendsto x := by simpa using ht x

noncomputable def upperOfDyadic (a : α → ℕ → ℕ)
    (hm : ∀ x, Antitone (fun n => Hutter.dyadic (a x n) n))
    (ht : ∀ x, Tendsto (fun n => Hutter.dyadic (a x n) n) atTop (𝓝 (f x))) :
    UpperApproximation f where
  approx x n := dyadicRat (a x n) n
  monotone x m n h := (Rat.cast_le (K := ℝ)).1 (by simpa using hm x h)
  tendsto x := by
    change Tendsto (fun n => (dyadicRat (a x n) n : ℝ)) atTop (𝓝 (f x))
    simpa using ht x

theorem lower_forget [Primcodable α] (hf : Hutter.LowerSemicomputable f) :
    Nonempty (LowerApproximation f) := by
  obtain ⟨a, _, hm, ht⟩ := hf
  exact ⟨lowerOfDyadic a hm ht⟩

theorem upper_forget [Primcodable α] (hf : Hutter.UpperSemicomputable f) :
    Nonempty (UpperApproximation f) := by
  obtain ⟨a, _, hm, ht⟩ := hf
  exact ⟨upperOfDyadic a hm ht⟩

/-- Recover an effective claim only from a computable producer matching every stage. -/
theorem lower_effective_of_matching [Primcodable α] (hf : LowerApproximation f)
    (a : α → ℕ → ℕ) (ha : Computable₂ a)
    (heq : ∀ x n, hf.approx x n = dyadicRat (a x n) n) :
    Hutter.LowerSemicomputable f := by
  refine ⟨a, ha, ?_, ?_⟩
  · intro x m n h
    simpa only [← cast_dyadicRat, ← heq] using Rat.cast_le.2 (hf.monotone x h)
  · intro x
    simpa only [rational_interpret, heq, cast_dyadicRat] using hf.tendsto x

theorem upper_effective_of_matching [Primcodable α] (hf : UpperApproximation f)
    (a : α → ℕ → ℕ) (ha : Computable₂ a)
    (heq : ∀ x n, hf.approx x n = dyadicRat (a x n) n) :
    Hutter.UpperSemicomputable f := by
  refine ⟨a, ha, ?_, ?_⟩
  · intro x m n h
    simpa only [← cast_dyadicRat, ← heq] using Rat.cast_le.2 (hf.antitone x h)
  · intro x
    simpa only [heq, cast_dyadicRat] using hf.converges x

/-- Natural dyadic producers cannot converge to a negative target. -/
theorem hutter_approximable_nonneg [Primcodable α] (hf : Hutter.Approximable f) (x : α) :
    0 ≤ f x := by
  obtain ⟨a, _, ht⟩ := hf
  exact ge_of_tendsto' (ht x) (fun n => by unfold Hutter.dyadic; positivity)

/-- This boundary applies even though the signed constant has an exact analytic approximation. -/
theorem negative_one_not_hutter : ¬Hutter.Approximable (fun _ : ℕ => (-1 : ℝ)) := by
  intro h
  have := hutter_approximable_nonneg h 0
  norm_num at this

/-- Counters are operational state, distinct from the observed interval. -/
@[ext] structure Stages where
  lower : ℕ
  upper : ℕ
  deriving DecidableEq, Repr

inductive Direction where
  | lower
  | upper
  deriving DecidableEq, Repr

def advance : Direction → Stages → Stages
  | .lower, s => { s with lower := s.lower + 1 }
  | .upper, s => { s with upper := s.upper + 1 }

/-- An ordered execution retains every supplied event occurrence. -/
def execute (events : List Direction) (initial : Stages) : Stages :=
  events.foldl (fun s event => advance event s) initial

theorem execute_append (xs ys : List Direction) (s : Stages) :
    execute (xs ++ ys) s = execute ys (execute xs s) := List.foldl_append

theorem advance_commute (s : Stages) :
    advance .upper (advance .lower s) = advance .lower (advance .upper s) := rfl

/-- The event orders remain distinct, even when their final states agree. -/
theorem update_histories_distinct :
    ([Direction.lower, .upper] : List Direction) ≠ [.upper, .lower] := by decide

variable (lo : LowerApproximation f) (hi : UpperApproximation f)

def observe (x : α) (s : Stages) : ℚ × ℚ :=
  (lo.approx x s.lower, hi.approx x s.upper)

def interval (x : α) (s : Stages) : Set ℝ :=
  Set.Icc (lo.approx x s.lower : ℝ) (hi.approx x s.upper : ℝ)

def width (x : α) (s : Stages) : ℝ :=
  (hi.approx x s.upper : ℝ) - (lo.approx x s.lower : ℝ)

theorem interval_sound (x : α) (s : Stages) : f x ∈ interval lo hi x s :=
  ⟨lo.approx_le x s.lower, hi.approx_ge x s.upper⟩

theorem interval_nested (x : α) (s t : Stages) (hl : s.lower ≤ t.lower)
    (hu : s.upper ≤ t.upper) : interval lo hi x t ⊆ interval lo hi x s :=
  Set.Icc_subset_Icc (Rat.cast_le.2 (lo.monotone x hl))
    (Rat.cast_le.2 (hi.antitone x hu))

theorem advance_nested (x : α) (event : Direction) (s : Stages) :
    interval lo hi x (advance event s) ⊆ interval lo hi x s := by
  cases event <;> exact interval_nested lo hi x _ _ (by simp [advance]) (by simp [advance])

theorem execute_nested (x : α) (events : List Direction) (s : Stages) :
    interval lo hi x (execute events s) ⊆ interval lo hi x s := by
  induction events generalizing s with
  | nil => exact Set.Subset.rfl
  | cons event events ih =>
      exact (ih (advance event s)).trans (advance_nested lo hi x event s)

theorem width_nonneg (x : α) (s : Stages) : 0 ≤ width lo hi x s :=
  sub_nonneg.2 ((lo.approx_le x s.lower).trans (hi.approx_ge x s.upper))

theorem width_antitone (x : α) (s t : Stages) (hl : s.lower ≤ t.lower)
    (hu : s.upper ≤ t.upper) : width lo hi x t ≤ width lo hi x s :=
  sub_le_sub (Rat.cast_le.2 (hi.antitone x hu)) (Rat.cast_le.2 (lo.monotone x hl))

/-- The convergence theorem observes any cofinal counter path, including asynchronous ones. -/
theorem width_tendsto_zero (x : α) (path : ℕ → Stages)
    (hl : Tendsto (fun n => (path n).lower) atTop atTop)
    (hu : Tendsto (fun n => (path n).upper) atTop atTop) :
    Tendsto (fun n => width lo hi x (path n)) atTop (𝓝 0) := by
  simpa [width] using ((hi.converges x).comp hu).sub ((lo.tendsto x).comp hl)

/-- Execution driven by an infinite event schedule. -/
def trajectory (schedule : ℕ → Direction) (initial : Stages) : ℕ → Stages
  | 0 => initial
  | n + 1 => advance (schedule n) (trajectory schedule initial n)

theorem trajectory_sound (x : α) (schedule : ℕ → Direction) (initial : Stages) (n : ℕ) :
    f x ∈ interval lo hi x (trajectory schedule initial n) := interval_sound lo hi x _

theorem trajectory_nested (x : α) (schedule : ℕ → Direction) (initial : Stages) (n : ℕ) :
    interval lo hi x (trajectory schedule initial (n + 1)) ⊆
      interval lo hi x (trajectory schedule initial n) :=
  advance_nested lo hi x (schedule n) _

/-- Infinite executions and finite event histories agree at every finite stage. -/
theorem trajectory_eq_execute (schedule : ℕ → Direction) (initial : Stages) (n : ℕ) :
    trajectory schedule initial n =
      execute ((List.range n).map schedule) initial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [trajectory, ih, List.range_succ, execute, List.foldl_append]

/-- A concrete fair scheduler; fairness is progress of counters, not a speed bound. -/
def alternating (n : ℕ) : Direction := if n % 2 = 0 then .lower else .upper

theorem alternating_counters (n : ℕ) :
    trajectory alternating ⟨0, 0⟩ n = ⟨(n + 1) / 2, n / 2⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [trajectory, ih, alternating]
      split_ifs with h <;> ext <;> simp only [advance] <;> omega

theorem alternating_lower_cofinal :
    Tendsto (fun n => (trajectory alternating ⟨0, 0⟩ n).lower) atTop atTop := by
  refine tendsto_atTop.2 (fun b => eventually_atTop.2 ⟨2 * b, fun n hn => ?_⟩)
  rw [alternating_counters]
  dsimp
  omega

theorem alternating_upper_cofinal :
    Tendsto (fun n => (trajectory alternating ⟨0, 0⟩ n).upper) atTop atTop := by
  refine tendsto_atTop.2 (fun b => eventually_atTop.2 ⟨2 * b, fun n hn => ?_⟩)
  rw [alternating_counters]
  dsimp
  omega

theorem alternating_width_tendsto_zero (x : α) :
    Tendsto (fun n => width lo hi x (trajectory alternating ⟨0, 0⟩ n)) atTop (𝓝 0) :=
  width_tendsto_zero lo hi x _ alternating_lower_cofinal alternating_upper_cofinal

/-! ## Separating examples -/

/-- The input domain is unbounded, although each stage is already exact. -/
noncomputable def naturalExact : LowerApproximation (fun n : ℕ => (n : ℝ)) where
  approx n _ := n
  monotone _ := monotone_const
  tendsto _ := by simp

/-- Positive effective control, using the existing computable floor-dyadic construction. -/
theorem natural_effective : Hutter.LowerSemicomputable (fun n : ℕ => (n : ℝ)) := by
  simpa using Hutter.LowerSemicomputable.of_natRatio
    (fun n : ℕ => n) (fun _ => 1) Computable.id (Computable.const 1) (fun _ => Nat.zero_lt_one)

theorem naturals_no_uniform_bound : ¬∃ M : ℝ, ∀ n : ℕ, (n : ℝ) ≤ M := by
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := exists_nat_gt M
  exact (not_lt_of_ge (hM n)) hn

/-- Multiplication applies without any uniform bound over the input domain. -/
theorem unbounded_product_stages (x n : ℕ) :
    ((naturalExact.mul naturalExact (fun k => Nat.cast_nonneg k)
      (fun k => Nat.cast_nonneg k)).approx x n : ℝ) = (x : ℝ) ^ 2 := by
  simp [LowerApproximation.mul, naturalExact, sq]

/-- Negative initial stages converging to a nonnegative target. -/
noncomputable def initiallyNegative : LowerApproximation (fun _ : Unit => (0 : ℝ)) :=
  LowerApproximation.of_bounds (fun _ n => if n = 0 then -1 else 0)
    (by intro _ n; cases n <;> norm_num)
    (by intro _ n; split_ifs <;> norm_num)
    (by
      intro _ ε hε
      refine ⟨1, fun n hn => ?_⟩
      have : n ≠ 0 := by omega
      simpa [this] using hε)

theorem unclipped_product_exceeds_target :
    (initiallyNegative.approx () 0 : ℝ) * (initiallyNegative.approx () 0 : ℝ) > 0 := by
  norm_num [initiallyNegative, LowerApproximation.of_bounds]

theorem clipped_product_preserves_target :
    ((initiallyNegative.mul initiallyNegative (fun _ => le_rfl)
      (fun _ => le_rfl)).approx () 0 : ℝ) = 0 := by
  norm_num [LowerApproximation.mul, initiallyNegative, LowerApproximation.of_bounds]

theorem signed_exact_analytic : Nonempty (LowerApproximation (fun _ : ℕ => (-1 : ℝ))) :=
  ⟨by simpa using (LowerApproximation.const_rat (α := ℕ) (-1))⟩

/-- Two nontrivial endpoint sequences around the same target. -/
noncomputable def unitLower : LowerApproximation (fun _ : Unit => (1 : ℝ)) where
  approx _ n := 1 - 1 / (n + 1 : ℚ)
  monotone _ _ _ h := sub_le_sub_left
    (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)) 1
  tendsto _ := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

noncomputable def unitUpper : UpperApproximation (fun _ : Unit => (1 : ℝ)) where
  approx _ n := (1 + 1 / (n + 1 : ℚ) : ℚ)
  monotone _ m n h := by
    change (1 + 1 / (n + 1 : ℚ) : ℚ) ≤ 1 + 1 / (m + 1 : ℚ)
    simpa only [add_comm] using add_le_add_left
      (one_div_le_one_div_of_le (a := (m + 1 : ℚ)) (b := (n + 1 : ℚ))
        (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)) 1
  tendsto _ := by
    change Tendsto (fun n : ℕ => ((1 + 1 / (n + 1 : ℚ) : ℚ) : ℝ)) atTop (𝓝 1)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem commuting_updates_distinct_midpoints :
    observe unitLower unitUpper () (advance .lower ⟨0, 0⟩) = ((1 / 2 : ℚ), 2) ∧
    observe unitLower unitUpper () (advance .upper ⟨0, 0⟩) = ((0 : ℚ), 3 / 2) ∧
    observe unitLower unitUpper () (advance .lower ⟨0, 0⟩) ≠
      observe unitLower unitUpper () (advance .upper ⟨0, 0⟩) := by
  norm_num [observe, advance, unitLower, unitUpper, UpperApproximation.approx,
    OrderDual.ofDual, Equiv.refl]
  exact ⟨rfl, rfl⟩

theorem starvation_counters (n : ℕ) :
    trajectory (fun _ => .lower) ⟨0, 0⟩ n = ⟨n, 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simp [trajectory, ih, advance]

theorem starvation_width (n : ℕ) :
    width unitLower unitUpper () (trajectory (fun _ => .lower) ⟨0, 0⟩ n) =
      1 + 1 / (n + 1 : ℝ) := by
  rw [starvation_counters]
  change (((1 + 1 / (0 + 1 : ℚ) : ℚ) : ℝ) -
    ((1 - 1 / (n + 1 : ℚ) : ℚ) : ℝ)) = 1 + 1 / (n + 1 : ℝ)
  push_cast
  norm_num
  ring

theorem starvation_width_tendsto_one :
    Tendsto (fun n => width unitLower unitUpper ()
      (trajectory (fun _ => .lower) ⟨0, 0⟩ n)) atTop (𝓝 1) := by
  simp_rw [starvation_width]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem starvation_width_not_zero :
    ¬Tendsto (fun n => width unitLower unitUpper ()
      (trajectory (fun _ => .lower) ⟨0, 0⟩ n)) atTop (𝓝 0) := by
  intro h
  have hbad : (1 : ℝ) = 0 := tendsto_nhds_unique starvation_width_tendsto_one h
  norm_num at hbad

end

end Mettapedia.Computability.RationalApproximationBridge
