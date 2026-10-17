import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Infix
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Probability is nondeterminism resolved by a scheduler

Nondeterministic choice says that either branch may happen and gives no
weights; probabilistic choice says which branch happens how often.  A program
with both denotes a probability only once each choice is **resolved** by a
scheduler, which may itself flip a coin.  So the answer to "is probability the
view without choice?" is: probability is the view after a scheduler has been
fixed, and the honest view of a program with choice is the set of distributions
of all its resolutions, a credal set.

`Program X` has returns, nondeterministic choices and coins.  A `Scheduler`
gives, at each choice position, the probability of the left branch; `prob σ E`
is the probability of the event `E` under it.

* **Without choice there is one distribution** (`prob_choiceFree`): every
  scheduler gives the same probabilities.
* **The envelope is attained by deterministic schedulers**
  (`exists_deterministic_le`, `exists_deterministic_ge`): for every admissible
  scheduler there are deterministic ones giving no larger and no smaller
  probability.  Randomizing a choice never extends the envelope; it fills the
  convex set between its extreme points.  This is why convex sets of
  distributions are the right combination of the two effects (the convex
  powerset of Varacca and Winskel, and of Keimel and Plotkin's mixed
  powerdomains).
* **Pure choice between two outcomes is total ignorance**
  (`choice_probabilities`): the probabilities of the left outcome over all
  admissible schedulers are exactly `[0, 1]`, the vacuous credal set, which is
  also the interval readout of zero evidence
  (`Mettapedia.PLN.TruthValues.EvidenceHorizonInterval`, at no samples).
* **Counting is one scheduler among many** (`Controls.counting_not_fair`): the
  additive readout of `Mettapedia.CategoryTheory.NondeterminismProbability`
  counts each path once, and normalizing it agrees with the scheduler that
  weights choices by their numbers of paths, not with fair coins at each
  choice.

Evidence weighting differs from both: an evidence count records how often a
proposition was observed, a probability weights alternatives that sum to one,
and a nondeterministic choice carries no weight at all.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.SchedulerResolution

universe u

/-- Programs with nondeterministic and probabilistic choice. -/
inductive Program (X : Type u)
  | ret (x : X)
  | choose (left right : Program X)
  | coin (p : ℝ) (left right : Program X)

variable {X : Type u}

namespace Program

/-- Coins are probabilities. -/
def WellFormed : Program X → Prop
  | ret _ => True
  | choose left right => left.WellFormed ∧ right.WellFormed
  | coin p left right => 0 ≤ p ∧ p ≤ 1 ∧ left.WellFormed ∧ right.WellFormed

/-- No nondeterministic choice. -/
def ChoiceFree : Program X → Prop
  | ret _ => True
  | choose _ _ => False
  | coin _ left right => left.ChoiceFree ∧ right.ChoiceFree

end Program

open Program

/-- A scheduler: the probability of the left branch at each choice position.
Positions are paths from the root, most recent direction first. -/
abbrev Scheduler := List Bool → ℝ

/-- A scheduler gives probabilities. -/
def Admissible (σ : Scheduler) : Prop := ∀ position, 0 ≤ σ position ∧ σ position ≤ 1

/-- A scheduler that never flips a coin. -/
def Deterministic (σ : Scheduler) : Prop := ∀ position, σ position = 0 ∨ σ position = 1

/-- **The probability of an event** under a scheduler. -/
def prob (σ : Scheduler) (E : X → Prop) [DecidablePred E] : List Bool → Program X → ℝ
  | _, ret x => if E x then 1 else 0
  | position, choose left right =>
      σ position * prob σ E (false :: position) left +
        (1 - σ position) * prob σ E (true :: position) right
  | position, coin p left right =>
      p * prob σ E (false :: position) left + (1 - p) * prob σ E (true :: position) right

variable (E : X → Prop) [DecidablePred E]

/-- The probability depends only on the scheduler below the current position. -/
theorem prob_congr {σ τ : Scheduler} (program : Program X) (position : List Bool)
    (agree : ∀ q, position <:+ q → σ q = τ q) : prob σ E position program = prob τ E position program := by
  induction program generalizing position with
  | ret x => rfl
  | choose left right ihl ihr =>
      simp only [prob]
      rw [agree position (List.suffix_refl _),
        ihl (false :: position) fun q h => agree q ((List.suffix_cons _ _).trans h),
        ihr (true :: position) fun q h => agree q ((List.suffix_cons _ _).trans h)]
  | coin p left right ihl ihr =>
      simp only [prob]
      rw [ihl (false :: position) fun q h => agree q ((List.suffix_cons _ _).trans h),
        ihr (true :: position) fun q h => agree q ((List.suffix_cons _ _).trans h)]

/-- **Without choice there is one distribution.** -/
theorem prob_choiceFree (σ τ : Scheduler) (program : Program X) (free : program.ChoiceFree)
    (position : List Bool) : prob σ E position program = prob τ E position program := by
  induction program generalizing position with
  | ret x => rfl
  | choose left right _ _ => exact free.elim
  | coin p left right ihl ihr =>
      simp only [prob]
      rw [ihl free.1, ihr free.2]

theorem prob_nonneg_le_one {σ : Scheduler} (admissible : Admissible σ) (program : Program X)
    (wf : program.WellFormed) (position : List Bool) :
    0 ≤ prob σ E position program ∧ prob σ E position program ≤ 1 := by
  induction program generalizing position with
  | ret x =>
      simp only [prob]
      split_ifs <;> norm_num
  | choose left right ihl ihr =>
      obtain ⟨l0, l1⟩ := ihl wf.1 (false :: position)
      obtain ⟨r0, r1⟩ := ihr wf.2 (true :: position)
      obtain ⟨s0, s1⟩ := admissible position
      simp only [prob]
      constructor
      · have : 0 ≤ 1 - σ position := by linarith
        positivity
      · nlinarith
  | coin p left right ihl ihr =>
      obtain ⟨p0, p1, wl, wr⟩ := wf
      obtain ⟨l0, l1⟩ := ihl wl (false :: position)
      obtain ⟨r0, r1⟩ := ihr wr (true :: position)
      simp only [prob]
      constructor
      · have : 0 ≤ 1 - p := by linarith
        positivity
      · nlinarith

/-- Combine schedulers for the two subtrees with a decision at the current position. -/
def splice (position : List Bool) (bit : ℝ) (σl σr : Scheduler) : Scheduler := fun q =>
  if false :: position <:+ q then σl q else if true :: position <:+ q then σr q else bit

theorem splice_here (position : List Bool) (bit : ℝ) (σl σr : Scheduler) :
    splice position bit σl σr position = bit := by
  have notLeft : ¬ (false :: position <:+ position) := fun h => by
    have := h.length_le; simp at this
  have notRight : ¬ (true :: position <:+ position) := fun h => by
    have := h.length_le; simp at this
  simp [splice, notLeft, notRight]

theorem splice_left (position : List Bool) (bit : ℝ) (σl σr : Scheduler) (program : Program X) :
    prob (splice position bit σl σr) E (false :: position) program =
      prob σl E (false :: position) program :=
  prob_congr E program _ fun q h => by simp [splice, h]

theorem splice_right (position : List Bool) (bit : ℝ) (σl σr : Scheduler) (program : Program X) :
    prob (splice position bit σl σr) E (true :: position) program =
      prob σr E (true :: position) program := by
  refine prob_congr E program _ fun q h => ?_
  have notLeft : ¬ (false :: position <:+ q) := by
    intro h'
    rcases List.suffix_or_suffix_of_suffix h h' with s | s
    · have := s.length_le
      have := List.IsSuffix.eq_of_length s (by simp)
      simp at this
    · have := List.IsSuffix.eq_of_length s (by simp)
      simp at this
  simp [splice, notLeft, h]

theorem splice_deterministic {position : List Bool} {bit : ℝ} {σl σr : Scheduler}
    (hb : bit = 0 ∨ bit = 1) (hl : Deterministic σl) (hr : Deterministic σr) :
    Deterministic (splice position bit σl σr) := by
  intro q
  unfold splice
  split_ifs
  · exact hl q
  · exact hr q
  · exact hb

/-- **The lower envelope is attained by a deterministic scheduler.** -/
theorem exists_deterministic_le {σ : Scheduler} (admissible : Admissible σ) (program : Program X)
    (wf : program.WellFormed) (position : List Bool) :
    ∃ τ, Deterministic τ ∧ prob τ E position program ≤ prob σ E position program := by
  induction program generalizing position with
  | ret x => exact ⟨fun _ => 0, fun _ => Or.inl rfl, le_rfl⟩
  | choose left right ihl ihr =>
      obtain ⟨τl, dl, hl⟩ := ihl wf.1 (false :: position)
      obtain ⟨τr, dr, hr⟩ := ihr wf.2 (true :: position)
      set u := prob τl E (false :: position) left
      set v := prob τr E (true :: position) right
      refine ⟨splice position (if u ≤ v then 1 else 0) τl τr,
        splice_deterministic (by split_ifs <;> simp) dl dr, ?_⟩
      simp only [prob]
      rw [splice_here, splice_left, splice_right]
      obtain ⟨s0, s1⟩ := admissible position
      have bound : (if u ≤ v then (1 : ℝ) else 0) * u + (1 - if u ≤ v then (1 : ℝ) else 0) * v ≤
          σ position * u + (1 - σ position) * v := by
        split_ifs with h <;> nlinarith
      calc _ ≤ σ position * u + (1 - σ position) * v := bound
        _ ≤ _ := by
          have : 0 ≤ 1 - σ position := by linarith
          nlinarith
  | coin p left right ihl ihr =>
      obtain ⟨p0, p1, wl, wr⟩ := wf
      obtain ⟨τl, dl, hl⟩ := ihl wl (false :: position)
      obtain ⟨τr, dr, hr⟩ := ihr wr (true :: position)
      refine ⟨splice position 0 τl τr, splice_deterministic (Or.inl rfl) dl dr, ?_⟩
      simp only [prob]
      rw [splice_left, splice_right]
      have : 0 ≤ 1 - p := by linarith
      nlinarith

/-- **The upper envelope is attained by a deterministic scheduler.** -/
theorem exists_deterministic_ge {σ : Scheduler} (admissible : Admissible σ) (program : Program X)
    (wf : program.WellFormed) (position : List Bool) :
    ∃ τ, Deterministic τ ∧ prob σ E position program ≤ prob τ E position program := by
  induction program generalizing position with
  | ret x => exact ⟨fun _ => 0, fun _ => Or.inl rfl, le_rfl⟩
  | choose left right ihl ihr =>
      obtain ⟨τl, dl, hl⟩ := ihl wf.1 (false :: position)
      obtain ⟨τr, dr, hr⟩ := ihr wf.2 (true :: position)
      set u := prob τl E (false :: position) left
      set v := prob τr E (true :: position) right
      refine ⟨splice position (if v ≤ u then 1 else 0) τl τr,
        splice_deterministic (by split_ifs <;> simp) dl dr, ?_⟩
      simp only [prob]
      rw [splice_here, splice_left, splice_right]
      obtain ⟨s0, s1⟩ := admissible position
      have bound : σ position * u + (1 - σ position) * v ≤
          (if v ≤ u then (1 : ℝ) else 0) * u + (1 - if v ≤ u then (1 : ℝ) else 0) * v := by
        split_ifs with h <;> nlinarith
      calc _ ≤ σ position * u + (1 - σ position) * v := by
            have : 0 ≤ 1 - σ position := by linarith
            nlinarith
        _ ≤ _ := bound
  | coin p left right ihl ihr =>
      obtain ⟨p0, p1, wl, wr⟩ := wf
      obtain ⟨τl, dl, hl⟩ := ihl wl (false :: position)
      obtain ⟨τr, dr, hr⟩ := ihr wr (true :: position)
      refine ⟨splice position 0 τl τr, splice_deterministic (Or.inl rfl) dl dr, ?_⟩
      simp only [prob]
      rw [splice_left, splice_right]
      have : 0 ≤ 1 - p := by linarith
      nlinarith

/-- **Pure choice between two outcomes is total ignorance**: its probabilities
over all admissible schedulers are exactly `[0, 1]`. -/
theorem choice_probabilities :
    {r | ∃ σ, Admissible σ ∧ prob σ (· = true) [] (choose (ret true) (ret false)) = r} =
      Set.Icc 0 1 := by
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · rintro ⟨σ, admissible, rfl⟩
    exact prob_nonneg_le_one _ admissible (choose (ret true) (ret false))
      (show (choose (ret true) (ret false) : Program Bool).WellFormed from ⟨trivial, trivial⟩) []
  · rintro ⟨r0, r1⟩
    refine ⟨fun _ => r, fun _ => ⟨r0, r1⟩, ?_⟩
    simp [prob]

/-! ## Controls -/

namespace Controls

/-- A three-way choice built from two binary choices. -/
def threeWay : Program (Fin 3) := choose (ret 0) (choose (ret 1) (ret 2))

/-- The additive readout of an event: every path counted once. -/
def countMass (E : Fin 3 → Prop) [DecidablePred E] : Program (Fin 3) → ℝ
  | ret x => if E x then 1 else 0
  | choose left right => countMass E left + countMass E right
  | coin p left right => p * countMass E left + (1 - p) * countMass E right

/-- **Counting is one scheduler among many**: the normalized count gives the
first outcome `1/3`, fair coins give `1/2`, and the scheduler that weights each
choice by its numbers of paths gives `1/3`. -/
theorem counting_not_fair :
    countMass (· = 0) threeWay / countMass (fun _ => True) threeWay = 1 / 3 ∧
      prob (fun _ => 1 / 2) (· = 0) [] threeWay = 1 / 2 ∧
      prob (fun position => if position = [] then 1 / 3 else 1 / 2) (· = 0) [] threeWay = 1 / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [countMass, prob, threeWay] <;> decide

end Controls

end Mettapedia.CategoryTheory.SchedulerResolution
