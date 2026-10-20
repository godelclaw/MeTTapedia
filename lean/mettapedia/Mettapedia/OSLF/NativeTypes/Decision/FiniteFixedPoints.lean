import Mettapedia.Order.FiniteSetFixedPoints
import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

/-!
# A finite execution strategy for semantic fixed points

The input operator is independently monotone on sets. A computable finite-set
step must realize that operator, rather than choosing the meaning of a formula.
Lower approximations can justify least-fixed-point membership early; upper
approximations can justify greatest-fixed-point nonmembership early. Opposite
answers require the finite-carrier bound. These are internal strategy results,
not a formula language or a completeness claim for an open explored universe.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.FiniteFixedPoints

open Mettapedia.Order.FiniteSetFixedPoints
open Reference.Core

universe u
variable {α : Type u}

/-- A finite-set implementation of an independently given monotone operator. -/
structure Strategy (semantic : Set α →o Set α) where
  step : Finset α → Finset α
  step_correct : ∀ states, (↑(step states) : Set α) = semantic (↑states : Set α)

namespace Strategy

variable {semantic : Set α →o Set α} (strategy : Strategy semantic)

def iterate (budget : Nat) (states : Finset α) : Finset α :=
  strategy.step^[budget] states

def lower (budget : Nat) : Finset α := strategy.iterate budget ∅

def upper [Fintype α] (budget : Nat) : Finset α := strategy.iterate budget Finset.univ

theorem iterate_correct (budget : Nat) (states : Finset α) :
    (↑(strategy.iterate budget states) : Set α) =
      (semantic : Set α → Set α)^[budget] (↑states : Set α) := by
  induction budget with
  | zero => rfl
  | succ budget ih =>
      simpa only [iterate, Function.iterate_succ_apply', strategy.step_correct] using
        congrArg semantic ih

theorem lower_correct (budget : Nat) :
    (↑(strategy.lower budget) : Set α) = lowerApproximation semantic budget := by
  simpa [lower, lowerApproximation] using strategy.iterate_correct budget ∅

theorem upper_correct [Fintype α] (budget : Nat) :
    (↑(strategy.upper budget) : Set α) = upperApproximation semantic budget := by
  simpa [upper, upperApproximation] using strategy.iterate_correct budget Finset.univ

theorem lower_le_lfp (budget : Nat) :
    (↑(strategy.lower budget) : Set α) ⊆ semantic.lfp := by
  rw [strategy.lower_correct]
  exact lowerApproximation_le_lfp semantic budget

theorem gfp_le_upper [Fintype α] (budget : Nat) :
    semantic.gfp ⊆ (↑(strategy.upper budget) : Set α) := by
  rw [strategy.upper_correct]
  exact gfp_le_upperApproximation semantic budget

variable [Fintype α]

theorem lower_at_card :
    (↑(strategy.lower (Fintype.card α)) : Set α) = semantic.lfp := by
  rw [strategy.lower_correct]
  simpa [lowerApproximation, Nat.card_eq_fintype_card] using
    (lfp_eq_iterate_empty semantic).symm

theorem upper_at_card :
    (↑(strategy.upper (Fintype.card α)) : Set α) = semantic.gfp := by
  rw [strategy.upper_correct]
  simpa [upperApproximation, Nat.card_eq_fintype_card] using
    (gfp_eq_iterate_univ semantic).symm

theorem lower_exact (budget : Nat) (enough : Fintype.card α ≤ budget) :
    (↑(strategy.lower budget) : Set α) = semantic.lfp := by
  apply Set.Subset.antisymm (strategy.lower_le_lfp budget)
  rw [← strategy.lower_at_card, strategy.lower_correct, strategy.lower_correct]
  exact lowerApproximation_mono semantic enough

theorem upper_exact (budget : Nat) (enough : Fintype.card α ≤ budget) :
    (↑(strategy.upper budget) : Set α) = semantic.gfp := by
  apply Set.Subset.antisymm ?_ (strategy.gfp_le_upper budget)
  rw [← strategy.upper_at_card, strategy.upper_correct, strategy.upper_correct]
  exact upperApproximation_antitone semantic enough

/-- A positive least-fixed-point answer needs only an entering approximation.
Absence is conclusive once the finite carrier has been exhausted. -/
def least [DecidableEq α] (budget : Nat) (state : α) : Outcome (state ∈ semantic.lfp) :=
  if member : state ∈ strategy.lower budget then
    .proved (strategy.lower_le_lfp budget member)
  else if enough : Fintype.card α ≤ budget then
    .refuted (fun proof => member (by
      change state ∈ (↑(strategy.lower budget) : Set α)
      rw [strategy.lower_exact budget enough]
      exact proof))
  else .unknown

/-- A negative greatest-fixed-point answer needs only a departing
approximation. Retained membership is conclusive at the finite bound. -/
def greatest [DecidableEq α] (budget : Nat) (state : α) : Outcome (state ∈ semantic.gfp) :=
  if member : state ∈ strategy.upper budget then
    if enough : Fintype.card α ≤ budget then
      .proved (by
        change state ∈ (↑(strategy.upper budget) : Set α) at member
        rw [strategy.upper_exact budget enough] at member
        exact member)
    else .unknown
  else .refuted (fun proof => member (strategy.gfp_le_upper budget proof))

variable [DecidableEq α]

theorem least_decided (budget : Nat) (state : α) (enough : Fintype.card α ≤ budget) :
    (strategy.least budget state).Decided := by
  unfold least
  split
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

theorem greatest_decided (budget : Nat) (state : α) (enough : Fintype.card α ≤ budget) :
    (strategy.greatest budget state).Decided := by
  unfold greatest
  split
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

theorem least_unknown_iff (budget : Nat) (state : α) :
    (strategy.least budget state).answer = none ↔
      state ∉ strategy.lower budget ∧ budget < Fintype.card α := by
  unfold least
  split
  · simp_all [Outcome.answer]
  · split <;> simp_all [Outcome.answer]

theorem greatest_unknown_iff (budget : Nat) (state : α) :
    (strategy.greatest budget state).answer = none ↔
      state ∈ strategy.upper budget ∧ budget < Fintype.card α := by
  unfold greatest
  split
  · split <;> simp_all [Outcome.answer]
  · simp_all [Outcome.answer]

theorem least_positive_iff (budget : Nat) (state : α) (enough : Fintype.card α ≤ budget) :
    (strategy.least budget state).answer = some true ↔ state ∈ semantic.lfp := by
  constructor
  · exact Outcome.positive _
  · intro member
    have found : state ∈ strategy.lower budget := by
      change state ∈ (↑(strategy.lower budget) : Set α)
      rw [strategy.lower_exact budget enough]
      exact member
    simp [least, found, Outcome.answer]

theorem greatest_positive_iff (budget : Nat) (state : α) (enough : Fintype.card α ≤ budget) :
    (strategy.greatest budget state).answer = some true ↔ state ∈ semantic.gfp := by
  constructor
  · exact Outcome.positive _
  · intro member
    have found : state ∈ strategy.upper budget := strategy.gfp_le_upper budget member
    simp [greatest, found, enough, Outcome.answer]

theorem least_negative_iff (budget : Nat) (state : α) (enough : Fintype.card α ≤ budget) :
    (strategy.least budget state).answer = some false ↔ state ∉ semantic.lfp := by
  constructor
  · exact Outcome.negative _
  · intro absent
    have missing : state ∉ strategy.lower budget :=
      fun member => absent (strategy.lower_le_lfp budget member)
    simp [least, missing, enough, Outcome.answer]

theorem greatest_negative_iff (budget : Nat) (state : α) (enough : Fintype.card α ≤ budget) :
    (strategy.greatest budget state).answer = some false ↔ state ∉ semantic.gfp := by
  constructor
  · exact Outcome.negative _
  · intro absent
    have missing : state ∉ strategy.upper budget := by
      change state ∉ (↑(strategy.upper budget) : Set α)
      rw [strategy.upper_exact budget enough]
      exact absent
    simp [greatest, missing, Outcome.answer]

omit [Fintype α] [DecidableEq α] in
/-- Continuing an approximation reuses its current finite set. -/
theorem iterate_resume (first second : Nat) (states : Finset α) :
    strategy.iterate second (strategy.iterate first states) =
      strategy.iterate (first + second) states := by
  unfold iterate
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- The invariant identifies a saved approximation with its original seed.
An arbitrary externally supplied finite set does not establish this invariant. -/
structure Cursor (seed : Finset α) where
  rounds : Nat
  states : Finset α
  reached : states = strategy.iterate rounds seed

def begin (seed : Finset α) : strategy.Cursor seed := ⟨0, seed, rfl⟩

variable {strategy}

def Cursor.resume {seed : Finset α} (cursor : strategy.Cursor seed) (budget : Nat) :
    strategy.Cursor seed where
  rounds := cursor.rounds + budget
  states := strategy.iterate budget cursor.states
  reached := by rw [cursor.reached, strategy.iterate_resume]

omit [Fintype α] [DecidableEq α] in
theorem Cursor.resume_add {seed : Finset α} (cursor : strategy.Cursor seed) (first second : Nat) :
    (cursor.resume first).resume second = cursor.resume (first + second) := by
  cases cursor
  simp only [Cursor.resume, Nat.add_assoc, iterate_resume]

/-- Read a resumed least approximation without rebuilding it from the seed. -/
def Cursor.least (cursor : strategy.Cursor ∅) (state : α) : Outcome (state ∈ semantic.lfp) :=
  if member : state ∈ cursor.states then
    .proved (strategy.lower_le_lfp cursor.rounds (by simpa [cursor.reached, lower] using member))
  else if enough : Fintype.card α ≤ cursor.rounds then
    .refuted (fun proof => member (by
      rw [cursor.reached]
      change state ∈ (↑(strategy.lower cursor.rounds) : Set α)
      rw [strategy.lower_exact cursor.rounds enough]
      exact proof))
  else .unknown

/-- Read a resumed greatest approximation without rebuilding it from the seed. -/
def Cursor.greatest (cursor : strategy.Cursor Finset.univ) (state : α) : Outcome (state ∈ semantic.gfp) :=
  if member : state ∈ cursor.states then
    if enough : Fintype.card α ≤ cursor.rounds then
      .proved (by
        rw [cursor.reached] at member
        change state ∈ (↑(strategy.upper cursor.rounds) : Set α) at member
        rw [strategy.upper_exact cursor.rounds enough] at member
        exact member)
    else .unknown
  else .refuted (fun proof => member (by
    rw [cursor.reached]
    exact strategy.gfp_le_upper cursor.rounds proof))

theorem Cursor.least_eq (cursor : strategy.Cursor ∅) (state : α) :
    cursor.least state = strategy.least cursor.rounds state := by
  rcases cursor with ⟨rounds, states, reached⟩
  cases reached
  rfl

theorem Cursor.greatest_eq (cursor : strategy.Cursor Finset.univ) (state : α) :
    cursor.greatest state = strategy.greatest cursor.rounds state := by
  rcases cursor with ⟨rounds, states, reached⟩
  cases reached
  rfl

end Strategy

end Mettapedia.OSLF.NativeTypes.Decision.FiniteFixedPoints
