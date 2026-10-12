import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Policies

/-!
# State cells as exclusive cells

The regions of this development are stated over any separation algebra of
values.  A state cell is the algebra of exclusive ownership
(`GSLT.SeparationAlgebra.Excl`): a cell is empty or owns one whole value, and two
owned values are never separate.  This module gives the write of a cell as a
step over that algebra and repeats on it the instances that `Regions.Policies`
gives with a cell modelled as a store holding one occurrence.

* `CellRules.write` replaces the value a cell owns; it fires exactly when the
  cell owns the old value (`CellRules.write_fires_iff`), and it is a step
  (`Step.writeCell`).
* `ExclusiveCell.write_fires` and `ExclusiveCell.write_refused`: a positive and
  a negative firing.
* `ExclusiveCell.two_writers_conflict`: two alternatives that write one cell are
  not independent; the wave policy reports the conflict and the cell keeps its
  value; the policy that publishes nothing is silent.
* `ExclusiveCell.counter_stays_under_publishNone` and
  `ExclusiveCell.counter_advances_under_publishWave`: the counter of two
  directives.
* `ExclusiveCell.committed_second_writer_stuck`: in the committed mode the second
  alternative finds the cell already written and has no answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.GSLT.SeparationAlgebra

universe u v

variable {Location : Type u} {Content : Type v} [DecidableEq Location]

/-- **The write of a cell**: the cell at `location` owns `old`, and afterwards it
owns `new`. -/
def CellRules.write (location : Location) (old new : Content) :
    LocalRule Location (Excl Content) :=
  LocalRule.unguarded (Pi.single location (.own old)) (Pi.single location (.own new)) {location}
    (fun other outside => by
      have different : other ≠ location := by simpa using outside
      simp [different])
    (fun other outside => by
      have different : other ≠ location := by simpa using outside
      simp [different])

/-- **The write fires exactly when the cell owns the old value**, and then the
cell owns the new value and every other cell is as it was. -/
theorem CellRules.write_fires_iff (location : Location) (old new : Content)
    (source target : Location → Excl Content) :
    (CellRules.write location old new).Fires source target ↔
      source location = .own old ∧ target = Function.update source location (.own new) := by
  constructor
  · rintro ⟨-, frame, consumedSeparate, -, rfl, rfl⟩
    have frameEmpty : frame location = .empty := by
      have separate := consumedSeparate location
      simp only [CellRules.write, LocalRule.unguarded, Pi.single_eq_same] at separate
      rcases separate with owned | empty
      · cases owned
      · exact empty
    constructor
    · show (Pi.single location (Excl.own old) : Location → Excl Content) location +
        frame location = .own old
      rw [Pi.single_eq_same]
      rfl
    · funext other
      by_cases same : other = location
      · subst same
        rw [Function.update_self]
        show (Pi.single other (Excl.own new) : Location → Excl Content) other + frame other =
          Excl.own new
        rw [Pi.single_eq_same]
        rfl
      · rw [Function.update_of_ne same]
        show (Pi.single location (Excl.own new) : Location → Excl Content) other + frame other =
          (Pi.single location (Excl.own old) : Location → Excl Content) other + frame other
        rw [Pi.single_eq_of_ne same, Pi.single_eq_of_ne same]
  · rintro ⟨owns, rfl⟩
    refine ⟨trivial, Function.update source location .empty, ?_, ?_, ?_, ?_⟩
    · intro other
      by_cases same : other = location
      · subst same
        exact Or.inr (Function.update_self ..)
      · exact Or.inl (by simp [CellRules.write, LocalRule.unguarded, same, Excl.zero_def])
    · intro other
      by_cases same : other = location
      · subst same
        exact Or.inr (Function.update_self ..)
      · exact Or.inl (by simp [CellRules.write, LocalRule.unguarded, same, Excl.zero_def])
    · funext other
      by_cases same : other = location
      · subst same
        show source other = (Pi.single other (Excl.own old) : Location → Excl Content) other +
          Function.update source other Excl.empty other
        rw [Pi.single_eq_same, Function.update_self, owns]
        rfl
      · show source other = (Pi.single location (Excl.own old) : Location → Excl Content) other +
          Function.update source location Excl.empty other
        rw [Pi.single_eq_of_ne same, Function.update_of_ne same]
        rfl
    · funext other
      by_cases same : other = location
      · subst same
        show Function.update source other (Excl.own new) other =
          (Pi.single other (Excl.own new) : Location → Excl Content) other +
            Function.update source other Excl.empty other
        rw [Pi.single_eq_same, Function.update_self, Function.update_self]
        rfl
      · show Function.update source location (Excl.own new) other =
          (Pi.single location (Excl.own new) : Location → Excl Content) other +
            Function.update source location Excl.empty other
        rw [Pi.single_eq_of_ne same, Function.update_of_ne same, Function.update_of_ne same]
        rfl

/-- The write of a cell, as a step. -/
def Step.writeCell [DecidableEq Content] (location : Location) (old new : Content) :
    Step Location (Excl Content) where
  rule := CellRules.write location old new
  fire source :=
    if source location = .own old then some (Function.update source location (.own new))
    else none
  fire_eq_some_iff := by
    intro source target
    rw [CellRules.write_fires_iff]
    constructor
    · intro fires
      split at fires
      · next owns =>
        cases fires
        exact ⟨owns, rfl⟩
      · cases fires
    · rintro ⟨owns, rfl⟩
      rw [if_pos owns]

/-! ## Controls -/

namespace ExclusiveCell

/-- One cell that owns `0`. -/
def start : Unit → Excl ℕ := fun _ => .own 0

/-- **Positive**: the write from `0` to `1` fires on the cell that owns `0`. -/
theorem write_fires :
    ((Step.writeCell () 0 1).fire start).map (fun world => world ()) = some (.own 1) := by
  decide

/-- **Negative**: the write from `5` does not fire on it. -/
theorem write_refused : ((Step.writeCell () 5 1).fire start).isSome = false := by
  decide

/-- One alternative: write `1` over `0` and answer. -/
def branch (first : Bool) : Region Unit (Excl ℕ) Bool :=
  .step (Step.writeCell () 0 1) (.answer (Readout.const first))

/-- Both alternatives. -/
def bumpChoice : Region Unit (Excl ℕ) Bool :=
  Region.alternatives [branch true, branch false]

/-- **Two writers of one cell conflict.**  Their proposals are not independent;
both answer in the branch-local mode; the wave policy reports the conflict and
the cell keeps what it owned; the policy that publishes nothing returns the same
answers without a report. -/
theorem two_writers_conflict :
    ¬ ((bumpChoice.branchLocal start).map Prod.snd).Pairwise Proposal.Independent ∧
      (bumpChoice.observe Policy.publishWave start).1 = [true, false] ∧
      (bumpChoice.observe Policy.publishWave start).2.isNone = true ∧
      (bumpChoice.observe Policy.publishNone start).2.map (fun world => world ()) =
        some (.own 0) := by
  decide

/-- **In the committed mode the second writer is stuck**: the cell no longer owns
what it wants to replace, so there is one answer. -/
theorem committed_second_writer_stuck :
    (bumpChoice.committed start).1 = [true] ∧ (bumpChoice.committed start).2 () = .own 1 := by
  decide

/-- Bump the counter that owns `count`, then read it. -/
def bumpFrom (count : ℕ) : Region Unit (Excl ℕ) (Excl ℕ) :=
  .step (Step.writeCell () count (count + 1)) (.answer (Readout.valueAt ()))

/-- Bump the counter, whatever it owns up to `2`. -/
def bump : Region Unit (Excl ℕ) (Excl ℕ) :=
  Region.alternatives [bumpFrom 0, bumpFrom 1, bumpFrom 2]

/-- Read the counter. -/
def get : Region Unit (Excl ℕ) (Excl ℕ) :=
  .answer (Readout.valueAt ())

/-- **Publish nothing: the counter never advances.** -/
theorem counter_stays_under_publishNone :
    (runDirectives Policy.publishNone [bump, bump, get] start).1 =
      [([.own 1], false), ([.own 1], false), ([.own 0], false)] := by
  decide

/-- **A wave or a conflict: the counter advances.** -/
theorem counter_advances_under_publishWave :
    (runDirectives Policy.publishWave [bump, bump, get] start).1 =
      [([.own 1], false), ([.own 2], false), ([.own 2], false)] := by
  decide

end ExclusiveCell

#print axioms CellRules.write_fires_iff
#print axioms ExclusiveCell.write_fires
#print axioms ExclusiveCell.write_refused
#print axioms ExclusiveCell.two_writers_conflict
#print axioms ExclusiveCell.committed_second_writer_stuck
#print axioms ExclusiveCell.counter_stays_under_publishNone
#print axioms ExclusiveCell.counter_advances_under_publishWave

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
