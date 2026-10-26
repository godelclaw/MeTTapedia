import Mettapedia.Languages.MeTTa.TransformQuantifiers
import Mettapedia.GSLT.Causality.SpaceRemovalContracts

/-!
# The removal contracts as transforms

A take source over a pattern has one row per stored occurrence the pattern accepts; committing a row
takes that occurrence and writes nothing (`takeRows`). The removal contracts of `SpaceRemovalContracts`
are the two quantifiers over it:

* **remove every match, with its count, is `every`** (`every_take_iff_removeAll`,
  `every_take_count`): the amalgamated firing is always enabled, leaves what the pattern rejects, and
  commits as many rows as the contract reports;
* **remove one, or fail, is `each`** over the rows of one atom (`each_take_iff_removeOne`): a firing
  exists exactly when the contract succeeds, with the same result, and the absence of the atom leaves
  no firing (`each_take_none_of_absent`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TransformQuantifiers

open Mettapedia.GSLT.Causality.SpaceRemoval

universe u

variable {α : Type u} [DecidableEq α]

/-- Rows of a take source: the matched occurrence is taken; nothing is written. -/
def takeFootprints : Footprints α α where
  take := fun x => {x}
  write := fun _ => 0

/-- The rows of a take source over a pattern: the stored occurrences it accepts. -/
def takeRows (pattern : α → Prop) [DecidablePred pattern] (M : Multiset α) : Multiset α :=
  M.filter pattern

omit [DecidableEq α] in
theorem totalTake_takeRows (pattern : α → Prop) [DecidablePred pattern] (M : Multiset α) :
    takeFootprints.totalTake (takeRows pattern M) = M.filter pattern := by
  simp [Footprints.totalTake, takeFootprints, takeRows, Multiset.sum_map_singleton]

omit [DecidableEq α] in
theorem totalWrite_takeRows (pattern : α → Prop) [DecidablePred pattern] (M : Multiset α) :
    takeFootprints.totalWrite (takeRows pattern M) = 0 := by
  simp [Footprints.totalWrite, takeFootprints]

/-- **Remove every match is `every` over a take source.** -/
theorem every_take_iff_removeAll (pattern : α → Prop) [DecidablePred pattern] (M N : Multiset α) :
    takeFootprints.EveryStep (takeRows pattern M) M N ↔ N = (removeAll M pattern).1 := by
  rw [Footprints.EveryStep, totalTake_takeRows, totalWrite_takeRows, add_zero]
  have left : M - M.filter pattern = M.filter fun r => ¬ pattern r := by
    rw [tsub_eq_iff_eq_add_of_le (Multiset.filter_le _ _), add_comm, Multiset.filter_add_not]
  rw [left]
  exact ⟨fun step => step.2, fun same => ⟨Multiset.filter_le _ _, same⟩⟩

omit [DecidableEq α] in
/-- **`every` commits as many rows as the contract reports removed.** -/
theorem every_take_count (pattern : α → Prop) [DecidablePred pattern] (M : Multiset α) :
    Multiset.card (takeRows pattern M) = (removeAll M pattern).2 := rfl

/-- **Remove one, or fail, is `each` over the rows of one atom.** -/
theorem each_take_iff_removeOne (M N : Multiset α) (a : α) :
    takeFootprints.EachStep (takeRows (· = a) M) M N ↔ removeOne M a = some N := by
  rw [removeOne_eq_some_iff]
  constructor
  · rintro ⟨x, member, -, rfl⟩
    obtain ⟨present, rfl⟩ := Multiset.mem_filter.mp member
    refine ⟨present, ?_⟩
    simp [Footprints.fire, takeFootprints, Multiset.sub_singleton, Multiset.cons_erase present]
  · rintro ⟨present, rfl⟩
    refine ⟨a, Multiset.mem_filter.mpr ⟨Multiset.mem_cons_self a N, rfl⟩,
      Multiset.singleton_le.mpr (Multiset.mem_cons_self a N), ?_⟩
    simp [Footprints.fire, takeFootprints, Multiset.sub_singleton]

/-- **An absent atom leaves `each` no firing**, where today's removal answers anyway. -/
theorem each_take_none_of_absent (M N : Multiset α) (a : α) (absent : a ∉ M) :
    ¬ takeFootprints.EachStep (takeRows (· = a) M) M N := by
  rw [each_take_iff_removeOne, (removeOne_eq_none_iff M a).mpr absent]
  simp

end Mettapedia.Languages.MeTTa.TransformQuantifiers
