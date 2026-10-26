import Mettapedia.GSLT.Causality.ResourceInteraction

/-!
# Removing from a space: what is removed, and what the removal answers

A space holds a bag of atoms. Four removal contracts are in use or proposed:

* **remove one, or fail** (`removeOne`): remove one occurrence; when there is none, there is no result.
* **remove exactly `n`, or fail** (`removeExactly`): remove `n` occurrences at once, or none.
* **remove every match, and count** (`removeAll`): remove every element a pattern accepts; the answer is
  how many were removed.
* **remove one if present, and report** (`removeReport`): remove one occurrence when there is one; the
  answer says whether there was.

## What each contract is

* Removing one occurrence, or failing, is exactly one firing of the rule that takes the atom and keeps and
  produces nothing (`removeOne_eq_some_iff_step`): its success set is the rule's applicability. It undoes an
  addition (`removeOne_cons`) and fails exactly on absence (`removeOne_eq_none_iff`).
* Removing exactly `n` is the firing of the rule taking `n` copies (`removeExactly_eq_some_iff`); `n = 1` is
  the first contract (`removeExactly_one`).
* Removing every match answers the count of matches (`removeAll_count`), leaves nothing to remove a second
  time (`removeAll_idempotent`), and always succeeds.
* The report reads absence. A `false` answer is not stable: adding the atom later makes the same call answer
  `true` (`report_false_not_stable`). A report is a removal together with a read of the whole count of the atom.

## On a set store

When every atom occurs at most once, removing one occurrence of a ground atom and removing every occurrence
agree, and the count is `1` or `0` (`removeOne_eq_removeAll_of_nodup`, `removeAll_absent`).

## Composition

* Two successful removals in sequence are one removal of both (`removeOne_bind_removeOne`).
* Without a rollback, a first removal that succeeded stays when the second fails, while removing the pair at
  once fails and changes nothing (`sequential_removal_not_atomic`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.SpaceRemoval

open Mettapedia.GSLT.Causality.ResourceInteraction

universe u

variable {R : Type u} [DecidableEq R]

/-! ## The contracts -/

/-- **Remove one occurrence, or fail.** -/
def removeOne (M : Multiset R) (a : R) : Option (Multiset R) :=
  if a ∈ M then some (M.erase a) else none

/-- **Remove exactly `n` occurrences, or fail.** -/
def removeExactly (M : Multiset R) (n : ℕ) (a : R) : Option (Multiset R) :=
  if n ≤ M.count a then some (M - Multiset.replicate n a) else none

/-- **Remove a whole bag at once, or fail.** -/
def removeBag (M B : Multiset R) : Option (Multiset R) :=
  if B ≤ M then some (M - B) else none

/-- **Remove every element the pattern accepts**, answering what is left and how many were removed. -/
def removeAll (M : Multiset R) (pattern : R → Prop) [DecidablePred pattern] : Multiset R × ℕ :=
  (M.filter fun r => ¬ pattern r, (M.filter pattern).card)

/-- **Remove one occurrence if present, and report whether there was one.** -/
def removeReport (M : Multiset R) (a : R) : Multiset R × Bool :=
  (M.erase a, decide (a ∈ M))

/-! ## Remove one, or fail -/

theorem removeOne_cons (M : Multiset R) (a : R) : removeOne (a ::ₘ M) a = some M := by
  simp [removeOne]

theorem removeOne_eq_none_iff (M : Multiset R) (a : R) : removeOne M a = none ↔ a ∉ M := by
  unfold removeOne
  split <;> simp_all

theorem removeOne_eq_some_iff (M N : Multiset R) (a : R) :
    removeOne M a = some N ↔ a ∈ M ∧ a ::ₘ N = M := by
  unfold removeOne
  split
  · rename_i present
    constructor
    · rintro ⟨⟩
      exact ⟨present, Multiset.cons_erase present⟩
    · rintro ⟨-, rfl⟩
      simp
  · rename_i absent
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun present => absent present |>.elim

/-- The rule that takes one atom and keeps and produces nothing. -/
def takeOne : System.{u, u} R where
  Site := PUnit
  Instance := fun _ => R
  consume := fun (a : R) => {a}
  read := fun _ => 0
  produce := fun _ => 0

/-- **Removing one occurrence, or failing, is one firing of the rule that takes the atom.** -/
theorem removeOne_eq_some_iff_step (M N : Multiset R) (a : R) :
    removeOne M a = some N ↔
      takeOne.Enables M (site := PUnit.unit) a ∧ N = takeOne.fire M (site := PUnit.unit) a := by
  rw [removeOne_eq_some_iff]
  simp only [System.Enables, System.fire, takeOne, add_zero, Multiset.singleton_le]
  constructor
  · rintro ⟨present, rfl⟩
    refine ⟨Multiset.mem_cons_self a N, ?_⟩
    rw [Multiset.sub_singleton, Multiset.erase_cons_head]
  · rintro ⟨present, rfl⟩
    rw [Multiset.sub_singleton]
    exact ⟨present, Multiset.cons_erase present⟩

/-! ## Remove exactly `n` -/

theorem removeExactly_eq_some_iff (M N : Multiset R) (n : ℕ) (a : R) :
    removeExactly M n a = some N ↔ Multiset.replicate n a ≤ M ∧ N = M - Multiset.replicate n a := by
  unfold removeExactly
  rw [← Multiset.le_count_iff_replicate_le]
  split
  · rename_i enough
    exact ⟨fun h => ⟨enough, (Option.some.inj h).symm⟩, fun h => by rw [h.2]⟩
  · rename_i short
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun enough => absurd enough short

theorem removeExactly_one (M : Multiset R) (a : R) : removeExactly M 1 a = removeOne M a := by
  unfold removeExactly removeOne
  by_cases present : a ∈ M
  · have one : 1 ≤ M.count a := Multiset.one_le_count_iff_mem.mpr present
    simp [present, one, Multiset.sub_singleton]
  · simp [present]

/-! ## Remove every match, and count -/

omit [DecidableEq R] in
theorem removeAll_fst_add (M : Multiset R) (pattern : R → Prop) [DecidablePred pattern] :
    (removeAll M pattern).1 + M.filter pattern = M := by
  rw [removeAll, add_comm]
  exact Multiset.filter_add_not pattern M

/-- **The answer counts the occurrences removed.** For a ground atom it is the atom's count. -/
theorem removeAll_count (M : Multiset R) (a : R) : (removeAll M (· = a)).2 = M.count a := by
  simp only [removeAll]
  rw [Multiset.count_eq_card_filter_eq]
  congr 1
  exact Multiset.filter_congr fun _ _ => eq_comm

omit [DecidableEq R] in
/-- **Removing every match a second time removes nothing.** -/
theorem removeAll_idempotent (M : Multiset R) (pattern : R → Prop) [DecidablePred pattern] :
    removeAll (removeAll M pattern).1 pattern = ((removeAll M pattern).1, 0) := by
  simp only [removeAll, Multiset.filter_filter, Prod.mk.injEq]
  constructor
  · exact Multiset.filter_congr fun _ _ => by simp
  · rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro r _ both
    exact both.2 both.1

/-! ## Remove and report -/

theorem removeReport_snd (M : Multiset R) (a : R) : (removeReport M a).2 = true ↔ a ∈ M := by
  simp [removeReport]

theorem removeReport_fst (M : Multiset R) (a : R) : (removeReport M a).1 = (removeOne M a).getD M := by
  unfold removeReport removeOne
  by_cases present : a ∈ M
  · simp [present]
  · simp [present]

/-- **A `false` report is not stable**: the same call answers `true` once the atom is added. The report
reads the absence of the atom. -/
theorem report_false_not_stable (M : Multiset R) (a : R) (absent : a ∉ M) :
    (removeReport M a).2 = false ∧ M ≤ a ::ₘ M ∧ (removeReport (a ::ₘ M) a).2 = true := by
  refine ⟨by simp [removeReport, absent], Multiset.le_cons_self M a, by simp [removeReport]⟩

/-! ## On a set store -/

/-- **On a set store, removing one occurrence of a ground atom removes every occurrence**, and the count
is `1`. -/
theorem removeOne_eq_removeAll_of_nodup {M N : Multiset R} {a : R} (nodup : M.Nodup)
    (removed : removeOne M a = some N) : removeAll M (· = a) = (N, 1) := by
  obtain ⟨present, rfl⟩ := (removeOne_eq_some_iff M N a).mp removed
  have notIn : a ∉ N := (Multiset.nodup_cons.mp nodup).1
  have rest : N.filter (· = a) = 0 :=
    Multiset.filter_eq_nil.mpr fun r member equal => notIn (equal ▸ member)
  have kept : N.filter (fun r => ¬ r = a) = N :=
    Multiset.filter_eq_self.mpr fun r member equal => notIn (equal ▸ member)
  simp only [removeAll, Prod.mk.injEq]
  constructor
  · rw [Multiset.filter_cons_of_neg _ (by simp), kept]
  · rw [Multiset.filter_cons_of_pos (p := fun x => x = a) _ rfl, rest]
    rfl

/-- **Removing an absent atom removes nothing, and the count is `0`.** -/
theorem removeAll_absent (M : Multiset R) (a : R) (absent : a ∉ M) : removeAll M (· = a) = (M, 0) := by
  simp only [removeAll, Prod.mk.injEq]
  constructor
  · rw [Multiset.filter_eq_self]
    intro r member equal
    exact absent (equal ▸ member)
  · rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro r member equal
    exact absent (equal ▸ member)

/-! ## Composition -/

/-- **Two successful removals in sequence are one removal of both.** -/
theorem removeOne_bind_removeOne {M N P : Multiset R} {a b : R} (first : removeOne M a = some N)
    (second : removeOne N b = some P) : removeBag M {a, b} = some P := by
  obtain ⟨_, rfl⟩ := (removeOne_eq_some_iff _ _ _).mp first
  obtain ⟨_, rfl⟩ := (removeOne_eq_some_iff _ _ _).mp second
  have pair : ({a, b} : Multiset R) = a ::ₘ b ::ₘ 0 := rfl
  unfold removeBag
  rw [if_pos (by rw [pair]; exact Multiset.cons_le_cons a (Multiset.cons_le_cons b (Multiset.zero_le P)))]
  rw [pair, Multiset.sub_cons, Multiset.erase_cons_head, Multiset.sub_cons, Multiset.erase_cons_head,
    tsub_zero]

/-- **Removals in sequence are not one removal.** From `{a}`, removing `a` succeeds and removing `b` then
fails, leaving the empty bag; removing `a` and `b` at once fails and leaves `{a}`. Without a rollback, the
sequence reaches a bag that the joint removal never does. -/
theorem sequential_removal_not_atomic {a b : R} (different : a ≠ b) :
    removeOne ({a} : Multiset R) a = some 0 ∧ removeOne (0 : Multiset R) b = none ∧
      removeBag ({a} : Multiset R) {a, b} = none := by
  refine ⟨?_, by simp [removeOne], ?_⟩
  · simp [removeOne]
  · unfold removeBag
    rw [if_neg]
    intro le
    have count := Multiset.count_le_of_le b le
    simp [different.symm] at count

end Mettapedia.GSLT.Causality.SpaceRemoval
