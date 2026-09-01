import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push

/-!
# Boundary-language closure on a five-cycle

This file isolates the finite logical heart of Birkhoff's short five-cycle
argument.  It does not enumerate boundary colourings.  Instead it assumes the
two generic Kempe implications for two cyclic families of boundary behaviours
and proves that two nonempty languages satisfying them cannot be pointwise
disjoint.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace FiveCycleBoundaryClosure

/-- The next position on a cyclically ordered five-element boundary. -/
def next (index : Fin 5) : Fin 5 := index + 1

/-- The preceding position on a cyclically ordered five-element boundary. -/
def previous (index : Fin 5) : Fin 5 := index - 1

@[simp]
theorem next_previous (index : Fin 5) : next (previous index) = index := by
  fin_cases index <;> rfl

theorem previous_four_eq_next (index : Fin 5) :
    previous (previous (previous (previous index))) = next index := by
  fin_cases index <;> rfl

/-- The two abstract boundary families and the two Kempe implications used by
the short five-cycle argument. -/
structure Closure (primary secondary : Fin 5 → Prop) : Prop where
  secondary_of_primary_drop : ∀ index,
    primary index → ¬ primary (next index) → secondary index
  primary_of_next_missing : ∀ index,
    ¬ primary (next index) → ¬ secondary (next index) → primary index

/-- A nonconstant predicate on the cyclic five-set drops across some forward
edge. -/
theorem exists_drop {predicate : Fin 5 → Prop}
    (hsome : ∃ index, predicate index)
    (hnone : ∃ index, ¬ predicate index) :
    ∃ index, predicate index ∧ ¬ predicate (next index) := by
  rcases hsome with ⟨someIndex, hsomeIndex⟩
  rcases hnone with ⟨noneIndex, hnoneIndex⟩
  by_contra hdrop
  push Not at hdrop
  have hnextOne : predicate (next someIndex) :=
    hdrop someIndex hsomeIndex
  have hnextTwo : predicate (next (next someIndex)) :=
    hdrop (next someIndex) hnextOne
  have hnextThree : predicate (next (next (next someIndex))) :=
    hdrop (next (next someIndex)) hnextTwo
  have hnextFour : predicate (next (next (next (next someIndex)))) :=
    hdrop (next (next (next someIndex))) hnextThree
  have hnoneTrue : predicate noneIndex := by
    fin_cases someIndex <;> fin_cases noneIndex <;>
      simp_all [next]
  exact hnoneIndex hnoneTrue

/-- If one language realizes both boundary families at a position, pointwise
disjointness and the closure rules force the other language to realize both
families at the preceding position. -/
theorem transfer_previous
    {firstPrimary firstSecondary secondPrimary secondSecondary : Fin 5 → Prop}
    (secondClosure : Closure secondPrimary secondSecondary)
    (primaryDisjoint : ∀ index, firstPrimary index → ¬ secondPrimary index)
    (secondaryDisjoint : ∀ index, firstSecondary index → ¬ secondSecondary index)
    (index : Fin 5)
    (hprimary : firstPrimary index)
    (hsecondary : firstSecondary index) :
    secondPrimary (previous index) ∧ secondSecondary (previous index) := by
  have hsecondPrimary : ¬ secondPrimary index :=
    primaryDisjoint index hprimary
  have hsecondSecondary : ¬ secondSecondary index :=
    secondaryDisjoint index hsecondary
  have hpreviousPrimary : secondPrimary (previous index) :=
    secondClosure.primary_of_next_missing (previous index)
      (by simpa using hsecondPrimary) (by simpa using hsecondSecondary)
  exact ⟨hpreviousPrimary,
    secondClosure.secondary_of_primary_drop (previous index)
      hpreviousPrimary (by simpa using hsecondPrimary)⟩

/-- **Abstract Birkhoff five-cycle heart.**  Two boundary languages which
each realize a primary behaviour and satisfy the two Kempe closure rules
must overlap in either a primary or a secondary behaviour. -/
theorem not_pointwise_disjoint
    {firstPrimary firstSecondary secondPrimary secondSecondary : Fin 5 → Prop}
    (firstClosure : Closure firstPrimary firstSecondary)
    (secondClosure : Closure secondPrimary secondSecondary)
    (firstNonempty : ∃ index, firstPrimary index)
    (secondNonempty : ∃ index, secondPrimary index) :
    ¬ ((∀ index, ¬ (firstPrimary index ∧ secondPrimary index)) ∧
      (∀ index, ¬ (firstSecondary index ∧ secondSecondary index))) := by
  rintro ⟨primaryDisjoint, secondaryDisjoint⟩
  have firstToSecondPrimary : ∀ index,
      firstPrimary index → ¬ secondPrimary index :=
    fun index hfirst hsecond => primaryDisjoint index ⟨hfirst, hsecond⟩
  have secondToFirstPrimary : ∀ index,
      secondPrimary index → ¬ firstPrimary index :=
    fun index hsecond hfirst => primaryDisjoint index ⟨hfirst, hsecond⟩
  have firstToSecondSecondary : ∀ index,
      firstSecondary index → ¬ secondSecondary index :=
    fun index hfirst hsecond => secondaryDisjoint index ⟨hfirst, hsecond⟩
  have secondToFirstSecondary : ∀ index,
      secondSecondary index → ¬ firstSecondary index :=
    fun index hsecond hfirst => secondaryDisjoint index ⟨hfirst, hsecond⟩
  obtain ⟨secondIndex, hsecondPrimary⟩ := secondNonempty
  have hfirstMissing : ¬ firstPrimary secondIndex :=
    secondToFirstPrimary secondIndex hsecondPrimary
  obtain ⟨index, hfirstPrimary, hfirstNextMissing⟩ :=
    exists_drop firstNonempty ⟨secondIndex, hfirstMissing⟩
  have hfirstSecondary : firstSecondary index :=
    firstClosure.secondary_of_primary_drop index hfirstPrimary
      hfirstNextMissing
  obtain ⟨hsecondPreviousPrimary, hsecondPreviousSecondary⟩ :=
    transfer_previous secondClosure firstToSecondPrimary
      firstToSecondSecondary index hfirstPrimary hfirstSecondary
  obtain ⟨hfirstPreviousTwoPrimary, hfirstPreviousTwoSecondary⟩ :=
    transfer_previous firstClosure secondToFirstPrimary
      secondToFirstSecondary (previous index) hsecondPreviousPrimary
      hsecondPreviousSecondary
  obtain ⟨hsecondPreviousThreePrimary, hsecondPreviousThreeSecondary⟩ :=
    transfer_previous secondClosure firstToSecondPrimary
      firstToSecondSecondary (previous (previous index))
      hfirstPreviousTwoPrimary hfirstPreviousTwoSecondary
  obtain ⟨hfirstPreviousFourPrimary, _⟩ :=
    transfer_previous firstClosure secondToFirstPrimary
      secondToFirstSecondary (previous (previous (previous index)))
      hsecondPreviousThreePrimary hsecondPreviousThreeSecondary
  rw [previous_four_eq_next] at hfirstPreviousFourPrimary
  exact hfirstNextMissing hfirstPreviousFourPrimary

end FiveCycleBoundaryClosure

end Mettapedia.GraphTheory.FourColor.Compositional
