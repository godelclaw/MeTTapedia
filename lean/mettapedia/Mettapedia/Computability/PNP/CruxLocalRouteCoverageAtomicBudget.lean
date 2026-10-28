import Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetExactnessReduction

/-!
# PNP local route coverage: atomic evidence budget anchors

Atomic-evidence budget exactness coverage anchors for the local PNP crux
packet.
-/

namespace Mettapedia.Computability.PNP

/-- The v13 atomic-evidence budget ledger entry is covered only at the full
finite exactness boundary: no-double-counting gives the upper budget bound,
charging every positive-cost atom gives the lower bound, strict under/over
budget localize to omitted/double-counted positive-cost atoms, the full
exactness-side conjunction gives exact equality, and the cancellation surface
shows that exact equality plus equivalence of the two side conditions is still
not enough. -/
def V13AtomicEvidenceBudgetCoverage : Prop :=
  ((∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
        S.NoDoubleCounting → S.coordinateSummedCost ≤ S.atomBudget) ∧
    (∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
        S.AllPositiveCostAtomsCharged → S.atomBudget ≤ S.coordinateSummedCost) ∧
    (∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
        S.atomBudget < S.coordinateSummedCost → S.DoubleCountedAtom) ∧
    ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
      S.coordinateSummedCost < S.atomBudget → S.MissedPositiveCostAtom) ∧
  ((∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
        S.ExactnessSideConditions → S.coordinateSummedCost = S.atomBudget) ∧
    (∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
        S.coordinateSummedCost = S.atomBudget →
          (S.ExactnessSideConditions ↔ S.NoDoubleCounting)) ∧
    ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
      S.coordinateSummedCost = S.atomBudget →
        (S.ExactnessSideConditions ↔ S.AllPositiveCostAtomsCharged)) ∧
  ¬ ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
      S.coordinateSummedCost = S.atomBudget →
        (S.NoDoubleCounting ↔ S.AllPositiveCostAtomsCharged) →
        S.ExactnessSideConditions

@[simp] theorem v13AtomicEvidenceBudgetCoverage :
    V13AtomicEvidenceBudgetCoverage := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro Coord Atom _FintypeCoord _FintypeAtom S _DecidableRel hno
      exact
        V13AtomicEvidenceBudgetSurface.coordinateSummedCost_le_atomBudget_of_noDoubleCounting
          S hno
    · intro Coord Atom _FintypeCoord _FintypeAtom S _DecidableRel hall
      exact
        V13AtomicEvidenceBudgetSurface.atomBudget_le_coordinateSummedCost_of_allPositiveCostAtomsCharged
          S hall
    · intro Coord Atom _FintypeCoord _FintypeAtom S _DecidableRel hlt
      exact
        V13AtomicEvidenceBudgetSurface.doubleCountedAtom_of_atomBudget_lt_coordinateSummedCost
          S hlt
    · intro Coord Atom _FintypeCoord _FintypeAtom S _DecidableRel hlt
      exact
        V13AtomicEvidenceBudgetSurface.missedPositiveCostAtom_of_coordinateSummedCost_lt_atomBudget
          S hlt
  · refine ⟨?_, ?_, ?_⟩
    · intro Coord Atom _FintypeCoord _FintypeAtom S _DecidableRel hexact
      exact
        V13AtomicEvidenceBudgetSurface.coordinateSummedCost_eq_atomBudget_of_exactnessSideConditions
          S hexact
    · intro Coord Atom _FintypeCoord _FintypeAtom S _DecidableRel heq
      exact
        V13AtomicEvidenceBudgetSurface.exactnessSideConditions_iff_noDoubleCounting_of_coordinateSummedCost_eq_atomBudget
          S heq
    · intro Coord Atom _FintypeCoord _FintypeAtom S _DecidableRel heq
      exact
        V13AtomicEvidenceBudgetSurface.exactnessSideConditions_iff_allPositiveCostAtomsCharged_of_coordinateSummedCost_eq_atomBudget
          S heq
  · exact
      not_forall_coordinateSummedCost_eq_atomBudget_and_sideConditionEquivalence_implies_exactnessSideConditions

/-- Route-coverage anchor: a one-atom/two-coordinate surface proves that the
once-per-atom budget can undercount the coordinate-summed cost by a factor of
the charge multiplicity. -/
theorem v13AtomicEvidenceBudgetCoverage_anchor_doubleCountedAtom_blocks :
    v13DoubleCountedBudgetSurface.atomBudget = 1 ∧
      v13DoubleCountedBudgetSurface.coordinateSummedCost = 2 ∧
      ¬ v13DoubleCountedBudgetSurface.NoDoubleCounting ∧
      v13DoubleCountedBudgetSurface.atomBudget <
        v13DoubleCountedBudgetSurface.coordinateSummedCost := by
  exact
    ⟨v13DoubleCountedBudgetSurface_atomBudget,
      v13DoubleCountedBudgetSurface_coordinateSummedCost,
      v13DoubleCountedBudgetSurface_not_noDoubleCounting,
      v13DoubleCountedBudgetSurface_atomBudget_lt_coordinateSummedCost⟩

/-- Route-coverage anchor: the cancellation surface shows that exact aggregate
budget equality plus equivalence of the two structural side conditions still
does not certify the full exactness conjunction. -/
theorem v13AtomicEvidenceBudgetCoverage_anchor_cancellation_blocks :
    v13CancellationBudgetSurface.coordinateSummedCost =
        v13CancellationBudgetSurface.atomBudget ∧
      (v13CancellationBudgetSurface.NoDoubleCounting ↔
        v13CancellationBudgetSurface.AllPositiveCostAtomsCharged) ∧
      ¬ v13CancellationBudgetSurface.ExactnessSideConditions := by
  exact
    v13CancellationBudgetSurface_exact_budget_with_sideConditionEquivalence_without_exactnessSideConditions

end Mettapedia.Computability.PNP
