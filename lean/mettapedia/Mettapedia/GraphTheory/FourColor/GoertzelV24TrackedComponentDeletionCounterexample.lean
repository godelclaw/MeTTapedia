import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
import Mathlib.Tactic.FinCases

/-!
# A component receipt does not determine connectivity after support deletion

The cumulative tracked state used by the literal-Cell factor records support
and connected components relative to persistent ports.  A boundary rebase,
however, changes a finite switch support.  This module records the elementary
reason that a deletion-safe core receipt cannot be reconstructed from the
component partition alone.

The four-vertex path and even four-cycle have the same support and the same
complete reachability relation, hence the same exact supported residual code
when no ports are distinguished.  Removing their common interface vertex `1`
disconnects vertices `0` and `2` in the path but not in the cycle.  These are
the path/cycle shapes which occur in a properly two-coloured tracked graph;
the fixture does not rely on an odd tracked cycle.
Consequently any
exact Cell--rebase recurrence must either retain deletion-sensitive prefix
data or prove a source-specific theorem which reconstructs it.  Merely
reusing the component receipt is unsound.

This is a state-interface counterexample, not a counterexample to the
compositional Four-Color route or to the source's `Count` factorization.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TrackedComponentDeletionCounterexample

open GoertzelV24SimpleGraphPortResidualFactorContraction
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open SimpleGraph

/-- The path `0--1--2--3`. -/
def path : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(2, 3)} : Set (Sym2 (Fin 4)))

/-- The even cycle `0--1--2--3--0` on the same four vertices. -/
def evenCycle : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(2, 3), s(0, 3)} : Set (Sym2 (Fin 4)))

/-- The retained interface after the common switch coordinate `1` is removed. -/
abbrev Retained := {vertex : Fin 4 // vertex ≠ 1}

def retainedZero : Retained := ⟨0, by decide⟩

def retainedTwo : Retained := ⟨2, by decide⟩

def retainedThree : Retained := ⟨3, by decide⟩

theorem path_all_reachable (left right : Fin 4) : path.Reachable left right := by
  fin_cases left <;> fin_cases right
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by simp [path])
  · exact (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 0 1)).trans
      (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 1 2))
  · exact ((SimpleGraph.Adj.reachable (by simp [path] : path.Adj 0 1)).trans
      (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 1 2))).trans
        (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 2 3))
  · exact SimpleGraph.Adj.reachable (by simp [path])
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by simp [path])
  · exact (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 1 2)).trans
      (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 2 3))
  · exact (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 2 1)).trans
      (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 1 0))
  · exact SimpleGraph.Adj.reachable (by simp [path])
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by simp [path])
  · exact ((SimpleGraph.Adj.reachable (by simp [path] : path.Adj 3 2)).trans
      (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 2 1))).trans
        (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 1 0))
  · exact (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 3 2)).trans
      (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 2 1))
  · exact SimpleGraph.Adj.reachable (by simp [path])
  · exact SimpleGraph.Reachable.refl _

theorem evenCycle_all_reachable (left right : Fin 4) :
    evenCycle.Reachable left right := by
  fin_cases left <;> fin_cases right
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by simp [evenCycle])
  · exact (SimpleGraph.Adj.reachable (by simp [evenCycle] : evenCycle.Adj 0 3)).trans
      (SimpleGraph.Adj.reachable (by simp [evenCycle] : evenCycle.Adj 3 2))
  · exact SimpleGraph.Adj.reachable (by simp [evenCycle])
  · exact SimpleGraph.Adj.reachable (by simp [evenCycle])
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by simp [evenCycle])
  · exact (SimpleGraph.Adj.reachable (by simp [evenCycle] : evenCycle.Adj 1 0)).trans
      (SimpleGraph.Adj.reachable (by simp [evenCycle] : evenCycle.Adj 0 3))
  · exact (SimpleGraph.Adj.reachable (by simp [evenCycle] : evenCycle.Adj 2 1)).trans
      (SimpleGraph.Adj.reachable (by simp [evenCycle] : evenCycle.Adj 1 0))
  · exact SimpleGraph.Adj.reachable (by simp [evenCycle])
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by simp [evenCycle])
  · exact SimpleGraph.Adj.reachable (by simp [evenCycle])
  · exact (SimpleGraph.Adj.reachable (by simp [evenCycle] : evenCycle.Adj 3 0)).trans
      (SimpleGraph.Adj.reachable (by simp [evenCycle] : evenCycle.Adj 0 1))
  · exact SimpleGraph.Adj.reachable (by simp [evenCycle])
  · exact SimpleGraph.Reachable.refl _

theorem path_all_supported (vertex : Fin 4) : vertex ∈ path.support := by
  fin_cases vertex <;> simp [path, SimpleGraph.mem_support]

theorem evenCycle_all_supported (vertex : Fin 4) :
    vertex ∈ evenCycle.support := by
  fin_cases vertex <;> simp [evenCycle, SimpleGraph.mem_support]

private theorem boundedPortResidualCode_ext
    {Interface Port : Type*}
    {first second : BoundedPortResidualCode Interface Port}
    (hattaches : first.attaches = second.attaches)
    (hresidual : first.residualConnected = second.residualConnected) :
    first = second := by
  cases first
  cases second
  cases hattaches
  cases hresidual
  rfl

private theorem boundedSupportedPortResidualCode_ext
    {Interface Port : Type*}
    {first second : BoundedSupportedPortResidualCode Interface Port}
    (hbase : first.toBoundedPortResidualCode =
      second.toBoundedPortResidualCode)
    (hinterface : first.interfaceActive = second.interfaceActive)
    (hport : first.portActive = second.portActive) : first = second := by
  cases first
  cases second
  cases hbase
  cases hinterface
  cases hport
  rfl

/-- Before deletion, the exact support-sensitive component receipts agree.
The port type is empty, so the receipt sees the complete component partition
and activity table on all four vertices. -/
theorem exactSupportedPortResidualCode_path_eq_evenCycle :
    exactSupportedPortResidualCode path id (Empty.elim : Empty → Fin 4) =
      exactSupportedPortResidualCode evenCycle id (Empty.elim : Empty → Fin 4) := by
  apply boundedSupportedPortResidualCode_ext
  · apply boundedPortResidualCode_ext
    · funext interface port
      exact Empty.elim port
    · funext left right
      simp [exactSupportedPortResidualCode, exactPortResidualCode,
        path_all_reachable, evenCycle_all_reachable]
  · funext interface
    simp [exactSupportedPortResidualCode, path_all_supported,
      evenCycle_all_supported]
  · funext port
    exact Empty.elim port

/-- The path loses `0--2` connectivity when the common switch coordinate is
removed from its support. -/
theorem path_not_reachable_after_remove :
    ¬ (path.induce {vertex | vertex ≠ 1}).Reachable retainedZero retainedTwo := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  intro hreach
  have hzero : ∀ right : Retained,
      ¬ (path.induce {vertex | vertex ≠ 1}).Adj retainedZero right := by
    intro right
    rcases right with ⟨right, hright⟩
    change ¬ path.Adj 0 right
    fin_cases right <;> simp_all [path]
  have heq : ∀ {vertex : Retained},
      Relation.ReflTransGen (path.induce {vertex | vertex ≠ 1}).Adj
          retainedZero vertex →
        retainedZero = vertex := by
    intro vertex hvertex
    induction hvertex with
    | refl => rfl
    | tail hreach hadj ih =>
        subst ih
        exact (hzero _ hadj).elim
  exact (by decide : retainedZero ≠ retainedTwo) (heq hreach)

/-- The even cycle retains `0--2` connectivity after the same support removal,
using the surviving path `0--3--2`. -/
theorem evenCycle_reachable_after_remove :
    (evenCycle.induce {vertex | vertex ≠ 1}).Reachable retainedZero retainedTwo := by
  exact (SimpleGraph.Adj.reachable
      (show (evenCycle.induce {vertex | vertex ≠ 1}).Adj retainedZero
          retainedThree by
        change evenCycle.Adj (0 : Fin 4) 3
        simp [evenCycle])).trans
    (SimpleGraph.Adj.reachable
      (show (evenCycle.induce {vertex | vertex ≠ 1}).Adj retainedThree
          retainedTwo by
        change evenCycle.Adj (3 : Fin 4) 2
        simp [evenCycle]))

/-- Equal pre-removal component receipts can have different post-removal
answers for the same named switch. -/
theorem exists_equal_receipt_with_different_deleted_reachability :
    ∃ first second : SimpleGraph (Fin 4),
      exactSupportedPortResidualCode first id (Empty.elim : Empty → Fin 4) =
        exactSupportedPortResidualCode second id (Empty.elim : Empty → Fin 4) ∧
      ¬ (first.induce {vertex | vertex ≠ 1}).Reachable retainedZero retainedTwo ∧
      (second.induce {vertex | vertex ≠ 1}).Reachable retainedZero retainedTwo := by
  exact ⟨path, evenCycle, exactSupportedPortResidualCode_path_eq_evenCycle,
    path_not_reachable_after_remove, evenCycle_reachable_after_remove⟩

end GoertzelV24TrackedComponentDeletionCounterexample

end Mettapedia.GraphTheory.FourColor
