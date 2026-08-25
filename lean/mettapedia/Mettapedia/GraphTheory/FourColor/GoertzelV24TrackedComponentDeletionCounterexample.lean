import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
import Mathlib.Tactic.FinCases

/-!
# A component receipt does not determine connectivity after support deletion

The cumulative tracked state used by the literal-Cell factor records support
and connected components relative to persistent ports.  A boundary rebase,
however, changes a finite switch support.  This module records the elementary
reason that a deletion-safe core receipt cannot be reconstructed from the
component partition alone.

The three-vertex path and triangle have the same support and the same complete
reachability relation, hence the same exact supported residual code when no
ports are distinguished.  Removing their common interface vertex `1`
disconnects vertices `0` and `2` in the path but not in the triangle.
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

/-- The path `0--1--2`. -/
def path : SimpleGraph (Fin 3) :=
  SimpleGraph.fromEdgeSet ({s(0, 1), s(1, 2)} : Set (Sym2 (Fin 3)))

/-- The triangle on the same three vertices. -/
def triangle : SimpleGraph (Fin 3) :=
  SimpleGraph.fromEdgeSet ({s(0, 1), s(1, 2), s(0, 2)} : Set (Sym2 (Fin 3)))

/-- The retained interface after the common switch coordinate `1` is removed. -/
abbrev Retained := {vertex : Fin 3 // vertex ≠ 1}

def retainedZero : Retained := ⟨0, by decide⟩

def retainedTwo : Retained := ⟨2, by decide⟩

theorem path_all_reachable (left right : Fin 3) : path.Reachable left right := by
  fin_cases left <;> fin_cases right
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by simp [path])
  · exact (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 0 1)).trans
      (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 1 2))
  · exact SimpleGraph.Adj.reachable (by simp [path])
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by simp [path])
  · exact (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 2 1)).trans
      (SimpleGraph.Adj.reachable (by simp [path] : path.Adj 1 0))
  · exact SimpleGraph.Adj.reachable (by simp [path])
  · exact SimpleGraph.Reachable.refl _

theorem triangle_all_reachable (left right : Fin 3) :
    triangle.Reachable left right := by
  fin_cases left <;> fin_cases right
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by simp [triangle])
  · exact SimpleGraph.Adj.reachable (by simp [triangle])
  · exact SimpleGraph.Adj.reachable (by simp [triangle])
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by simp [triangle])
  · exact SimpleGraph.Adj.reachable (by simp [triangle])
  · exact SimpleGraph.Adj.reachable (by simp [triangle])
  · exact SimpleGraph.Reachable.refl _

theorem path_all_supported (vertex : Fin 3) : vertex ∈ path.support := by
  fin_cases vertex <;> simp [path, SimpleGraph.mem_support]

theorem triangle_all_supported (vertex : Fin 3) :
    vertex ∈ triangle.support := by
  fin_cases vertex <;> simp [triangle, SimpleGraph.mem_support]

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
and activity table on all three vertices. -/
theorem exactSupportedPortResidualCode_path_eq_triangle :
    exactSupportedPortResidualCode path id (Empty.elim : Empty → Fin 3) =
      exactSupportedPortResidualCode triangle id (Empty.elim : Empty → Fin 3) := by
  apply boundedSupportedPortResidualCode_ext
  · apply boundedPortResidualCode_ext
    · funext interface port
      exact Empty.elim port
    · funext left right
      simp [exactSupportedPortResidualCode, exactPortResidualCode,
        path_all_reachable, triangle_all_reachable]
  · funext interface
    simp [exactSupportedPortResidualCode, path_all_supported,
      triangle_all_supported]
  · funext port
    exact Empty.elim port

/-- The path loses `0--2` connectivity when the common switch coordinate is
removed from its support. -/
theorem path_not_reachable_after_remove :
    ¬ (path.induce {vertex | vertex ≠ 1}).Reachable retainedZero retainedTwo := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  intro hreach
  have hno : ∀ left right : Retained,
      ¬ (path.induce {vertex | vertex ≠ 1}).Adj left right := by
    intro left right
    rcases left with ⟨left, hleft⟩
    rcases right with ⟨right, hright⟩
    change ¬ path.Adj left right
    fin_cases left <;> fin_cases right <;> simp_all [path]
  have heq : ∀ {vertex : Retained},
      Relation.ReflTransGen (path.induce {vertex | vertex ≠ 1}).Adj
          retainedZero vertex →
        retainedZero = vertex := by
    intro vertex hvertex
    induction hvertex with
    | refl => rfl
    | tail _ hadj _ => exact (hno _ _ hadj).elim
  exact (by decide : retainedZero ≠ retainedTwo) (heq hreach)

/-- The triangle retains `0--2` connectivity after the same support removal. -/
theorem triangle_reachable_after_remove :
    (triangle.induce {vertex | vertex ≠ 1}).Reachable retainedZero retainedTwo := by
  apply SimpleGraph.Adj.reachable
  change triangle.Adj (0 : Fin 3) 2
  simp [triangle]

/-- Equal pre-removal component receipts can have different post-removal
answers for the same named switch. -/
theorem exists_equal_receipt_with_different_deleted_reachability :
    ∃ first second : SimpleGraph (Fin 3),
      exactSupportedPortResidualCode first id (Empty.elim : Empty → Fin 3) =
        exactSupportedPortResidualCode second id (Empty.elim : Empty → Fin 3) ∧
      ¬ (first.induce {vertex | vertex ≠ 1}).Reachable retainedZero retainedTwo ∧
      (second.induce {vertex | vertex ≠ 1}).Reachable retainedZero retainedTwo := by
  exact ⟨path, triangle, exactSupportedPortResidualCode_path_eq_triangle,
    path_not_reachable_after_remove, triangle_reachable_after_remove⟩

end GoertzelV24TrackedComponentDeletionCounterexample

end Mettapedia.GraphTheory.FourColor
