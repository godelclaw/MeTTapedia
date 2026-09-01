import Mettapedia.GraphTheory.FiniteEdgePatchConnectivity
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite boundary connectivity states

A graph can expose its component relation on any fixed finite list of ports as
another finite simple graph.  Two distinct ports are adjacent in this state
exactly when their images are connected in the original graph.  Reachability
in the state is therefore equivalent to reachability of the represented
vertices, even when several ports name the same vertex.

This is the mathematical interface used by compositional consumers: the
ambient graph may be arbitrarily large, while its connectivity behaviour at a
fixed boundary belongs to a finite type.
-/

namespace SimpleGraph

universe u v

variable {V : Type u} {Port : Type v}

/-- The component relation of `G`, observed through a family of labelled
ports.  Distinct labels may represent the same ambient vertex. -/
def boundaryConnectivityState
    (G : SimpleGraph V) (vertex : Port → V) : SimpleGraph Port where
  Adj left right := left ≠ right ∧ G.Reachable (vertex left) (vertex right)
  symm := ⟨by
    intro left right relation
    exact ⟨relation.1.symm, relation.2.symm⟩⟩
  loopless := ⟨by
    intro port relation
    exact relation.1 rfl⟩

@[simp]
theorem boundaryConnectivityState_adj
    (G : SimpleGraph V) (vertex : Port → V) (left right : Port) :
    (boundaryConnectivityState G vertex).Adj left right ↔
      left ≠ right ∧ G.Reachable (vertex left) (vertex right) :=
  Iff.rfl

/-- The finite state records exactly the ambient component relation on its
ports. -/
theorem boundaryConnectivityState_reachable_iff
    (G : SimpleGraph V) (vertex : Port → V) (left right : Port) :
    (boundaryConnectivityState G vertex).Reachable left right ↔
      G.Reachable (vertex left) (vertex right) := by
  constructor
  · intro hstate
    have hpath := (reachable_iff_reflTransGen left right).mp hstate
    exact Relation.ReflTransGen.trans_induction_on
      (motive := fun {x y} _ => G.Reachable (vertex x) (vertex y))
      hpath
      (fun _ => Reachable.rfl)
      (fun hxy => hxy.2)
      (fun _ _ hxy hyz => hxy.trans hyz)
  · intro hambient
    by_cases heq : left = right
    · subst right
      exact Reachable.rfl
    · exact (boundaryConnectivityState_adj G vertex left right).2
        ⟨heq, hambient⟩ |>.reachable

/-- Two graphs induce the same labelled boundary state exactly when they
induce the same reachability relation on every pair of represented ports. -/
theorem boundaryConnectivityState_eq_iff
    (first second : SimpleGraph V) (vertex : Port → V) :
    boundaryConnectivityState first vertex =
        boundaryConnectivityState second vertex ↔
      ∀ left right : Port,
        first.Reachable (vertex left) (vertex right) ↔
          second.Reachable (vertex left) (vertex right) := by
  constructor
  · intro hstate left right
    rw [← boundaryConnectivityState_reachable_iff first vertex left right,
      hstate, boundaryConnectivityState_reachable_iff second vertex left right]
  · intro hreach
    ext left right
    simp only [boundaryConnectivityState_adj]
    exact and_congr_right fun _ => hreach left right

/-- The Boolean adjacency matrix is an injective code for finite simple
graphs.  It provides a deliberately coarse but explicit state-count bound. -/
noncomputable def adjacencyMatrixCode
    (G : SimpleGraph Port) : Port → Port → Bool := by
  classical
  exact fun left right => decide (G.Adj left right)

theorem adjacencyMatrixCode_injective [DecidableEq Port] :
    Function.Injective (adjacencyMatrixCode (Port := Port)) := by
  classical
  intro first second hcode
  ext left right
  have hentry := congrFun (congrFun hcode left) right
  simpa only [adjacencyMatrixCode, decide_eq_decide] using hentry

/-- A labelled connectivity state on `n` ports has at most `2^(n*n)` possible
values.  Symmetry, looplessness, and transitivity make the true count much
smaller; the coarse bound is convenient for pumping. -/
theorem card_simpleGraph_le_two_pow_sq
    [Fintype Port] [DecidableEq Port] :
    Fintype.card (SimpleGraph Port) ≤
      2 ^ (Fintype.card Port * Fintype.card Port) := by
  calc
    Fintype.card (SimpleGraph Port) ≤
        Fintype.card (Port → Port → Bool) :=
      Fintype.card_le_of_injective adjacencyMatrixCode
        adjacencyMatrixCode_injective
    _ = 2 ^ (Fintype.card Port * Fintype.card Port) := by
      simp only [Fintype.card_fun, Fintype.card_bool, pow_mul]

end SimpleGraph
