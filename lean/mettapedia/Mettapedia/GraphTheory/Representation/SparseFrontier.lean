import Mettapedia.GraphTheory.Representation.NeighborTraversal
import Mettapedia.GraphTheory.Representation.MatrixSemantics
import Mettapedia.GSLT.Dynamics.OrderedListFold
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# One sparse traversal semantics for adjacency rows and CSR

Both storage layouts supply the same neighbor-enumeration contract. The shared
ordered-fold GSLT then visits each row entry exactly once. Its independent
list-fold endpoint is the dense adjacency action, and repeated sparse rounds
are the existing matrix frontier and walk count.

The edge-visit account counts neither row-header access nor list slicing,
matrix construction, coefficient arithmetic or memory allocation. Packing
rows preserves their actual lists, not only the graph they describe.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Representation.SparseFrontier

open scoped BigOperators
open NeighborEnumeration

open Mettapedia.GSLT.Dynamics

variable {n : Nat}

local instance (graph : AdjacencyRows.Rep n) : DecidableRel (AdjacencyRows.denote graph).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∈ graph.row _))

local instance (graph : CSR.Rep n) : DecidableRel (CSR.denote graph).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∈ CSR.row graph _))

local instance (graph : AdjacencyMatrix.Rep n) :
    DecidableRel (AdjacencyMatrix.denote graph).Adj := MatrixBridge.denoteDecidableRel graph

def ofRows (graph : AdjacencyRows.Rep n) : NeighborEnumeration (AdjacencyRows.denote graph) where
  row := graph.row
  nodup := graph.nodup
  mem_iff _ _ := Iff.rfl

def ofCSR (graph : CSR.Rep n) : NeighborEnumeration (CSR.denote graph) :=
  ofRows (Transformations.csrToRows graph)

/-- Matrix expansion uses the existing proved refinement, including its
no-duplication law; it does not invent a second matrix-to-row algorithm. -/
def ofMatrix (graph : AdjacencyMatrix.Rep n) : NeighborEnumeration (AdjacencyMatrix.denote graph) :=
  (ofRows (Transformations.matrixToRows graph)).transport
    (Transformations.matrixToRows_commutes graph)

theorem packed_update_eq {A : Type*} [AddMonoid A]
    (graph : AdjacencyRows.Rep n) (values : Fin n → A) (target : Fin n) :
    ((ofCSR (Transformations.rowsToCSR graph)).update values target) =
      (ofRows graph).update values target := by
  unfold NeighborEnumeration.update
  simp only [ofCSR, ofRows, Transformations.csrToRows_rowsToCSR]

/-- Packing preserves each sparse iteration, including for a noncommutative
additive monoid: its proof uses equality of rows, not just their permutation. -/
theorem packed_iterate_eq {A : Type*} [AddMonoid A]
    (graph : AdjacencyRows.Rep n) (initial : Fin n → A) (length : Nat) :
    (ofCSR (Transformations.rowsToCSR graph)).iterate initial length =
      (ofRows graph).iterate initial length := by
  induction length with
  | zero => rfl
  | succ length inductionHypothesis =>
      simp only [iterate, inductionHypothesis]
      funext target
      exact congrArg Measured.value (packed_update_eq graph _ target)

/-- A sparse round on any enumeration of the matrix's graph is the existing
row-frontier recurrence; symmetry supplies the row/column convention bridge. -/
theorem iterate_eq_frontier (R : Type*) [Semiring R]
    (graph : AdjacencyMatrix.Rep n)
    (enumeration : NeighborEnumeration (AdjacencyMatrix.denote graph))
    (source : Fin n) (length : Nat) :
    enumeration.iterate (fun target => if source = target then (1 : R) else 0) length =
      MatrixSemantics.frontier R graph source length := by
  induction length with
  | zero => rfl
  | succ length inductionHypothesis =>
      funext target
      change (enumeration.update (enumeration.iterate _ length) target).value = _
      rw [update_eq_row_action, inductionHypothesis]
      rfl

theorem rows_iterate_eq_frontier (R : Type*) [Semiring R]
    (graph : AdjacencyRows.Rep n) (source : Fin n) (length : Nat) :
    (ofRows graph).iterate (fun target => if source = target then (1 : R) else 0) length =
      MatrixSemantics.frontier R (Transformations.rowsToMatrix graph) source length := by
  simpa only [iterate_transport] using iterate_eq_frontier R (Transformations.rowsToMatrix graph)
    ((ofRows graph).transport (Transformations.rowsToMatrix_commutes graph).symm) source length

theorem csr_iterate_eq_frontier (R : Type*) [Semiring R]
    (graph : CSR.Rep n) (source : Fin n) (length : Nat) :
    (ofCSR graph).iterate (fun target => if source = target then (1 : R) else 0) length =
      MatrixSemantics.frontier R (Transformations.rowsToMatrix (Transformations.csrToRows graph))
        source length := by
  exact rows_iterate_eq_frontier R (Transformations.csrToRows graph) source length

theorem rows_count_walks (R : Type*) [Semiring R]
    (graph : AdjacencyRows.Rep n) (source target : Fin n) (length : Nat) :
    (ofRows graph).iterate (fun vertex => if source = vertex then (1 : R) else 0) length target =
      (Nat.card {walk : (AdjacencyRows.denote graph).Walk source target |
        walk.length = length} : R) := by
  rw [rows_iterate_eq_frontier, MatrixSemantics.frontier_eq_walk_count,
    ← Nat.card_eq_fintype_card, Transformations.rowsToMatrix_commutes]

theorem csr_count_walks (R : Type*) [Semiring R]
    (graph : CSR.Rep n) (source target : Fin n) (length : Nat) :
    (ofCSR graph).iterate (fun vertex => if source = vertex then (1 : R) else 0) length target =
      (Nat.card {walk : (CSR.denote graph).Walk source target |
        walk.length = length} : R) := by
  exact rows_count_walks R (Transformations.csrToRows graph) source target length

/-- Every complete operational row path has the specified sum and exact
transition count. The relation cannot invent an alternative endpoint. -/
theorem traversal_complete {A : Type} [AddMonoid A]
    {graph : SimpleGraph (Fin n)} (enumeration : NeighborEnumeration graph)
    (values : Fin n → A) (target : Fin n) (result : A)
    (path : (OrderedListFold.theory (fun total vertex => total + values vertex)).RewritePath
      (.active (enumeration.row target) 0) (.done result)) :
    result = (enumeration.update values target).value ∧
      path.length = (enumeration.update values target).work + 1 :=
  OrderedListFold.complete_path _ _ _ _ path

/-- Construct an actual operational witness, without supplying its answer
as a premise to any transition. -/
def traversalPath {A : Type} [AddMonoid A]
    {graph : SimpleGraph (Fin n)} (enumeration : NeighborEnumeration graph)
    (values : Fin n → A) (target : Fin n) :
    (OrderedListFold.theory (fun total vertex => total + values vertex)).RewritePath
      (.active (enumeration.row target) 0) (.done (enumeration.update values target).value) :=
  OrderedListFold.runPath _ _ _

/-- A whole sparse round visits twice the number of undirected edges. This
accounts for neighbor entries, not machine instructions or elapsed time. -/
theorem round_visits {A : Type*} [AddMonoid A]
    {graph : SimpleGraph (Fin n)} [DecidableRel graph.Adj]
    (enumeration : NeighborEnumeration graph) (values : Fin n → A) :
    (∑ target, (enumeration.update values target).work) = 2 * graph.edgeFinset.card := by
  simp_rw [update_work_eq_degree]
  exact graph.sum_degrees_eq_twice_card_edges

end Mettapedia.GraphTheory.Representation.SparseFrontier
