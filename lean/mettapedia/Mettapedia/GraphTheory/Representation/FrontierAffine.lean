import Mettapedia.GraphTheory.Representation.MatrixSemantics
import Mettapedia.Algebra.MatrixAffineSummary

/-!
# Graph frontiers as ordered affine actions

A row-frontier update is the existing matrix-affine action with transposed
adjacency and zero offset. Its zero/one adjacency coefficients commute with
every state weight, so the existing row recurrence agrees with the
column-vector convention of `MatrixAffineSummary` over any semiring.
The bridge therefore reuses the established action, ordered fold, prefix scan,
and blocked-scan laws instead of introducing another recursive evaluator.

Constant graph stretches recover `MatrixSemantics.frontier` at every prefix.
Changing graphs are processed in their supplied order: regrouping chunks is
exact, while reordering requires commuting updates. Two individually symmetric
graphs below give a concrete failure of unrestricted reordering.

These statements concern exact semiring arithmetic and mathematical lists.
They assert neither a running-time improvement nor a physical implementation
of matrix storage, parallel execution, or machine arithmetic.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Representation.FrontierAffine

open Mettapedia.Algebra
open MatrixSemantics
open Matrix
open scoped BigOperators RightActions

variable (R : Type*) [Semiring R] {n m : Nat}

/-- One row-frontier update, represented by the existing affine summary. -/
def graphUpdate (graph : AdjacencyMatrix.Rep n) : MatrixAffineSummary (Fin n) R :=
  ⟨(adjacency R graph).transpose, 0⟩

/-- The initial frontier has one occurrence at the chosen source. -/
def sourceVector (source : Fin n) : Fin n → R :=
  fun target => if source = target then 1 else 0

/-- Summaries use the affine monoid's execution order: the head acts first. -/
def summarize (graphs : List (AdjacencyMatrix.Rep n)) : MatrixAffineSummary (Fin n) R :=
  (graphs.map (graphUpdate R)).prod

/-- This is the existing affine run on the graph updates, not a new evaluator. -/
def run (graphs : List (AdjacencyMatrix.Rep n)) (initial : Fin n → R) : Fin n → R :=
  MatrixAffineSummary.run (graphs.map (graphUpdate R)) initial

/-- Retain the initial state and every subsequent frontier using `List.scanl`. -/
def trajectory (graphs : List (AdjacencyMatrix.Rep n)) (initial : Fin n → R) :
    List (Fin n → R) :=
  graphs.scanl (fun state graph => (graphUpdate R graph).act state) initial

theorem graphUpdate_act (graph : AdjacencyMatrix.Rep n) (state : Fin n → R) :
    (graphUpdate R graph).act state =
      fun target => ∑ middle, state middle * adjacency R graph middle target := by
  funext target
  simp only [graphUpdate, MatrixAffineSummary.act, Pi.add_apply, Pi.zero_apply,
    add_zero, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro middle _
  cases edge : graph.cell middle target <;> simp [adjacency_apply, edge]

/-- The actual frontier recurrence is one application of the affine action. -/
theorem graphUpdate_frontier (graph : AdjacencyMatrix.Rep n) (source : Fin n)
    (length : Nat) :
    (graphUpdate R graph).act (frontier R graph source length) =
      frontier R graph source (length + 1) := by
  rw [graphUpdate_act]
  rfl

theorem sourceVector_eq_frontier_zero (graph : AdjacencyMatrix.Rep n) (source : Fin n) :
    sourceVector R source = frontier R graph source 0 := rfl

theorem run_eq_summary (graphs : List (AdjacencyMatrix.Rep n)) (initial : Fin n → R) :
    run R graphs initial = (summarize R graphs).act initial :=
  MatrixAffineSummary.run_eq_prod_act _ _

@[simp] theorem run_nil (initial : Fin n → R) : run R [] initial = initial := rfl

@[simp] theorem run_cons (graph : AdjacencyMatrix.Rep n)
    (graphs : List (AdjacencyMatrix.Rep n)) (initial : Fin n → R) :
    run R (graph :: graphs) initial = run R graphs ((graphUpdate R graph).act initial) := rfl

theorem summarize_append (first second : List (AdjacencyMatrix.Rep n)) :
    summarize R (first ++ second) = summarize R first * summarize R second := by
  simp [summarize]

/-- Splitting a run changes its bracketing, retaining the order of updates. -/
theorem run_append (first second : List (AdjacencyMatrix.Rep n)) (initial : Fin n → R) :
    run R (first ++ second) initial = run R second (run R first initial) := by
  simp only [run_eq_summary, summarize_append, MatrixAffineSummary.act_mul]

/-- A constant stretch has the actual matrix power and no accumulated offset. -/
theorem summarize_constant (graph : AdjacencyMatrix.Rep n) (length : Nat) :
    summarize R (List.replicate length graph) =
      ⟨(adjacency R graph).transpose ^ length, 0⟩ := by
  rw [summarize, List.map_replicate, List.prod_replicate, MatrixAffineSummary.pow_eq]
  simp [graphUpdate]

theorem power_act_frontier (graph : AdjacencyMatrix.Rep n) (source : Fin n) (length : Nat) :
    ((graphUpdate R graph) ^ length).act (sourceVector R source) =
      frontier R graph source length := by
  induction length with
  | zero =>
      rw [pow_zero, MatrixAffineSummary.act_one]
      rfl
  | succ length inductionHypothesis =>
      rw [pow_succ, MatrixAffineSummary.act_mul, inductionHypothesis, graphUpdate_frontier]

/-- The generic constant-run action law computes the existing graph frontier. -/
theorem run_constant (graph : AdjacencyMatrix.Rep n) (source : Fin n) (length : Nat) :
    run R (List.replicate length graph) (sourceVector R source) =
      frontier R graph source length := by
  rw [run_eq_summary, summarize, List.map_replicate, List.prod_replicate,
    power_act_frontier]

/-- Every prefix summary acts on the same initial state. -/
theorem trajectory_eq_prefix_actions (graphs : List (AdjacencyMatrix.Rep n))
    (initial : Fin n → R) :
    trajectory R graphs initial =
      ((graphs.map (graphUpdate R)).scanl (· * ·) 1).map (fun summary => summary.act initial) := by
  simpa only [trajectory, List.scanl_map, MatrixAffineSummary.op_smul_eq_act] using
    (ActionFold.scanl_op_smul (graphs.map (graphUpdate R)) initial)

/-- No intermediate state is lost by the summary/prefix representation. -/
theorem trajectory_get (graphs : List (AdjacencyMatrix.Rep n)) (initial : Fin n → R)
    (index : Nat) (bound : index < (trajectory R graphs initial).length) :
    (trajectory R graphs initial)[index] = run R (graphs.take index) initial := by
  rw [run_eq_summary]
  have generic := ActionFold.getElem_scanl_op_smul
    (graphs.map (graphUpdate R)) initial index
    (by simpa only [trajectory, List.length_scanl, List.length_map] using bound)
  simpa only [trajectory, List.scanl_map, MatrixAffineSummary.op_smul_eq_act,
    summarize, List.map_take] using generic

/-- The entire constant-graph trajectory is the original length-indexed frontier. -/
theorem trajectory_constant (graph : AdjacencyMatrix.Rep n) (source : Fin n) (length : Nat) :
    trajectory R (List.replicate length graph) (sourceVector R source) =
      (List.range (length + 1)).map (fun count => frontier R graph source count) := by
  apply List.ext_getElem
  · simp [trajectory]
  · intro index firstBound secondBound
    have atMost : index ≤ length := by
      simpa only [trajectory, List.length_scanl, List.length_replicate,
        Nat.lt_succ_iff] using firstBound
    rw [trajectory_get R _ _ index firstBound]
    simp only [List.take_replicate, Nat.min_eq_left atMost, run_constant,
      List.getElem_map, List.getElem_range]

/-- Chunk products retain the complete ordered summary. -/
theorem summarize_chunks (chunks : List (List (AdjacencyMatrix.Rep n))) :
    summarize R chunks.flatten = (chunks.map (summarize R)).prod := by
  induction chunks with
  | nil => simp [summarize]
  | cons chunk chunks inductionHypothesis =>
      simp only [List.flatten_cons, summarize_append, inductionHypothesis,
        List.map_cons, List.prod_cons]

/-- The existing affine executor can consume one summary per chunk. -/
theorem run_chunks (chunks : List (List (AdjacencyMatrix.Rep n))) (initial : Fin n → R) :
    run R chunks.flatten initial =
      MatrixAffineSummary.run (chunks.map (summarize R)) initial := by
  rw [run_eq_summary, summarize_chunks, MatrixAffineSummary.run_eq_prod_act]

/-- Three-phase blocked scanning reproduces every original frontier, including
all chunk interiors rather than just the final state. -/
theorem trajectory_chunks (chunks : List (List (AdjacencyMatrix.Rep n)))
    (initial : Fin n → R) :
    trajectory R chunks.flatten initial =
      initial :: (List.zipWith
        (fun start chunk => (trajectory R chunk start).tail)
        ((chunks.map (summarize R)).scanl (fun state summary => summary.act state) initial)
        chunks).flatten := by
  have generic := ActionFold.scanl_op_smul_flatten
    (chunks.map (fun chunk => chunk.map (graphUpdate R))) initial
  rw [← List.map_flatten] at generic
  simpa only [List.map_map, List.scanl_map, List.zipWith_map_right,
    MatrixAffineSummary.op_smul_eq_act, trajectory, summarize, Function.comp_def] using generic

/-- A permutation is licensed by commuting summaries, not by associativity. -/
theorem run_perm {first second : List (AdjacencyMatrix.Rep n)}
    (permutation : first.Perm second)
    (commuting : ∀ firstGraph ∈ first, ∀ secondGraph ∈ first,
      Commute (graphUpdate R firstGraph) (graphUpdate R secondGraph))
    (initial : Fin n → R) : run R first initial = run R second initial := by
  simpa only [run, MatrixAffineSummary.run, List.foldl_map,
    MatrixAffineSummary.op_smul_eq_act] using
    (ActionFold.foldl_map_op_smul_perm (graphUpdate R) permutation commuting initial)

/-! ## Relabelling all states and graph updates together -/

/-- Vertex reindexing acts on vectors by the inverse coordinate map. -/
def reindexState (vertices : Fin n ≃ Fin m) (state : Fin n → R) : Fin m → R :=
  state ∘ vertices.symm

theorem reindexState_sourceVector (vertices : Fin n ≃ Fin m) (source : Fin n) :
    reindexState R vertices (sourceVector R source) = sourceVector R (vertices source) := by
  funext target
  simp [reindexState, sourceVector, Equiv.eq_symm_apply]

/-- The graph update intertwines the actual coordinate equivalence. -/
theorem graphUpdate_reindex (vertices : Fin n ≃ Fin m) (graph : AdjacencyMatrix.Rep n)
    (state : Fin n → R) :
    (graphUpdate R (reindex vertices graph)).act (reindexState R vertices state) =
      reindexState R vertices ((graphUpdate R graph).act state) := by
  unfold graphUpdate MatrixAffineSummary.act
  simp only [add_zero]
  rw [← adjacency_reindex R vertices graph]
  change (adjacency R graph).transpose.submatrix vertices.symm vertices.symm *ᵥ
      (state ∘ vertices.symm) = ((adjacency R graph).transpose *ᵥ state) ∘ vertices.symm
  rw [Matrix.submatrix_mulVec_equiv]
  simp [Function.comp_def]

theorem run_reindex (vertices : Fin n ≃ Fin m) (graphs : List (AdjacencyMatrix.Rep n))
    (initial : Fin n → R) :
    run R (graphs.map (reindex vertices)) (reindexState R vertices initial) =
      reindexState R vertices (run R graphs initial) := by
  induction graphs generalizing initial with
  | nil => rfl
  | cons graph graphs inductionHypothesis =>
      simp only [List.map_cons, run_cons, graphUpdate_reindex, inductionHypothesis]

/-- Relabelling transports the whole trajectory, not merely its endpoint. -/
theorem trajectory_reindex (vertices : Fin n ≃ Fin m) (graphs : List (AdjacencyMatrix.Rep n))
    (initial : Fin n → R) :
    trajectory R (graphs.map (reindex vertices)) (reindexState R vertices initial) =
      (trajectory R graphs initial).map (reindexState R vertices) := by
  induction graphs generalizing initial with
  | nil => rfl
  | cons graph graphs inductionHypothesis =>
      simp only [trajectory, List.map_cons, List.scanl_cons]
      rw [graphUpdate_reindex]
      exact congrArg (List.cons (reindexState R vertices initial)) (inductionHypothesis _)

namespace Controls

def firstEdge : AdjacencyMatrix.Rep 3 :=
  Transformations.toMatrix (EdgeList.presentation 3) ⟨[⟨0, 1⟩]⟩

def secondEdge : AdjacencyMatrix.Rep 3 :=
  Transformations.toMatrix (EdgeList.presentation 3) ⟨[⟨1, 2⟩]⟩

/-- The constant-graph adapter recovers an independently checked walk count. -/
theorem constant_path_counts_two_returns :
    run Nat (List.replicate 2 MatrixSemantics.Controls.path3) (sourceVector Nat 1) 1 = 2 := by
  rw [run_constant]
  exact MatrixSemantics.Controls.path3_frontier_counts_two_returns

/-- Symmetric graph matrices need not commute as successive updates. -/
theorem symmetric_updates_reorder_changes_endpoint :
    (adjacency Nat firstEdge).IsSymm ∧ (adjacency Nat secondEdge).IsSymm ∧
      run Nat [firstEdge, secondEdge] (sourceVector Nat 0) 2 = 1 ∧
      run Nat [secondEdge, firstEdge] (sourceVector Nat 0) 2 = 0 := by
  let : DecidableRel (AdjacencyMatrix.denote firstEdge).Adj :=
    MatrixBridge.denoteDecidableRel firstEdge
  let : DecidableRel (AdjacencyMatrix.denote secondEdge).Adj :=
    MatrixBridge.denoteDecidableRel secondEdge
  refine ⟨SimpleGraph.isSymm_adjMatrix _, SimpleGraph.isSymm_adjMatrix _, ?_⟩
  constructor <;> decide

theorem graph_updates_do_not_commute :
    ¬ Commute (graphUpdate Nat firstEdge) (graphUpdate Nat secondEdge) := by
  intro commuting
  have same := congrArg (fun summary : MatrixAffineSummary (Fin 3) Nat =>
    summary.act (sourceVector Nat 0) 2) commuting.eq
  have different :
      (graphUpdate Nat firstEdge * graphUpdate Nat secondEdge).act (sourceVector Nat 0) 2 ≠
        (graphUpdate Nat secondEdge * graphUpdate Nat firstEdge).act (sourceVector Nat 0) 2 := by
    decide
  exact different same

end Controls

end Mettapedia.GraphTheory.Representation.FrontierAffine
