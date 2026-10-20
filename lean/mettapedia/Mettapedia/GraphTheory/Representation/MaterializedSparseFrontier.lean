import Mettapedia.GraphTheory.Representation.SparseFrontier
import Mettapedia.GraphTheory.Representation.EdgeListToMatrixModule

/-!
# From an authored matrix-construction module to sparse walk semantics

The existing module reader recovers the authored construction theory. Its
actual construction path ends in a matrix expression. Existing row expansion
and CSR packing then expose that matrix to the shared sparse traversal.
The resulting counts concern walks in the original edge-list graph meaning.

No new module grammar, reader, graph evaluator or rewrite table is introduced.
The source module's canonical text format and its native implementation
boundaries remain those of `EdgeListToMatrixModule`.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Representation.MaterializedSparseFrontier

open Mettapedia.GSLT.LanguageDef

variable {n : Nat}

/-- The matrix expression reached by the authored construction path. -/
def matrix (graph : EdgeList.Rep n) : AdjacencyMatrix.Rep n :=
  (EdgeListToMatrixLanguageDef.buildExpr .empty graph.entries).denote

/-- Existing row expansion and packing expose the constructed matrix. -/
def packed (graph : EdgeList.Rep n) : CSR.Rep n :=
  Transformations.rowsToCSR (Transformations.matrixToRows (matrix graph))

theorem packed_denote (graph : EdgeList.Rep n) :
    CSR.denote (packed graph) = EdgeList.denote graph := by
  rw [packed, Transformations.rowsToCSR_commutes, Transformations.matrixToRows_commutes]
  unfold matrix
  rw [EdgeListToMatrixLanguageDef.complete_denotes_refinement]
  exact Transformations.toMatrix_commutes (EdgeList.presentation n) graph

/-- The supplied sparse evaluator counts walks in the independently denoted
input graph, after the actual authored materialization endpoint is used. -/
theorem sparse_count_walks (R : Type*) [Semiring R] (graph : EdgeList.Rep n)
    (source target : Fin n) (length : Nat) :
    (SparseFrontier.ofCSR (packed graph)).iterate
        (fun vertex => if source = vertex then (1 : R) else 0) length target =
      (Nat.card {walk : (EdgeList.denote graph).Walk source target |
        walk.length = length} : R) := by
  rw [SparseFrontier.csr_count_walks, packed_denote]

/-- One complete statement connects text reading, construction occurrences
and the sparse query's mathematical meaning. Construction and query costs
are kept distinct; the latter are supplied by `SparseFrontier.round_visits`.
-/
theorem module_to_sparse_walks (R : Type*) [Semiring R] (graph : EdgeList.Rep n)
    (source target : Fin n) (length : Nat) :
    (ModuleFormat.readText? ModuleFormat.upstreamLimits EdgeListToMatrixModule.moduleText).bind
        (fun parsed => parsed.val.exports.head?.bind (fun entry =>
          ModuleFormat.Portable.admitSpecification? EdgeListToMatrixModule.schema
            ModuleFormat.Portable.exportsCodec entry.spec)) =
        some EdgeListToMatrixModule.quoted ∧
      (EdgeListToMatrixModule.constructionPath graph.entries .empty).length =
        graph.entries.length + 1 ∧
      (SparseFrontier.ofCSR (packed graph)).iterate
          (fun vertex => if source = vertex then (1 : R) else 0) length target =
        (Nat.card {walk : (EdgeList.denote graph).Walk source target |
          walk.length = length} : R) :=
  ⟨EdgeListToMatrixModule.read_moduleText_export,
    EdgeListToMatrixModule.constructionPath_length _ _,
    sparse_count_walks R graph source target length⟩

end Mettapedia.GraphTheory.Representation.MaterializedSparseFrontier
