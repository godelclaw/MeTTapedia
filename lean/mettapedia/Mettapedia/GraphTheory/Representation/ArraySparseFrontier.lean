import Mettapedia.GSLT.Dynamics.ArrayFoldCorrespondence
import Mettapedia.GraphTheory.Representation.WeightedSparseFrontier

/-!
# Packed array realization of sparse graph traversal

The CSR payload is compiled once to an immutable backing array. A query selects
the existing row's bounded slice, and the direct indexed fold reads that slice
without allocating a list. The source row's order and duplicates, when present
in a weighted row, are retained. Scalar arithmetic remains exact semiring
arithmetic; this is not a machine-floating-point or C-heap verification.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Representation.ArraySparseFrontier

open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.LanguageDef.CArray0SequenceHosting
open Mettapedia.Algebra
open Matrix

variable {n : Nat}

/-- Both headers and payload are actual arrays. Bounds are invariants of
the compiled descriptor, not work repeated by the query loop. -/
structure PackedCSR (n : Nat) where
  offsets : Array Nat
  offsets_size : offsets.size = n + 1
  cells : Array (Fin n)
  ordered : Monotone (fun index : Fin (n + 1) =>
    offsets[index.val]'(by rw [offsets_size]; exact index.isLt))
  last : offsets[n]'(by rw [offsets_size]; omega) = cells.size

def PackedCSR.offset (packed : PackedCSR n) (index : Fin (n + 1)) : Nat :=
  packed.offsets[index.val]'(by rw [packed.offsets_size]; exact index.isLt)

/-- Compilation is explicit and may be amortized over multiple queries. -/
def compileCSR (graph : CSR.Rep n) : PackedCSR n where
  offsets := Array.ofFn graph.offset
  offsets_size := by simp
  cells := graph.neighbors.toArray
  ordered := by simpa using graph.offset_mono
  last := by simpa using graph.offset_last

/-- Row slices retain the same compiled backing array and advance only
indices. No list-to-array conversion occurs in this function or its loop. -/
def csrSlice (packed : PackedCSR n) (vertex : Fin n) : StackSlice (Fin n) where
  cells := packed.cells
  start := packed.offset vertex.castSucc
  count := packed.offset vertex.succ - packed.offset vertex.castSucc
  inBounds := by
    have ordered := packed.ordered (Fin.le_of_lt vertex.castSucc_lt_succ)
    have bounded := packed.ordered
      (show vertex.succ ≤ (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) from by
        change vertex.val + 1 ≤ n
        omega)
    change packed.offset vertex.castSucc ≤ packed.offset vertex.succ at ordered
    change packed.offset vertex.succ ≤ packed.offset ⟨n, Nat.lt_succ_self n⟩ at bounded
    have last : packed.offset ⟨n, Nat.lt_succ_self n⟩ = packed.cells.size := packed.last
    rw [last] at bounded
    omega

theorem csrSlice_toList (graph : CSR.Rep n) (vertex : Fin n) :
    (csrSlice (compileCSR graph) vertex).toList = CSR.row graph vertex := by
  simp only [ArrayFold.slice_toList, csrSlice, compileCSR, PackedCSR.offset,
    Array.getElem_ofFn, CSR.row, CSR.start, CSR.stop]

/-- The packed native-style loop, independently defined through indexed reads. -/
def csrUpdate {R : Type} [AddMonoid R] (packed : PackedCSR n)
    (values : Fin n → R) (target : Fin n) : R :=
  ArrayFold.run (fun total vertex => total + values vertex) (csrSlice packed target) 0

theorem csrUpdate_eq {R : Type} [AddMonoid R] (graph : CSR.Rep n)
    (values : Fin n → R) (target : Fin n) :
    csrUpdate (compileCSR graph) values target = ((SparseFrontier.ofCSR graph).update values target).value := by
  rw [csrUpdate, ArrayFold.run_eq_foldl, csrSlice_toList]
  rfl

/-- Counted target execution agrees in result and entry reads with the
independent source neighbor traversal. -/
theorem csr_counted_eq {R : Type} [AddMonoid R] (graph : CSR.Rep n)
    (values : Fin n → R) (target : Fin n) :
    ArrayFold.runCounted (fun total vertex => total + values vertex) (csrSlice (compileCSR graph) target) 0 =
      (((SparseFrontier.ofCSR graph).update values target).value,
        ((SparseFrontier.ofCSR graph).update values target).work) := by
  rw [ArrayFold.runCounted_exact, ← csrUpdate, csrUpdate_eq]
  congr 1
  exact (ArrayFold.slice_toList_length (csrSlice (compileCSR graph) target)).symm.trans
    (congrArg List.length (csrSlice_toList graph target))

/-- Weighted rows use the same array loop, retaining arbitrary repeated
coordinates and their coefficient order. -/
def weightedRow {I R : Type} [Add R] [Mul R] (cells : Array (I × R))
    (values : I → R) (initial : R) : R :=
  ArrayFold.run (fun total entry => total + entry.2 * values entry.1)
    (StackSlice.ofArray cells) initial

theorem weightedRow_eq {I R : Type} [Add R] [Mul R] (cells : Array (I × R))
    (values : I → R) (initial : R) :
    weightedRow cells values initial = SparseLinearMap.rowRun cells.toList values initial := by
  rw [weightedRow, ArrayFold.run_eq_foldl, StackSlice.toList_ofArray]
  rfl

/-- Immutable array compilation of every sparse row, independent of graph
symmetry or simple-graph invariants. -/
def compileRows {I J R : Type} (kernel : SparseLinearMap I J R) : J → Array (I × R) :=
  fun output => (kernel output).toArray

theorem compiled_apply_eq {I J R : Type} [Zero R] [Add R] [Mul R]
    (kernel : SparseLinearMap I J R) (values : I → R) (output : J) :
    weightedRow (compileRows kernel output) values 0 = kernel.apply values output := by
  rw [weightedRow_eq]
  simp only [compileRows, List.toList_toArray]
  rfl

/-- Dense meaning is preserved after independent array lowering. -/
theorem compiled_apply_eq_mulVec {I J R : Type} [Semiring R] [Fintype I] [DecidableEq I]
    (kernel : SparseLinearMap I J R) (values : I → R) (output : J) :
    weightedRow (compileRows kernel output) values 0 = (kernel.toMatrix *ᵥ values) output := by
  rw [compiled_apply_eq, SparseLinearMap.apply_eq_mulVec]

end Mettapedia.GraphTheory.Representation.ArraySparseFrontier
