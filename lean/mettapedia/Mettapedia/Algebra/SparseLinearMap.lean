import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mettapedia.GSLT.Dynamics.OrderedListFold

/-!
# Occurrence-preserving sparse semiring operators

Each output row stores ordered pairs of an input coordinate and a left
coefficient. Repeated coordinates are permitted and contribute additively.
The dense meaning sums coefficients at each coordinate; the sparse evaluator
instead traverses only stored occurrences. Their equality is proved, rather
than using the dense meaning as the implementation.

Composition expands pairs of occurrences in execution order. Its coefficients
multiply outer first, inner second, which matters over noncommutative semirings.
Duplicate aggregation is a mathematical quotient of this representation: it
does not preserve the entry count or the prefix trajectory.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra

open scoped BigOperators
open Matrix

/-- Ordered sparse rows; the carrier does not require finite input or output
types. Finiteness is needed only when comparing to ordinary matrices. -/
abbrev SparseLinearMap (Input Output R : Type*) := Output → List (Input × R)

namespace SparseLinearMap

variable {I J K R : Type*}

/-- Fold each stored occurrence. Duplicate input coordinates are not erased. -/
def rowRun [Add R] [Mul R] (entries : List (I × R)) (values : I → R) (initial : R) : R :=
  entries.foldl (fun total entry => total + entry.2 * values entry.1) initial

def apply [Zero R] [Add R] [Mul R] (kernel : SparseLinearMap I J R) (values : I → R) : J → R :=
  fun output => rowRun (kernel output) values 0

variable [Semiring R]

theorem rowRun_eq (entries : List (I × R)) (values : I → R) (initial : R) :
    rowRun entries values initial = initial + (entries.map (fun e => e.2 * values e.1)).sum := by
  induction entries generalizing initial with
  | nil => simp [rowRun]
  | cons entry rest ih =>
      simpa only [rowRun, List.foldl_cons, List.map_cons, List.sum_cons, add_assoc]
        using ih (initial + entry.2 * values entry.1)

theorem apply_eq (kernel : SparseLinearMap I J R) (values : I → R) (output : J) :
    kernel.apply values output = ((kernel output).map (fun e => e.2 * values e.1)).sum := by
  simp [apply, rowRun_eq]

section Dense

variable [DecidableEq I]

/-- Dense denotation sums all stored contributions to the selected cell. -/
def toMatrix (kernel : SparseLinearMap I J R) : Matrix J I R :=
  fun output input => ((kernel output).map
    (fun e => if e.1 = input then e.2 else 0)).sum

theorem toMatrix_nil : toMatrix (fun _ : J => ([] : List (I × R))) = 0 := by
  ext output input
  simp [toMatrix]

theorem toMatrix_row_cons (entry : I × R) (rest : List (I × R)) (input : I) :
    ((entry :: rest).map (fun e => if e.1 = input then e.2 else 0)).sum =
      (if entry.1 = input then entry.2 else 0) +
        (rest.map (fun e => if e.1 = input then e.2 else 0)).sum := by simp

variable [Fintype I]

private theorem row_dense (entries : List (I × R)) (values : I → R) :
    (entries.map (fun e => e.2 * values e.1)).sum =
      ∑ input, (entries.map (fun e => if e.1 = input then e.2 else 0)).sum * values input := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
      rw [← ih]
      congr 1
      simp [ite_mul, Finset.sum_ite_eq]

/-- Sparse occurrence traversal implements the independently defined dense
matrix-vector product. No no-duplication premise is needed. -/
theorem apply_eq_mulVec (kernel : SparseLinearMap I J R) (values : I → R) :
    kernel.apply values = kernel.toMatrix *ᵥ values := by
  funext output
  exact (apply_eq kernel values output).trans (row_dense (kernel output) values)

end Dense

/-- Compose in data-flow order: `first` acts before `second`. Each outer
occurrence expands the corresponding inner row without deduplication. -/
def compose (first : SparseLinearMap I J R) (second : SparseLinearMap J K R) :
    SparseLinearMap I K R := fun output =>
  (second output).flatMap (fun outer =>
    (first outer.1).map (fun inner => (inner.1, outer.2 * inner.2)))

def identity : SparseLinearMap I I R := fun input => [(input, 1)]

@[simp] theorem identity_compose (kernel : SparseLinearMap I J R) :
    identity.compose kernel = kernel := by
  funext output
  simp [compose, identity]

@[simp] theorem compose_identity (kernel : SparseLinearMap I J R) :
    kernel.compose identity = kernel := by
  funext output
  simp [compose, identity]

/-- Associativity holds at the ordered occurrence list, before taking any
matrix or result quotient. -/
theorem compose_assoc {L : Type*} (first : SparseLinearMap I J R)
    (second : SparseLinearMap J K R) (third : SparseLinearMap K L R) :
    (first.compose second).compose third = first.compose (second.compose third) := by
  funext output
  simp [compose, List.flatMap_assoc, List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def, mul_assoc]

private theorem sum_map_left_mul (entries : List (I × R)) (values : I → R) (coefficient : R) :
    (entries.map (fun e => coefficient * e.2 * values e.1)).sum =
      coefficient * (entries.map (fun e => e.2 * values e.1)).sum := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.map_cons, List.sum_cons, mul_add]
      rw [ih, mul_assoc]

theorem apply_compose (first : SparseLinearMap I J R) (second : SparseLinearMap J K R)
    (values : I → R) : (first.compose second).apply values = second.apply (first.apply values) := by
  funext output
  simp only [apply_eq, compose]
  induction second output with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
        List.map_cons, List.sum_cons, Function.comp_def]
      rw [sum_map_left_mul, ih]

/-- The denotation of sparse composition is ordinary matrix multiplication,
in the column-vector convention: second matrix times first matrix. -/
theorem toMatrix_compose [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (first : SparseLinearMap I J R) (second : SparseLinearMap J K R) :
    (first.compose second).toMatrix = second.toMatrix * first.toMatrix := by
  apply Matrix.ext
  intro output input
  have same := congrFun (apply_compose first second (Pi.single input 1)) output
  simp only [apply_eq_mulVec, Matrix.mulVec_single_one] at same
  exact same

/-- Entry counts distinguish representations even when their matrices agree. -/
def visits (kernel : SparseLinearMap I J R) (output : J) : Nat := (kernel output).length

theorem visits_compose (first : SparseLinearMap I J R) (second : SparseLinearMap J K R)
    (output : K) :
    (first.compose second).visits output =
      ((second output).map (fun outer => (first outer.1).length)).sum := by
  simp [visits, compose, List.length_flatMap]

theorem apply_eq_of_matrix_eq [Fintype I] [DecidableEq I]
    {first second : SparseLinearMap I J R} (same : first.toMatrix = second.toMatrix)
    (values : I → R) : first.apply values = second.apply values := by
  rw [apply_eq_mulVec, apply_eq_mulVec, same]

/-- Coefficient interpretation commutes with sparse execution, but need not
be injective. No claim that the readout retains information is required. -/
def map {S : Type*} [Semiring S] (coefficients : R →+* S)
    (kernel : SparseLinearMap I J R) : SparseLinearMap I J S :=
  fun output => (kernel output).map (fun entry => (entry.1, coefficients entry.2))

theorem apply_map {S : Type*} [Semiring S] (coefficients : R →+* S)
    (kernel : SparseLinearMap I J R) (values : I → R) :
    (kernel.map coefficients).apply (coefficients ∘ values) = coefficients ∘ kernel.apply values := by
  funext output
  simp only [apply_eq, map, List.map_map, Function.comp_def, map_list_sum, map_mul]

end SparseLinearMap

end Mettapedia.Algebra
