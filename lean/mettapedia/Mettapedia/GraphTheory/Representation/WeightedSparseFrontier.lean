import Mettapedia.Algebra.SparseLinearMap
import Mettapedia.GraphTheory.Representation.SparseFrontier

/-!
# Neighbor enumeration as a sparse linear operator

The unweighted graph traversal is the unit-coefficient instance of the general
occurrence-preserving sparse operator. This bridge connects the established
row and CSR interfaces to weighted composition without re-proving their walk
semantics or silently discarding parallel occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Representation.WeightedSparseFrontier

open Mettapedia.Algebra
open scoped BigOperators

variable {V R : Type*} [Semiring R] {graph : SimpleGraph V}

def ofEnumeration (enumeration : NeighborEnumeration graph) : SparseLinearMap V V R :=
  fun output => (enumeration.row output).map (fun input => (input, 1))

theorem apply_ofEnumeration (enumeration : NeighborEnumeration graph) (values : V → R) :
    (ofEnumeration enumeration).apply values = enumeration.act values := by
  funext output
  simp only [SparseLinearMap.apply_eq, ofEnumeration, List.map_map,
    Function.comp_def, one_mul, NeighborEnumeration.act, NeighborEnumeration.update_value]

theorem matrix_ofEnumeration [Fintype V] [DecidableEq V] [DecidableRel graph.Adj]
    (enumeration : NeighborEnumeration graph) :
    (ofEnumeration enumeration : SparseLinearMap V V R).toMatrix = graph.adjMatrix R := by
  ext output input
  have same := congrFun (apply_ofEnumeration enumeration (Pi.single input (1 : R))) output
  simp only [SparseLinearMap.apply_eq_mulVec, NeighborEnumeration.act_eq_mulVec,
    Matrix.mulVec_single_one] at same
  exact same

theorem visits_ofEnumeration (enumeration : NeighborEnumeration graph) (output : V) :
    (ofEnumeration enumeration : SparseLinearMap V V R).visits output =
      (enumeration.row output).length := by simp [ofEnumeration, SparseLinearMap.visits]

namespace Controls

def duplicated : SparseLinearMap Unit Unit Nat := fun _ => [((), 2), ((), 3)]
def aggregated : SparseLinearMap Unit Unit Nat := fun _ => [((), 5)]

/-- Aggregation preserves the linear meaning but changes the operation account. -/
theorem same_matrix_different_visits :
    duplicated.toMatrix = aggregated.toMatrix ∧
      duplicated.visits () = 2 ∧ aggregated.visits () = 1 := by
  constructor
  · ext output input
    cases output
    cases input
    decide
  · decide

/-- Composition multiplies outer and inner coefficients in their actual order. -/
def upper : Matrix (Fin 2) (Fin 2) Nat := !![0, 1; 0, 0]
def lower : Matrix (Fin 2) (Fin 2) Nat := !![0, 0; 1, 0]

def first : SparseLinearMap Unit Unit (Matrix (Fin 2) (Fin 2) Nat) := fun _ => [((), upper)]
def second : SparseLinearMap Unit Unit (Matrix (Fin 2) (Fin 2) Nat) := fun _ => [((), lower)]

theorem coefficient_order_matters :
    (first.compose second).apply (fun _ => 1) () ≠
      (second.compose first).apply (fun _ => 1) () := by decide

end Controls

end Mettapedia.GraphTheory.Representation.WeightedSparseFrontier
