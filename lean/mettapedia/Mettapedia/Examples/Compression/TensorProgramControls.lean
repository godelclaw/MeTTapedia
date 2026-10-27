import Mettapedia.Algorithms.Compression.PartialDag
import Mettapedia.Algorithms.Compression.TypedDag
import Mettapedia.Algorithms.Compression.TypedDagRegion

/-! Partial-operator DAG laws. Typed recipe admission, TP1 byte correspondence,
module projection and numerical kernels are independently checked by the native
tensor-program gate; these declarations do not verify the C implementation. -/

open Mettapedia.Algorithms.Compression

#print axioms PartialDag.arguments_append
#print axioms PartialDag.first_fault
#print axioms PartialDag.argument_fault_prevents_operator
#print axioms PartialDag.evaluate_unfold
#print axioms PartialDag.Controls.unused_fault_preserves_roots_and_duplicates
#print axioms PartialDag.Controls.used_fault_reaches_only_its_dependents
#print axioms PartialDag.Controls.argument_order_selects_the_first_fault
#print axioms PartialDag.Controls.malformed_reference_is_not_an_operator_fault

namespace TypedProgramControls

open KolmogorovComplexity TypedDag CompactDag

inductive Payload where
  | number : Nat → Payload
  | mask : Bool → Payload
  | opaque : Payload
  deriving DecidableEq, Repr

def kind : Payload → Option Bool
  | .number _ => some false
  | .mask _ => some true
  | .opaque => none

def leafType (bytes : BinString) : Option Bool :=
  some (bytes = [false])

def fetch (bytes : BinString) : Option Payload :=
  if bytes = [true] then some .opaque
  else if bytes = [false] then some (.mask true) else some (.number 7)

def contract (tag : BinString) : Option (Contract Bool) :=
  if tag = [] then some ⟨[false, false], false⟩ else some ⟨[false], false⟩

def kernel (tag : BinString) : List Payload → Option Payload
  | [.number first, .number second] => if tag = [] then some (.number (first + second)) else none
  | [.number _] => some (.mask true)
  | _ => none

theorem declared_sort_does_not_grant_a_value_kind :
    leafValue kind leafType fetch [true] = none := by decide

theorem wrong_kernel_result_is_rejected :
    nodeValue kind contract kernel [false] [some (.number 7)] = none := by decide

theorem wrong_operand_sort_is_rejected_statically :
    inferRecords leafType contract [.leaf [], .leaf [false], .node [] [0, 1]] [] = none := by decide

theorem well_typed_kernel_failure_does_not_erase_an_independent_root :
    let forest : Forest := ⟨[1, 0], [.leaf [], .node [false] [0]]⟩
    inferRecords leafType contract forest.records [] = some [false, false] ∧
      CompactDag.evaluate (leafValue kind leafType fetch) (nodeValue kind contract kernel) forest =
        some [none, some (.number 7)] := by decide

end TypedProgramControls

#print axioms TypedDag.checked_fits
#print axioms TypedDag.gather_aligned
#print axioms TypedDag.arguments_sorted
#print axioms TypedDag.operator_arguments_sorted
#print axioms TypedDag.record_sound
#print axioms TypedDag.inferRecords_sound
#print axioms TypedDag.roots_sound
#print axioms TypedProgramControls.declared_sort_does_not_grant_a_value_kind
#print axioms TypedProgramControls.wrong_kernel_result_is_rejected
#print axioms TypedProgramControls.wrong_operand_sort_is_rejected_statically
#print axioms TypedProgramControls.well_typed_kernel_failure_does_not_erase_an_independent_root

#print axioms TypedDagRegion.indices_mem_iff
#print axioms TypedDagRegion.indices_zero_mem_iff
#print axioms TypedDagRegion.tuples_mem_iff
#print axioms TypedDagRegion.extensions_mem_iff
#print axioms TypedDagRegion.extension_infers
#print axioms TypedDagRegion.Controls.repeated_operands_remain_independent_positions
#print axioms TypedDagRegion.Controls.absent_sort_yields_no_operand_tuple
#print axioms TypedDagRegion.Controls.duplicate_instructions_preserve_occurrences
