import Mettapedia.Machines.ResourceOwnership
import Mettapedia.GSLT.Core.PolicyFamilyContextClosure

/-!
# Exact tracing minimizes retained cells under complete path observations

The observation class consists of every finite `walk` starting at a valid
source root, including failed walks and complete endpoint cells. A reachable
cell has a successful finite root-path witness, proved by induction on the
existing reachability derivation. Consequently any candidate heap with the
same observations must retain that very cell at that very address.

The exact tracing collector attains the resulting lower bounds on allocated
cell count and declared bytes. This is a storage optimum for fixed-address,
full-cell observations. It is not an optimum for moving or compressing heaps,
recomputation, physical allocator overhead, collection time, or unrestricted
program contexts. A different observation or realization class needs its own
comparison. Each current allocation set is finite; the address universe need
not be finite and no future growth bound is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResourceOwnership.Optimality

universe uValue uOwner

variable {Address : Type} {Value : Type uValue} {Owner : Type uOwner}
  [DecidableEq Address]

/-- Every reachable resource has a finite successful path from an actual,
allocated owner-root. Shared graphs and cycles need no acyclicity premise. -/
theorem live_path_witness (heap : Heap Address Value) (roots : Roots Owner Address)
    {address : Address} (live : Live heap roots address) :
    ∃ pair ∈ roots, pair.2 ∈ heap.allocated ∧
      ∃ path cell, walk heap pair.2 path = some (address, cell) := by
  induction live with
  | @root address rooted =>
      obtain ⟨pair, member, same⟩ := Finset.mem_image.mp rooted.2
      obtain ⟨cell, found⟩ := (heap.allocated_iff address).mp rooted.1
      refine ⟨pair, member, same.symm ▸ rooted.1, [], cell, ?_⟩
      simp only [walk, same, found, Option.map_some]
  | @step previous address prior edge ih =>
      obtain ⟨pair, member, valid, path, previousCell, reached⟩ := ih
      obtain ⟨edgeCell, found, reference⟩ := edge
      obtain ⟨cell, atAddress⟩ := (heap.allocated_iff address).mp
        (heap.closed previous edgeCell found address reference)
      refine ⟨pair, member, valid, path ++ [address], cell, ?_⟩
      rw [walk_append_of_success heap path [address] reached]
      simp only [walk, found, Option.bind_some, if_pos reference, atAddress, Option.map_some]

/-- All finite path observations at source-valid roots are equal. Invalid
source root addresses are not capabilities to newly allocated candidate cells. -/
def SameRootPaths (source candidate : Heap Address Value) (roots : Roots Owner Address) : Prop :=
  ∀ pair ∈ roots, pair.2 ∈ source.allocated → ∀ path,
    walk candidate pair.2 path = walk source pair.2 path

/-- Complete path observations force full lookup equality at every live
address. Retention is the conclusion, not a premise of the comparison. -/
theorem live_cell_forced (source candidate : Heap Address Value) (roots : Roots Owner Address)
    (observations : SameRootPaths source candidate roots) {address : Address}
    (live : Live source roots address) : candidate.lookup address = source.lookup address := by
  obtain ⟨pair, member, valid, path, cell, reached⟩ := live_path_witness source roots live
  have sourceLookup := walk_success_lookup source path reached
  have candidateLookup := walk_success_lookup candidate path
    ((observations pair member valid path).trans reached)
  exact candidateLookup.trans sourceLookup.symm

/-- Any observationally equivalent fixed-address heap allocates the entire
transitive source footprint, including shared or cyclic descendants. -/
theorem footprint_subset_candidate (source candidate : Heap Address Value)
    (roots : Roots Owner Address) (observations : SameRootPaths source candidate roots) :
    footprint source roots ⊆ candidate.allocated := by
  intro address member
  have live := (mem_footprint source roots address).mp member
  obtain ⟨cell, found⟩ := (source.allocated_iff address).mp (live_allocated source roots live)
  exact (candidate.allocated_iff address).mpr
    ⟨cell, (live_cell_forced source candidate roots observations live).trans found⟩

theorem retained_cells_le (source candidate : Heap Address Value)
    (roots : Roots Owner Address) (observations : SameRootPaths source candidate roots) :
    (footprint source roots).card ≤ candidate.allocated.card :=
  Finset.card_le_card (footprint_subset_candidate source candidate roots observations)

/-- Full-cell equality includes the declared byte weight, so extra candidate
allocations cannot reduce the cost of the cells forced by root observations. -/
theorem retained_bytes_le (source candidate : Heap Address Value)
    (roots : Roots Owner Address) (observations : SameRootPaths source candidate roots) :
    retainedBytes source roots ≤ allocatedBytes candidate := by
  calc
    retainedBytes source roots = ∑ address ∈ footprint source roots, cellBytes candidate address := by
      apply Finset.sum_congr rfl
      intro address member
      simp only [cellBytes, live_cell_forced source candidate roots observations
        ((mem_footprint source roots address).mp member)]
    _ ≤ allocatedBytes candidate :=
      Finset.sum_le_sum_of_subset (footprint_subset_candidate source candidate roots observations)

/-- Exact tracing belongs to the comparison class: all successful and failed
root paths retain their full observations. -/
theorem collect_same_root_paths (source : Heap Address Value) (roots : Roots Owner Address) :
    SameRootPaths source (collect source roots) roots := by
  intro pair member valid path
  exact walk_collect source roots (live_of_root source roots member valid) path

/-- Exact tracing attains the minimum number of allocated cells. -/
theorem collect_minimal_cells (source candidate : Heap Address Value)
    (roots : Roots Owner Address) (observations : SameRootPaths source candidate roots) :
    (collect source roots).allocated.card ≤ candidate.allocated.card :=
  retained_cells_le source candidate roots observations

/-- Exact tracing attains the minimum declared allocation bytes. -/
theorem collect_minimal_bytes (source candidate : Heap Address Value)
    (roots : Roots Owner Address) (observations : SameRootPaths source candidate roots) :
    allocatedBytes (collect source roots) ≤ allocatedBytes candidate := by
  rw [allocatedBytes_collect]
  exact retained_bytes_le source candidate roots observations

/-- The admissible collector and both lower bounds are stated together; no
runtime or alternative representation optimum is implied. -/
theorem collect_attains_minimum (source : Heap Address Value) (roots : Roots Owner Address) :
    SameRootPaths source (collect source roots) roots ∧
      ∀ candidate, SameRootPaths source candidate roots →
        (collect source roots).allocated.card ≤ candidate.allocated.card ∧
          allocatedBytes (collect source roots) ≤ allocatedBytes candidate := by
  refine ⟨collect_same_root_paths source roots, ?_⟩
  intro candidate observations
  exact ⟨collect_minimal_cells source candidate roots observations,
    collect_minimal_bytes source candidate roots observations⟩

/-! ## Shared cycles and insufficient observation controls -/

namespace Controls

open Examples

/-- Two owners share opposite nodes of the same cycle. Node zero is garbage. -/
def cycleRoots : Roots Nat (Fin 3) := {(0, 1), (1, 2)}

theorem cycle_not_zero {address : Fin 3} (live : Live cyclicHeap cycleRoots address) :
    address ≠ 0 := by
  induction live with
  | @root address rooted =>
      have rootAddress : address = 1 ∨ address = 2 := by
        simpa [Heap.toStore, rootAddresses, cycleRoots] using rooted.2
      rcases rootAddress with rfl | rfl <;> decide
  | @step previous address _ edge _ =>
      obtain ⟨cell, found, reference⟩ := edge
      change some (cyclicCell previous) = some cell at found
      cases found
      by_cases zero : previous = 0
      · have same : address = 1 := by simpa [cyclicCell, zero] using reference
        simp [same]
      · by_cases one : previous = 1
        · have same : address = 2 := by simpa [cyclicCell, zero, one] using reference
          simp [same]
        · have same : address = 1 := by simpa [cyclicCell, zero, one] using reference
          simp [same]

theorem cycle_footprint : footprint cyclicHeap cycleRoots = {1, 2} := by
  ext address
  rw [mem_footprint]
  constructor
  · intro live
    have different := cycle_not_zero live
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro member
    rcases Finset.mem_insert.mp member with rfl | member
    · exact live_of_root cyclicHeap cycleRoots (owner := 0) (by decide) (by decide)
    · have same : address = 2 := Finset.mem_singleton.mp member
      subst address
      exact live_of_root cyclicHeap cycleRoots (owner := 1) (by decide) (by decide)

theorem cycle_minimum_is_two_cells_and_32_bytes :
    (collect cyclicHeap cycleRoots).allocated.card = 2 ∧
      allocatedBytes (collect cyclicHeap cycleRoots) = 32 := by
  constructor
  · rw [allocated_collect, cycle_footprint]
    decide
  · rw [allocatedBytes_collect]
    unfold retainedBytes
    rw [cycle_footprint]
    decide

theorem every_same_cycle_observer_pays (candidate : Heap (Fin 3) Nat)
    (observations : SameRootPaths cyclicHeap candidate cycleRoots) :
    2 ≤ candidate.allocated.card ∧ 32 ≤ allocatedBytes candidate := by
  simpa only [cycle_minimum_is_two_cells_and_32_bytes.1,
    cycle_minimum_is_two_cells_and_32_bytes.2] using
    (collect_attains_minimum cyclicHeap cycleRoots).2 candidate observations

/-- A root-only payload observer cannot see that the root's outgoing edge
was deleted and its descendant was discarded. The candidate is still closed. -/
def isolatedRoot : Heap Nat Nat where
  lookup address := if address = 0 then some ⟨0, ∅, 1⟩ else none
  allocated := {0}
  allocated_iff address := by
    by_cases same : address = 0 <;> simp [same]
  closed address cell found next reference := by
    split at found
    next _ => cases found; simp at reference
    next _ => cases found

theorem root_payload_is_insufficient :
    ((Examples.chainHeap 1).lookup 0).map Cell.value =
        (isolatedRoot.lookup 0).map Cell.value ∧
      isolatedRoot.allocated.card < (footprint (Examples.chainHeap 1) Examples.oneRoot).card ∧
      walk isolatedRoot 0 [1] ≠ walk (Examples.chainHeap 1) 0 [1] := by
  rw [Examples.chain_footprint]
  decide

theorem missing_descendant_rejects_candidate :
    ¬ SameRootPaths (Examples.chainHeap 1) isolatedRoot Examples.oneRoot := by
  intro observations
  have same := observations ((), 0) (by decide) (by decide) [1]
  exact root_payload_is_insufficient.2.2 same

end Controls

end Mettapedia.Machines.ResourceOwnership.Optimality

namespace Mettapedia.Machines.ResourceOwnership.Optimality.ContextualReferences

open Mettapedia.GSLT.Core
open MutableObservation

universe uValue uReadout

variable {Address : Type} {Value : Type uValue} [DecidableEq Address]

/-- One selected reference in an actual finite heap. -/
structure Client (Address : Type) (Value : Type uValue) where
  heap : Heap Address Value
  reference : Address

/-- One interaction scope; each edge writes its supplied payload at the
selected reference. Starting allocated references remain allocated after every
edge. This profile grants reads at every address and writes at the hole. -/
inductive Scope (Value : Type uValue) where
  | heap

instance : Quiver (Scope Value) where
  Hom := fun _ _ => Value

def execute {a b : Scope Value} (value : a ⟶ b)
    (client : Client Address Value) : Client Address Value :=
  ⟨client.heap.writePayload client.reference value, client.reference⟩

/-- `none` reads the selected reference; `some anchor` reads a fixed address.
Absence is an explicit observation. All operations of this profile are total
on heaps; it is not an interpretation of arbitrary foreign operations. -/
def base (_scope : Scope Value) : PolicyFamily (Client Address Value) where
  Policy := Option Address
  Result := fun _ => Option Value
  decide := fun anchor client => client.heap.readPayload (anchor.getD client.reference)

/-- Reuse the existing finite-path closure, including its actual dependent
policy indices, execution and greatest-stable-relation construction. -/
def observations : PolicyFamily (Client Address Value) :=
  PolicyFamily.ContextClosure.family execute base (.heap : Scope Value)

omit [DecidableEq Address] in
/-- Before permitting mutations, same-heap clients are identified precisely
by their selected scalar observations, despite the available fixed anchors. -/
theorem base_equivalent_iff (heap : Heap Address Value) (left right : Address) :
    (base (.heap : Scope Value)).PolicyEquivalent ⟨heap, left⟩ ⟨heap, right⟩ ↔
      PayloadEq heap left right := by
  constructor
  · intro same
    exact same none
  · intro same anchor
    cases anchor with
    | none => exact same
    | some anchor => rfl

/-- A one-edge path followed by the actual anchored read is a member of the
constructed context family. No substitution-preservation law is assumed. -/
theorem write_probe (heap : Heap Address Value) (left right : Address)
    (same : observations.PolicyEquivalent
      (⟨heap, left⟩ : Client Address Value) ⟨heap, right⟩)
    (value : Value) (anchor : Address) :
    (heap.writePayload left value).readPayload anchor =
      (heap.writePayload right value).readPayload anchor := by
  let operation : (Scope.heap : Scope Value) ⟶ Scope.heap := value
  exact same ⟨.heap, operation.toPath, some anchor⟩

/-- Closing scalar observations under the specified writes characterizes
reference identity on allocated cells with two distinguishable payload values.
It does not require an arbitrary comparison operator to promise this closure. -/
theorem contextual_equivalent_iff [Nontrivial Value] (heap : Heap Address Value)
    (left right : Address) (leftLive : left ∈ heap.allocated)
    (rightLive : right ∈ heap.allocated) :
    observations.PolicyEquivalent (⟨heap, left⟩ : Client Address Value) ⟨heap, right⟩ ↔
      left = right := by
  constructor
  · intro same
    apply (full_writeReadEq_iff heap left right leftLive rightLive).mp
    intro value anchor
    by_cases anchorLive : anchor ∈ heap.allocated
    · simpa only [writeRead, leftLive, rightLive, anchorLive, and_self, if_true] using
        write_probe heap left right same value anchor
    · simp only [writeRead, anchorLive, and_false, if_false]
  · rintro rfl policy
    rfl

/-- Every sufficient implementation of this declared workload must retain
the selected-reference distinction. The conclusion concerns information;
it gives no runtime lower bound or globally preferred representation. -/
theorem sufficient_readout_separates_references [Nontrivial Value]
    {Readout : Type uReadout} (readout : Client Address Value → Readout)
    (realization : observations.ReadoutRealization readout)
    (heap : Heap Address Value) (left right : Address)
    (leftLive : left ∈ heap.allocated) (rightLive : right ∈ heap.allocated)
    (same : readout ⟨heap, left⟩ = readout ⟨heap, right⟩) : left = right := by
  apply (contextual_equivalent_iff heap left right leftLive rightLive).mp
  intro policy
  exact (realization.agrees policy ⟨heap, left⟩).symm.trans
    ((congrArg (realization.run policy) same).trans
      (realization.agrees policy ⟨heap, right⟩))

namespace Controls

open MutableObservation.Controls (pairHeap)

/-- The same two allocated cells satisfy the coarser read-only promise and
fail the mutation-closed promise. Both are actual nonempty policy families. -/
theorem added_write_context_separates_equal_scalars :
    (base (.heap : Scope Nat)).PolicyEquivalent
      (⟨pairHeap, 0⟩ : Client (Fin 2) Nat) ⟨pairHeap, 1⟩ ∧
    ¬ observations.PolicyEquivalent
      (⟨pairHeap, 0⟩ : Client (Fin 2) Nat) ⟨pairHeap, 1⟩ := by
  constructor
  · exact (base_equivalent_iff pairHeap 0 1).mpr (by decide)
  · intro same
    have identity := (contextual_equivalent_iff pairHeap 0 1 (by decide) (by decide)).mp same
    exact (by decide : (0 : Fin 2) ≠ 1) identity

end Controls

end Mettapedia.Machines.ResourceOwnership.Optimality.ContextualReferences

/-!
## Selected-only mutable observations

The same writable client graph also admits a coarser contextual equivalence
when every read is restricted to its selected cell. The following construction
retains actual writes and all finite paths, while withholding fixed external
anchors. It models this declared observation scope, not arbitrary read-dependent
branching, physical exclusivity or a global comparison policy.
-/

namespace Mettapedia.Machines.ResourceOwnership.Optimality.ContextualReferences.SelectedOnly

open Mettapedia.GSLT.Core

universe uValue

variable {Address : Type} {Value : Type uValue} [DecidableEq Address]

/-- The original family is reindexed to its actual selected-cell coordinate.
The unit policy index selects a real observation; it is not a constant answer. -/
def base (scope : Scope Value) : PolicyFamily (Client Address Value) :=
  (ContextualReferences.base scope).reindex (fun (_ : Unit) => none)

/-- Close the restricted observers under the unchanged actual writes. -/
def observations : PolicyFamily (Client Address Value) :=
  PolicyFamily.ContextClosure.family execute base (.heap : Scope Value)

/-- The existing restriction witness forgets only the fixed external anchors,
while retaining all of the original write paths. -/
def restriction : PolicyFamily.OperationReindex
    (ContextualReferences.observations : PolicyFamily (Client Address Value)) observations id :=
  PolicyFamily.ContextClosure.restrictConsumers execute ContextualReferences.base
    (fun (_ : Scope Value) (_ : Unit) => none) .heap

/-- The actual selected lookup in the client's explicit heap. -/
def selectedRead (client : Client Address Value) : Option Value :=
  client.heap.readPayload client.reference

/-- A genuine write changes the selected observed value, while preserving
honest absence. This law follows from the concrete heap update and lookup. -/
theorem selectedRead_after_write {a b : Scope Value} (value : a ⟶ b)
    (client : Client Address Value) :
    selectedRead (execute value client) = (selectedRead client).map (fun _ => value) := by
  cases found : client.heap.lookup client.reference <;>
    simp [selectedRead, execute, Heap.readPayload, found]

/-- Equality of selected observations survives every shared write operation,
without requiring the references or the full heaps to agree. -/
theorem selectedRead_write_stable {a b : Scope Value} (value : a ⟶ b)
    (left right : Client Address Value) (same : selectedRead left = selectedRead right) :
    selectedRead (execute value left) = selectedRead (execute value right) := by
  rw [selectedRead_after_write, selectedRead_after_write, same]

/-- This is a mutable observation relation closed under all finite paths of
the existing write graph. Allocation hypotheses and two distinct payload
values are not required for this selected-only characterization. -/
theorem contextual_equivalent_iff (left right : Client Address Value) :
    observations.PolicyEquivalent left right ↔ selectedRead left = selectedRead right := by
  constructor
  · intro same
    exact same ⟨.heap, .nil, ()⟩
  · intro same
    apply PolicyFamily.ContextClosure.greatest execute base
      (fun _ left right => selectedRead left = selectedRead right) ?_ ?_ same
    · intro scope left right related policy
      cases policy
      exact related
    · intro a b value left right related
      exact selectedRead_write_stable value left right related

/-- The same-initial-heap specialization compares the live scalar values,
not the selected resource addresses. -/
theorem same_heap_equivalent_iff (heap : Heap Address Value) (left right : Address) :
    observations.PolicyEquivalent (⟨heap, left⟩ : Client Address Value) ⟨heap, right⟩ ↔
      MutableObservation.PayloadEq heap left right :=
  contextual_equivalent_iff _ _

/-- The canonical operation-stability theorem applies to the actual restricted
family; no substitution congruence is supplied as a premise. -/
theorem operation_stable (value : Value) (left right : Client Address Value)
    (same : observations.PolicyEquivalent left right) :
    observations.PolicyEquivalent
      (execute (a := (.heap : Scope Value)) (b := .heap) value left)
      (execute (a := (.heap : Scope Value)) (b := .heap) value right) :=
  PolicyFamily.ContextClosure.operation_stable execute base value same

/-- Agreement holds after an arbitrary actual finite write path, including
the empty path. This uses the constructed family, not another path evaluator. -/
theorem actual_path_reads_agree (path : Quiver.Path (Scope.heap : Scope Value) .heap)
    (left right : Client Address Value) (same : selectedRead left = selectedRead right) :
    selectedRead (PolicyFamily.ContextClosure.runPath execute path left) =
      selectedRead (PolicyFamily.ContextClosure.runPath execute path right) :=
  (contextual_equivalent_iff left right).mpr same ⟨.heap, path, ()⟩

theorem anchored_equivalence_implies_selected (left right : Client Address Value)
    (same : ContextualReferences.observations.PolicyEquivalent left right) :
    observations.PolicyEquivalent left right :=
  restriction.preserves_policyEquivalent same

namespace Controls

open MutableObservation.Controls (pairHeap)

def left : Client (Fin 2) Nat := ⟨pairHeap, 0⟩

def right : Client (Fin 2) Nat := ⟨pairHeap, 1⟩

/-- Both cells are actually allocated, distinct and mutably equivalent for
the selected-only workload, yet the unchanged anchored family separates them. -/
theorem distinct_mutable_cells_are_selected_equivalent :
    left.reference ∈ left.heap.allocated ∧ right.reference ∈ right.heap.allocated ∧
      left.reference ≠ right.reference ∧ observations.PolicyEquivalent left right ∧
      ¬ ContextualReferences.observations.PolicyEquivalent left right := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact (contextual_equivalent_iff left right).mpr (by decide)
  · exact ContextualReferences.Controls.added_write_context_separates_equal_scalars.2

theorem genuine_write_changes_selected_observations :
    selectedRead left = some 7 ∧ selectedRead right = some 7 ∧
      selectedRead (execute (a := (.heap : Scope Nat)) (b := .heap) (9 : Nat) left) = some 9 ∧
      selectedRead (execute (a := (.heap : Scope Nat)) (b := .heap) (9 : Nat) right) = some 9 := by decide

theorem arbitrary_mutation_preserves_selected_equivalence (value : Nat) :
    observations.PolicyEquivalent
      (execute (a := (.heap : Scope Nat)) (b := .heap) value left) (execute (a := (.heap : Scope Nat)) (b := .heap) value right) :=
  operation_stable value left right distinct_mutable_cells_are_selected_equivalent.2.2.2.1

theorem arbitrary_finite_mutations_keep_selected_readouts_equal
    (path : Quiver.Path (Scope.heap : Scope Nat) .heap) :
    selectedRead (PolicyFamily.ContextClosure.runPath execute path left) =
      selectedRead (PolicyFamily.ContextClosure.runPath execute path right) :=
  actual_path_reads_agree path left right (by decide)

/-- The writes affect different actual cells. The selected observations agree
while the external anchor distinguishes the resulting heaps. -/
theorem external_anchor_still_distinguishes_actual_writes :
    (execute (a := (.heap : Scope Nat)) (b := .heap) (9 : Nat) left).heap.readPayload 0 = some 9 ∧
      (execute (a := (.heap : Scope Nat)) (b := .heap) (9 : Nat) right).heap.readPayload 0 = some 7 ∧
      selectedRead (execute (a := (.heap : Scope Nat)) (b := .heap) (9 : Nat) left) =
        selectedRead (execute (a := (.heap : Scope Nat)) (b := .heap) (9 : Nat) right) := by decide

/-- The characterization is not constant equivalence: the empty context
separates different current selected values. -/
theorem unequal_selected_values_are_not_equivalent :
    ¬ observations.PolicyEquivalent
      (execute (a := (.heap : Scope Nat)) (b := .heap) (9 : Nat) left) right := by
  rw [contextual_equivalent_iff]
  decide

/-- A common write can erase an old observed distinction, although zero-step
observations correctly distinguished the two clients before that write. -/
theorem a_shared_write_can_merge_prior_value_classes :
    ¬ observations.PolicyEquivalent (⟨pairHeap.writePayload 0 9, 0⟩ : Client (Fin 2) Nat) right ∧
      observations.PolicyEquivalent
        (execute (a := (.heap : Scope Nat)) (b := .heap) (3 : Nat) (⟨pairHeap.writePayload 0 9, 0⟩ : Client (Fin 2) Nat))
        (execute (a := (.heap : Scope Nat)) (b := .heap) (3 : Nat) right) := by
  constructor
  · rw [contextual_equivalent_iff]
    decide
  · rw [contextual_equivalent_iff]
    decide

def emptyHeap : Heap (Fin 2) Nat where
  lookup _ := none
  allocated := ∅
  allocated_iff _ := by simp
  closed _ _ found _ _ := by cases found

theorem absent_references_are_observably_absent_and_equivalent :
    selectedRead (⟨emptyHeap, 0⟩ : Client (Fin 2) Nat) = none ∧
      selectedRead (execute (a := (.heap : Scope Nat)) (b := .heap) (9 : Nat)
        (⟨emptyHeap, 0⟩ : Client (Fin 2) Nat)) = none ∧
      observations.PolicyEquivalent (⟨emptyHeap, 0⟩ : Client (Fin 2) Nat) ⟨emptyHeap, 1⟩ := by
  refine ⟨rfl, by decide, ?_⟩
  rw [contextual_equivalent_iff]
  rfl

theorem absence_and_allocated_value_are_distinguished :
    ¬ observations.PolicyEquivalent (⟨emptyHeap, 0⟩ : Client (Fin 2) Nat) left := by
  rw [contextual_equivalent_iff]
  decide

end Controls

end Mettapedia.Machines.ResourceOwnership.Optimality.ContextualReferences.SelectedOnly
