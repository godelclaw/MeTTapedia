import Mettapedia.Machines.CMemory.ExecutableStorage
import Mettapedia.Machines.ReadyQueue
import Mettapedia.Machines.Cursor.Fold
import Mettapedia.Machines.Cursor.SequenceCost
import Mettapedia.GSLT.Contracts.RunAccounts
import Mettapedia.Machines.ResourceOwnership
import Mettapedia.Algebra.OccurrenceIdentity
import Mettapedia.Machines.Cursor.TailSummary

/-!
# Publication and cancellation of owned answer cursors

Answer occurrences are kept in a list; ownership roots are a finite set of
owner/address pairs. Publishing duplicate occurrences therefore retains one
physical graph without erasing either occurrence. A bounded observation may
retain the residual. Commitment instead exports the selected answer roots,
removes the delimited owners, and collects the graph those remaining roots
can reach.

The resource graph is the finite heap of `ResourceOwnership`, whose liveness
uses the existing store-reachability judgment. Cancellation does not evaluate
the abandoned continuation and does not roll back the supplied world. A checked
address and payload relocation preserves publication, selected observations and
retained bytes, including duplicate answer occurrences. Native root discovery,
finalizers and the implementation of that copy remain separate obligations.

A discovery catalogue is one delimited owner. Taking prepared proposals
publishes each selected root to its own owner and then cancels that catalogue
once. An untaken address is collected only when no surviving root reaches it.
Releasing one selected owner retains a sibling graph. Operational roots stay
distinct from observer roots, and a semantic reference may still retain storage.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.OwnedLifecycle

open Mettapedia.Machines.ResourceOwnership

variable {Owner Address Value World : Type}
  [DecidableEq Owner] [DecidableEq Address]

/-- Root ownership is shared; answer occurrence multiplicity remains separate. -/
def answerRoots (owner : Owner) (answers : List Address) : Roots Owner Address :=
  (answers.map (fun address => (owner, address))).toFinset

@[simp] theorem mem_answerRoots (owner other : Owner)
    (answers : List Address) (address : Address) :
    (other, address) ∈ answerRoots owner answers ↔
      other = owner ∧ address ∈ answers := by
  simp only [answerRoots, List.mem_toFinset, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨source, member, sameOwner, sameAddress⟩
    exact ⟨sameOwner.symm, sameAddress ▸ member⟩
  · rintro ⟨rfl, member⟩
    exact ⟨address, member, rfl, rfl⟩

def publish (roots : Roots Owner Address) (owner : Owner)
    (answers : List Address) : Roots Owner Address :=
  roots ∪ answerRoots owner answers

theorem publish_mono (roots : Roots Owner Address) (owner : Owner)
    (answers : List Address) : roots ⊆ publish roots owner answers :=
  Finset.subset_union_left

/-- The output owner is a caller outside the delimiter being cancelled. -/
def commitRoots (roots : Roots Owner Address) (dead : Finset Owner)
    (output : Owner) (answers : List Address) : Roots Owner Address :=
  cancel (publish roots output answers) dead

theorem commitRoots_eq (roots : Roots Owner Address) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead) :
    commitRoots roots dead output answers =
      cancel roots dead ∪ answerRoots output answers := by
  ext pair
  rcases pair with ⟨owner, address⟩
  simp only [commitRoots, publish, mem_cancel, Finset.mem_union, mem_answerRoots]
  constructor
  · rintro ⟨old | ⟨rfl, selected⟩, surviving⟩
    · exact Or.inl ⟨old, surviving⟩
    · exact Or.inr ⟨rfl, selected⟩
  · rintro (⟨old, surviving⟩ | ⟨rfl, selected⟩)
    · exact ⟨Or.inl old, surviving⟩
    · exact ⟨Or.inr ⟨rfl, selected⟩, outside⟩

theorem retained_roots_subset_commit (roots : Roots Owner Address)
    (dead : Finset Owner) (output : Owner) (answers : List Address)
    (outside : output ∉ dead) :
    cancel roots dead ⊆ commitRoots roots dead output answers := by
  rw [commitRoots_eq roots dead output answers outside]
  exact Finset.subset_union_left

theorem answer_roots_subset_commit (roots : Roots Owner Address)
    (dead : Finset Owner) (output : Owner) (answers : List Address)
    (outside : output ∉ dead) :
    answerRoots output answers ⊆ commitRoots roots dead output answers := by
  rw [commitRoots_eq roots dead output answers outside]
  exact Finset.subset_union_right

/-- Selection exports a root before cancellation, including a root that was
previously reachable only through the abandoned cursor's internal graph. -/
theorem selected_live_after_commit (heap : Heap Address Value)
    (roots : Roots Owner Address) (dead : Finset Owner) (output : Owner)
    (answers : List Address) (outside : output ∉ dead)
    {address : Address} (selected : address ∈ answers)
    (allocated : address ∈ heap.allocated) :
    Live heap (commitRoots roots dead output answers) address := by
  apply live_of_root heap (commitRoots roots dead output answers)
  · apply answer_roots_subset_commit roots dead output answers outside
    exact (mem_answerRoots output output answers address).mpr ⟨rfl, selected⟩
  · exact allocated

/-- Every descendant of an exported answer survives, not just its top node. -/
theorem answer_graph_live_after_commit (heap : Heap Address Value)
    (roots : Roots Owner Address) (dead : Finset Owner) (output : Owner)
    (answers : List Address) (outside : output ∉ dead) {address : Address}
    (live : Live heap (answerRoots output answers) address) :
    Live heap (commitRoots roots dead output answers) address :=
  live_mono heap (answer_roots_subset_commit roots dead output answers outside) live

/-- The caller's surviving roots retain their entire reachable graphs. -/
theorem outer_graph_live_after_commit (heap : Heap Address Value)
    (roots : Roots Owner Address) (dead : Finset Owner) (output : Owner)
    (answers : List Address) (outside : output ∉ dead) {address : Address}
    (live : Live heap (cancel roots dead) address) :
    Live heap (commitRoots roots dead output answers) address :=
  live_mono heap (retained_roots_subset_commit roots dead output answers outside) live

/-- Publication followed by cancellation retains exactly the union of the
caller graph and exported answer graphs. No other old owner remains a root. -/
theorem live_commit_iff (heap : Heap Address Value)
    (roots : Roots Owner Address) (dead : Finset Owner) (output : Owner)
    (answers : List Address) (outside : output ∉ dead) (address : Address) :
    Live heap (commitRoots roots dead output answers) address ↔
      Live heap (cancel roots dead) address ∨
      Live heap (answerRoots output answers) address := by
  rw [commitRoots_eq roots dead output answers outside]
  rw [live_iff_root heap (cancel roots dead ∪ answerRoots output answers) address,
    live_iff_root heap (cancel roots dead) address,
    live_iff_root heap (answerRoots output answers) address]
  simp only [Finset.mem_union]
  constructor
  · rintro ⟨pair, retained | exported, live⟩
    · exact Or.inl ⟨pair, retained, live⟩
    · exact Or.inr ⟨pair, exported, live⟩
  · rintro (⟨pair, retained, live⟩ | ⟨pair, exported, live⟩)
    · exact ⟨pair, Or.inl retained, live⟩
    · exact ⟨pair, Or.inr exported, live⟩

/-- Resource collection operates below the semantic world. -/
structure Session (Owner Address Value World : Type)
    [DecidableEq Owner] [DecidableEq Address] where
  heap : Heap Address Value
  roots : Roots Owner Address
  world : World

noncomputable def closeScope (state : Session Owner Address Value World)
    (dead : Finset Owner) : Session Owner Address Value World :=
  let roots := cancel state.roots dead
  ⟨collect state.heap roots, roots, state.world⟩

noncomputable def commit (state : Session Owner Address Value World)
    (dead : Finset Owner) (output : Owner) (answers : List Address) :
    Session Owner Address Value World :=
  let roots := commitRoots state.roots dead output answers
  ⟨collect state.heap roots, roots, state.world⟩

@[simp] theorem closeScope_world (state : Session Owner Address Value World)
    (dead : Finset Owner) : (closeScope state dead).world = state.world := rfl

@[simp] theorem commit_world (state : Session Owner Address Value World)
    (dead : Finset Owner) (output : Owner) (answers : List Address) :
    (commit state dead output answers).world = state.world := rfl

/-- Complete cell lookup exposes payload, references and accounting size. -/
def observe (heap : Heap Address Value) (answers : List Address) :
    List (Option (Cell Address Value)) := answers.map heap.lookup

theorem commit_preserves_selected_observation
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead)
    (allocated : ∀ address ∈ answers, address ∈ state.heap.allocated) :
    observe (commit state dead output answers).heap answers =
      observe state.heap answers := by
  apply List.map_congr_left
  intro address selected
  exact lookup_collect_of_live state.heap _ (selected_live_after_commit
    state.heap state.roots dead output answers outside selected
      (allocated address selected))

/-- Read each ordered answer in the session's semantic world. Equal resource
addresses do not supply the binding or interpretation context of a return. -/
def observeContext {Observation : Type}
    (state : Session Owner Address Value World) (answers : List Address)
    (interpret : World → Option (Cell Address Value) → Observation) : List Observation :=
  (observe state.heap answers).map (interpret state.world)

/-- Actual publication and collection preserve every world-indexed readout of
selected complete cells, including duplicate answer occurrences. -/
theorem commit_preserves_contextual_observation {Observation : Type}
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead)
    (allocated : ∀ address ∈ answers, address ∈ state.heap.allocated)
    (interpret : World → Option (Cell Address Value) → Observation) :
    observeContext (commit state dead output answers) answers interpret =
      observeContext state answers interpret := by
  unfold observeContext
  rw [commit_world, commit_preserves_selected_observation state dead output answers
    outside allocated]

/-- Keeping storage cannot repair a substituted semantic world. This decoder
exposes the world on every cell occurrence, so any nonempty answer list detects
that substitution even when the resource heap is unchanged. -/
theorem changed_world_changes_contextual_observation
    (state : Session Owner Address Value World) (other : World)
    (different : state.world ≠ other) (address : Address) (rest : List Address) :
    observeContext state (address :: rest) (fun world cell => (world, cell)) ≠
      observeContext {state with world := other} (address :: rest)
        (fun world cell => (world, cell)) := by
  intro same
  have heads := List.cons.inj same
  exact different (congrArg Prod.fst heads.1)

theorem commit_preserves_answer_graph
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead)
    {address : Address} (live : Live state.heap (answerRoots output answers) address) :
    (commit state dead output answers).heap.lookup address = state.heap.lookup address :=
  lookup_collect_of_live state.heap _ (answer_graph_live_after_commit
    state.heap state.roots dead output answers outside live)

theorem commit_preserves_outer_graph
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead)
    {address : Address} (live : Live state.heap (cancel state.roots dead) address) :
    (commit state dead output answers).heap.lookup address = state.heap.lookup address :=
  lookup_collect_of_live state.heap _ (outer_graph_live_after_commit
    state.heap state.roots dead output answers outside live)

/-- Publishing the starts of the captured paths protects their whole
reachable graphs. Failed paths and duplicated observations remain unchanged. -/
theorem commit_preserves_paths
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (output : Owner) (paths : List (Address × List Address)) (outside : output ∉ dead)
    (allocated : ∀ query ∈ paths, query.1 ∈ state.heap.allocated) :
    RequestBorrow.observe (commit state dead output (paths.map Prod.fst)).heap paths =
      RequestBorrow.observe state.heap paths := by
  apply List.map_congr_left
  intro query member
  exact walk_collect state.heap _ (selected_live_after_commit state.heap state.roots dead
    output (paths.map Prod.fst) outside (List.mem_map.mpr ⟨query, member, rfl⟩)
      (allocated query member)) query.2

section Relocation

variable {DestinationAddress DestinationValue : Type}
variable [DecidableEq DestinationAddress]

/-- Copying resource storage keeps the actual semantic world. Host authority
must be checked separately before a runtime installs this session. -/
def relocateSession (state : Session Owner Address Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation state.heap destination) :
    Session Owner DestinationAddress DestinationValue World :=
  ⟨destination, copy.roots state.roots, state.world⟩

theorem relocate_answerRoots {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (owner : Owner) (answers : List Address) :
    copy.roots (answerRoots owner answers) =
      answerRoots owner (answers.map copy.address) := by
  ext pair
  rcases pair with ⟨other, address⟩
  rw [mem_answerRoots]
  constructor
  · intro member
    obtain ⟨⟨originalOwner, original⟩, present, same⟩ := Finset.mem_image.mp member
    have selected := (mem_answerRoots owner originalOwner answers original).mp present
    exact ⟨(congrArg Prod.fst same).symm.trans selected.1,
      List.mem_map.mpr ⟨original, selected.2, congrArg Prod.snd same⟩⟩
  · rintro ⟨sameOwner, member⟩
    obtain ⟨original, present, sameAddress⟩ := List.mem_map.mp member
    exact Finset.mem_image.mpr ⟨(owner, original),
      (mem_answerRoots owner owner answers original).mpr ⟨rfl, present⟩,
      Prod.ext sameOwner.symm sameAddress⟩

/-- Publication and delimiter cancellation commute with the checked copy.
Owner identities are kept; selected occurrence order remains in the list. -/
theorem relocate_commitRoots {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (dead : Finset Owner) (output : Owner) (answers : List Address) :
    copy.roots (commitRoots roots dead output answers) =
      commitRoots (copy.roots roots) dead output (answers.map copy.address) := by
  have publication : copy.roots (publish roots output answers) =
      publish (copy.roots roots) output (answers.map copy.address) := by
    unfold publish
    rw [show copy.roots (roots ∪ answerRoots output answers) =
      copy.roots roots ∪ copy.roots (answerRoots output answers) from Finset.image_union _ _]
    rw [relocate_answerRoots copy]
  unfold commitRoots
  rw [copy.roots_cancel, publication]

omit [DecidableEq Address] in
/-- Complete cells are read from destination storage. No equality of payloads
substitutes for transporting their outgoing references. -/
theorem relocate_observation {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (answers : List Address) :
    observe destination (answers.map copy.address) =
      (observe source answers).map (Option.map (Cell.relocate copy.address copy.payload)) := by
  simp only [observe, List.map_map]
  apply List.map_congr_left
  intro address _
  exact copy.lookup_eq address

/-- A representation change transports complete cells through the existing
relocation. The readout receives the original semantic world. Its cell decoder
must respect that representation map; pointer transport alone cannot imply it. -/
theorem relocate_contextual_observation {Observation : Type}
    (state : Session Owner Address Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation state.heap destination) (answers : List Address)
    (readSource : World → Option (Cell Address Value) → Observation)
    (readDestination : World → Option (Cell DestinationAddress DestinationValue) → Observation)
    (decode : ∀ cell, readDestination state.world
      (cell.map (Cell.relocate copy.address copy.payload)) = readSource state.world cell) :
    observeContext (relocateSession state destination copy) (answers.map copy.address)
      readDestination = observeContext state answers readSource := by
  unfold observeContext
  rw [show (relocateSession state destination copy).world = state.world from rfl]
  rw [show (relocateSession state destination copy).heap = destination from rfl]
  rw [relocate_observation copy answers, List.map_map]
  apply List.map_congr_left
  intro cell _
  exact decode cell

/-- An exported answer survives cancellation in either representation, with
the same ordered occurrence list and transported complete cells. -/
theorem relocate_commit_observation
    (state : Session Owner Address Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation state.heap destination) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead)
    (allocated : ∀ address ∈ answers, address ∈ state.heap.allocated) :
    observe (commit (relocateSession state destination copy) dead output
      (answers.map copy.address)).heap (answers.map copy.address) =
      (observe (commit state dead output answers).heap answers).map
        (Option.map (Cell.relocate copy.address copy.payload)) := by
  rw [commit_preserves_selected_observation state dead output answers outside allocated]
  rw [commit_preserves_selected_observation]
  · exact relocate_observation copy answers
  · exact outside
  · intro address member
    obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
    exact (copy.allocated_iff original).mpr (allocated original selected)

/-- A copied capture can be read after retiring its source scope. The reads
use the destination graph, with every ordered path and alias transported. -/
theorem relocate_commit_paths
    (state : Session Owner Address Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation state.heap destination) (dead : Finset Owner)
    (output : Owner) (paths : List (Address × List Address)) (outside : output ∉ dead)
    (allocated : ∀ query ∈ paths, query.1 ∈ state.heap.allocated) :
    RequestBorrow.observe (commit (relocateSession state destination copy) dead output
        ((RequestBorrow.relocatePaths copy.address paths).map Prod.fst)).heap
      (RequestBorrow.relocatePaths copy.address paths) =
      (RequestBorrow.observe state.heap paths).map (Option.map fun pair =>
        (copy.address pair.1, pair.2.relocate copy.address copy.payload)) := by
  rw [commit_preserves_paths]
  · exact copy.observe_paths_eq paths
  · exact outside
  · intro query member
    obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
    exact (copy.allocated_iff original.1).mpr (allocated original selected)

/-- Cursor publication supplies the destination roots for a checked borrow.
Source refusal is preserved, and an accepted view reads only the graph left
after publication and cancellation. Repeated and failed paths stay ordered. -/
theorem relocate_commit_checked_borrow
    (state : Session Owner Address Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation state.heap destination) (dead : Finset Owner)
    (output : Owner) (epoch : Nat) (sourceStamp : RequestBorrow.Stamp Owner)
    (view : RequestBorrow.View Owner Address) (outside : output ∉ dead)
    (allocated : ∀ query ∈ view.paths, query.1 ∈ state.heap.allocated) :
    (RequestBorrow.transport ⟨sourceStamp, state.heap⟩
        ⟨⟨output, epoch⟩, destination⟩ copy view).bind
      (RequestBorrow.read ⟨⟨output, epoch⟩,
        (commit (relocateSession state destination copy) dead output
          ((RequestBorrow.relocatePaths copy.address view.paths).map Prod.fst)).heap⟩) =
      (RequestBorrow.read ⟨sourceStamp, state.heap⟩ view).map
        (List.map (Option.map fun pair =>
          (copy.address pair.1, pair.2.relocate copy.address copy.payload))) := by
  by_cases issued : view.stamp = sourceStamp
  · simp only [RequestBorrow.transport, RequestBorrow.View.transportIfCurrent, if_pos issued, Option.bind_some,
      RequestBorrow.read, ↓reduceIte, Option.map_some]
    congr 1
    exact relocate_commit_paths state destination copy dead output view.paths outside allocated
  · simp only [RequestBorrow.transport, RequestBorrow.View.transportIfCurrent, Option.bind_none, RequestBorrow.read,
      if_neg issued, Option.map_none]

/-- The copied and original published graphs have equal retained byte
weights. Copying and speculative execution work are separate charges. -/
theorem relocate_commit_storage
    (state : Session Owner Address Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation state.heap destination) (dead : Finset Owner)
    (output : Owner) (answers : List Address) :
    allocatedBytes (commit (relocateSession state destination copy) dead output
      (answers.map copy.address)).heap = allocatedBytes (commit state dead output answers).heap := by
  change allocatedBytes (collect destination
    (commitRoots (copy.roots state.roots) dead output (answers.map copy.address))) =
      allocatedBytes (collect state.heap (commitRoots state.roots dead output answers))
  rw [allocatedBytes_collect, allocatedBytes_collect,
    ← relocate_commitRoots copy state.roots dead output answers, copy.retainedBytes_eq]

end Relocation

/-- Garbage from the abandoned search is reclaimed unless either an outer
owner or a published answer still reaches it, possibly through a cycle. -/
theorem commit_reclaims_unprotected
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead)
    (address : Address)
    (notOuter : ¬ Live state.heap (cancel state.roots dead) address)
    (notAnswer : ¬ Live state.heap (answerRoots output answers) address) :
    (commit state dead output answers).heap.lookup address = none := by
  apply lookup_collect_of_not_live state.heap _
  rw [live_commit_iff state.heap state.roots dead output answers outside address]
  exact not_or.mpr ⟨notOuter, notAnswer⟩

theorem closeScope_reclaims_final_owner
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (address : Address)
    (lastOwners : ∀ pair ∈ state.roots,
      Live state.heap {pair} address → pair.1 ∈ dead) :
    (closeScope state dead).heap.lookup address = none :=
  final_owners_reclaimed state.heap state.roots dead address lastOwners

/-- The output list is not quotiented by the root set. -/
theorem duplicate_answer_observation
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (output : Owner) (address : Address) (outside : output ∉ dead)
    (allocated : address ∈ state.heap.allocated) :
    observe (commit state dead output [address, address]).heap [address, address] =
      [state.heap.lookup address, state.heap.lookup address] := by
  rw [commit_preserves_selected_observation state dead output [address, address]
    outside (by
      intro other member
      have same : other = address := by simpa using member
      simpa [same] using allocated)]
  rfl

theorem answerRoots_card_le (owner : Owner) (answers : List Address) :
    (answerRoots owner answers).card ≤ answers.length := by
  simpa only [answerRoots, List.length_map] using
    List.toFinset_card_le (answers.map (fun address => (owner, address)))

theorem commit_root_count (roots : Roots Owner Address) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead) :
    (commitRoots roots dead output answers).card ≤ roots.card + answers.length := by
  rw [commitRoots_eq roots dead output answers outside]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (Finset.card_le_card (cancel_subset roots dead))
      (answerRoots_card_le output answers))

/-- Bounded publication has a bounded retained heap only when the transitive
footprint and cell-size hypotheses also hold. An answer count alone is not a
bound on the graph behind those answers. Shared graphs are counted only once
by the actual collector; the right side is a conservative upper bound. -/
theorem commit_byte_bound (state : Session Owner Address Value World)
    (dead : Finset Owner) (output : Owner) (answers : List Address)
    (outside : output ∉ dead) (perRoot bytes : Nat)
    (bounded : ∀ pair ∈ commitRoots state.roots dead output answers,
      (footprint state.heap {pair}).card ≤ perRoot)
    (weights : ∀ address ∈ footprint state.heap
      (commitRoots state.roots dead output answers),
      cellBytes state.heap address ≤ bytes) :
    allocatedBytes (commit state dead output answers).heap ≤
      (state.roots.card + answers.length) * perRoot * bytes := by
  change allocatedBytes (collect state.heap _) ≤ _
  rw [allocatedBytes_collect]
  exact retainedBytes_le_root_footprints state.heap _ _ perRoot bytes
    (commit_root_count state.roots dead output answers outside) bounded weights

/-! ## Amortized transport for useful collections

The native single-frontier collector publishes a fresh copy only when at least
one quarter of the old arena is discarded. The following account uses measured
byte counts, separate from producer firings and answer multiplicities. It bounds
the bytes copied by successful collections in terms of ordinary allocation;
declined copy attempts and copy-table metadata are separate implementation costs.
-/

namespace CollectionAccounting

/-- Allocation since the previous collection, followed by the bytes retained
in the freshly published region. These counts need not count answer occurrences. -/
structure Cycle where
  allocated : Nat
  retained : Nat

def copiedBytes (cycles : List Cycle) : Nat :=
  (cycles.map Cycle.retained).sum

def allocatedBetween (cycles : List Cycle) : Nat :=
  (cycles.map Cycle.allocated).sum

def endingBytes (initial : Nat) : List Cycle → Nat
  | [] => initial
  | cycle :: rest => endingBytes cycle.retained rest

/-- Integer-rounded quarter reclamation, with a nontrivial collection floor.
The native floor of 64 KiB is stronger than the twelve bytes needed here. -/
def Useful (initial : Nat) : List Cycle → Prop
  | [] => True
  | cycle :: rest =>
      12 ≤ initial + cycle.allocated ∧
      cycle.retained ≤ initial + cycle.allocated - (initial + cycle.allocated) / 4 ∧
      Useful cycle.retained rest

theorem retained_le_four_discarded (before after : Nat)
    (floor : 12 ≤ before) (useful : after ≤ before - before / 4) :
    after ≤ 4 * (before - after) := by
  omega

/-- The retained heap is a potential. Each accepted copy spends at most four
times the potential released by reclamation, including integer rounding. -/
theorem copied_with_potential_le (cycles : List Cycle) (initial : Nat)
    (useful : Useful initial cycles) :
    copiedBytes cycles + 4 * endingBytes initial cycles ≤
      4 * (initial + allocatedBetween cycles) := by
  induction cycles generalizing initial with
  | nil => simp [copiedBytes, allocatedBetween, endingBytes]
  | cons cycle rest ih =>
      obtain ⟨floor, reclaimed, remaining⟩ := useful
      have step := retained_le_four_discarded
        (initial + cycle.allocated) cycle.retained floor reclaimed
      have tail := ih cycle.retained remaining
      simp only [copiedBytes, allocatedBetween, List.map_cons, List.sum_cons,
        endingBytes] at *
      omega

/-- Arbitrarily many successful collections cannot repeatedly charge the same
unchanged live graph: cumulative copied bytes are bounded by incoming storage. -/
theorem copied_le_allocated (cycles : List Cycle) (initial : Nat)
    (useful : Useful initial cycles) :
    copiedBytes cycles ≤ 4 * (initial + allocatedBetween cycles) := by
  have bound := copied_with_potential_le cycles initial useful
  omega

/-- A real sequence allocates 100 bytes per interval, retains ten, and copies
only thirty across its three successful collections. -/
theorem repeated_small_frontier :
    Useful 0 [⟨100, 10⟩, ⟨100, 10⟩, ⟨100, 10⟩] ∧
    copiedBytes [⟨100, 10⟩, ⟨100, 10⟩, ⟨100, 10⟩] = 30 := by
  simp [Useful, copiedBytes]

/-- Without the useful-reclamation check, repeated copies of the unchanged
graph violate the allocation bound. This is rejected by the actual policy. -/
theorem full_copy_is_not_useful :
    let cycles : List Cycle := List.replicate 5 ⟨0, 100⟩
    ¬ Useful 100 cycles ∧
    copiedBytes cycles > 4 * (100 + allocatedBetween cycles) := by
  simp [Useful, copiedBytes, allocatedBetween, List.replicate_succ]

end CollectionAccounting

namespace SpeculativeBudget

/-- Storage relocation is not a new execution allowance. These mathematical
events do not prescribe a native history allocation. The graph preservation
obligations of collection are established separately above. -/
inductive Event where
  | transition | collection
  deriving DecidableEq

def transitions : List Event → Nat
  | [] => 0
  | .transition :: rest => 1 + transitions rest
  | .collection :: rest => transitions rest

/-- The native cursor checks the transition purse before executing the next
step. Collection may reclaim storage but leaves this purse unchanged. -/
def spend : Nat → List Event → Option Nat
  | remaining, [] => some remaining
  | 0, .transition :: _ => none
  | remaining + 1, .transition :: rest => spend remaining rest
  | remaining, .collection :: rest => spend remaining rest

/-- The operational purse agrees with the independently counted transitions,
including traces with arbitrarily many intervening collections. -/
theorem spend_eq_some_iff (events : List Event) (budget remaining : Nat) :
    spend budget events = some remaining ↔ transitions events + remaining = budget := by
  induction events generalizing budget with
  | nil => simp [spend, transitions, eq_comm]
  | cons event rest ih =>
      cases event with
      | collection => exact ih budget
      | transition =>
          cases budget with
          | zero => simp [spend, transitions]
          | succ budget =>
              simp only [spend, transitions]
              rw [ih]
              omega

/-- An accepted attempt never executes more transitions than originally
granted, even when dead storage is repeatedly reclaimed. -/
theorem accepted_work_bound (events : List Event) (budget remaining : Nat)
    (accepted : spend budget events = some remaining) : transitions events ≤ budget := by
  have exactCount := (spend_eq_some_iff events budget remaining).mp accepted
  omega

/-- Splitting execution for observation does not invent another allowance. -/
theorem spend_append (first second : List Event) (budget : Nat) :
    spend budget (first ++ second) =
      (spend budget first).bind (fun remaining => spend remaining second) := by
  induction first generalizing budget with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | collection => exact ih budget
      | transition =>
          cases budget with
          | zero => rfl
          | succ budget => exact ih budget

theorem collections_preserve_remaining (count budget : Nat) :
    spend budget (List.replicate count .collection) = some budget := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [List.replicate_succ, spend] using ih

/-- Collection cannot make a second step legal under a one-step purse;
a separately granted two-step purse admits the same execution. -/
theorem reclamation_is_not_reauthorization :
    spend 1 [.transition, .collection, .transition] = none ∧
    spend 2 [.transition, .collection, .transition] = some 0 := by decide

end SpeculativeBudget

/-! ## Suspended multi-frame frontiers -/

namespace Frontier

/-- Continuation identity and its instruction position survive storage moves.
The locals are roots, even when no current argument refers to them. -/
structure Capture (Address : Type) where
  identity : Nat
  equation : Nat
  step : Nat
  slot : Nat
  locals : List Address
  deriving DecidableEq, Repr

structure Frame (Address : Type) where
  identity : Nat
  nextEquation : Nat
  arguments : List Address
  continuations : List (Capture Address)
  deriving DecidableEq, Repr

/-- Pending delivery and an undo frontier are retained until their boundary
is discharged. A collector that cannot enumerate them must decline there. -/
structure State (Address : Type) where
  frames : List (Frame Address)
  pending : List Address
  undo : List (Frame Address)
  deriving DecidableEq, Repr

def Capture.map {B : Type} (f : Address → B) (capture : Capture Address) : Capture B :=
  ⟨capture.identity, capture.equation, capture.step, capture.slot, capture.locals.map f⟩

def Frame.map {B : Type} (f : Address → B) (frame : Frame Address) : Frame B :=
  ⟨frame.identity, frame.nextEquation, frame.arguments.map f,
    frame.continuations.map (Capture.map f)⟩

def State.map {B : Type} (f : Address → B) (state : State Address) : State B :=
  ⟨state.frames.map (Frame.map f), state.pending.map f,
    state.undo.map (Frame.map f)⟩

def captureRoots : List (Capture Address) → List Address
  | [] => []
  | capture :: rest => capture.locals ++ captureRoots rest

def Frame.roots (frame : Frame Address) : List Address :=
  frame.arguments ++ captureRoots frame.continuations

def frameRoots : List (Frame Address) → List Address
  | [] => []
  | frame :: rest => frame.roots ++ frameRoots rest

def State.rootList (state : State Address) : List Address :=
  frameRoots state.frames ++ state.pending ++ frameRoots state.undo

def State.roots (state : State Address) (owner : Owner) : Roots Owner Address :=
  answerRoots owner state.rootList

omit [DecidableEq Owner] [DecidableEq Address] in
theorem captureRoots_map {B : Type} (f : Address → B)
    (captures : List (Capture Address)) :
    captureRoots (captures.map (Capture.map f)) = (captureRoots captures).map f := by
  induction captures with
  | nil => rfl
  | cons capture rest ih => simp [captureRoots, Capture.map, ih]

omit [DecidableEq Owner] [DecidableEq Address] in
theorem Frame.roots_map {B : Type} (f : Address → B) (frame : Frame Address) :
    (frame.map f).roots = frame.roots.map f := by
  simp [Frame.map, Frame.roots, captureRoots_map]

omit [DecidableEq Owner] [DecidableEq Address] in
theorem frameRoots_map {B : Type} (f : Address → B) (frames : List (Frame Address)) :
    frameRoots (frames.map (Frame.map f)) = (frameRoots frames).map f := by
  induction frames with
  | nil => rfl
  | cons frame rest ih => simp [frameRoots, Frame.roots_map, ih]

omit [DecidableEq Owner] [DecidableEq Address] in
theorem State.rootList_map {B : Type} (f : Address → B) (state : State Address) :
    (state.map f).rootList = state.rootList.map f := by
  simp [State.map, State.rootList, frameRoots_map]

section Copy

variable {B W : Type} [DecidableEq B]
variable {source : Heap Address Value} {destination : Heap B W}

/-- One injective relocation is shared by arguments, saved locals, pending
delivery and undo roots. Separate copy episodes need not preserve aliases. -/
theorem relocated_roots (copy : Relocation source destination)
    (state : State Address) (owner : Owner) :
    (state.map copy.address).roots owner = copy.roots (state.roots owner) := by
  rw [State.roots, State.rootList_map, ← relocate_answerRoots]
  rfl

omit [DecidableEq Address] in
theorem saved_observations (copy : Relocation source destination)
    (state : State Address) :
    observe destination (state.map copy.address).rootList =
      (observe source state.rootList).map
        (Option.map (Cell.relocate copy.address copy.payload)) := by
  rw [State.rootList_map]
  exact relocate_observation copy state.rootList

/-- This includes aliases between a current argument and a continuation
local, and shared descendants reached by different captured paths. -/
theorem saved_aliases (copy : Relocation source destination)
    (argument saved : Address) (argumentPath localPath : List Address) :
    Aliases destination (copy.address argument) (argumentPath.map copy.address)
        (copy.address saved) (localPath.map copy.address) ↔
      Aliases source argument argumentPath saved localPath :=
  copy.aliases_iff argument saved argumentPath localPath

omit [DecidableEq Address] in
/-- Ordered equation positions are not inferred again after copying. -/
theorem equation_positions (copy : Relocation source destination) (state : State Address) :
    (state.map copy.address).frames.map (fun frame => (frame.identity, frame.nextEquation)) =
      state.frames.map (fun frame => (frame.identity, frame.nextEquation)) := by
  simp [State.map, List.map_map, Frame.map]

theorem retirement_preserves_saved_graph (copy : Relocation source destination)
    (state : State Address) (oldOwner nextOwner : Owner) (different : nextOwner ≠ oldOwner)
    (address : Address) (live : Live source (state.roots oldOwner) address) :
    Live destination
      (release (transfer ((state.map copy.address).roots oldOwner) oldOwner nextOwner)
        oldOwner) (copy.address address) := by
  rw [relocated_roots copy]
  apply copy.live_after_source_retirement _ oldOwner nextOwner different _ address live
  intro pair member
  exact ((mem_answerRoots oldOwner pair.1 state.rootList pair.2).mp member).1

end Copy

/-- The native collector copies the live projection, not every allocation
ever made in the source arena. Closing that projection before relocation
preserves every enumerated root observation while discarding old garbage. -/
theorem collected_saved_observations (heap : Heap Address Value)
    (state : State Address) (owner : Owner) {B W : Type} [DecidableEq B]
    (destination : Heap B W)
    (copy : Relocation (collect heap (state.roots owner)) destination)
    (allocated : ∀ address ∈ state.rootList, address ∈ heap.allocated) :
    observe destination (state.map copy.address).rootList =
      (observe heap state.rootList).map (Option.map (Cell.relocate copy.address copy.payload)) := by
  rw [saved_observations copy]
  congr 1
  apply List.map_congr_left
  intro address member
  exact lookup_collect_of_live heap _ (live_of_root heap _
    ((mem_answerRoots owner owner state.rootList address).mpr ⟨rfl, member⟩)
    (allocated address member))



/-- The graph bound counts all transitive storage beneath each live root.
The metadata term accounts separately for frames and continuation records.
There is no completed-iteration term; bounding root count alone is insufficient. -/
theorem storage_bound (heap : Heap Address Value) (state : State Address) (owner : Owner)
    (rootLimit perRoot cellSize metadata metadataLimit : Nat)
    (rootCount : state.rootList.length ≤ rootLimit)
    (bounded : ∀ pair ∈ state.roots owner, (footprint heap {pair}).card ≤ perRoot)
    (weights : ∀ address ∈ footprint heap (state.roots owner),
      cellBytes heap address ≤ cellSize)
    (metadataBound : metadata ≤ metadataLimit) :
    allocatedBytes (collect heap (state.roots owner)) + metadata ≤
      rootLimit * perRoot * cellSize + metadataLimit := by
  rw [allocatedBytes_collect]
  apply Nat.add_le_add _ metadataBound
  apply retainedBytes_le_root_footprints heap _ rootLimit perRoot cellSize _ bounded weights
  exact (List.toFinset_card_le _).trans (by simpa [State.roots, answerRoots] using rootCount)

namespace Controls

def savedOnly : State (Fin 3) :=
  ⟨[⟨4, 1, [0], [⟨8, 2, 3, 0, [2, 2]⟩]⟩], [1], []⟩

theorem omitted_saved_local_is_missing :
    savedOnly.rootList = [0, 2, 2, 1] ∧
      (2 : Fin 3) ∉ frameRoots (Address := Fin 3) [⟨4, 1, [0], []⟩] := by decide

theorem shared_saved_root_remains_two_occurrences :
    (savedOnly.map (fun address => address.val + 10)).rootList = [10, 12, 12, 11] :=
  by decide

end Controls

end Frontier

/-! ## Authentication and transport of issued returns

An issued handle is authenticated against four independent registry fields.
Physical store identity is separate from logical occurrence identity; the
parent lineage stays with the external continuation owner. The executable
scan below exposes its visited-row cost and is checked against membership,
not defined by that membership judgment. Payload relocation and complete
root discovery remain separate from registry authentication.
-/

namespace IssuedReturn

open Mettapedia.Algebra

variable {Provider : Type} [DecidableEq Provider]

structure Row (Address Provider : Type) where
  occurrence : Nat
  token : Nat
  payload : Address
  provider : Provider
  deriving DecidableEq, Repr

structure Handle (Address Provider : Type) where
  store : Nat
  parent : Nat
  row : Row Address Provider
  deriving DecidableEq, Repr

structure Registry (Address Provider : Type) where
  identity : Nat
  rows : List (Row Address Provider)
  deriving DecidableEq, Repr

def rowMatches (row wanted : Row Address Provider) : Bool :=
  row.occurrence == wanted.occurrence && row.token == wanted.token &&
    row.payload == wanted.payload && row.provider == wanted.provider

theorem rowMatches_iff (row wanted : Row Address Provider) :
    rowMatches row wanted = true ↔ row = wanted := by
  cases row
  cases wanted
  simp [rowMatches, Row.mk.injEq, and_assoc]

/-- Linear search returns the first matching physical slot and charges each
row it actually visits. A refusal after exhausting the rows keeps that cost. -/
def scan (wanted : Row Address Provider) : List (Row Address Provider) → Option Nat × Nat
  | [] => (none, 0)
  | row :: rest =>
      if rowMatches row wanted then (some 0, 1)
      else
        let tail := scan wanted rest
        (tail.1.map Nat.succ, tail.2 + 1)

theorem scan_none_iff (wanted : Row Address Provider) (rows : List (Row Address Provider)) :
    (scan wanted rows).1 = none ↔ wanted ∉ rows := by
  induction rows with
  | nil => simp [scan]
  | cons row rest ih =>
      by_cases same : row = wanted
      · subst row
        simp [scan, (rowMatches_iff wanted wanted).mpr rfl]
      · have different : rowMatches row wanted = false := by
          cases found : rowMatches row wanted with
          | false => rfl
          | true => exact (same ((rowMatches_iff row wanted).mp found)).elim
        simp [scan, different, ih, Ne.symm same]

theorem scan_selected (wanted : Row Address Provider) (rows : List (Row Address Provider))
    (index : Nat) (selected : (scan wanted rows).1 = some index) :
    rows[index]? = some wanted ∧ (scan wanted rows).2 = index + 1 := by
  induction rows generalizing index with
  | nil => simp [scan] at selected
  | cons row rest ih =>
      by_cases found : rowMatches row wanted = true
      · have same := (rowMatches_iff row wanted).mp found
        simp only [scan, found, if_true, Option.some.injEq] at selected
        subst index
        constructor
        · exact congrArg some same
        · simp only [scan, found, if_true]
      · have different : rowMatches row wanted = false := Bool.eq_false_iff.mpr found
        simp only [scan, different, Bool.false_eq_true, if_false] at selected
        obtain ⟨tailIndex, accepted, rfl⟩ := Option.map_eq_some_iff.mp selected
        obtain ⟨lookup, visits⟩ := ih tailIndex accepted
        constructor
        · simpa only [List.getElem?_cons_succ] using lookup
        · simp only [scan, different, Bool.false_eq_true, if_false]
          rw [visits]

theorem scan_refused_cost (wanted : Row Address Provider)
    (rows : List (Row Address Provider)) (refused : (scan wanted rows).1 = none) :
    (scan wanted rows).2 = rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      have absent := (scan_none_iff wanted (row :: rest)).mp refused
      have different : rowMatches row wanted = false := by
        apply Bool.eq_false_iff.mpr
        intro found
        exact absent (List.mem_cons.mpr (Or.inl ((rowMatches_iff row wanted).mp found).symm))
      have tailRefused : (scan wanted rest).1 = none :=
        (scan_none_iff wanted rest).mpr (fun member => absent (List.mem_cons_of_mem _ member))
      simp only [scan, different, Bool.false_eq_true, if_false,
        List.length_cons, ih tailRefused]

theorem scan_visits_le (wanted : Row Address Provider) (rows : List (Row Address Provider)) :
    (scan wanted rows).2 ≤ rows.length := by
  induction rows with
  | nil => exact Nat.le_refl _
  | cons row rest ih =>
      simp only [scan]
      split
      · exact Nat.succ_le_succ (Nat.zero_le rest.length)
      · simp only [List.length_cons]
        exact Nat.succ_le_succ ih

/-- Store and token zero are refusal sentinels. Parent lineage is not a
registry field and cannot be authenticated by this lookup alone. -/
def lookup (registry : Registry Address Provider) (handle : Handle Address Provider) :
    Option Nat × Nat :=
  if handle.store = 0 ∨ handle.store ≠ registry.identity ∨ handle.row.token = 0 then
    (none, 0)
  else scan handle.row registry.rows

def Authenticated (registry : Registry Address Provider)
    (handle : Handle Address Provider) : Prop :=
  handle.store ≠ 0 ∧ handle.store = registry.identity ∧
    handle.row.token ≠ 0 ∧ handle.row ∈ registry.rows

omit [DecidableEq Address] [DecidableEq Provider] in
/-- Reordering complete issued rows preserves authority. Physical lookup
positions and their charged work are deliberately absent from this observer. -/
theorem authentication_of_rows_perm (left right : Registry Address Provider)
    (identity : left.identity = right.identity) (rows : left.rows.Perm right.rows)
    (handle : Handle Address Provider) :
    Authenticated left handle ↔ Authenticated right handle := by
  simp only [Authenticated, identity, rows.mem_iff]

theorem lookup_authenticates (registry : Registry Address Provider)
    (handle : Handle Address Provider) :
    (lookup registry handle).1 ≠ none ↔ Authenticated registry handle := by
  by_cases invalid : handle.store = 0 ∨ handle.store ≠ registry.identity ∨ handle.row.token = 0
  · simp only [lookup, if_pos invalid, ne_eq, not_true_eq_false]
    simp only [Authenticated]
    tauto
  · simp only [lookup, if_neg invalid, Authenticated, ne_eq, scan_none_iff]
    tauto

theorem lookup_wrong_store (registry : Registry Address Provider)
    (handle : Handle Address Provider) (wrong : handle.store ≠ registry.identity) :
    lookup registry handle = (none, 0) := by
  simp [lookup, wrong]

theorem lookup_selected (registry : Registry Address Provider)
    (handle : Handle Address Provider) (index : Nat)
    (selected : (lookup registry handle).1 = some index) :
    registry.rows[index]? = some handle.row ∧ (lookup registry handle).2 = index + 1 := by
  by_cases invalid : handle.store = 0 ∨ handle.store ≠ registry.identity ∨ handle.row.token = 0
  · simp [lookup, invalid] at selected
  · simpa only [lookup, if_neg invalid] using
      scan_selected handle.row registry.rows index (by simpa only [lookup, if_neg invalid] using selected)

theorem lookup_visits_le (registry : Registry Address Provider) (handle : Handle Address Provider) :
    (lookup registry handle).2 ≤ registry.rows.length := by
  simp only [lookup]
  split
  · exact Nat.zero_le _
  · exact scan_visits_le handle.row registry.rows

def Row.map {B : Type} (address : Address → B) (row : Row Address Provider) : Row B Provider :=
  ⟨row.occurrence, row.token, address row.payload, row.provider⟩

omit [DecidableEq Address] [DecidableEq Provider] in
theorem Row.map_injective {B : Type} (address : Address → B)
    (injective : Function.Injective address) : Function.Injective (Row.map (Provider := Provider) address) := by
  intro left right same
  cases left
  cases right
  simp only [Row.map, Row.mk.injEq] at same ⊢
  exact ⟨same.1, same.2.1, injective same.2.2.1, same.2.2.2⟩

theorem rowMatches_map {B : Type} [DecidableEq B] (address : Address → B)
    (injective : Function.Injective address) (row wanted : Row Address Provider) :
    rowMatches (row.map address) (wanted.map address) = rowMatches row wanted := by
  apply Bool.eq_iff_iff.mpr
  rw [rowMatches_iff, rowMatches_iff]
  exact ⟨fun same => Row.map_injective address injective same, congrArg (Row.map address)⟩

/-- A single injective relocation keeps the actual slot and its lookup cost.
Equal values at different addresses are not coalesced. -/
theorem scan_map {B : Type} [DecidableEq B] (address : Address → B)
    (injective : Function.Injective address) (wanted : Row Address Provider)
    (rows : List (Row Address Provider)) :
    scan (wanted.map address) (rows.map (Row.map address)) = scan wanted rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [List.map_cons, scan, rowMatches_map address injective, ih]

def Registry.relocate {B : Type} (fresh : Nat) (address : Address → B)
    (registry : Registry Address Provider) : Registry B Provider :=
  ⟨fresh, registry.rows.map (Row.map address)⟩

def Handle.relocate {B : Type} (fresh : Nat) (address : Address → B)
    (handle : Handle Address Provider) : Handle B Provider :=
  ⟨fresh, handle.parent, handle.row.map address⟩

/-- Only handles already owned by the source store enter this transport.
Blindly rekeying a foreign handle would discard that authentication premise. -/
theorem lookup_relocate {B : Type} [DecidableEq B] (address : Address → B)
    (injective : Function.Injective address) (registry : Registry Address Provider)
    (handle : Handle Address Provider) (fresh : Nat)
    (owned : handle.store = registry.identity) (sourceLive : registry.identity ≠ 0)
    (destinationLive : fresh ≠ 0) :
    lookup (registry.relocate fresh address) (handle.relocate fresh address) =
      lookup registry handle := by
  have sourceGuard :
      (handle.store = 0 ∨ handle.store ≠ registry.identity ∨ handle.row.token = 0) ↔
        handle.row.token = 0 := by
    rw [owned]
    simp [sourceLive]
  have destinationGuard :
      ((handle.relocate fresh address).store = 0 ∨
        (handle.relocate fresh address).store ≠ (registry.relocate fresh address).identity ∨
        (handle.relocate fresh address).row.token = 0) ↔ handle.row.token = 0 := by
    simp [Handle.relocate, Registry.relocate, Row.map, destinationLive]
  simp only [lookup, sourceGuard, destinationGuard]
  split
  · rfl
  · exact scan_map address injective handle.row registry.rows

theorem transported_authentication {B : Type} [DecidableEq B] (address : Address → B)
    (injective : Function.Injective address) (registry : Registry Address Provider)
    (handle : Handle Address Provider) (fresh : Nat)
    (owned : handle.store = registry.identity) (sourceLive : registry.identity ≠ 0)
    (destinationLive : fresh ≠ 0) :
    Authenticated (registry.relocate fresh address) (handle.relocate fresh address) ↔
      Authenticated registry handle := by
  rw [← lookup_authenticates, lookup_relocate address injective registry handle fresh
    owned sourceLive destinationLive, lookup_authenticates]

omit [DecidableEq Address] in
theorem old_return_refused {B : Type} [DecidableEq B] (address : Address → B)
    (registry : Registry Address Provider) (handle : Handle B Provider) (fresh : Nat)
    (old : handle.store = registry.identity) (different : registry.identity ≠ fresh) :
    lookup (registry.relocate fresh address) handle = (none, 0) := by
  apply lookup_wrong_store
  simpa only [Registry.relocate, old] using different

/-- Checked complete preparation preserves every issued-handle membership.
The prepared enumeration may change its scan positions and lookup costs. -/
theorem coverage_authentication (registry : Registry Address Provider)
    (proposed : List (Row Address Provider))
    (checked : OccurrenceIdentity.coverageCheck Row.occurrence registry.rows proposed = true)
    (handle : Handle Address Provider) :
    Authenticated { registry with rows := proposed } handle ↔ Authenticated registry handle := by
  have complete := (OccurrenceIdentity.coverageCheck_iff Row.occurrence registry.rows proposed).mp checked
  exact authentication_of_rows_perm {registry with rows := proposed} registry rfl complete.1 handle

/-- Payload root discovery keeps one physical root for aliases without
forgetting the logical occurrences checked by complete coverage. -/
theorem coverage_payload_roots (actual proposed : List (Row Address Provider))
    (checked : OccurrenceIdentity.coverageCheck Row.occurrence actual proposed = true)
    (owner : Owner) :
    answerRoots owner (proposed.map Row.payload) = answerRoots owner (actual.map Row.payload) := by
  have complete := (OccurrenceIdentity.coverageCheck_iff Row.occurrence actual proposed).mp checked
  ext pair
  rw [mem_answerRoots, mem_answerRoots]
  exact and_congr_right (fun _ => (complete.1.map Row.payload).mem_iff)

section GraphTransport

variable {B W : Type} [DecidableEq B]
variable {source : Heap Address Value} {destination : Heap B W}

/-- Authentication and liveness are distinct premises. One injective graph
copy preserves the issued slot, lookup work and every reachable payload path
after publication to a different owner and retirement of the original. -/
theorem transported_return_retirement (copy : Relocation source destination)
    (registry : Registry Address Provider) (handle : Handle Address Provider) (fresh : Nat)
    (owned : handle.store = registry.identity) (sourceLive : registry.identity ≠ 0)
    (destinationLive : fresh ≠ 0) (roots : Roots Owner Address)
    (originalOwner nextOwner : Owner) (different : nextOwner ≠ originalOwner)
    (ownedRoots : ∀ pair ∈ roots, pair.1 = originalOwner)
    (rooted : Live source roots handle.row.payload) (path : List Address) :
    lookup (registry.relocate fresh copy.address) (handle.relocate fresh copy.address) =
        lookup registry handle ∧
      walk (collect destination
        (release (transfer (copy.roots roots) originalOwner nextOwner) originalOwner))
        (copy.address handle.row.payload) (path.map copy.address) =
        (walk source handle.row.payload path).map (fun result =>
          (copy.address result.1, result.2.relocate copy.address copy.payload)) := by
  constructor
  · exact lookup_relocate copy.address copy.injective registry handle fresh
      owned sourceLive destinationLive
  · rw [walk_collect destination _
      (copy.live_after_source_retirement roots originalOwner nextOwner different ownedRoots _ rooted)]
    exact copy.walk_eq handle.row.payload path

end GraphTransport

namespace Controls

def source : Registry Nat Nat := ⟨17, [⟨7, 41, 0, 5⟩, ⟨8, 42, 0, 5⟩]⟩
def first : Handle Nat Nat := ⟨17, 6, ⟨7, 41, 0, 5⟩⟩
def second : Handle Nat Nat := ⟨17, 6, ⟨8, 42, 0, 5⟩⟩

/-- The target table is independently authored, with a relocated shared
payload and fresh physical store identity. Logical occurrences stay distinct. -/
def destination : Registry Nat Nat := ⟨31, [⟨7, 41, 10, 5⟩, ⟨8, 42, 10, 5⟩]⟩
def firstCopied : Handle Nat Nat := ⟨31, 6, ⟨7, 41, 10, 5⟩⟩
def secondCopied : Handle Nat Nat := ⟨31, 6, ⟨8, 42, 10, 5⟩⟩

theorem distinct_occurrences_share_payload :
    lookup source first = (some 0, 1) ∧ lookup source second = (some 1, 2) ∧
      lookup destination firstCopied = (some 0, 1) ∧
      lookup destination secondCopied = (some 1, 2) ∧
      firstCopied.row.payload = secondCopied.row.payload ∧
      firstCopied.row.occurrence ≠ secondCopied.row.occurrence := by decide

theorem exact_fields_and_fresh_store_are_required :
    lookup destination { firstCopied with store := 17 } = (none, 0) ∧
      lookup destination { firstCopied with row.token := 42 } = (none, 2) ∧
      lookup destination { firstCopied with row.occurrence := 8 } = (none, 2) ∧
      lookup destination { firstCopied with row.payload := 11 } = (none, 2) ∧
      lookup destination { firstCopied with row.provider := 9 } = (none, 2) := by decide

theorem zero_sentinels_decline_without_scan :
    lookup destination { firstCopied with store := 0 } = (none, 0) ∧
      lookup destination { firstCopied with row.token := 0 } = (none, 0) := by decide

/-- The four-field lease table does not attest to the externally retained
parent lineage. A separately checked parent checkpoint remains necessary. -/
theorem parent_lineage_is_external :
    lookup destination { firstCopied with parent := 999 } = (some 0, 1) := by decide

theorem blindly_rekeying_foreign_handle_authenticates :
    lookup source { first with store := 99 } = (none, 0) ∧
      lookup destination (({ first with store := 99 } : Handle Nat Nat).relocate
        31 (fun address => address + 10)) = (some 0, 1) := by decide

/-- Coalescing distinct payload addresses admits a handle refused at source,
even though occurrence and token have not changed. -/
theorem lossy_payload_map_invents_authentication :
    lookup source { first with row.payload := 1 } = (none, 2) ∧
      lookup (source.relocate 31 (fun _ => 0))
        (({ first with row.payload := 1 } : Handle Nat Nat).relocate 31 (fun _ => 0)) =
        (some 0, 1) := by decide

theorem complete_preparation_keeps_aliases_and_occurrences :
    OccurrenceIdentity.coverageCheck Row.occurrence source.rows [second.row, first.row] = true ∧
      OccurrenceIdentity.coverageCheck Row.occurrence source.rows [first.row, first.row] = false := by decide

open ResourceOwnership.Examples

def rootedRegistry : Registry (Fin 3) Nat := ⟨17, [⟨7, 41, 0, 5⟩]⟩
def rootedHandle : Handle (Fin 3) Nat := ⟨17, 6, ⟨7, 41, 0, 5⟩⟩
def copiedRegistry : Registry (Fin 4) Nat := ⟨31, [⟨7, 41, 1, 5⟩]⟩
def copiedHandle : Handle (Fin 4) Nat := ⟨31, 6, ⟨7, 41, 1, 5⟩⟩

/-- A transferred return remains authenticated and its shared cyclic
descendant can be read after the old owner has retired. -/
theorem transferred_return_keeps_cyclic_payload :
    lookup copiedRegistry copiedHandle = (some 0, 1) ∧
      walk (collect copiedHeap
        (release (transfer (shiftedCopy.roots ({(0, 0)} : Roots Nat (Fin 3))) 0 7) 0))
        1 [2, 3] = some (3, copiedCell 3) := by
  constructor
  · decide
  · have transported := transported_return_retirement shiftedCopy rootedRegistry rootedHandle 31
      (by decide) (by decide) (by decide) ({(0, 0)} : Roots Nat (Fin 3)) 0 7
      (by decide) (by intro pair member; exact congrArg Prod.fst (Finset.mem_singleton.mp member))
      (live_of_root cyclicHeap _ (owner := 0) (by decide) (by decide)) [1, 2]
    exact transported.2

/-- Successful registry lookup alone cannot keep any payload alive. -/
theorem accepted_handle_without_roots_loses_payload :
    lookup copiedRegistry copiedHandle = (some 0, 1) ∧
      walk (collect copiedHeap (∅ : Roots Nat (Fin 4))) 1 [2, 3] = none := by
  constructor
  · decide
  · have absent : (collect copiedHeap (∅ : Roots Nat (Fin 4))).lookup 1 = none :=
      lookup_collect_of_not_live copiedHeap _ (not_live_empty copiedHeap 1)
    simp only [walk, absent, Option.bind_none]

end Controls

/-! ## Issuing, returning and requeueing authenticated occurrences -/

open Mettapedia.Algebra.OccurrenceIdentity
open Mettapedia.Machines.Cursor.TailSummary

/-- Authentication charges the actual visited prefix even when no release
occurs. Success retires exactly that physical registry row and clears only
its issued authority; payload, provider, occurrence and parent are retained. -/
def releaseIssued (registry : Registry Address Provider) (handle : Handle Address Provider) :
    Option (Registry Address Provider × Handle Address Provider) × Nat :=
  let found := lookup registry handle
  let reply := do
    let index ← found.1
    let pair ← extractByLast index registry.rows
    some ({ registry with rows := pair.2 },
      { handle with store := 0, row.token := 0 })
  (reply, found.2)

theorem releaseIssued_account (registry : Registry Address Provider)
    (handle : Handle Address Provider) :
    (releaseIssued registry handle).2 = (lookup registry handle).2 := rfl

theorem releaseIssued_refused (registry : Registry Address Provider)
    (handle : Handle Address Provider) (refused : (lookup registry handle).1 = none) :
    releaseIssued registry handle = (none, (lookup registry handle).2) := by
  simp only [releaseIssued, refused, bind, Option.bind_none]

theorem releaseIssued_selected (registry : Registry Address Provider)
    (handle : Handle Address Provider) (index : Nat)
    (accepted : (lookup registry handle).1 = some index) :
    ∃ remaining,
      releaseIssued registry handle =
        (some ({ registry with rows := remaining },
          { handle with store := 0, row.token := 0 }), index + 1) ∧
      (handle.row :: remaining).Perm registry.rows := by
  obtain ⟨atIndex, cost⟩ := lookup_selected registry handle index accepted
  have picked := extractByLast_selected index registry.rows
  rw [atIndex] at picked
  obtain ⟨pair, extraction, same⟩ := Option.map_eq_some_iff.mp picked
  have selected : pair.1 = handle.row := same
  refine ⟨pair.2, ?_, ?_⟩
  · simp only [releaseIssued, accepted, extraction, cost, bind, Option.bind_some]
  · simpa only [← selected] using
      extractByLast_permutation index registry.rows pair.1 pair.2 extraction

/-- Every successful release preserves the namespace and removes exactly one
complete row. This exposes the actual extraction result without repeating its
lookup proof at each consumer. -/
theorem releaseIssued_remainder (registry : Registry Address Provider)
    (handle : Handle Address Provider) (next : Registry Address Provider)
    (cleared : Handle Address Provider)
    (released : (releaseIssued registry handle).1 = some (next, cleared)) :
    next.identity = registry.identity ∧ (handle.row :: next.rows).Perm registry.rows := by
  cases found : (lookup registry handle).1 with
  | none =>
      rw [releaseIssued_refused registry handle found] at released
      cases released
  | some index =>
      obtain ⟨remaining, exactRelease, retained⟩ := releaseIssued_selected registry handle index found
      rw [exactRelease] at released
      have same := congrArg Prod.fst (Option.some.inj released)
      dsimp only at same
      rw [← same]
      exact ⟨rfl, retained⟩

/-- When both release orders succeed, their remaining issued rows agree as a
multiset, with the original namespace. This says neither that the physical
arrays agree nor that their authentication scans cost the same. -/
theorem releaseIssued_commute
    (registry afterFirst afterSecond finalFirst finalSecond : Registry Address Provider)
    (first second clearedFirst clearedSecond clearedAfterFirst clearedAfterSecond :
      Handle Address Provider)
    (firstRelease : (releaseIssued registry first).1 = some (afterFirst, clearedFirst))
    (secondRelease : (releaseIssued registry second).1 = some (afterSecond, clearedSecond))
    (thenSecond : (releaseIssued afterFirst second).1 = some (finalFirst, clearedAfterFirst))
    (thenFirst : (releaseIssued afterSecond first).1 = some (finalSecond, clearedAfterSecond)) :
    finalFirst.identity = finalSecond.identity ∧ finalFirst.rows.Perm finalSecond.rows := by
  obtain ⟨firstId, firstRows⟩ := releaseIssued_remainder _ _ _ _ firstRelease
  obtain ⟨secondId, secondRows⟩ := releaseIssued_remainder _ _ _ _ secondRelease
  obtain ⟨finalFirstId, finalFirstRows⟩ := releaseIssued_remainder _ _ _ _ thenSecond
  obtain ⟨finalSecondId, finalSecondRows⟩ := releaseIssued_remainder _ _ _ _ thenFirst
  refine ⟨(finalFirstId.trans firstId).trans (finalSecondId.trans secondId).symm, ?_⟩
  have forward := (finalFirstRows.cons first.row).trans firstRows
  have backward := (finalSecondRows.cons second.row).trans secondRows
  have reordered := (List.Perm.swap second.row first.row finalSecond.rows).trans backward
  exact (forward.trans reordered.symm).cons_inv.cons_inv

/-- A release exists exactly when the independently specified issued authority
is present. Physical row extraction does not add an admission assumption. -/
theorem releaseIssued_exists_iff (registry : Registry Address Provider)
    (handle : Handle Address Provider) :
    (∃ next cleared, (releaseIssued registry handle).1 = some (next, cleared)) ↔
      Authenticated registry handle := by
  constructor
  · rintro ⟨next, cleared, released⟩
    apply (lookup_authenticates registry handle).mp
    intro missing
    rw [releaseIssued_refused registry handle missing] at released
    cases released
  · intro authorized
    have present := (lookup_authenticates registry handle).mpr authorized
    cases found : (lookup registry handle).1 with
    | none => exact (present found).elim
    | some index =>
      obtain ⟨remaining, released, _⟩ := releaseIssued_selected registry handle index found
      exact ⟨_, _, congrArg Prod.fst released⟩

theorem releaseIssued_keeps_other (registry : Registry Address Provider)
    (handle survivor : Handle Address Provider)
    (next : Registry Address Provider) (cleared : Handle Address Provider)
    (visits : Nat)
    (released : releaseIssued registry handle = (some (next, cleared), visits))
    (different : survivor.row ≠ handle.row) :
    Authenticated next survivor ↔ Authenticated registry survivor := by
  obtain ⟨sameId, retained⟩ :=
    releaseIssued_remainder registry handle next cleared (congrArg Prod.fst released)
  have sameMembers : survivor.row ∈ next.rows ↔ survivor.row ∈ registry.rows := by
    simpa only [List.mem_cons, different, false_or] using retained.mem_iff (a := survivor.row)
  simp only [Authenticated, sameId, sameMembers]

theorem releaseIssued_removes_unique (registry : Registry Address Provider)
    (handle : Handle Address Provider) (next : Registry Address Provider)
    (cleared : Handle Address Provider) (visits : Nat)
    (released : releaseIssued registry handle = (some (next, cleared), visits))
    (unique : registry.rows.Nodup) :
    handle.row ∉ next.rows ∧ next.rows.Nodup ∧ next.rows.length + 1 = registry.rows.length := by
  obtain ⟨_, retained⟩ :=
    releaseIssued_remainder registry handle next cleared (congrArg Prod.fst released)
  obtain ⟨removed, survivors⟩ := List.nodup_cons.mp (retained.nodup_iff.mpr unique)
  exact ⟨removed, survivors, retained.length_eq⟩



/-- Relocation commutes with physical-row release, including its visited-prefix
account and the complete surviving registry order. Only the issued handle is
rekeyed; clearing its authority remains clearing, rather than a new issue. -/
theorem releaseIssued_relocate {B : Type} [DecidableEq B]
    (address : Address → B) (injective : Function.Injective address)
    (registry : Registry Address Provider) (handle : Handle Address Provider)
    (fresh : Nat) (owned : handle.store = registry.identity)
    (sourceLive : registry.identity ≠ 0) (destinationLive : fresh ≠ 0) :
    releaseIssued (registry.relocate fresh address) (handle.relocate fresh address) =
      ((releaseIssued registry handle).1.map (fun pair =>
        (pair.1.relocate fresh address, pair.2.relocate 0 address)),
        (releaseIssued registry handle).2) := by
  unfold releaseIssued
  rw [lookup_relocate address injective registry handle fresh owned sourceLive destinationLive]
  cases found : (lookup registry handle).1 with
  | none => simp only [found, bind, Option.bind_none, Option.map_none]
  | some index =>
      simp only [found, Registry.relocate, bind, Option.bind_some, extractByLast_map]
      cases extractByLast index registry.rows with
      | none => rfl
      | some pair => rfl


namespace EditControls

def third : Row Nat Nat := ⟨9, 43, 0, 5⟩
def source : Registry Nat Nat := ⟨17, [Controls.first.row, Controls.second.row, third]⟩
def afterRelease : Registry Nat Nat := ⟨17, [third, Controls.second.row]⟩

theorem swapping_changes_later_lookup_cost :
    releaseIssued source Controls.first =
      (some (afterRelease, { Controls.first with store := 0, row.token := 0 }), 1) ∧
      lookup source ⟨17, 6, third⟩ = (some 2, 3) ∧
      lookup afterRelease ⟨17, 6, third⟩ = (some 0, 1) := by decide

theorem refused_authentication_retains_visited_work :
    releaseIssued source { Controls.first with row.provider := 999 } = (none, 3) ∧
      releaseIssued source { Controls.first with store := 999 } = (none, 0) := by decide

theorem release_preserves_payload_parent_and_provider :
    (releaseIssued source Controls.first).1.map (fun pair =>
      (pair.2.parent, pair.2.row.payload, pair.2.row.provider, pair.2.row.occurrence)) =
        some (6, 0, 5, 7) ∧
      (releaseIssued source { Controls.first with parent := 999 }).1.map (fun pair => pair.2.parent) =
        some 999 := by decide

private def twoReleases (registry : Registry Nat Nat) (first second : Handle Nat Nat) :
    Option (Registry Nat Nat × Nat) :=
  let before := releaseIssued registry first
  before.1.bind fun intermediate =>
    let after := releaseIssued intermediate.1 second
    after.1.map fun result => (result.1, before.2 + after.2)

/-- The same surviving authority can have different physical row orders. -/
theorem independent_release_order_changes_layout :
    let fourth : Row Nat Nat := ⟨10, 44, 0, 5⟩
    let registry : Registry Nat Nat :=
      ⟨17, [Controls.first.row, Controls.second.row, third, fourth]⟩
    twoReleases registry Controls.first Controls.second =
      some (⟨17, [fourth, third]⟩, 3) ∧
    twoReleases registry Controls.second Controls.first =
      some (⟨17, [third, fourth]⟩, 3) ∧
    twoReleases registry Controls.first Controls.second ≠
      twoReleases registry Controls.second Controls.first := by decide

/-- Even when the final physical registry agrees, scan costs can differ. -/
theorem independent_release_order_changes_cost :
    twoReleases source Controls.first ⟨17, 6, third⟩ =
      some (⟨17, [Controls.second.row]⟩, 2) ∧
    twoReleases source ⟨17, 6, third⟩ Controls.first =
      some (⟨17, [Controls.second.row]⟩, 4) := by decide

end EditControls

namespace TransportEditControls

def moved : Registry Nat Nat := EditControls.source.relocate 70 (fun n => n + 10)
def movedFirst : Handle Nat Nat := Controls.first.relocate 70 (fun n => n + 10)

theorem release_keeps_aliases_and_scan_positions :
    releaseIssued moved movedFirst =
      (some (EditControls.afterRelease.relocate 70 (fun n => n + 10),
        ({ Controls.first with store := 0, row.token := 0 }).relocate 0 (fun n => n + 10)), 1) ∧
      lookup (EditControls.afterRelease.relocate 70 (fun n => n + 10))
        ((⟨17, 6, EditControls.third⟩ : Handle Nat Nat).relocate 70 (fun n => n + 10)) =
        (some 0, 1) := by decide

theorem stale_handle_is_not_rekeyed_by_release :
    releaseIssued moved Controls.first = (none, 0) := by decide

end TransportEditControls


/-- Separate issued occurrences and tokens; payloads may be shared. Positive
identity fields are namespace authority, not a pointer-lifetime proof. -/
def Registry.Valid (registry : Registry Address Provider) : Prop :=
  registry.identity ≠ 0 ∧
    (registry.rows.map Row.occurrence).Nodup ∧
    (registry.rows.map Row.token).Nodup ∧
    ∀ row ∈ registry.rows, row.occurrence ≠ 0 ∧ row.token ≠ 0

omit [DecidableEq Address] [DecidableEq Provider] in
theorem Registry.Valid.rows_unique (registry : Registry Address Provider)
    (valid : registry.Valid) : registry.rows.Nodup :=
  List.Nodup.of_map Row.occurrence valid.2.1

theorem releaseIssued_preserves_validity (registry : Registry Address Provider)
    (handle : Handle Address Provider) (next : Registry Address Provider)
    (cleared : Handle Address Provider) (visits : Nat)
    (valid : registry.Valid)
    (released : releaseIssued registry handle = (some (next, cleared), visits)) :
    next.Valid := by
  obtain ⟨sameId, retained⟩ :=
    releaseIssued_remainder registry handle next cleared (congrArg Prod.fst released)
  refine ⟨sameId ▸ valid.1, ?_, ?_, ?_⟩
  · have whole := (retained.map Row.occurrence).nodup_iff.mpr valid.2.1
    exact (List.nodup_cons.mp whole).2
  · have whole := (retained.map Row.token).nodup_iff.mpr valid.2.2.1
    exact (List.nodup_cons.mp whole).2
  · intro row present
    exact valid.2.2.2 row (retained.mem_iff.mp (List.mem_cons_of_mem _ present))

theorem releaseIssued_revokes_old_and_cleared (registry : Registry Address Provider)
    (handle : Handle Address Provider) (next : Registry Address Provider)
    (cleared : Handle Address Provider) (visits : Nat)
    (valid : registry.Valid)
    (released : releaseIssued registry handle = (some (next, cleared), visits)) :
    ¬ Authenticated next handle ∧ lookup next cleared = (none, 0) := by
  have removed := releaseIssued_removes_unique registry handle next cleared visits released
    (valid.rows_unique registry)
  have noOld : ¬ Authenticated next handle := by
    intro authorized
    exact removed.1 authorized.2.2.2
  refine ⟨noOld, ?_⟩
  cases found : (lookup registry handle).1 with
  | none =>
      rw [releaseIssued_refused registry handle found] at released
      cases (congrArg (fun result => result.1) released)
  | some index =>
      obtain ⟨remaining, exactRelease, _⟩ := releaseIssued_selected registry handle index found
      rw [exactRelease] at released
      have equality := Option.some.inj (congrArg Prod.fst released)
      have sameHandle := congrArg Prod.snd equality
      dsimp only at sameHandle
      rw [← sameHandle]
      simp [lookup]

namespace ValidEditControls

theorem registry_keys_are_independent_of_aliases :
    EditControls.source.Valid ∧
      EditControls.source.rows.map Row.payload = [0, 0, 0] := by unfold Registry.Valid; decide

theorem duplicate_occurrence_with_different_token_is_invalid :
    ¬ ({ EditControls.source with rows :=
      [Controls.first.row, { Controls.first.row with token := 100 }] }).Valid := by unfold Registry.Valid; decide

theorem duplicate_token_with_different_occurrence_is_invalid :
    ¬ ({ EditControls.source with rows :=
      [Controls.first.row, { Controls.first.row with occurrence := 100 }] }).Valid := by unfold Registry.Valid; decide

end ValidEditControls


/-- A failed complete prefix remains in the charge when a following segment
supplies the first matching row. No membership claim is imported from a
compiled getter. -/
theorem scan_append_of_missing (wanted : Row Address Provider)
    (prior following : List (Row Address Provider)) (absent : wanted ∉ prior) :
    scan wanted (prior ++ following) =
      ((scan wanted following).1.map (fun index => prior.length + index),
        prior.length + (scan wanted following).2) := by
  induction prior with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.zero_add]
      cases result : scan wanted following with
      | mk found visits =>
          cases found <;> rfl
  | cons row rest ih =>
      have different : rowMatches row wanted = false := by
        apply Bool.eq_false_iff.mpr
        intro same
        exact absent (List.mem_cons.mpr (Or.inl ((rowMatches_iff row wanted).mp same).symm))
      have tailAbsent : wanted ∉ rest := fun h => absent (List.mem_cons_of_mem row h)
      rw [List.cons_append, scan, different]
      simp only [Bool.false_eq_true, if_false, ih tailAbsent, List.length_cons,
        Option.map_map, Nat.add_assoc, Nat.add_comm]
      congr 2
      funext index
      simp only [Function.comp_apply]
      omega

/-- Issued-row publication after its reservation and queue-selection boundary.
Only the token and store are new; the parent and payload/provider occurrence
come from the selected handle. Allocation and selection costs are separate. -/
def registerIssued (registry : Registry Address Provider)
    (selected : Handle Address Provider) (token : Nat) :
    Registry Address Provider × Handle Address Provider :=
  let issued := { selected with store := registry.identity, row.token := token }
  ({ registry with rows := registry.rows ++ [issued.row] }, issued)

omit [DecidableEq Address] [DecidableEq Provider] in
theorem registerIssued_authenticates (registry : Registry Address Provider)
    (selected : Handle Address Provider) (token : Nat)
    (live : registry.identity ≠ 0) (positive : token ≠ 0) :
    Authenticated (registerIssued registry selected token).1
      (registerIssued registry selected token).2 := by
  simp [registerIssued, Authenticated, live, positive]

theorem registerIssued_lookup (registry : Registry Address Provider)
    (selected : Handle Address Provider) (token : Nat)
    (live : registry.identity ≠ 0) (positive : token ≠ 0)
    (freshOccurrence : selected.row.occurrence ∉ registry.rows.map Row.occurrence) :
    lookup (registerIssued registry selected token).1
      (registerIssued registry selected token).2 =
      (some registry.rows.length, registry.rows.length + 1) := by
  have absent : { selected.row with token := token } ∉ registry.rows := by
    intro present
    apply freshOccurrence
    exact List.mem_map.mpr ⟨_, present, rfl⟩
  change lookup
    ⟨registry.identity, registry.rows ++ [{ selected.row with token := token }]⟩
    ⟨registry.identity, selected.parent, { selected.row with token := token }⟩ = _
  simp only [lookup, live, positive, ne_eq]
  rw [scan_append_of_missing _ _ _ absent]
  simp [scan, rowMatches]

omit [DecidableEq Address] [DecidableEq Provider] in
theorem registerIssued_preserves_validity (registry : Registry Address Provider)
    (selected : Handle Address Provider) (token : Nat)
    (valid : registry.Valid) (positiveOccurrence : selected.row.occurrence ≠ 0)
    (positiveToken : token ≠ 0)
    (freshOccurrence : selected.row.occurrence ∉ registry.rows.map Row.occurrence)
    (freshToken : token ∉ registry.rows.map Row.token) :
    (registerIssued registry selected token).1.Valid := by
  refine ⟨valid.1, ?_, ?_, ?_⟩
  · simpa only [registerIssued, List.map_append, List.map_cons, List.map_nil,
      List.concat_eq_append] using
      (List.Nodup.concat freshOccurrence valid.2.1)
  · simpa only [registerIssued, List.map_append, List.map_cons, List.map_nil,
      List.concat_eq_append] using
      (List.Nodup.concat freshToken valid.2.2.1)
  · intro row member
    simp only [registerIssued, List.mem_append, List.mem_singleton] at member
    rcases member with before | added
    · exact valid.2.2.2 row before
    · subst row
      exact ⟨positiveOccurrence, positiveToken⟩

namespace IssueEditControls

def selected : Handle Nat Nat := ⟨0, 7, ⟨10, 0, 0, 5⟩⟩

theorem last_token_is_issued_and_looked_up :
    reserveInclusive 255 255 = (some 255, 0) ∧
      lookup (registerIssued EditControls.source selected 255).1
        (registerIssued EditControls.source selected 255).2 = (some 3, 4) ∧
      (registerIssued EditControls.source selected 255).2.parent = 7 := by decide

theorem equal_payloads_do_not_erase_the_new_occurrence :
    (registerIssued EditControls.source selected 44).1.rows.map Row.payload = [0, 0, 0, 0] ∧
      (registerIssued EditControls.source selected 44).1.rows.map Row.occurrence = [7, 8, 9, 10] :=
    by decide

end IssueEditControls

/-- Logical key checks for requeue admission; addresses and provider identities
are not occurrence keys. The charged scan stops at the first duplicate. -/
def missingOccurrenceBits (occurrence : Nat) (queue : List (Handle Address Provider)) : List Bool :=
  queue.map (fun handle => handle.row.occurrence != occurrence)

omit [DecidableEq Address] [DecidableEq Provider] in
theorem missingOccurrenceBits_complete (occurrence : Nat)
    (queue : List (Handle Address Provider)) :
    scanAll (missingOccurrenceBits occurrence queue) = true ↔
      occurrence ∉ queue.map (fun handle => handle.row.occurrence) := by
  rw [scanAll_eq_true_iff]
  simp [missingOccurrenceBits, List.mem_map]

omit [DecidableEq Address] [DecidableEq Provider] in
theorem missingOccurrenceBits_full_cost (occurrence : Nat)
    (queue : List (Handle Address Provider))
    (fresh : occurrence ∉ queue.map (fun handle => handle.row.occurrence)) :
    scanAllCost (missingOccurrenceBits occurrence queue) = queue.length := by
  have all := (scanAll_eq_true_iff _).mp ((missingOccurrenceBits_complete occurrence queue).mpr fresh)
  simpa [missingOccurrenceBits] using scanAllCost_eq_length _ all

/-- The committed store edit after lookup, duplicate refusal, and successful
buffer reservation. The complete queue is retained; returned authority is
cleared. Allocation and layout effects precede this edit and are separate. -/
def commitRequeue (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (index : Nat) : Option (Registry Address Provider × List (Handle Address Provider)) := do
  let pair ← extractByLast index registry.rows
  some ({ registry with rows := pair.2 },
    queue ++ [{ handle with store := 0, row.token := 0 }])

theorem commitRequeue_correspondence (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (index : Nat) (accepted : (lookup registry handle).1 = some index) :
    commitRequeue registry queue handle index =
      (releaseIssued registry handle).1.map (fun pair => (pair.1, queue ++ [pair.2])) := by
  simp only [commitRequeue, releaseIssued, accepted, bind, Option.bind_some]
  cases extractByLast index registry.rows with
  | none => rfl
  | some pair => rfl

theorem commitRequeue_retains_frontier (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (index : Nat) (accepted : (lookup registry handle).1 = some index) :
    ∃ remaining,
      commitRequeue registry queue handle index =
        some ({ registry with rows := remaining },
          queue ++ [{ handle with store := 0, row.token := 0 }]) ∧
      (handle.row :: remaining).Perm registry.rows ∧
      (queue ++ [{ handle with store := 0, row.token := 0 }]).map
        (fun item : Handle Address Provider => item.row.occurrence) =
          queue.map (fun item : Handle Address Provider => item.row.occurrence) ++ [handle.row.occurrence] := by
  obtain ⟨remaining, exactRelease, retained⟩ := releaseIssued_selected registry handle index accepted
  refine ⟨remaining, ?_, retained, ?_⟩
  · rw [commitRequeue_correspondence registry queue handle index accepted, exactRelease]
    rfl
  · simp

omit [DecidableEq Address] [DecidableEq Provider] in
/-- Every previously issued row keeps its authority when a fresh row is
appended. This does not validate the lifetime of its external owner. -/
theorem registerIssued_keeps_other (registry : Registry Address Provider)
    (selected survivor : Handle Address Provider) (token : Nat)
    (authorized : Authenticated registry survivor) :
    Authenticated (registerIssued registry selected token).1 survivor := by
  rcases authorized with ⟨positiveStore, sameStore, positiveToken, present⟩
  exact ⟨positiveStore, sameStore, positiveToken, List.mem_append_left _ present⟩

/-- Extract the committed edit's exact release. No second lookup or issue is
performed by the edit, so the prior scanned prefix is its only lookup charge. -/
theorem commitRequeue_release (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (index : Nat) (accepted : (lookup registry handle).1 = some index)
    (next : Registry Address Provider) (pending : List (Handle Address Provider))
    (committed : commitRequeue registry queue handle index = some (next, pending)) :
    releaseIssued registry handle =
      (some (next, { handle with store := 0, row.token := 0 }), index + 1) ∧
      pending = queue ++ [{ handle with store := 0, row.token := 0 }] := by
  obtain ⟨remaining, edit, _⟩ := commitRequeue_retains_frontier registry queue handle index accepted
  rw [edit] at committed
  have equality := Option.some.inj committed
  have sameRegistry := congrArg Prod.fst equality
  have sameQueue := congrArg Prod.snd equality
  dsimp only at sameRegistry sameQueue
  constructor
  · obtain ⟨remaining', release, _⟩ := releaseIssued_selected registry handle index accepted
    rw [commitRequeue_correspondence registry queue handle index accepted, release] at edit
    have equality' := Option.some.inj edit
    have remainingSame := congrArg (fun pair => pair.1.rows) equality'
    dsimp only at remainingSame
    rw [release, remainingSame, sameRegistry]
  · exact sameQueue.symm

theorem commitRequeue_valid_and_revoked (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (index : Nat) (accepted : (lookup registry handle).1 = some index)
    (next : Registry Address Provider) (pending : List (Handle Address Provider))
    (valid : registry.Valid)
    (committed : commitRequeue registry queue handle index = some (next, pending)) :
    next.Valid ∧ ¬ Authenticated next handle := by
  have release := (commitRequeue_release registry queue handle index accepted next pending committed).1
  exact ⟨releaseIssued_preserves_validity registry handle next _ _ valid release,
    (releaseIssued_revokes_old_and_cleared registry handle next _ _ valid release).1⟩

/-- Conservation as a bag of production fields, including shared payloads.
Registry slot order and authority remain separate observable components. -/
theorem commitRequeue_keyed_values {Value : Type}
    (reading : Nat → Address → Provider → Value)
    (registry : Registry Address Provider) (queue : List (Handle Address Provider))
    (handle : Handle Address Provider) (index : Nat)
    (accepted : (lookup registry handle).1 = some index)
    (next : Registry Address Provider) (pending : List (Handle Address Provider))
    (committed : commitRequeue registry queue handle index = some (next, pending)) :
    ((pending.map (fun item => reading item.row.occurrence item.row.payload item.row.provider)) ++
      next.rows.map (fun row => reading row.occurrence row.payload row.provider)).Perm
      ((queue.map (fun item => reading item.row.occurrence item.row.payload item.row.provider)) ++
        registry.rows.map (fun row => reading row.occurrence row.payload row.provider)) := by
  obtain ⟨remaining, edit, retained, _⟩ := commitRequeue_retains_frontier registry queue handle index accepted
  rw [edit] at committed
  have equality := Option.some.inj committed
  have sameRegistry := congrArg Prod.fst equality
  have sameQueue := congrArg Prod.snd equality
  dsimp only at sameRegistry sameQueue
  rw [← sameRegistry, ← sameQueue]
  simpa only [List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.singleton_append] using
    ((retained.map (fun row => reading row.occurrence row.payload row.provider)).append_left
      (queue.map (fun item => reading item.row.occurrence item.row.payload item.row.provider)))

namespace RequeueEditControls

def queued : List (Handle Nat Nat) := [IssueEditControls.selected]

theorem requeue_retains_order_payload_alias_and_parent :
    commitRequeue EditControls.source queued Controls.first 0 =
      some (EditControls.afterRelease,
        [IssueEditControls.selected, { Controls.first with store := 0, row.token := 0 }]) ∧
      (Controls.first.parent, Controls.first.row.payload) = (6, 0) := by decide

theorem duplicate_occurrence_is_refused_despite_different_payload :
    Mettapedia.Machines.Cursor.TailSummary.scanAll
      (missingOccurrenceBits 7
        [{ Controls.first with store := 0, row.token := 0, row.payload := 100 }]) = false ∧
      Mettapedia.Machines.Cursor.TailSummary.scanAllCost
        (missingOccurrenceBits 7
          [IssueEditControls.selected,
            { Controls.first with store := 0, row.token := 0, row.payload := 100 },
            Controls.second]) = 2 := by decide

end RequeueEditControls

/-- Read-only requeue preflight: authenticate before checking queued keys.
Its receipt contains exactly the rows visited by those two scans. Buffer
reservation and the committed edit are different operations. -/
def preflightRequeue (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider) : Option Nat × Nat :=
  let found := lookup registry handle
  match found.1 with
  | none => (none, found.2)
  | some index =>
      let bits := missingOccurrenceBits handle.row.occurrence queue
      (if scanAll bits then some index else none, found.2 + scanAllCost bits)

theorem preflightRequeue_refused_authority (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (refused : (lookup registry handle).1 = none) :
    preflightRequeue registry queue handle = (none, (lookup registry handle).2) := by
  simp only [preflightRequeue, refused]

theorem preflightRequeue_exact (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (index : Nat) (accepted : (lookup registry handle).1 = some index)
    (fresh : handle.row.occurrence ∉ queue.map (fun item => item.row.occurrence)) :
    preflightRequeue registry queue handle = (some index, index + 1 + queue.length) := by
  have scan := (missingOccurrenceBits_complete handle.row.occurrence queue).mpr fresh
  have cost := missingOccurrenceBits_full_cost handle.row.occurrence queue fresh
  have visited := (lookup_selected registry handle index accepted).2
  simp only [preflightRequeue, accepted, scan, if_true, cost, visited]

theorem preflightRequeue_success_iff (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (index : Nat) :
    (preflightRequeue registry queue handle).1 = some index ↔
      (lookup registry handle).1 = some index ∧
        handle.row.occurrence ∉ queue.map (fun item => item.row.occurrence) := by
  unfold preflightRequeue
  cases selected : (lookup registry handle).1 with
  | none => simp [selected]
  | some found =>
      by_cases allowed : scanAll (missingOccurrenceBits handle.row.occurrence queue) = true
      · have fresh := (missingOccurrenceBits_complete handle.row.occurrence queue).mp allowed
        simp [selected, allowed, fresh]
      · have duplicate : ¬ handle.row.occurrence ∉ queue.map (fun item => item.row.occurrence) := by
          intro fresh
          exact allowed ((missingOccurrenceBits_complete handle.row.occurrence queue).mpr fresh)
        constructor
        · intro impossible
          simp [selected, allowed] at impossible
        · rintro ⟨_, fresh⟩
          exact (duplicate fresh).elim

/-- Relocating addresses and the store authority preserves both scan phases.
The queue's occurrence keys and their order remain the same. -/
theorem preflightRequeue_relocate {B : Type} [DecidableEq B]
    (address : Address → B) (injective : Function.Injective address)
    (registry : Registry Address Provider) (queue : List (Handle Address Provider))
    (handle : Handle Address Provider) (fresh : Nat)
    (owned : handle.store = registry.identity)
    (sourceLive : registry.identity ≠ 0) (destinationLive : fresh ≠ 0) :
    preflightRequeue (registry.relocate fresh address)
      (queue.map (Handle.relocate 0 address)) (handle.relocate fresh address) =
        preflightRequeue registry queue handle := by
  unfold preflightRequeue
  rw [lookup_relocate address injective registry handle fresh owned sourceLive destinationLive]
  have bits : missingOccurrenceBits (handle.relocate fresh address).row.occurrence
      (queue.map (Handle.relocate 0 address)) =
        missingOccurrenceBits handle.row.occurrence queue := by
    simp [missingOccurrenceBits, List.map_map, Handle.relocate, Row.map]
  simp only [bits]

namespace PreflightControls

theorem duplicate_refusal_retains_both_scan_prefixes :
    preflightRequeue EditControls.source
      [IssueEditControls.selected, Controls.first, Controls.second] Controls.first = (none, 3) ∧
      preflightRequeue EditControls.source [Controls.first]
        { Controls.first with store := 999 } = (none, 0) := by decide

theorem shared_payload_does_not_refuse_requeue :
    preflightRequeue EditControls.source [IssueEditControls.selected] Controls.first = (some 0, 2) :=
    by decide

end PreflightControls

/-- Every retained token precedes the next token; zero is an exhausted
frontier and cannot be used for a further issue. -/
def Registry.TokensBefore (registry : Registry Address Provider) (next : Nat) : Prop :=
  next = 0 ∨ ∀ row ∈ registry.rows, row.token < next

omit [DecidableEq Address] [DecidableEq Provider] in
theorem issued_token_is_fresh (registry : Registry Address Provider)
    (maximum current issued after : Nat)
    (before : registry.TokensBefore current)
    (reserved : reserveInclusive maximum current = (some issued, after)) :
    issued ≠ 0 ∧ issued ∉ registry.rows.map Row.token := by
  obtain ⟨positive, _, same, _⟩ := (reserveInclusive_issued_iff _ _ _ _).mp reserved
  have rows := before.resolve_left (by omega)
  refine ⟨by omega, ?_⟩
  intro present
  obtain ⟨row, member, equality⟩ := List.mem_map.mp present
  have below := rows row member
  omega

omit [DecidableEq Address] [DecidableEq Provider] in
theorem registerIssued_preserves_token_frontier (registry : Registry Address Provider)
    (selected : Handle Address Provider) (maximum current issued after : Nat)
    (before : registry.TokensBefore current)
    (reserved : reserveInclusive maximum current = (some issued, after)) :
    (registerIssued registry selected issued).1.TokensBefore after := by
  obtain ⟨positive, _, same, next⟩ := (reserveInclusive_issued_iff _ _ _ _).mp reserved
  have rows := before.resolve_left (by omega)
  by_cases final : current = maximum
  · left
    simpa only [final, if_true] using next
  · right
    intro row present
    simp only [registerIssued, List.mem_append, List.mem_singleton] at present
    rcases present with old | new
    · have below := rows row old
      simp only [final, if_false] at next
      omega
    · subst row
      simp only [final, if_false] at next
      dsimp only
      omega

omit [DecidableEq Address] [DecidableEq Provider] in
theorem registerIssued_valid_after_reservation (registry : Registry Address Provider)
    (selected : Handle Address Provider) (maximum current issued after : Nat)
    (valid : registry.Valid) (before : registry.TokensBefore current)
    (positiveOccurrence : selected.row.occurrence ≠ 0)
    (freshOccurrence : selected.row.occurrence ∉ registry.rows.map Row.occurrence)
    (reserved : reserveInclusive maximum current = (some issued, after)) :
    (registerIssued registry selected issued).1.Valid ∧
      (registerIssued registry selected issued).1.TokensBefore after := by
  have fresh := issued_token_is_fresh registry maximum current issued after before reserved
  exact ⟨registerIssued_preserves_validity registry selected issued valid positiveOccurrence
      fresh.1 freshOccurrence fresh.2,
    registerIssued_preserves_token_frontier registry selected maximum current issued after before reserved⟩

namespace TokenFrontierControls

theorem final_issue_keeps_namespace_valid :
    EditControls.source.TokensBefore 255 ∧
      (registerIssued EditControls.source IssueEditControls.selected 255).1.TokensBefore 0 ∧
      (registerIssued EditControls.source IssueEditControls.selected 255).1.Valid := by
  unfold Registry.TokensBefore Registry.Valid
  decide

theorem resetting_frontier_would_reissue_an_old_token :
    reserveInclusive 255 41 = (some 41, 42) ∧
      ¬ EditControls.source.TokensBefore 41 ∧
      ¬ (registerIssued EditControls.source IssueEditControls.selected 41).1.Valid := by
  unfold Registry.TokensBefore Registry.Valid
  decide

end TokenFrontierControls

end IssuedReturn

namespace Examples

open ResourceOwnership.Examples

def cursorSession : Session Nat (Fin 3) Nat Nat :=
  ⟨cyclicHeap, {(0, 0)}, 7⟩

def copiedCursorSession : Session Nat (Fin 4) Nat Nat :=
  relocateSession cursorSession copiedHeap shiftedCopy

def capturedPaths : List (Fin 3 × List (Fin 3)) :=
  [(0, [1, 2]), (0, [1, 2]), (0, [2])]

/-- The capture keeps two successful reads of a shared cyclic descendant
and one failed edge test. Retiring its source owner preserves all three. -/
theorem copied_paths_survive_retirement :
    RequestBorrow.observe (commit copiedCursorSession {0} 7 [1, 1, 1]).heap
      (RequestBorrow.relocatePaths relocationAddress capturedPaths) =
      [some (3, copiedCell 3), some (3, copiedCell 3), none] := by
  have copied := relocate_commit_paths cursorSession copiedHeap shiftedCopy {0} 7
    capturedPaths (by decide) (by intro query _; exact Finset.mem_univ query.1)
  exact copied

/-- The checked view is published to the output lifetime before the cursor
owner retires. Its three occurrences agree with the independent readout. -/
theorem checked_cursor_borrow_survives_retirement :
    (RequestBorrow.transport ⟨⟨0, 3⟩, cursorSession.heap⟩
      ⟨⟨7, 3⟩, copiedHeap⟩ shiftedCopy ⟨⟨0, 3⟩, capturedPaths⟩).bind
      (RequestBorrow.read ⟨⟨7, 3⟩, (commit copiedCursorSession {0} 7 [1, 1, 1]).heap⟩) =
      some [some (3, copiedCell 3), some (3, copiedCell 3), none] := by
  calc
    _ = (RequestBorrow.read ⟨⟨0, 3⟩, cursorSession.heap⟩
        (⟨⟨0, 3⟩, capturedPaths⟩ : RequestBorrow.View Nat (Fin 3))).map
        (List.map (Option.map fun pair =>
          (shiftedCopy.address pair.1,
            pair.2.relocate shiftedCopy.address shiftedCopy.payload))) :=
      relocate_commit_checked_borrow cursorSession copiedHeap shiftedCopy {0} 7 3
        ⟨0, 3⟩ ⟨⟨0, 3⟩, capturedPaths⟩ (by decide)
        (by intro query _; exact Finset.mem_univ query.1)
    _ = _ := by decide

/-- Publishing every path cannot convert an obsolete source generation
into an authorized borrow. The checker refuses before a destination read. -/
theorem checked_cursor_stale_borrow_refused :
    (RequestBorrow.transport ⟨⟨0, 4⟩, cursorSession.heap⟩
      ⟨⟨7, 3⟩, copiedHeap⟩ shiftedCopy ⟨⟨0, 3⟩, capturedPaths⟩).bind
      (RequestBorrow.read ⟨⟨7, 3⟩, (commit copiedCursorSession {0} 7 [1, 1, 1]).heap⟩) =
      none := by
  have different : (⟨0, 3⟩ : RequestBorrow.Stamp Nat) ≠ ⟨0, 4⟩ := by decide
  simp only [RequestBorrow.transport, RequestBorrow.View.transportIfCurrent, if_neg different, Option.bind_none]

/-- Retiring the output owner erases both successful observations, despite
the copied cells having existed before collection. -/
theorem retired_capture_owner_loses_paths :
    RequestBorrow.observe (commit copiedCursorSession {0} 0 [1, 1, 1]).heap
      (RequestBorrow.relocatePaths relocationAddress capturedPaths) = [none, none, none] := by
  have cleared : commitRoots copiedCursorSession.roots {0} 0 [1, 1, 1] = ∅ := by decide
  change RequestBorrow.observe (collect copiedHeap _) _ = _
  rw [cleared]
  have absent : (collect copiedHeap (∅ : Roots Nat (Fin 4))).lookup
      (relocationAddress 0) = none :=
    lookup_collect_of_not_live copiedHeap _ (not_live_empty copiedHeap 1)
  simp only [RequestBorrow.observe, RequestBorrow.relocatePaths, capturedPaths,
    List.map_cons, List.map_nil, walk, absent, Option.bind_none]

/-- Publishing the outer copied node cannot repair missing reference
relocation: the same endpoint payloads no longer provide the same paths. -/
theorem copied_outer_pointer_does_not_certify_capture :
    RequestBorrow.observe unrelocatedReferencesHeap
      (RequestBorrow.relocatePaths relocationAddress capturedPaths) = [none, none, none] ∧
    RequestBorrow.observe copiedHeap
      (RequestBorrow.relocatePaths relocationAddress capturedPaths) =
      [some (3, copiedCell 3), some (3, copiedCell 3), none] := by decide

/-- Two answer occurrences share one copied cyclic graph. Retiring the
cursor retains that graph once, while destination observations keep both
occurrences and the original semantic world. -/
theorem copied_duplicate_answers_survive :
    observe (commit copiedCursorSession {0} 1 [2, 2]).heap [2, 2] =
      [some (copiedCell 2), some (copiedCell 2)] ∧
    allocatedBytes (commit copiedCursorSession {0} 1 [2, 2]).heap = 32 ∧
      (commit copiedCursorSession {0} 1 [2, 2]).world = 7 := by
  constructor
  · exact duplicate_answer_observation copiedCursorSession {0} 1 2 (by decide) (by decide)
  · constructor
    · change allocatedBytes (collect copiedHeap
        (commitRoots copiedCursorSession.roots {0} 1 [2, 2])) = 32
      have rootsExact : commitRoots copiedCursorSession.roots {0} 1 [2, 2] =
          ({(1, 2)} : Roots Nat (Fin 4)) := by decide
      have valid : ValidRoots copiedHeap ({(1, 2)} : Roots Nat (Fin 4)) := by
        intro pair member
        have same := Finset.mem_singleton.mp member
        subst pair
        decide
      rw [rootsExact, allocatedBytes_collect, ← censusBytes_eq_retainedBytes copiedHeap _ valid]
      decide
    · rfl

/-- The yielded value is a descendant of the cursor's old root. Publishing
it to the caller preserves both it and its shared cyclic successor. -/
theorem export_before_close_survives :
    (commit cursorSession {0} 1 [1]).heap.lookup 1 = some (cyclicCell 1) ∧
    (commit cursorSession {0} 1 [1]).heap.lookup 2 = some (cyclicCell 2) := by
  have root : Live cyclicHeap (answerRoots 1 [1]) 1 :=
    live_of_root cyclicHeap _ (owner := 1) (by simp) (by decide)
  constructor
  · exact commit_preserves_answer_graph cursorSession {0} 1 [1] (by decide) root
  · exact commit_preserves_answer_graph cursorSession {0} 1 [1] (by decide)
      (live_step cyclicHeap _ root rfl (by decide))

/-- Closing before publishing an escaping answer destroys the cell that its
pointer used to denote. Publishing the answer before closing preserves it. -/
theorem close_before_export_loses_answer :
    (closeScope cursorSession {0}).heap.lookup 1 = none ∧
    (commit cursorSession {0} 1 [1]).heap.lookup 1 ≠ none := by
  constructor
  · apply closeScope_reclaims_final_owner
    intro pair member _
    have same : pair = (0, 0) := by simpa [cursorSession] using member
    simp [same]
  · rw [export_before_close_survives.1]
    exact Option.some_ne_none _

/-- Publishing into the very scope being cancelled cannot export a value. -/
theorem canceled_output_owner_is_not_export :
    (commit cursorSession {0} 0 [1]).heap.lookup 1 = none := by
  have cleared : commitRoots cursorSession.roots {0} 0 [1] = ∅ := by decide
  change (collect cyclicHeap _).lookup 1 = none
  rw [cleared]
  exact lookup_collect_of_not_live cyclicHeap _ (not_live_empty cyclicHeap 1)

end Examples

/-! ## Prepared proposals

The catalogue is an owner in the existing root set. Each taken proposal is
one address published by the existing `publish`, and the catalogue cancellation
is the existing `closeScope`. `commit` remains the one-owner form of the same
two steps. Payload, world, ordered path reads and reachable cells are the
observations already preserved by collection. An address still reached from
outside the catalogue is not untaken. Observer-only references and semantic
history retention stay the laws in `ResourceOwnership`.
-/

section PreparedProposals

/-- Iterated publication. Duplicate selected pairs share one physical root;
the caller's list keeps the occurrences. -/
def publishSelections (roots : Roots Owner Address)
    (selections : List (Owner × Address)) : Roots Owner Address :=
  selections.foldl (fun acc item => publish acc item.1 [item.2]) roots

theorem answerRoots_singleton (owner : Owner) (address : Address) :
    answerRoots owner [address] = {(owner, address)} := by
  ext pair
  rcases pair with ⟨other, located⟩
  simp only [mem_answerRoots, List.mem_singleton, Finset.mem_singleton, Prod.mk.injEq]

theorem publishSelections_step (roots : Roots Owner Address)
    (head : Owner × Address) (tail : List (Owner × Address)) :
    publishSelections roots (head :: tail) =
      publishSelections (publish roots head.1 [head.2]) tail := by
  unfold publishSelections
  simp only [List.foldl_cons]

theorem publishSelections_mono (roots : Roots Owner Address)
    (selections : List (Owner × Address)) :
    roots ⊆ publishSelections roots selections := by
  induction selections generalizing roots with
  | nil =>
      unfold publishSelections
      simp only [List.foldl_nil]
      exact Finset.Subset.refl roots
  | cons head tail ih =>
      rw [publishSelections_step]
      exact (publish_mono roots head.1 [head.2]).trans (ih _)

theorem publishSelections_selected (roots : Roots Owner Address)
    (selections : List (Owner × Address)) (owner : Owner) (address : Address)
    (member : (owner, address) ∈ selections) :
    (owner, address) ∈ publishSelections roots selections := by
  induction selections generalizing roots with
  | nil => cases member
  | cons head tail ih =>
      rw [publishSelections_step]
      rcases List.mem_cons.mp member with same | later
      · cases same
        refine publishSelections_mono _ tail ?_
        exact Finset.mem_union.mpr (Or.inr ((mem_answerRoots owner owner [address] address).mpr
          ⟨rfl, List.mem_singleton.mpr rfl⟩))
      · exact ih _ later

theorem publishSelections_eq (roots : Roots Owner Address)
    (selections : List (Owner × Address)) :
    publishSelections roots selections =
      roots ∪ (selections.map fun item => (item.1, item.2)).toFinset := by
  induction selections generalizing roots with
  | nil =>
      simp only [publishSelections, List.foldl_nil, List.map_nil, List.toFinset_nil,
        Finset.union_empty]
  | cons head tail ih =>
      rw [publishSelections_step, ih, publish, answerRoots_singleton, List.map_cons,
        List.toFinset_cons, Finset.insert_eq, Finset.union_assoc]

/-- A selected owner outside the catalogue still holds its exported root
after that catalogue is removed. -/
theorem selected_root_survives_catalogue (roots : Roots Owner Address)
    (selections : List (Owner × Address)) (catalogue : Finset Owner)
    (owner : Owner) (address : Address)
    (taken : (owner, address) ∈ selections) (distinct : owner ∉ catalogue) :
    (owner, address) ∈ cancel (publishSelections roots selections) catalogue :=
  (mem_cancel _ catalogue _).mpr
    ⟨publishSelections_selected roots selections owner address taken, distinct⟩

theorem selected_answer_survives_catalogue (roots : Roots Owner Address)
    (selections : List (Owner × Address)) (catalogue : Finset Owner)
    (owner : Owner) (proposal : Address)
    (taken : (owner, proposal) ∈ selections) (distinct : owner ∉ catalogue) :
    answerRoots owner [proposal] ⊆
      cancel (publishSelections roots selections) catalogue := by
  intro pair member
  rcases pair with ⟨other, located⟩
  obtain ⟨sameOwner, selectedAddress⟩ :=
    (mem_answerRoots owner other [proposal] located).mp member
  cases sameOwner
  cases List.mem_singleton.mp selectedAddress
  exact selected_root_survives_catalogue roots selections catalogue owner proposal taken distinct

/-- Publish every taken proposal, then cancel the catalogue once. -/
noncomputable def exportProposals (state : Session Owner Address Value World)
    (selections : List (Owner × Address)) (catalogue : Finset Owner) :
    Session Owner Address Value World :=
  closeScope { state with roots := publishSelections state.roots selections } catalogue

theorem exportProposals_world (state : Session Owner Address Value World)
    (selections : List (Owner × Address)) (catalogue : Finset Owner) :
    (exportProposals state selections catalogue).world = state.world := by
  unfold exportProposals
  rw [closeScope_world]

theorem exportProposals_preserves_reachable
    (state : Session Owner Address Value World)
    (selections : List (Owner × Address)) (catalogue : Finset Owner)
    (owner : Owner) (proposal target : Address)
    (taken : (owner, proposal) ∈ selections) (distinct : owner ∉ catalogue)
    (live : Live state.heap (answerRoots owner [proposal]) target) :
    (exportProposals state selections catalogue).heap.lookup target =
      state.heap.lookup target := by
  unfold exportProposals
  exact lookup_collect_of_live state.heap _
    (live_mono state.heap
      (selected_answer_survives_catalogue state.roots selections catalogue owner proposal
        taken distinct) live)

theorem exportProposals_preserves_payload
    (state : Session Owner Address Value World)
    (selections : List (Owner × Address)) (catalogue : Finset Owner)
    (owner : Owner) (proposal : Address)
    (taken : (owner, proposal) ∈ selections) (distinct : owner ∉ catalogue)
    (allocated : proposal ∈ state.heap.allocated) :
    (exportProposals state selections catalogue).heap.lookup proposal =
      state.heap.lookup proposal :=
  exportProposals_preserves_reachable state selections catalogue owner proposal proposal
    taken distinct (live_of_root state.heap _
      ((mem_answerRoots owner owner [proposal] proposal).mpr
        ⟨rfl, List.mem_singleton.mpr rfl⟩) allocated)

theorem exportProposals_preserves_context {Observation : Type}
    (state : Session Owner Address Value World)
    (selections : List (Owner × Address)) (catalogue : Finset Owner)
    (owner : Owner) (proposal : Address)
    (taken : (owner, proposal) ∈ selections) (distinct : owner ∉ catalogue)
    (allocated : proposal ∈ state.heap.allocated)
    (interpret : World → Option (Cell Address Value) → Observation) :
    observeContext (exportProposals state selections catalogue) [proposal] interpret =
      observeContext state [proposal] interpret := by
  unfold observeContext observe
  rw [exportProposals_world]
  simp only [List.map_cons, List.map_nil]
  rw [exportProposals_preserves_payload state selections catalogue owner proposal
    taken distinct allocated]

/-- Path starts that were exported remain readable, in order, after the
catalogue cancellation. The session world is the captured environment. -/
theorem exportProposals_preserves_paths
    (state : Session Owner Address Value World)
    (selections : List (Owner × Address)) (catalogue : Finset Owner)
    (paths : List (Address × List Address))
    (protectedStart : ∀ query ∈ paths, ∃ owner,
      (owner, query.1) ∈ selections ∧ owner ∉ catalogue)
    (allocated : ∀ query ∈ paths, query.1 ∈ state.heap.allocated) :
    RequestBorrow.observe (exportProposals state selections catalogue).heap paths =
      RequestBorrow.observe state.heap paths := by
  unfold exportProposals
  apply List.map_congr_left
  intro query member
  obtain ⟨owner, taken, distinct⟩ := protectedStart query member
  exact walk_collect state.heap _
    (live_of_root state.heap _
      (selected_root_survives_catalogue state.roots selections catalogue owner query.1
        taken distinct) (allocated query member)) query.2

/-- An address that survives neither an owner outside the catalogue nor a
taken proposal is reclaimed with the catalogue. A surviving outside root or a
selected graph, including a shared descendant, is a real reference and is not
claimed here. -/
theorem exportProposals_reclaims_unreferenced
    (state : Session Owner Address Value World)
    (selections : List (Owner × Address)) (catalogue : Finset Owner)
    (address : Address)
    (notOuter : ¬ Live state.heap (cancel state.roots catalogue) address)
    (notTaken : ∀ owner proposal, (owner, proposal) ∈ selections → owner ∉ catalogue →
      ¬ Live state.heap (answerRoots owner [proposal]) address) :
    (exportProposals state selections catalogue).heap.lookup address = none := by
  unfold exportProposals
  apply lookup_collect_of_not_live
  intro live
  rw [live_iff_root] at live
  obtain ⟨pair, member, origin⟩ := live
  obtain ⟨present, surviving⟩ := (mem_cancel _ catalogue pair).mp member
  rw [publishSelections_eq] at present
  rcases Finset.mem_union.mp present with original | selected
  · apply notOuter
    refine live_mono state.heap ?_ origin
    intro single singleMember
    have same : single = pair := Finset.mem_singleton.mp singleMember
    rw [same]
    exact (mem_cancel state.roots catalogue pair).mpr ⟨original, surviving⟩
  · obtain ⟨item, itemMember, samePair⟩ := List.mem_map.mp (List.mem_toFinset.mp selected)
    cases samePair
    exact notTaken item.1 item.2 itemMember surviving
      ((live_congr_rootAddresses state.heap {(item.1, item.2)}
        (answerRoots item.1 [item.2]) (by rw [answerRoots_singleton]) address).mp origin)

/-- Cancelling the catalogue before any export removes a proposal whose only
protecting roots belong to that catalogue. -/
theorem catalogue_cancel_before_export_reclaims
    (state : Session Owner Address Value World) (catalogue : Owner) (proposal : Address)
    (catalogueOnly : ∀ pair ∈ state.roots,
      Live state.heap {pair} proposal → pair.1 = catalogue) :
    (closeScope state {catalogue}).heap.lookup proposal = none :=
  closeScope_reclaims_final_owner state {catalogue} proposal (by
    intro pair member live
    exact Finset.mem_singleton.mpr (catalogueOnly pair member live))

/-- Publishing back into the owner being cancelled does not export. -/
theorem export_into_cancelled_owner_reclaims
    (state : Session Owner Address Value World) (owner : Owner) (proposal : Address)
    (noOutside : ∀ pair ∈ publish state.roots owner [proposal],
      Live state.heap {pair} proposal → pair.1 = owner) :
    (closeScope { state with
        roots := publish state.roots owner [proposal] } {owner}).heap.lookup proposal = none := by
  refine closeScope_reclaims_final_owner
    { state with roots := publish state.roots owner [proposal] } {owner} proposal ?_
  intro pair member live
  exact Finset.mem_singleton.mpr (noOutside pair member live)

theorem closeScope_preserves_sibling_payload
    (state : Session Owner Address Value World) (selected sibling : Owner)
    (proposal : Address) (different : sibling ≠ selected)
    (held : (sibling, proposal) ∈ state.roots)
    (allocated : proposal ∈ state.heap.allocated) :
    (closeScope state {selected}).heap.lookup proposal = state.heap.lookup proposal ∧
      (closeScope state {selected}).world = state.world := by
  have outside : sibling ∉ ({selected} : Finset Owner) := by
    intro member
    exact different (Finset.mem_singleton.mp member)
  have rooted : (sibling, proposal) ∈ cancel state.roots {selected} :=
    (mem_cancel state.roots {selected} (sibling, proposal)).mpr ⟨held, outside⟩
  exact ⟨lookup_collect_of_live state.heap _
      (live_of_root state.heap (cancel state.roots {selected}) rooted allocated),
    closeScope_world _ _⟩

theorem closeScope_preserves_sibling_graph
    (state : Session Owner Address Value World) (selected sibling : Owner)
    {address : Address} (different : sibling ≠ selected)
    (live : Live state.heap (state.roots.filter fun pair => pair.1 = sibling) address) :
    (closeScope state {selected}).heap.lookup address = state.heap.lookup address := by
  apply lookup_collect_of_live
  refine live_cancel_other_owner state.heap state.roots {selected} sibling ?_ live
  intro member
  exact different (Finset.mem_singleton.mp member)

/-- Cancelling every selected owner reclaims a resource that had no other
protector. Cancelling one of them does not. -/
theorem cancel_selected_pair_reclaims
    (state : Session Owner Address Value World) (first second : Owner)
    (address : Address)
    (onlyThese : ∀ pair ∈ state.roots,
      Live state.heap {pair} address → pair.1 = first ∨ pair.1 = second) :
    (closeScope state {first, second}).heap.lookup address = none := by
  refine closeScope_reclaims_final_owner state {first, second} address ?_
  intro pair member live
  rcases onlyThese pair member live with same | same
  · exact Finset.mem_insert.mpr (Or.inl same)
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr same))

/-- Export before catalogue retirement. `publish` installs each taken root and
`closeScope` retires the catalogue; one selected owner is the existing
`commit`. The selected cell, every cell reachable from it, the captured world
and the ordered path reads survive that retirement. -/
theorem export_before_catalogue_cancel {Observation : Type}
    (state : Session Owner Address Value World)
    (selections : List (Owner × Address)) (catalogue : Finset Owner)
    (owner : Owner) (proposal : Address)
    (paths : List (Address × List Address))
    (taken : (owner, proposal) ∈ selections) (distinct : owner ∉ catalogue)
    (allocated : proposal ∈ state.heap.allocated)
    (pathStarts : ∀ query ∈ paths, ∃ selectedOwner,
      (selectedOwner, query.1) ∈ selections ∧ selectedOwner ∉ catalogue)
    (pathAllocated : ∀ query ∈ paths, query.1 ∈ state.heap.allocated)
    (interpret : World → Option (Cell Address Value) → Observation) :
    (exportProposals state selections catalogue).heap.lookup proposal =
        state.heap.lookup proposal ∧
      (exportProposals state selections catalogue).world = state.world ∧
      observeContext (exportProposals state selections catalogue) [proposal] interpret =
        observeContext state [proposal] interpret ∧
      RequestBorrow.observe (exportProposals state selections catalogue).heap paths =
        RequestBorrow.observe state.heap paths ∧
      (∀ target, Live state.heap (answerRoots owner [proposal]) target →
        (exportProposals state selections catalogue).heap.lookup target =
          state.heap.lookup target) := by
  refine ⟨exportProposals_preserves_payload state selections catalogue owner proposal
      taken distinct allocated,
    exportProposals_world state selections catalogue,
    exportProposals_preserves_context state selections catalogue owner proposal
      taken distinct allocated interpret,
    exportProposals_preserves_paths state selections catalogue paths pathStarts pathAllocated,
    ?_⟩
  intro target live
  exact exportProposals_preserves_reachable state selections catalogue owner proposal target
    taken distinct live

section RelocationExport

variable {DestinationAddress DestinationValue : Type}
variable [DecidableEq DestinationAddress]

theorem relocate_publishSelections {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (selections : List (Owner × Address)) :
    copy.roots (publishSelections roots selections) =
      publishSelections (copy.roots roots)
        (selections.map fun item => (item.1, copy.address item.2)) := by
  induction selections generalizing roots with
  | nil =>
      simp only [publishSelections, List.foldl_nil, List.map_nil]
  | cons head tail ih =>
      rw [publishSelections_step, List.map_cons, publishSelections_step]
      have published : copy.roots (publish roots head.1 [head.2]) =
          publish (copy.roots roots) head.1 [copy.address head.2] := by
        unfold publish
        rw [show copy.roots (roots ∪ answerRoots head.1 [head.2]) =
          copy.roots roots ∪ copy.roots (answerRoots head.1 [head.2]) from
          Finset.image_union _ _]
        rw [relocate_answerRoots copy head.1 [head.2]]
        rfl
      rw [ih, published]

theorem relocate_exportProposals (state : Session Owner Address Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation state.heap destination)
    (selections : List (Owner × Address)) (catalogue : Finset Owner) :
    copy.roots (exportProposals state selections catalogue).roots =
      (exportProposals (relocateSession state destination copy)
        (selections.map fun item => (item.1, copy.address item.2)) catalogue).roots := by
  unfold exportProposals closeScope relocateSession
  rw [Relocation.roots_cancel, relocate_publishSelections]

theorem relocate_exportProposals_payload
    (state : Session Owner Address Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation state.heap destination)
    (selections : List (Owner × Address)) (catalogue : Finset Owner)
    (owner : Owner) (proposal : Address)
    (taken : (owner, proposal) ∈ selections) (distinct : owner ∉ catalogue)
    (allocated : proposal ∈ state.heap.allocated) :
    (exportProposals (relocateSession state destination copy)
        (selections.map fun item => (item.1, copy.address item.2)) catalogue).heap.lookup
      (copy.address proposal) =
      ((exportProposals state selections catalogue).heap.lookup proposal).map
        (Cell.relocate copy.address copy.payload) := by
  have mapped : (owner, copy.address proposal) ∈
      selections.map fun item => (item.1, copy.address item.2) :=
    List.mem_map.mpr ⟨(owner, proposal), taken, rfl⟩
  have allocatedDest : copy.address proposal ∈ destination.allocated :=
    (copy.allocated_iff proposal).mpr allocated
  rw [exportProposals_preserves_payload (relocateSession state destination copy)
    (selections.map fun item => (item.1, copy.address item.2)) catalogue owner
    (copy.address proposal) mapped distinct allocatedDest]
  rw [show (relocateSession state destination copy).heap = destination from rfl]
  rw [copy.lookup_eq, exportProposals_preserves_payload state selections catalogue owner
    proposal taken distinct allocated]

end RelocationExport

#print axioms commit_preserves_selected_observation
#print axioms commit_reclaims_unprotected
#print axioms answerRoots_singleton
#print axioms publishSelections_mono
#print axioms publishSelections_selected
#print axioms publishSelections_eq
#print axioms selected_root_survives_catalogue
#print axioms exportProposals_world
#print axioms exportProposals_preserves_payload
#print axioms exportProposals_preserves_context
#print axioms exportProposals_preserves_paths
#print axioms exportProposals_preserves_reachable
#print axioms exportProposals_reclaims_unreferenced
#print axioms catalogue_cancel_before_export_reclaims
#print axioms export_into_cancelled_owner_reclaims
#print axioms closeScope_preserves_sibling_payload
#print axioms closeScope_preserves_sibling_graph
#print axioms cancel_selected_pair_reclaims
#print axioms export_before_catalogue_cancel
#print axioms relocate_publishSelections
#print axioms relocate_exportProposals
#print axioms relocate_exportProposals_payload
#print axioms Mettapedia.Machines.ResourceOwnership.live_cancel_other_owner
#print axioms Mettapedia.Machines.ResourceOwnership.live_release_other_owner

end PreparedProposals

end Mettapedia.Machines.Cursor.OwnedLifecycle

namespace Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement

/-!
Retained cancellation is an owner protocol with a concrete normalizer
instance. The converted instance walks the initialized primary slot prefix,
then fixed frame fields and header buffers; source syntax is borrowed.
Ownership-ticket logs are semantic instrumentation, not runtime allocations.
Its finite rank, ordered reference and remaining-service invoice are proved
from the actual updates. They are specification readouts, never work done to
begin or advance retirement.

The enclosing owner, child owner and borrowed context are distinct. A pending
or atomic reply retains the actual residual, while a complete child reply
only arms a separate final owner release. Atomic permission places work; it
does not supply resource authority or extend any external lifetime. Native
decoding, serialization, live context holds, opaque services and physical
prices remain instance obligations. Inspection-fuel composition does not
assert equality of arbitrary native callback grants or their batch policies.
-/

open Mettapedia.TypeTheory

variable {Token Context : Type}

inductive Status where
  | pending | complete | atomic
  deriving DecidableEq, Repr

/-- The optional key cursor has four owned allocation fields. Its source Atom fields
are borrowed; they are not part of this inventory. -/
structure KeyFields (Token : Type) where
  text : Option Token
  frames : Option Token
  alpha : Option Token
  control : Token

def KeyFields.inventory (fields : KeyFields Token) : List Token :=
  fields.text.toList ++ fields.frames.toList ++ fields.alpha.toList ++ [fields.control]

/-- An indexed view of the initialized primary key array. `length` is its
actual owned prefix, not the storage capacity or the source arity. -/
structure Frame (Token : Type) where
  identity : Nat
  extent : Nat
  length : Nat
  slots : Nat → Option Token
  key : Option (KeyFields Token)
  scratch : Option Token
  assembly : Option Token
  items : Option Token

def Frame.fixed (frame : Frame Token) : List Token :=
  (frame.key.toList.flatMap KeyFields.inventory) ++
    frame.scratch.toList ++ frame.assembly.toList ++ frame.items.toList

def Frame.keys (frame : Frame Token) : List Token :=
  (List.range frame.length).filterMap frame.slots

def Frame.inventory (frame : Frame Token) : List Token := frame.keys ++ frame.fixed

def Frame.Valid (frame : Frame Token) : Prop :=
  frame.length ≤ frame.extent ∧ ∀ i, frame.length ≤ i → i < frame.extent → frame.slots i = none

def Frame.pop (frame : Frame Token) : Frame Token :=
  { frame with length := frame.length - 1
               slots := Function.update frame.slots (frame.length - 1) none }

theorem KeyFields.inventory_length (fields : KeyFields Token) : fields.inventory.length ≤ 4 := by
  simp only [KeyFields.inventory, List.length_append, List.length_singleton]
  have a := (show fields.text.toList.length ≤ 1 from Option.length_toList_le)
  have b := (show fields.frames.toList.length ≤ 1 from Option.length_toList_le)
  have c := (show fields.alpha.toList.length ≤ 1 from Option.length_toList_le)
  omega

theorem Frame.fixed_length (frame : Frame Token) : frame.fixed.length ≤ 7 := by
  have keyBound : (frame.key.toList.flatMap KeyFields.inventory).length ≤ 4 := by
    cases found : frame.key with
    | none => simp
    | some fields => simpa using KeyFields.inventory_length fields
  have a := (show frame.scratch.toList.length ≤ 1 from Option.length_toList_le)
  have b := (show frame.assembly.toList.length ≤ 1 from Option.length_toList_le)
  have c := (show frame.items.toList.length ≤ 1 from Option.length_toList_le)
  simp only [Frame.fixed, List.length_append]
  omega

theorem Frame.pop_valid (frame : Frame Token) (valid : frame.Valid) (positive : 0 < frame.length) :
    frame.pop.Valid := by
  have bounded := valid.1
  constructor
  · dsimp [Frame.pop]
    omega
  · intro i beyond inside
    by_cases last : i = frame.length - 1
    · simp [Frame.pop, last]
    · have old : frame.length ≤ i := by dsimp [Frame.pop] at beyond; omega
      simpa [Frame.pop, last] using valid.2 i old inside

/-- A single actual tail-slot scan removes exactly its optional owned key.
The primary backing function is nulled before the state can be retained. -/
theorem Frame.pop_inventory (frame : Frame Token) (positive : 0 < frame.length) :
    frame.inventory.Perm ((frame.slots (frame.length - 1)).toList ++ frame.pop.inventory) := by
  have length : frame.length = (frame.length - 1) + 1 := by omega
  have earlier : (List.range (frame.length - 1)).filterMap frame.pop.slots =
      (List.range (frame.length - 1)).filterMap frame.slots := by
    apply List.filterMap_congr
    intro i member
    have before := List.mem_range.mp member
    simp [Frame.pop, Function.update_of_ne (by omega : i ≠ frame.length - 1)]
  have keys : frame.keys = frame.pop.keys ++ (frame.slots (frame.length - 1)).toList := by
    change (List.range frame.length).filterMap frame.slots =
      (List.range (frame.length - 1)).filterMap frame.pop.slots ++ (frame.slots (frame.length - 1)).toList
    rw [earlier, length, List.range_succ, List.filterMap_append]
    congr 1
  rw [Frame.inventory, keys]
  change (frame.pop.keys ++ (frame.slots (frame.length - 1)).toList ++ frame.fixed).Perm
    ((frame.slots (frame.length - 1)).toList ++ (frame.pop.keys ++ frame.fixed))
  exact (List.perm_append_comm.append_right frame.fixed).trans (by rw [List.append_assoc])

/-- Three owned header buffers: unpublished memo growth, committed memo
storage and the normalizer frame array. Memo images remain arena-owned. -/
structure Header (Token : Type) where
  growth : Option Token
  memo : Option Token
  frames : Option Token

def Header.inventory (header : Header Token) : List Token :=
  header.growth.toList ++ header.memo.toList ++ header.frames.toList

structure Drain (Token Context : Type) where
  frames : List (Frame Token)
  header : Option (Header Token)
  releasedRev : List Token
  scans : Nat
  frameDrops : Nat
  headerDrops : Nat
  freeCalls : Nat
  context : Context

def Drain.remaining (state : Drain Token Context) : List Token :=
  state.frames.flatMap Frame.inventory ++ state.header.toList.flatMap Header.inventory

def Drain.whole (state : Drain Token Context) : List Token := state.releasedRev.reverse ++ state.remaining

def Drain.Valid (state : Drain Token Context) : Prop := ∀ frame ∈ state.frames, frame.Valid

def Drain.ready (state : Drain Token Context) : Bool := state.frames.isEmpty && state.header.isNone

def Drain.potential (state : Drain Token Context) : Nat :=
  (state.frames.map (fun frame => frame.length + 1)).sum + state.header.toList.length

/-- One tail slot or one fixed-size frame/header cleanup. This is the
normalizer provider's actual ownership walk, not a flattened free list. -/
def Drain.step (state : Drain Token Context) : Drain Token Context :=
  match state.frames with
  | frame :: rest =>
      if frame.length = 0 then
        { state with frames := rest
                     releasedRev := frame.fixed.reverse ++ state.releasedRev
                     frameDrops := state.frameDrops + 1
                     freeCalls := state.freeCalls + (if frame.key.isSome then 4 else 0) + 3 }
      else
        { state with frames := frame.pop :: rest
                     releasedRev := (frame.slots (frame.length - 1)).toList ++ state.releasedRev
                     scans := state.scans + 1
                     freeCalls := state.freeCalls + 1 }
  | [] => match state.header with
    | none => state
    | some header =>
        { state with header := none
                     releasedRev := header.inventory.reverse ++ state.releasedRev
                     headerDrops := state.headerDrops + 1
                     freeCalls := state.freeCalls + 3 }

theorem Drain.step_context (state : Drain Token Context) : state.step.context = state.context := by
  unfold Drain.step
  split
  · split <;> rfl
  · split <;> rfl

theorem Drain.step_valid (state : Drain Token Context) (valid : state.Valid) : state.step.Valid := by
  cases frames : state.frames with
  | nil =>
      cases header : state.header <;> simp [Drain.step, frames, header, Drain.Valid]
  | cons frame rest =>
      by_cases empty : frame.length = 0
      · intro next member
        exact valid next (by simpa [Drain.step, frames, empty] using Or.inr member)
      · intro next member
        have old : frame.Valid := valid frame (by simp [frames])
        have members : next = frame.pop ∨ next ∈ rest := by
          simpa [Drain.step, frames, empty] using member
        rcases members with rfl | later
        · exact frame.pop_valid old (by omega)
        · exact valid next (by simp [frames, later])

theorem Drain.step_potential (state : Drain Token Context) (running : state.ready = false) :
    state.step.potential + 1 = state.potential := by
  cases frames : state.frames with
  | nil =>
      cases header : state.header with
      | none => simp [Drain.ready, frames, header] at running
      | some header => simp [Drain.step, Drain.potential, frames, header]
  | cons frame rest =>
      by_cases empty : frame.length = 0
      · simp only [Drain.step, frames, empty, ↓reduceIte, Drain.potential, List.map_cons, List.sum_cons]
        omega
      · simp only [Drain.step, frames, empty, ↓reduceIte, Drain.potential, Frame.pop,
          List.map_cons, List.sum_cons]
        omega

/-- Actual disposal conserves the resource partition, including nonnull
keys, fixed child controls and the unvisited outer frames/header. -/
theorem Drain.step_partition (state : Drain Token Context) : state.step.whole.Perm state.whole := by
  cases frames : state.frames with
  | nil =>
      cases header : state.header <;>
        simp [Drain.step, Drain.whole, Drain.remaining, frames, header, List.reverse_append]
  | cons frame rest =>
      by_cases empty : frame.length = 0
      · simp [Drain.step, Drain.whole, Drain.remaining, frames, empty, Frame.inventory,
          Frame.keys, List.reverse_append, List.append_assoc]
      · have localPart := (frame.pop_inventory (by omega)).symm
        have reverse : (frame.slots (frame.length - 1)).toList.reverse =
            (frame.slots (frame.length - 1)).toList := by
          cases frame.slots (frame.length - 1) <;> rfl
        have whole := (localPart.append_right
          (rest.flatMap Frame.inventory ++ state.header.toList.flatMap Header.inventory)).append_left
            state.releasedRev.reverse
        simpa [Drain.step, Drain.whole, Drain.remaining, frames, empty, List.reverse_append,
          reverse, List.append_assoc] using whole

theorem Drain.step_no_double_release (state : Drain Token Context) (unique : state.whole.Nodup) :
    state.step.releasedRev.Nodup := by
  have next := (state.step_partition.nodup_iff).mpr unique
  exact List.nodup_reverse.mp (List.nodup_append.mp next).1

theorem Drain.step_free_call_bound (state : Drain Token Context) :
    state.freeCalls ≤ state.step.freeCalls ∧ state.step.freeCalls ≤ state.freeCalls + 7 := by
  unfold Drain.step
  split
  · split
    · split <;> dsimp only <;> omega
    · dsimp only; omega
  · split
    · omega
    · dsimp only; omega

inductive Event (Token : Type) where
  | slot (frame ordinal : Nat) (key : Option Token)
  | frame (identity : Nat) (fields : List Token)
  | header (fields : List Token)
  deriving DecidableEq, Repr

def Drain.event (state : Drain Token Context) : Option (Event Token) :=
  match state.frames with
  | frame :: _ => if frame.length = 0 then some (.frame frame.identity frame.fixed)
      else some (.slot frame.identity (frame.length - 1) (frame.slots (frame.length - 1)))
  | [] => state.header.map (fun header => .header header.inventory)

def Drain.provider (Token Context : Type) : Provider (Sequence.protocol (Event Token)) where
  State _ _ := Drain Token Context
  step state _ := ⟨state.event, state.step⟩

def Drain.client : Client (P := Sequence.protocol (Event Token)) (Return := fun _ _ => List (Event Token)) :=
  Fold.client (fun reversed event => event :: reversed)

def Drain.charge : Charge (Drain.provider Token Context) :=
  fun state _ => if state.ready then 0 else 1

def Drain.packet (state : Drain Token Context) : Packet (Drain.provider Token Context) Drain.client () :=
  ⟨(), .pulling [], state⟩

def Drain.run (fuel : Nat) (state : Drain Token Context) :=
  advance (Drain.provider Token Context) Drain.client Drain.charge fuel state.packet

theorem Drain.event_none_iff (state : Drain Token Context) : state.event = none ↔ state.ready = true := by
  cases frames : state.frames with
  | nil => cases header : state.header <;> simp [Drain.event, Drain.ready, frames, header]
  | cons frame rest =>
      by_cases empty : frame.length = 0 <;> simp [Drain.event, Drain.ready, frames, empty]

theorem Drain.ready_step (state : Drain Token Context) (finished : state.ready = true) :
    state.step = state := by
  have parts : state.frames = [] ∧ state.header = none := by
    simpa [Drain.ready] using finished
  simp [Drain.step, parts.1, parts.2]

/-- One actual protocol request exposes one cleanup action, rather than
preparing a whole release word and then slicing that certificate. -/
theorem Drain.provider_action (state : Drain Token Context) (running : state.ready = false) :
    ∃ event, (Drain.provider Token Context).step (base := ()) (index := ()) state () =
      ⟨some event, state.step⟩ := by
  have present : state.event ≠ none := by
    intro absent
    have finished := (Drain.event_none_iff state).mp absent
    simp [running] at finished
  cases reply : state.event with
  | none => exact False.elim (present reply)
  | some event => exact ⟨event, by simp [Drain.provider, reply]⟩

theorem Drain.run_zero (state : Drain Token Context) :
    Drain.run 0 state = (0, .paused state.packet) := rfl

/-- Independent specification of the actual primary tail order. It is used
only as a semantic readout; neither beginning nor advancing computes it. -/
def Frame.reference (frame : Frame Token) : List (Event Token) :=
  ((List.range frame.length).reverse.map
    (fun i => Event.slot frame.identity i (frame.slots i))) ++ [.frame frame.identity frame.fixed]

def Drain.reference (state : Drain Token Context) : List (Event Token) :=
  state.frames.flatMap Frame.reference ++ state.header.toList.map (fun header => .header header.inventory)

theorem Frame.reference_pop (frame : Frame Token) (positive : 0 < frame.length) :
    frame.reference = .slot frame.identity (frame.length - 1) (frame.slots (frame.length - 1)) ::
      frame.pop.reference := by
  have length : frame.length = (frame.length - 1) + 1 := by omega
  have earlier : (List.range (frame.length - 1)).reverse.map
      (fun i => Event.slot frame.identity i (frame.pop.slots i)) =
      (List.range (frame.length - 1)).reverse.map
        (fun i => Event.slot frame.identity i (frame.slots i)) := by
    apply List.map_congr_left
    intro i member
    have before : i < frame.length - 1 := List.mem_range.mp (List.mem_reverse.mp member)
    simp [Frame.pop, Function.update_of_ne (by omega : i ≠ frame.length - 1)]
  change ((List.range frame.length).reverse.map (fun i => Event.slot frame.identity i (frame.slots i))) ++ _ =
    _ :: (((List.range (frame.length - 1)).reverse.map (fun i => Event.slot frame.identity i (frame.pop.slots i))) ++ _)
  rw [earlier, length, List.range_succ]
  simp [Frame.fixed, Frame.pop, List.reverse_append]

theorem Drain.reference_nil_iff (state : Drain Token Context) : state.reference = [] ↔ state.ready = true := by
  cases frames : state.frames with
  | nil => cases header : state.header <;> simp [Drain.reference, Drain.ready, frames, header]
  | cons frame rest => simp [Drain.reference, Drain.ready, Frame.reference, frames]

theorem Drain.reference_length (state : Drain Token Context) : state.reference.length = state.potential := by
  simp [Drain.reference, Frame.reference, Drain.potential, List.length_flatMap]

/-- The independently implemented provider follows the reference one head at
a time. The map is a proof readout, never preprocessing performed by a poll. -/
def Drain.referenceHom : Hom (Drain.provider Token Context) (Sequence.tails (Event Token)) where
  map state := state.reference
  step state request := by
    cases frames : state.frames with
    | nil =>
        cases header : state.header <;>
          simp [Drain.provider, Drain.event, Drain.step, Drain.reference, Sequence.tails,
            frames, header]
    | cons frame rest =>
        by_cases empty : frame.length = 0
        · simp [Drain.provider, Drain.event, Drain.step, Drain.reference, Frame.reference,
            frames, empty, Sequence.tails]
        · have head := Frame.reference_pop frame (by omega)
          simp only [Drain.provider, Drain.event, frames, empty, ↓reduceIte, Drain.reference,
            List.flatMap_cons, head, List.cons_append, Sequence.tails, Drain.step]

theorem Drain.local_charge (state : Drain Token Context) (request : Unit) :
    Drain.charge (base := ()) (index := ()) state request =
      Sequence.requested (Event Token) (base := ()) (index := ()) state.reference request := by
  by_cases ready : state.ready = true
  · have empty := state.reference_nil_iff.mpr ready
    simp [Drain.charge, Sequence.requested, ready, empty]
  · have nonempty := mt state.reference_nil_iff.mp ready
    cases word : state.reference with
    | nil => exact False.elim (nonempty word)
    | cons event rest => simp [Drain.charge, Sequence.requested, ready]

theorem Drain.prefix_cost (state : Drain Token Context) (fuel : Nat) (within : fuel ≤ state.potential) :
    (Drain.run fuel state).1 = fuel := by
  rw [Drain.run, Hom.advance_charge Drain.client Drain.referenceHom Drain.charge
    (Sequence.requested (Event Token)) (by intro _ _ state request; exact state.local_charge request)]
  exact SequenceCost.fold_prefix_requested (fun reversed event => event :: reversed)
    state.reference [] fuel (by simpa [state.reference_length] using within)

theorem Drain.completed_cost (state : Drain Token Context) :
    (Drain.run (state.potential + 2) state).1 = state.potential := by
  rw [Drain.run, Hom.advance_charge Drain.client Drain.referenceHom Drain.charge
    (Sequence.requested (Event Token)) (by intro _ _ state request; exact state.local_charge request)]
  change (advance (Sequence.tails (Event Token)) (Fold.client (fun reversed event => event :: reversed))
    (Sequence.requested (Event Token)) (state.potential + 2)
    (Fold.start _ (fun reversed event => event :: reversed) state.reference [])).1 = state.potential
  rw [← state.reference_length]
  exact SequenceCost.fold_complete_requested (fun reversed event => event :: reversed) state.reference []

def Drain.outcomeState : Outcome (Drain.provider Token Context) Drain.client () → Drain Token Context
  | .paused packet => packet.2.2
  | .done result => result.2.2

/-- Finiteness is derived from the actual tail updates. The independent
reference fixes the complete event order, including null-key inspections. -/
theorem Drain.finite_completion (state : Drain Token Context) :
    ∃ final, Drain.run (state.potential + 2) state =
      (state.potential, .done ⟨(), state.reference.reverse, final⟩) ∧ final.ready = true := by
  have observed := Drain.referenceHom.advance Drain.client Drain.charge
    (fun _ _ => 1) (state.potential + 2) state.packet
  have target := congrArg Prod.snd (Fold.complete_exact (fun reversed event => event :: reversed)
    state.reference [])
  rw [state.reference_length] at target
  have complete : (advance (Sequence.tails (Event Token)) Drain.client (fun _ _ => 1)
      (state.potential + 2) (Drain.referenceHom.packet Drain.client state.packet)).2 =
      .done ⟨(), state.reference.reverse, []⟩ := by
    simpa [Hom.packet, Drain.packet, Drain.referenceHom, Drain.client, Fold.start] using target
  rw [complete] at observed
  change Drain.referenceHom.outcome Drain.client (Drain.run (state.potential + 2) state).2 = _ at observed
  cases execution : Drain.run (state.potential + 2) state with
  | mk paid outcome =>
      have bill : paid = state.potential := by simpa [execution] using state.completed_cost
      cases outcome with
      | paused packet =>
          simp [execution, Hom.outcome, Outcome.mapState] at observed
      | done result =>
          rcases result with ⟨index, output, final⟩
          cases index
          have same : output = state.reference.reverse ∧ final.reference = [] := by
            simp only [execution, Hom.outcome, Outcome.mapState] at observed
            have result := Outcome.done.inj observed
            have pair := congrArg (fun value : Finished (Sequence.tails (Event Token))
              (Return := fun _ _ => List (Event Token)) () =>
                ((value.2.1, value.2.2) : List (Event Token) × List (Event Token))) result
            exact Prod.mk.inj pair
          exact ⟨final, by simp [bill, same.1], final.reference_nil_iff.mp same.2⟩

theorem Drain.split (state : Drain Token Context) (first later : Nat) :
    Drain.run (first + later) state =
      resume (Drain.provider Token Context) Drain.client Drain.charge later (Drain.run first state) :=
  advance_add _ _ _ first later state.packet

theorem Drain.resume_zero (previous : Nat × Outcome (Drain.provider Token Context) Drain.client ()) :
    resume (Drain.provider Token Context) Drain.client Drain.charge 0 previous = previous :=
  Cursor.resume_zero _ _ _ previous

/-- Lift local preservation through the existing cursor, including a return
inspection and a prefix paused immediately after a provider response. -/
private theorem Drain.client_pulling (output : List (Event Token)) :
    Drain.client.str () () (.pulling output) =
      ⟨.inr (), fun reply => match reply with
        | none => Fold.State.finished output
        | some event => .pulling (event :: output)⟩ := by
  unfold Drain.client Fold.client
  dsimp only
  simp only [TypeCat.ofHom, CategoryTheory.ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
  congr 1
  funext reply
  cases reply <;> rfl

theorem Drain.prefix_invariant (invariant : Drain Token Context → Prop)
    (preserved : ∀ state, invariant state → invariant state.step)
    (fuel : Nat) (control : Fold.State (List (Event Token))) (state : Drain Token Context)
    (initial : invariant state) :
    invariant (Drain.outcomeState (advance (Drain.provider Token Context) Drain.client Drain.charge
      fuel ⟨(), control, state⟩).2) := by
  induction fuel generalizing control state with
  | zero => exact initial
  | succ fuel ih =>
      cases control with
      | finished output => exact initial
      | pulling output =>
          simp only [advance, Drain.client_pulling]
          change invariant (Drain.outcomeState
            (advance (Drain.provider Token Context) Drain.client Drain.charge fuel
              ⟨(), (match state.event with
                | none => Fold.State.finished output
                | some event => .pulling (event :: output)), state.step⟩).2)
          cases reply : state.event with
          | none =>
              exact ih (.finished output) state.step (preserved state initial)
          | some event =>
              exact ih (.pulling (event :: output)) state.step (preserved state initial)

theorem Drain.prefix_valid (state : Drain Token Context) (valid : state.Valid) (fuel : Nat) :
    (Drain.outcomeState (Drain.run fuel state).2).Valid :=
  Drain.prefix_invariant Drain.Valid (fun _ => Drain.step_valid _) fuel (.pulling []) state valid

theorem Drain.prefix_partition (state : Drain Token Context) (fuel : Nat) :
    (Drain.outcomeState (Drain.run fuel state).2).whole.Perm state.whole := by
  apply Drain.prefix_invariant (fun next => next.whole.Perm state.whole)
    (fun next previous => next.step_partition.trans previous) fuel (.pulling []) state
  exact List.Perm.refl _

theorem Drain.prefix_no_double_release (state : Drain Token Context) (unique : state.whole.Nodup)
    (fuel : Nat) : (Drain.outcomeState (Drain.run fuel state).2).releasedRev.Nodup := by
  have kept := ((state.prefix_partition fuel).nodup_iff).mpr unique
  exact List.nodup_reverse.mp (List.nodup_append.mp kept).1

theorem Drain.prefix_context (state : Drain Token Context) (fuel : Nat) :
    (Drain.outcomeState (Drain.run fuel state).2).context = state.context :=
  Drain.prefix_invariant (fun next => next.context = state.context)
    (fun next previous => next.step_context.trans previous) fuel (.pulling []) state rfl

/-- A callback owns its child work only. It never receives the enclosing
owner field. Native alias separation and callback/context lifetime are
additional realization premises, not consequences of this type. -/
structure Reply (Work : Type) where
  status : Status
  used : Nat
  next : Work

abbrev Callback (Work : Type) := Bool → Work → Reply Work

/-- The cancellation fragment retains the full callback state and context.
The release log records actual enclosing-owner releases, not cleanup replies. -/
structure Execution (Owner Work Loan Context : Type) where
  owner : Option Owner
  work : Work
  loan : Option Loan
  context : Context
  accepted : Nat
  retiring : Bool
  releaseReady : Bool
  relocatable : Bool
  releasedRev : List Owner

variable {Owner Work Loan : Type}

def Execution.begin (state : Execution Owner Work Loan Context) : Execution Owner Work Loan Context :=
  { state with loan := none, retiring := true }

def Execution.release (state : Execution Owner Work Loan Context) (owner : Owner) :
    Execution Owner Work Loan Context :=
  { state with owner := none, releasedRev := owner :: state.releasedRev }

/-- One boundary action. A complete child reply only arms final release;
the enclosing owner is released by a subsequent, separately charged action.
The callback's units are declared service receipts, not physical prices. -/
def Execution.step (callback : Callback Work) (allowAtomic : Bool)
    (state : Execution Owner Work Loan Context) : Reply (Execution Owner Work Loan Context) :=
  match state.owner with
  | none => ⟨.complete, 0, state⟩
  | some owner =>
      if !state.retiring then ⟨.pending, 1, state.begin⟩
      else if state.releaseReady then ⟨.complete, 1, state.release owner⟩
      else
        let reply := callback allowAtomic state.work
        ⟨(if reply.status = .atomic then .atomic else .pending), reply.used,
          { state with work := reply.next, releaseReady := reply.status == .complete }⟩

/-- These are availability observations of the existing answer boundary.
After storage release the boundary is inert; no producer is resumed. -/
inductive AnswerAdmission where
  | available | interrupted | handoff
  deriving DecidableEq, Repr

def Execution.answerAdmission (state : Execution Owner Work Loan Context) : AnswerAdmission :=
  if state.owner.isNone then .handoff else if state.retiring then .interrupted else .available

def Execution.moveAdmitted (state : Execution Owner Work Loan Context) : Bool :=
  state.relocatable && !state.retiring

def Execution.inventory (state : Execution Owner Work Loan Context) : List Owner :=
  state.owner.toList ++ state.releasedRev

theorem Execution.begin_keeps_owner (state : Execution Owner Work Loan Context) :
    state.begin.owner = state.owner ∧ state.begin.work = state.work ∧
      state.begin.context = state.context ∧ state.begin.accepted = state.accepted ∧
      state.begin.loan = none ∧ state.begin.retiring = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Execution.step_context (callback : Callback Work) (allowAtomic : Bool)
    (state : Execution Owner Work Loan Context) :
    (state.step callback allowAtomic).next.context = state.context ∧
      (state.step callback allowAtomic).next.accepted = state.accepted := by
  cases owner : state.owner with
  | none => simp [Execution.step, owner]
  | some owner =>
      cases retiring : state.retiring <;> cases ready : state.releaseReady <;>
        simp [Execution.step, owner, retiring, ready, Execution.begin, Execution.release]

theorem Execution.child_reply_keeps_owner (callback : Callback Work) (allowAtomic : Bool)
    (state : Execution Owner Work Loan Context) (owner : Owner)
    (held : state.owner = some owner) (retiring : state.retiring = true)
    (notReady : state.releaseReady = false) :
    (state.step callback allowAtomic).next.owner = some owner ∧
      (state.step callback allowAtomic).next.work = (callback allowAtomic state.work).next ∧
      (state.step callback allowAtomic).next.releaseReady =
        ((callback allowAtomic state.work).status == .complete) := by
  simp [Execution.step, held, retiring, notReady]

theorem Execution.complete_reply_is_not_release (callback : Callback Work) (allowAtomic : Bool)
    (state : Execution Owner Work Loan Context) (owner : Owner)
    (held : state.owner = some owner) (retiring : state.retiring = true)
    (notReady : state.releaseReady = false)
    (complete : (callback allowAtomic state.work).status = .complete) :
    (state.step callback allowAtomic).status = .pending ∧
      (state.step callback allowAtomic).next.owner = some owner ∧
      (state.step callback allowAtomic).next.releaseReady = true ∧
      (state.step callback allowAtomic).next.releasedRev = state.releasedRev := by
  simp [Execution.step, held, retiring, notReady, complete]

theorem Execution.only_ready_releases (callback : Callback Work) (allowAtomic : Bool)
    (state : Execution Owner Work Loan Context) (owner : Owner)
    (held : state.owner = some owner)
    (released : (state.step callback allowAtomic).next.owner = none) :
    state.retiring = true ∧ state.releaseReady = true := by
  cases retiring : state.retiring <;> cases ready : state.releaseReady <;>
    simp [Execution.step, held, retiring, ready, Execution.begin, Execution.release] at released ⊢

theorem Execution.atomic_keeps_owner (callback : Callback Work) (allowAtomic : Bool)
    (state : Execution Owner Work Loan Context)
    (blocked : (state.step callback allowAtomic).status = .atomic) :
    (state.step callback allowAtomic).next.owner = state.owner ∧
      (state.step callback allowAtomic).next.releasedRev = state.releasedRev := by
  cases owner : state.owner with
  | none => simp [Execution.step, owner] at blocked
  | some owner =>
      cases retiring : state.retiring <;> cases ready : state.releaseReady <;>
        simp [Execution.step, owner, retiring, ready, Execution.begin, Execution.release] at blocked ⊢

theorem Execution.step_partition (callback : Callback Work) (allowAtomic : Bool)
    (state : Execution Owner Work Loan Context) :
    (state.step callback allowAtomic).next.inventory = state.inventory := by
  cases owner : state.owner with
  | none => simp [Execution.step, owner]
  | some owner =>
      cases retiring : state.retiring <;> cases ready : state.releaseReady <;>
        simp [Execution.step, owner, retiring, ready, Execution.begin, Execution.release, Execution.inventory]

theorem Execution.retiring_cannot_move (state : Execution Owner Work Loan Context)
    (retiring : state.retiring = true) : state.moveAdmitted = false := by
  simp [Execution.moveAdmitted, retiring]

theorem Execution.retiring_answer (state : Execution Owner Work Loan Context) (owner : Owner)
    (held : state.owner = some owner) (retiring : state.retiring = true) :
    state.answerAdmission = .interrupted := by
  simp [Execution.answerAdmission, held, retiring]

theorem Execution.released_answer (state : Execution Owner Work Loan Context) (released : state.owner = none) :
    state.answerAdmission = .handoff := by
  simp [Execution.answerAdmission, released]

def protocol : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Bool
  Position _ := Status
  next _ _ := ()

def Execution.provider (callback : Callback Work) : Provider protocol where
  State _ _ := Execution Owner Work Loan Context
  step state allowAtomic := ⟨(state.step callback allowAtomic).status,
    (state.step callback allowAtomic).next⟩

def Execution.charge (callback : Callback Work) : Charge
    (Execution.provider (Owner := Owner) (Loan := Loan) (Context := Context) callback) :=
  fun state allowAtomic => (state.step callback allowAtomic).used

/-- A single cancellation call stops at ATOMIC with its exact retained owner.
A later call may grant atomic work; it starts from that residual, not from
the original execution. Scheduler inspections and service units are distinct. -/
def Execution.client (allowAtomic : Bool) : Client (P := protocol) (Return := fun _ _ => Status) where
  V _ _ := Option Status
  str := fun _ _ => TypeCat.ofHom fun control => match control with
    | some status => ⟨.inl status, fun impossible => nomatch impossible⟩
    | none => ⟨.inr allowAtomic, fun (status : Status) =>
        if status = .pending then none else some status⟩

def Execution.packet (callback : Callback Work) (allowAtomic : Bool)
    (state : Execution Owner Work Loan Context) :
    Packet (Execution.provider (Owner := Owner) (Loan := Loan) (Context := Context) callback)
      (Execution.client allowAtomic) () := ⟨(), none, state⟩

def Execution.run (callback : Callback Work) (allowAtomic : Bool) (fuel : Nat)
    (state : Execution Owner Work Loan Context) :=
  advance (Execution.provider callback) (Execution.client allowAtomic) (Execution.charge callback)
    fuel (state.packet callback allowAtomic)

def Execution.outcomeState (callback : Callback Work) (allowAtomic : Bool) :
    Outcome (Execution.provider (Owner := Owner) (Loan := Loan) (Context := Context) callback)
      (Execution.client allowAtomic) () →
      Execution Owner Work Loan Context
  | .paused packet => packet.2.2
  | .done result => result.2.2

theorem Execution.run_zero (callback : Callback Work) (allowAtomic : Bool)
    (state : Execution Owner Work Loan Context) :
    state.run callback allowAtomic 0 = (0, .paused (state.packet callback allowAtomic)) := rfl

/-- Exact composition for protocol inspection fuel. A native callback can
batch several service units under one grant; this is not an arbitrary
callback's native grant-equality law. -/
theorem Execution.split (callback : Callback Work) (allowAtomic : Bool)
    (state : Execution Owner Work Loan Context) (first later : Nat) :
    state.run callback allowAtomic (first + later) =
      resume (Execution.provider callback) (Execution.client allowAtomic) (Execution.charge callback)
        later (state.run callback allowAtomic first) :=
  advance_add _ _ _ first later (state.packet callback allowAtomic)

private theorem Execution.client_poll (allowAtomic : Bool) :
    (Execution.client allowAtomic).str () () none =
      ⟨.inr allowAtomic, fun (status : Status) => if status = .pending then none else some status⟩ := by
  unfold Execution.client
  dsimp only
  simp only [TypeCat.ofHom, CategoryTheory.ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
  rfl

private theorem Execution.client_stopped (allowAtomic : Bool) (status : Status) :
    (Execution.client allowAtomic).str () () (some status) =
      ⟨.inl status, fun impossible => nomatch impossible⟩ := by
  unfold Execution.client
  dsimp only
  simp only [TypeCat.ofHom, CategoryTheory.ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
  congr 1
  funext impossible
  cases impossible

theorem Execution.advance_stopped (callback : Callback Work) (allowAtomic : Bool)
    (fuel : Nat) (status : Status) (state : Execution Owner Work Loan Context) :
    advance (Execution.provider callback) (Execution.client allowAtomic) (Execution.charge callback)
      (fuel + 1) (base := ()) ⟨(), some status, state⟩ = (0, .done ⟨(), status, state⟩) := by
  simp only [advance, Execution.client_stopped]

theorem Execution.advance_poll (callback : Callback Work) (allowAtomic : Bool)
    (fuel : Nat) (state : Execution Owner Work Loan Context) :
    advance (Execution.provider callback) (Execution.client allowAtomic) (Execution.charge callback)
      (fuel + 1) (base := ()) ⟨(), none, state⟩ =
      let reply := state.step callback allowAtomic
      let rest := advance (Execution.provider callback) (Execution.client allowAtomic) (Execution.charge callback)
        fuel (base := ()) ⟨(), (if reply.status = .pending then none else some reply.status), reply.next⟩
      (reply.used + rest.1, rest.2) := by
  simp only [advance, Execution.client_poll]
  rfl

theorem Execution.prefix_invariant (callback : Callback Work) (allowAtomic : Bool)
    (invariant : Execution Owner Work Loan Context → Prop)
    (preserved : ∀ state, invariant state → invariant (state.step callback allowAtomic).next)
    (fuel : Nat) (control : Option Status) (state : Execution Owner Work Loan Context)
    (initial : invariant state) :
    invariant (Execution.outcomeState callback allowAtomic
      (advance (Execution.provider callback) (Execution.client allowAtomic) (Execution.charge callback)
        fuel ⟨(), control, state⟩).2) := by
  induction fuel generalizing control state with
  | zero => exact initial
  | succ fuel ih =>
      cases control with
      | some status => exact initial
      | none =>
          simp only [advance, Execution.client_poll]
          change invariant (Execution.outcomeState callback allowAtomic
            (advance (Execution.provider callback) (Execution.client allowAtomic) (Execution.charge callback)
              fuel ⟨(), (if (state.step callback allowAtomic).status = .pending then none
                else some (state.step callback allowAtomic).status), (state.step callback allowAtomic).next⟩).2)
          exact ih _ _ (preserved state initial)

theorem Execution.prefix_partition (callback : Callback Work) (allowAtomic : Bool)
    (state : Execution Owner Work Loan Context) (fuel : Nat) :
    (Execution.outcomeState callback allowAtomic (state.run callback allowAtomic fuel).2).inventory =
      state.inventory :=
  Execution.prefix_invariant callback allowAtomic (fun next => next.inventory = state.inventory)
    (fun next previous => (next.step_partition callback allowAtomic).trans previous)
    fuel none state rfl

theorem Execution.prefix_release_at_most_once (callback : Callback Work) (allowAtomic : Bool)
    (state : Execution Owner Work Loan Context) (owner : Owner)
    (held : state.owner = some owner) (unreleased : state.releasedRev = []) (fuel : Nat) :
    (Execution.outcomeState callback allowAtomic (state.run callback allowAtomic fuel).2).releasedRev.length ≤ 1 := by
  have preserved := congrArg List.length (state.prefix_partition callback allowAtomic fuel)
  simp only [Execution.inventory, List.length_append] at preserved
  simp [held, unreleased] at preserved
  omega

theorem Execution.prefix_context (callback : Callback Work) (allowAtomic : Bool)
    (state : Execution Owner Work Loan Context) (fuel : Nat) :
    let final := Execution.outcomeState callback allowAtomic (state.run callback allowAtomic fuel).2
    final.context = state.context ∧ final.accepted = state.accepted :=
  Execution.prefix_invariant callback allowAtomic
    (fun next => next.context = state.context ∧ next.accepted = state.accepted)
    (fun next previous => ⟨(next.step_context callback allowAtomic).1.trans previous.1,
      (next.step_context callback allowAtomic).2.trans previous.2⟩) fuel none state ⟨rfl, rfl⟩

/-- A new cancellation invocation retains both the old paid account and the
actual provider residual. This is deliberately not `resume` of a done ATOMIC
client, which is inert even if more inspection fuel is supplied. -/
def Execution.regrant (callback : Callback Work) (oldPermission newPermission : Bool) (fuel : Nat)
    (previous : Nat × Outcome
      (Execution.provider (Owner := Owner) (Loan := Loan) (Context := Context) callback)
      (Execution.client oldPermission) ()) :=
  let next := (Execution.outcomeState callback oldPermission previous.2).run callback newPermission fuel
  (previous.1 + next.1, next.2)

theorem Execution.regrant_zero (callback : Callback Work) (oldPermission newPermission : Bool)
    (previous : Nat × Outcome
      (Execution.provider (Owner := Owner) (Loan := Loan) (Context := Context) callback)
      (Execution.client oldPermission) ()) :
    Execution.regrant callback oldPermission newPermission 0 previous =
      (previous.1, .paused
        ((Execution.outcomeState callback oldPermission previous.2).packet callback newPermission)) := by
  simp [Execution.regrant, Execution.run, advance]

theorem Execution.atomic_done_resume_inert (callback : Callback Work) (permission : Bool)
    (paid fuel : Nat) (state : Execution Owner Work Loan Context) :
    resume (Execution.provider callback) (Execution.client permission) (Execution.charge callback)
      fuel (base := ()) (paid, .done ⟨(), .atomic, state⟩) = (paid, .done ⟨(), .atomic, state⟩) := rfl

def Drain.actionCount (state : Drain Token Context) : Nat :=
  state.scans + state.frameDrops + state.headerDrops

theorem Drain.step_action_count (state : Drain Token Context) :
    state.step.actionCount = state.actionCount + (if state.ready then 0 else 1) := by
  cases frames : state.frames with
  | nil =>
      cases header : state.header <;>
        simp [Drain.step, Drain.ready, Drain.actionCount, frames, header]
      omega
  | cons frame rest =>
      by_cases empty : frame.length = 0 <;>
        simp [Drain.step, Drain.ready, Drain.actionCount, frames, empty] <;> omega

/-- The concrete Rho child owns its own begin action in addition to the
normalizer walk. The opaque tail service is called only after an explicit
atomic grant; its input/output service world is retained until then. -/
structure Normalizer (Token Context Service : Type) where
  owner : Option Token
  retiring : Bool
  drain : Drain Token Context
  service : Service
  atomicCalls : Nat
  releasedRev : List Token

variable {Service : Type}

abbrev AtomicTail (Token Context Service : Type) := Token → Context → Service → Service

def Normalizer.callback (tail : AtomicTail Token Context Service) :
    Callback (Normalizer Token Context Service) := fun allowAtomic state =>
  match state.owner with
  | none => ⟨.complete, 0, state⟩
  | some owner =>
      if !state.retiring then ⟨.pending, 1, { state with retiring := true }⟩
      else if !state.drain.ready then ⟨.pending, 1, { state with drain := state.drain.step }⟩
      else if !allowAtomic then ⟨.atomic, 0, state⟩
      else
        ⟨.complete, 1, { state with
          owner := none
          service := tail owner state.drain.context state.service
          atomicCalls := state.atomicCalls + 1
          releasedRev := owner :: state.releasedRev }⟩

def Normalizer.rank (state : Normalizer Token Context Service) : Nat :=
  if state.owner.isNone then 0 else (if state.retiring then 0 else 1) + state.drain.potential + 1

def Normalizer.actionCount (state : Normalizer Token Context Service) : Nat :=
  (if state.retiring then 1 else 0) + state.drain.actionCount + state.atomicCalls

theorem Normalizer.pending_keeps_child (tail : AtomicTail Token Context Service)
    (allowAtomic : Bool) (state : Normalizer Token Context Service)
    (pending : (Normalizer.callback tail allowAtomic state).status = .pending) :
    (Normalizer.callback tail allowAtomic state).next.owner = state.owner ∧
      (Normalizer.callback tail allowAtomic state).next.service = state.service ∧
      (Normalizer.callback tail allowAtomic state).next.atomicCalls = state.atomicCalls := by
  cases owner : state.owner with
  | none => simp [Normalizer.callback, owner] at pending
  | some owner =>
      cases retiring : state.retiring <;> cases ready : state.drain.ready <;>
        cases allowAtomic <;> simp [Normalizer.callback, owner, retiring, ready] at pending ⊢

theorem Normalizer.atomic_refusal (tail : AtomicTail Token Context Service)
    (state : Normalizer Token Context Service) (owner : Token)
    (held : state.owner = some owner) (begun : state.retiring = true)
    (ready : state.drain.ready = true) :
    Normalizer.callback tail false state = ⟨.atomic, 0, state⟩ := by
  simp [Normalizer.callback, held, begun, ready]

theorem Normalizer.granted_tail (tail : AtomicTail Token Context Service)
    (state : Normalizer Token Context Service) (owner : Token)
    (held : state.owner = some owner) (begun : state.retiring = true)
    (ready : state.drain.ready = true) :
    (Normalizer.callback tail true state).status = .complete ∧
      (Normalizer.callback tail true state).used = 1 ∧
      (Normalizer.callback tail true state).next.owner = none ∧
      (Normalizer.callback tail true state).next.atomicCalls = state.atomicCalls + 1 ∧
      (Normalizer.callback tail true state).next.service = tail owner state.drain.context state.service := by
  simp [Normalizer.callback, held, begun, ready]

theorem Normalizer.true_not_atomic (tail : AtomicTail Token Context Service)
    (state : Normalizer Token Context Service) :
    (Normalizer.callback tail true state).status ≠ .atomic := by
  cases owner : state.owner with
  | none => simp [Normalizer.callback, owner]
  | some owner =>
      cases begun : state.retiring <;> cases ready : state.drain.ready <;>
        simp [Normalizer.callback, owner, begun, ready]

theorem Normalizer.rank_decreases (tail : AtomicTail Token Context Service)
    (state : Normalizer Token Context Service) (owner : Token) (held : state.owner = some owner) :
    (Normalizer.callback tail true state).next.rank < state.rank := by
  cases begun : state.retiring with
  | false => simp [Normalizer.callback, held, begun, Normalizer.rank]
  | true =>
      cases ready : state.drain.ready with
      | true => simp [Normalizer.callback, held, begun, ready, Normalizer.rank]
      | false =>
          have decrease := state.drain.step_potential ready
          simp only [Normalizer.callback, held, begun, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, ready, Bool.not_false, Normalizer.rank, Option.isNone_some]
          omega

theorem Normalizer.action_balance (tail : AtomicTail Token Context Service)
    (allowAtomic : Bool) (state : Normalizer Token Context Service) :
    (Normalizer.callback tail allowAtomic state).next.actionCount =
      state.actionCount + (Normalizer.callback tail allowAtomic state).used := by
  cases owner : state.owner with
  | none => simp [Normalizer.callback, owner]
  | some owner =>
      cases begun : state.retiring with
      | false => simp [Normalizer.callback, owner, begun, Normalizer.actionCount]; omega
      | true =>
          cases ready : state.drain.ready with
          | false =>
              have count := state.drain.step_action_count
              simp [ready] at count
              simp [Normalizer.callback, owner, begun, ready, Normalizer.actionCount, count]
              omega
          | true =>
              cases allowAtomic <;>
                simp [Normalizer.callback, owner, begun, ready, Normalizer.actionCount]
              omega

theorem Normalizer.rank_balance (tail : AtomicTail Token Context Service)
    (state : Normalizer Token Context Service) :
    (Normalizer.callback tail true state).next.rank + (Normalizer.callback tail true state).used =
      state.rank := by
  cases owner : state.owner with
  | none => simp [Normalizer.callback, owner]
  | some owner =>
      cases begun : state.retiring with
      | false => simp [Normalizer.callback, owner, begun, Normalizer.rank]; omega
      | true =>
          cases ready : state.drain.ready with
          | true =>
              have zero : state.drain.potential = 0 := by
                rw [← state.drain.reference_length, state.drain.reference_nil_iff.mpr ready]
                rfl
              simp [Normalizer.callback, owner, begun, ready, Normalizer.rank, zero]
          | false =>
              have decrease := state.drain.step_potential ready
              simpa [Normalizer.callback, owner, begun, ready, Normalizer.rank] using decrease

theorem Normalizer.complete_child_cleared (tail : AtomicTail Token Context Service)
    (state : Normalizer Token Context Service)
    (complete : (Normalizer.callback tail true state).status = .complete) :
    (Normalizer.callback tail true state).next.owner = none := by
  cases owner : state.owner with
  | none => simp [Normalizer.callback, owner]
  | some owner =>
      cases begun : state.retiring <;> cases ready : state.drain.ready <;>
        simp [Normalizer.callback, owner, begun, ready] at complete ⊢

/-- Remaining declared actions and inspection rank are different measures.
An already-cleared child can acknowledge completion for zero service units,
but that acknowledgement still requires one protocol inspection. -/
def Execution.normalizerRemaining (state : Execution Owner (Normalizer Token Context Service) Loan Context) : Nat :=
  if state.owner.isNone then 0 else
    (if state.retiring then 0 else 1) + (if state.releaseReady then 0 else state.work.rank) + 1

def Execution.normalizerRank (state : Execution Owner (Normalizer Token Context Service) Loan Context) : Nat :=
  if state.owner.isNone then 0 else
    if !state.retiring then state.work.rank + 3 else if state.releaseReady then 1 else state.work.rank + 2

theorem Execution.normalizer_not_atomic (tail : AtomicTail Token Context Service)
    (state : Execution Owner (Normalizer Token Context Service) Loan Context) :
    (state.step (Normalizer.callback tail) true).status ≠ .atomic := by
  cases owner : state.owner with
  | none => simp [Execution.step, owner]
  | some owner =>
      have notAtomic := Normalizer.true_not_atomic tail state.work
      cases begun : state.retiring <;> cases ready : state.releaseReady <;>
        simp [Execution.step, owner, begun, ready, notAtomic]

theorem Execution.normalizer_complete_released (tail : AtomicTail Token Context Service)
    (state : Execution Owner (Normalizer Token Context Service) Loan Context)
    (complete : (state.step (Normalizer.callback tail) true).status = .complete) :
    (state.step (Normalizer.callback tail) true).next.owner = none := by
  cases owner : state.owner with
  | none => simp [Execution.step, owner]
  | some owner =>
      have notAtomic := Normalizer.true_not_atomic tail state.work
      cases begun : state.retiring <;> cases ready : state.releaseReady <;>
        simp [Execution.step, owner, begun, ready, notAtomic, Execution.release] at complete ⊢

theorem Execution.normalizer_rank_decreases (tail : AtomicTail Token Context Service)
    (state : Execution Owner (Normalizer Token Context Service) Loan Context)
    (owner : Owner) (held : state.owner = some owner) :
    (state.step (Normalizer.callback tail) true).next.normalizerRank < state.normalizerRank := by
  cases begun : state.retiring with
  | false =>
      simp [Execution.step, held, begun, Execution.begin, Execution.normalizerRank]
      split <;> omega
  | true =>
      cases ready : state.releaseReady with
      | true => simp [Execution.step, held, begun, ready, Execution.release, Execution.normalizerRank]
      | false =>
          have notAtomic := Normalizer.true_not_atomic tail state.work
          cases reply : (Normalizer.callback tail true state.work).status with
          | atomic => exact False.elim (notAtomic reply)
          | complete =>
              simp [Execution.step, held, begun, ready, reply, Execution.normalizerRank]
          | pending =>
              have smaller : (Normalizer.callback tail true state.work).next.rank < state.work.rank := by
                cases child : state.work.owner with
                | none => simp [Normalizer.callback, child] at reply
                | some childOwner => exact Normalizer.rank_decreases tail state.work childOwner child
              simp [Execution.step, held, begun, ready, reply, Execution.normalizerRank]
              omega

/-- The complete remaining-service invoice is derived from every concrete
case: outer begin, child begin, slot/frame/header walk, opaque tail and final
wrapper release. No callback invoice-completeness assumption is supplied. -/
theorem Execution.normalizer_work_balance (tail : AtomicTail Token Context Service)
    (state : Execution Owner (Normalizer Token Context Service) Loan Context) :
    (state.step (Normalizer.callback tail) true).next.normalizerRemaining +
      (state.step (Normalizer.callback tail) true).used = state.normalizerRemaining := by
  cases owner : state.owner with
  | none => simp [Execution.step, owner]
  | some owner =>
      cases begun : state.retiring with
      | false =>
          cases ready : state.releaseReady <;>
            simp [Execution.step, owner, begun, ready, Execution.begin, Execution.normalizerRemaining]
          omega
      | true =>
          cases ready : state.releaseReady with
          | true => simp [Execution.step, owner, begun, ready, Execution.release, Execution.normalizerRemaining]
          | false =>
              have balance := Normalizer.rank_balance tail state.work
              have notAtomic := Normalizer.true_not_atomic tail state.work
              cases reply : (Normalizer.callback tail true state.work).status with
              | atomic => exact False.elim (notAtomic reply)
              | pending =>
                  simp [Execution.step, owner, begun, ready, reply, Execution.normalizerRemaining]
                  omega
              | complete =>
                  have cleared := Normalizer.complete_child_cleared tail state.work reply
                  have rankZero : (Normalizer.callback tail true state.work).next.rank = 0 := by
                    simp [Normalizer.rank, cleared]
                  simp [rankZero] at balance
                  simp [Execution.step, owner, begun, ready, reply, Execution.normalizerRemaining]
                  omega

theorem Execution.normalizer_prefix_balance (tail : AtomicTail Token Context Service)
    (fuel : Nat) (control : Option Status)
    (state : Execution Owner (Normalizer Token Context Service) Loan Context) :
    let result := advance (Execution.provider (Normalizer.callback tail)) (Execution.client true)
      (Execution.charge (Normalizer.callback tail)) fuel ⟨(), control, state⟩
    (Execution.outcomeState (Normalizer.callback tail) true result.2).normalizerRemaining + result.1 =
      state.normalizerRemaining := by
  induction fuel generalizing control state with
  | zero => simp [advance, Execution.outcomeState]
  | succ fuel ih =>
      cases control with
      | some status => simp [Execution.advance_stopped, Execution.outcomeState]
      | none =>
          simp only [Execution.advance_poll]
          have rest := ih (if (state.step (Normalizer.callback tail) true).status = .pending then none
            else some (state.step (Normalizer.callback tail) true).status) (state.step (Normalizer.callback tail) true).next
          have first := state.normalizer_work_balance tail
          dsimp only at rest
          exact (Nat.add_left_comm _ _ _).trans
            ((congrArg (fun n => (state.step (Normalizer.callback tail) true).used + n) rest).trans
              ((Nat.add_comm _ _).trans first))

/-- Every finite child inventory completes when its explicit atomic tail is
granted. The bound is on this model's protocol inspections, not elapsed work
of allocator/provider services or a native callback's batching policy. -/
theorem Execution.normalizer_finite_completion (tail : AtomicTail Token Context Service)
    (state : Execution Owner (Normalizer Token Context Service) Loan Context) (fuel : Nat)
    (enough : state.normalizerRank + 2 ≤ fuel) :
    ∃ final, state.run (Normalizer.callback tail) true fuel =
      (state.normalizerRemaining, .done ⟨(), .complete, final⟩) ∧ final.owner = none := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      have positive : 0 < fuel := by omega
      cases owner : state.owner with
      | none =>
          cases fuel with
          | zero => omega
          | succ rest =>
              refine ⟨state, ?_, owner⟩
              simp only [Execution.run, Execution.packet, Execution.advance_poll,
                Execution.step, owner]
              simp [Execution.advance_stopped, Execution.normalizerRemaining, owner]
      | some heldOwner =>
          have smaller := state.normalizer_rank_decreases tail heldOwner owner
          have room : (state.step (Normalizer.callback tail) true).next.normalizerRank + 2 ≤ fuel := by omega
          have notAtomic := state.normalizer_not_atomic tail
          cases reply : (state.step (Normalizer.callback tail) true).status with
          | atomic => exact False.elim (notAtomic reply)
          | pending =>
              obtain ⟨final, done, released⟩ := ih (state.step (Normalizer.callback tail) true).next room
              refine ⟨final, ?_, released⟩
              have balance := state.normalizer_work_balance tail
              simp only [Execution.run, Execution.packet, Execution.advance_poll, reply, ↓reduceIte]
              change ((state.step (Normalizer.callback tail) true).used +
                ((state.step (Normalizer.callback tail) true).next.run (Normalizer.callback tail) true fuel).1,
                ((state.step (Normalizer.callback tail) true).next.run (Normalizer.callback tail) true fuel).2) = _
              rw [done]
              exact Prod.ext (by omega) rfl
          | complete =>
              have cleared := state.normalizer_complete_released tail reply
              refine ⟨(state.step (Normalizer.callback tail) true).next, ?_, cleared⟩
              have zero : (state.step (Normalizer.callback tail) true).next.normalizerRemaining = 0 := by
                simp [Execution.normalizerRemaining, cleared]
              have balance := state.normalizer_work_balance tail
              cases fuel with
              | zero => omega
              | succ rest =>
                  simp only [Execution.run, Execution.packet, Execution.advance_poll, reply,
                    reduceCtorEq, ↓reduceIte, Execution.advance_stopped, Nat.add_zero]
                  exact Prod.ext (by omega) rfl

open _root_.CategoryTheory Mettapedia.Effects

/-- Edges are exactly the actual boundary actions for their declared
permission. They contain no invoice or destination-correctness premise. -/
abbrev Execution.stepGraph (callback : Callback Work) : Quiver (Execution Owner Work Loan Context) where
  Hom before after := Σ permission : Bool, PLift ((before.step callback permission).next = after)

def Execution.serviceAccount (callback : Callback Work) :
    letI := Execution.stepGraph (Owner := Owner) (Loan := Loan) (Context := Context) callback
    RunAccount (Paths (Execution Owner Work Loan Context)) (Multiplicative Nat) := by
  letI := Execution.stepGraph (Owner := Owner) (Loan := Loan) (Context := Context) callback
  exact Mettapedia.GSLT.Contracts.Accounts.pathAccount
    (fun {before} {_after} edge => Multiplicative.ofAdd (before.step callback edge.1).used)

/-- Every actual cursor prefix yields a typed path of this same transition
graph with its exact service account. This is a proof witness over `advance`,
not another retirement interpreter or a supplied whole-run equality. -/
theorem Execution.actual_path_account (callback : Callback Work) (permission : Bool)
    (fuel : Nat) (control : Option Status) (state : Execution Owner Work Loan Context) :
    letI := Execution.stepGraph (Owner := Owner) (Loan := Loan) (Context := Context) callback
    ∃ path : Quiver.Path state (Execution.outcomeState callback permission
      (advance (Execution.provider callback) (Execution.client permission) (Execution.charge callback)
        fuel ⟨(), control, state⟩).2),
      (Execution.serviceAccount callback).of path = Multiplicative.ofAdd
        (advance (Execution.provider callback) (Execution.client permission) (Execution.charge callback)
          fuel (base := ()) ⟨(), control, state⟩).1 := by
  let _ := Execution.stepGraph (Owner := Owner) (Loan := Loan) (Context := Context) callback
  induction fuel generalizing control state with
  | zero => exact ⟨.nil, rfl⟩
  | succ fuel ih =>
      cases control with
      | some status =>
          rw [Execution.advance_stopped]
          exact ⟨.nil, rfl⟩
      | none =>
          rw [Execution.advance_poll]
          obtain ⟨path, accounted⟩ := ih
            (if (state.step callback permission).status = .pending then none
              else some (state.step callback permission).status) (state.step callback permission).next
          let edge : state ⟶ (state.step callback permission).next := ⟨permission, ⟨rfl⟩⟩
          have head : (Execution.serviceAccount callback).of edge.toPath =
              Multiplicative.ofAdd (state.step callback permission).used := by
            change (Mettapedia.GSLT.Contracts.Accounts.pathAccount
              (fun {before : Execution Owner Work Loan Context} {_after} (edge : before ⟶ _after) =>
                Multiplicative.ofAdd (before.step callback edge.1).used)).of
                ((Quiver.Path.nil : Quiver.Path state state).cons edge) = _
            rw [Mettapedia.GSLT.Contracts.Accounts.pathAccount_cons,
              Mettapedia.GSLT.Contracts.Accounts.pathAccount_nil]
            simp only [one_mul]
            rfl
          refine ⟨edge.toPath.comp path, ?_⟩
          change (Execution.serviceAccount callback).of (edge.toPath ≫ path) = _
          exact ((Execution.serviceAccount callback).of_comp edge.toPath path).trans
            ((congrArg₂ (fun x y : Multiplicative Nat => x * y) head accounted).trans rfl)

def Normalizer.inventory (state : Normalizer Token Context Service) : List Token :=
  state.owner.toList ++ state.releasedRev ++ state.drain.whole

theorem Normalizer.inventory_partition (tail : AtomicTail Token Context Service)
    (permission : Bool) (state : Normalizer Token Context Service) :
    (Normalizer.callback tail permission state).next.inventory.Perm state.inventory := by
  cases owner : state.owner with
  | none => simp [Normalizer.callback, owner]
  | some ownerToken =>
      cases begun : state.retiring with
      | false => simp [Normalizer.callback, owner, begun, Normalizer.inventory]
      | true =>
          cases ready : state.drain.ready with
          | false =>
              simpa [Normalizer.callback, owner, begun, ready, Normalizer.inventory] using
                state.drain.step_partition.append_left (ownerToken :: state.releasedRev)
          | true =>
              cases permission <;>
                simp [Normalizer.callback, owner, begun, ready, Normalizer.inventory]

/-- Child ownership plus the actual converted allocations. Borrowed syntax,
memo images and sort-item aliases are absent from this ownership inventory. -/
def Execution.normalizerInventory
    (state : Execution Token (Normalizer Token Context Service) Loan Context) : List Token :=
  state.inventory ++ state.work.inventory

theorem Execution.normalizer_partition (tail : AtomicTail Token Context Service) (permission : Bool)
    (state : Execution Token (Normalizer Token Context Service) Loan Context) :
    (state.step (Normalizer.callback tail) permission).next.normalizerInventory.Perm state.normalizerInventory := by
  cases owner : state.owner with
  | none => simp [Execution.step, owner]
  | some ownerToken =>
      cases begun : state.retiring with
      | false => simp [Execution.step, owner, begun, Execution.normalizerInventory, Execution.inventory, Execution.begin]
      | true =>
          cases ready : state.releaseReady with
          | true =>
              simp [Execution.step, owner, begun, ready, Execution.normalizerInventory,
                Execution.inventory, Execution.release]
          | false =>
              simpa [Execution.step, owner, begun, ready, Execution.normalizerInventory, Execution.inventory] using
                (Normalizer.inventory_partition tail permission state.work).append_left (ownerToken :: state.releasedRev)

theorem Execution.normalizer_prefix_partition (tail : AtomicTail Token Context Service)
    (permission : Bool) (state : Execution Token (Normalizer Token Context Service) Loan Context) (fuel : Nat) :
    (Execution.outcomeState (Normalizer.callback tail) permission
      (state.run (Normalizer.callback tail) permission fuel).2).normalizerInventory.Perm state.normalizerInventory := by
  exact Execution.prefix_invariant (Normalizer.callback tail) permission
    (fun next => next.normalizerInventory.Perm state.normalizerInventory)
    (fun next previous => (next.normalizer_partition tail permission).trans previous)
    fuel none state (List.Perm.refl _)

theorem Execution.normalizer_prefix_unique (tail : AtomicTail Token Context Service)
    (permission : Bool) (state : Execution Token (Normalizer Token Context Service) Loan Context)
    (unique : state.normalizerInventory.Nodup) (fuel : Nat) :
    (Execution.outcomeState (Normalizer.callback tail) permission
      (state.run (Normalizer.callback tail) permission fuel).2).normalizerInventory.Nodup :=
  ((state.normalizer_prefix_partition tail permission fuel).nodup_iff).mpr unique

namespace Controls

def mixedFrame : Frame Nat where
  identity := 5
  extent := 3
  length := 3
  slots := fun i => if i = 0 then some 10 else if i = 2 then some 12 else none
  key := some ⟨some 20, some 21, some 22, 23⟩
  scratch := some 24
  assembly := some 25
  items := some 26

def mixedDrain : Drain Nat Nat :=
  ⟨[mixedFrame], some ⟨some 30, some 31, some 32⟩, [], 0, 0, 0, 0, 9⟩

def mixedChild : Normalizer Nat Nat Nat := ⟨some 200, false, mixedDrain, 0, 0, []⟩

def mixedExecution : Execution Nat (Normalizer Nat Nat Nat) Nat Nat :=
  ⟨some 100, mixedChild, some 77, 9, 0, false, false, true, []⟩

def tail : AtomicTail Nat Nat Nat := fun owner context service => service + owner + context

def held : Execution Nat (Normalizer Nat Nat Nat) Nat Nat :=
  Execution.outcomeState (Normalizer.callback tail) false (mixedExecution.run (Normalizer.callback tail) false 10).2

theorem initialized_extent_and_distinct_ownership : mixedFrame.Valid ∧ mixedExecution.normalizerInventory.Nodup := by
  constructor
  · constructor
    · decide
    · intro i beyond inside
      change 3 ≤ i at beyond
      change i < 3 at inside
      omega
  · decide

theorem actual_tail_order : mixedDrain.reference =
    [.slot 5 2 (some 12), .slot 5 1 none, .slot 5 0 (some 10),
      .frame 5 [20, 21, 22, 23, 24, 25, 26], .header [30, 31, 32]] := by decide

theorem null_slot_is_paid_but_owns_nothing :
    mixedDrain.step.step.scans = 2 ∧ mixedDrain.step.step.freeCalls = 2 ∧
      mixedDrain.step.step.releasedRev = [12] ∧ mixedDrain.step.step.frames.head?.map Frame.length = some 1 := by
  decide

theorem zero_keeps_loan_and_owner :
    mixedExecution.run (Normalizer.callback tail) false 0 =
      (0, .paused (mixedExecution.packet (Normalizer.callback tail) false)) ∧
      mixedExecution.loan = some 77 := ⟨rfl, rfl⟩

theorem outer_then_child_begin :
    let afterOuter := (mixedExecution.step (Normalizer.callback tail) false).next
    afterOuter.retiring = true ∧ afterOuter.loan = none ∧ afterOuter.work.retiring = false ∧
      afterOuter.work.drain.scans = 0 ∧
      (afterOuter.step (Normalizer.callback tail) false).next.work.retiring = true ∧
      (afterOuter.step (Normalizer.callback tail) false).used = 1 := by decide

theorem atomic_retains_actual_paid_prefix :
    mixedExecution.run (Normalizer.callback tail) false 10 =
      (7, .done ⟨(), .atomic, held⟩) ∧
      held.owner = some 100 ∧ held.work.owner = some 200 ∧ held.work.drain.ready = true ∧
      held.work.drain.scans = 3 ∧ held.work.atomicCalls = 0 ∧ held.work.service = 0 := by
  simp [Execution.run, Execution.packet, Execution.advance_poll, Execution.advance_stopped,
    Execution.step, Execution.begin, Normalizer.callback, held, mixedExecution, mixedChild,
    mixedDrain, mixedFrame, Drain.ready, Drain.step, Frame.pop, Execution.outcomeState]

theorem ready_ack_keeps_wrapper :
    let result := mixedExecution.run (Normalizer.callback tail) true 8
    result.1 = 8 ∧
      (Execution.outcomeState (Normalizer.callback tail) true result.2).owner = some 100 ∧
      (Execution.outcomeState (Normalizer.callback tail) true result.2).work.owner = none ∧
      (Execution.outcomeState (Normalizer.callback tail) true result.2).releaseReady = true ∧
      (Execution.outcomeState (Normalizer.callback tail) true result.2).releasedRev = [] := by
  simp [Execution.run, Execution.packet, Execution.advance_poll,
    Execution.step, Execution.begin, Normalizer.callback, mixedExecution, mixedChild,
    mixedDrain, mixedFrame, Drain.ready, Drain.step, Frame.pop, Execution.outcomeState]

theorem actual_full_invoice_and_single_release :
    let result := mixedExecution.run (Normalizer.callback tail) true 12
    result.1 = 9 ∧
      (Execution.outcomeState (Normalizer.callback tail) true result.2).owner = none ∧
      (Execution.outcomeState (Normalizer.callback tail) true result.2).releasedRev = [100] ∧
      (Execution.outcomeState (Normalizer.callback tail) true result.2).work.releasedRev = [200] ∧
      (Execution.outcomeState (Normalizer.callback tail) true result.2).work.service = 209 := by
  simp [Execution.run, Execution.packet, Execution.advance_poll, Execution.advance_stopped,
    Execution.step, Execution.begin, Execution.release, Normalizer.callback, mixedExecution, mixedChild,
    mixedDrain, mixedFrame, Drain.ready, Drain.step, Frame.pop, Execution.outcomeState, tail]

theorem regrant_continues_without_restart :
    let result := Execution.regrant (Normalizer.callback tail) false true 3
      (mixedExecution.run (Normalizer.callback tail) false 10)
    result.1 = 9 ∧
      (Execution.outcomeState (Normalizer.callback tail) true result.2).owner = none ∧
      (Execution.outcomeState (Normalizer.callback tail) true result.2).work.drain.scans = 3 ∧
      (Execution.outcomeState (Normalizer.callback tail) true result.2).work.atomicCalls = 1 ∧
      (Execution.outcomeState (Normalizer.callback tail) true result.2).work.service = 209 := by
  simp [Execution.regrant, Execution.run, Execution.packet, Execution.advance_poll, Execution.advance_stopped,
    Execution.step, Execution.begin, Execution.release, Normalizer.callback, mixedExecution, mixedChild,
    mixedDrain, mixedFrame, Drain.ready, Drain.step, Frame.pop, Execution.outcomeState, tail]

theorem resume_atomic_does_not_regrant :
    resume (Execution.provider (Normalizer.callback tail)) (Execution.client false)
      (Execution.charge (Normalizer.callback tail)) 100
      (mixedExecution.run (Normalizer.callback tail) false 10) = (7, .done ⟨(), .atomic, held⟩) := by
  rw [atomic_retains_actual_paid_prefix.1]
  rfl

theorem retained_boundary_blocks_move_and_answers :
    held.moveAdmitted = false ∧ held.answerAdmission = .interrupted ∧
      (held.step (Normalizer.callback tail) false).next.owner = some 100 ∧
      (held.step (Normalizer.callback tail) false).used = 0 := by
  simp [held, Execution.run, Execution.packet, Execution.advance_poll, Execution.advance_stopped,
    Execution.step, Execution.begin, Normalizer.callback, mixedExecution, mixedChild,
    mixedDrain, mixedFrame, Drain.ready, Drain.step, Frame.pop, Execution.outcomeState,
    Execution.moveAdmitted, Execution.answerAdmission]

theorem released_boundary_is_inert :
    let final := Execution.outcomeState (Normalizer.callback tail) true
      (mixedExecution.run (Normalizer.callback tail) true 12).2
    final.answerAdmission = .handoff ∧ (final.step (Normalizer.callback tail) true).used = 0 ∧
      (final.step (Normalizer.callback tail) true).next.releasedRev = [100] := by
  simp [Execution.run, Execution.packet, Execution.advance_poll, Execution.advance_stopped,
    Execution.step, Execution.begin, Execution.release, Normalizer.callback, mixedExecution, mixedChild,
    mixedDrain, mixedFrame, Drain.ready, Drain.step, Frame.pop, Execution.outcomeState, Execution.answerAdmission]

def emptyFrame (identity : Nat) : Frame Nat := ⟨identity, 0, 0, fun _ => none, none, none, none, none⟩

def deepDrain : Drain Nat Nat := ⟨[emptyFrame 1, emptyFrame 2, emptyFrame 3], none, [], 0, 0, 0, 0, 9⟩

theorem empty_frames_are_individual_actions :
    deepDrain.reference = [.frame 1 [], .frame 2 [], .frame 3 []] ∧
      deepDrain.step.step.step.ready = true ∧ deepDrain.step.step.step.frameDrops = 3 ∧
      deepDrain.step.step.step.scans = 0 ∧ deepDrain.step.step.step.freeCalls = 9 := by decide

def repeatedTicket : Frame Nat :=
  { mixedFrame with slots := fun i => if i < 3 then some 10 else none }

theorem duplicate_ownership_is_not_admitted :
    ¬ repeatedTicket.inventory.Nodup ∧
      (repeatedTicket.pop.slots 2 = none) ∧ repeatedTicket.pop.pop.slots 1 = none := by decide

theorem completion_keeps_null_inspections_distinct :
    mixedDrain.step.step.step.step.step.freeCalls = 13 ∧
      mixedDrain.step.step.step.step.step.releasedRev.length = 12 ∧
      mixedDrain.step.step.step.step.step.releasedRev.reverse =
        [12, 10, 20, 21, 22, 23, 24, 25, 26, 30, 31, 32] := by decide

def wideFrame (width : Nat) : Frame Nat :=
  ⟨1, width, width, fun _ => none, none, none, none, some 40⟩

def wideExecution (width : Nat) : Execution Nat (Normalizer Nat Nat Nat) Nat Nat :=
  ⟨some 100, ⟨some 200, false,
    ⟨[wideFrame width], some ⟨none, none, some 50⟩, [], 0, 0, 0, 0, 9⟩, 0, 0, []⟩,
    some 77, 9, 0, false, false, true, []⟩

/-- An arbitrary initialized width has a complete model invoice. This does
not turn the explicitly atomic tail or allocator work into a physical bound. -/
theorem arbitrary_width_complete_invoice (width : Nat) :
    ∃ final, (wideExecution width).run (Normalizer.callback tail) true (width + 9) =
      (width + 6, .done ⟨(), .complete, final⟩) ∧ final.owner = none := by
  have remaining : (wideExecution width).normalizerRemaining = width + 6 := by
    simp [wideExecution, wideFrame, Execution.normalizerRemaining, Normalizer.rank, Drain.potential]
    omega
  have rank : (wideExecution width).normalizerRank + 2 ≤ width + 9 := by
    simp [wideExecution, wideFrame, Execution.normalizerRank, Normalizer.rank, Drain.potential]
    omega
  simpa only [remaining] using Execution.normalizer_finite_completion tail (wideExecution width) (width + 9) rank

theorem unconverted_service_units_do_not_bound_service_work :
    let reply := Normalizer.callback (fun (_owner _context : Nat) (service : Nat) => service + 1000)
      true held.work
    reply.used = 1 ∧ reply.next.service = held.work.service + 1000 ∧ reply.next.atomicCalls = 1 := by
  simp [held, Execution.run, Execution.packet, Execution.advance_poll, Execution.advance_stopped,
    Execution.step, Execution.begin, Normalizer.callback, mixedExecution, mixedChild,
    mixedDrain, mixedFrame, Drain.ready, Drain.step, Frame.pop, Execution.outcomeState]

end Controls

end Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement

namespace Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement

variable {Token Context Service Owner Loan : Type}

/-- Consistency of the actual child phases. A missing child owner is a
completed drain, never a way to abandon an initialized owned prefix. -/
def Normalizer.Valid (state : Normalizer Token Context Service) : Prop :=
  state.drain.Valid ∧ (state.owner = none → state.drain.ready = true)

/-- Release-ready records an acknowledged child completion. An absent outer
owner also requires that its child has already been cleared. This predicate
relates existing state fields; it supplies no invoice or disposal conclusion. -/
def Execution.Valid (state : Execution Owner (Normalizer Token Context Service) Loan Context) : Prop :=
  state.work.Valid ∧
    (state.releaseReady = true → state.work.owner = none) ∧
    (state.owner = none → state.work.owner = none)

theorem Drain.ready_remaining (state : Drain Token Context) (ready : state.ready = true) :
    state.remaining = [] := by
  have parts : state.frames = [] ∧ state.header = none := by
    simpa [Drain.ready] using ready
  simp [Drain.remaining, parts.1, parts.2]

theorem Normalizer.callback_valid (tail : AtomicTail Token Context Service)
    (permission : Bool) (state : Normalizer Token Context Service) (valid : state.Valid) :
    (Normalizer.callback tail permission state).next.Valid := by
  cases owner : state.owner with
  | none => simpa [Normalizer.callback, owner] using valid
  | some child =>
      cases begun : state.retiring with
      | false =>
          simpa [Normalizer.callback, owner, begun, Normalizer.Valid] using valid
      | true =>
          cases ready : state.drain.ready with
          | false =>
              simp only [Normalizer.callback, owner, begun, Bool.not_true, Bool.false_eq_true,
                ↓reduceIte, ready, Bool.not_false]
              exact ⟨state.drain.step_valid valid.1, by simp⟩
          | true =>
              cases permission with
              | false => simpa [Normalizer.callback, owner, begun, ready] using valid
              | true =>
                  simp only [Normalizer.callback, owner, begun, Bool.not_true, Bool.false_eq_true,
                    ↓reduceIte, ready]
                  exact ⟨valid.1, fun _ => ready⟩

theorem Normalizer.completed_callback_clears_child (tail : AtomicTail Token Context Service)
    (permission : Bool) (state : Normalizer Token Context Service)
    (complete : (Normalizer.callback tail permission state).status = .complete) :
    (Normalizer.callback tail permission state).next.owner = none := by
  cases owner : state.owner with
  | none => simp [Normalizer.callback, owner]
  | some child =>
      cases begun : state.retiring <;> cases ready : state.drain.ready <;>
        cases permission <;> simp [Normalizer.callback, owner, begun, ready] at complete ⊢

theorem Execution.normalizer_step_valid (tail : AtomicTail Token Context Service)
    (permission : Bool) (state : Execution Owner (Normalizer Token Context Service) Loan Context)
    (valid : state.Valid) : (state.step (Normalizer.callback tail) permission).next.Valid := by
  cases owner : state.owner with
  | none => simpa [Execution.step, owner] using valid
  | some outer =>
      cases begun : state.retiring with
      | false =>
          simpa [Execution.step, owner, begun, Execution.begin, Execution.Valid] using valid
      | true =>
          cases ready : state.releaseReady with
          | true =>
              have cleared := valid.2.1 ready
              simp only [Execution.step, owner, begun, Bool.not_true, Bool.false_eq_true,
                ↓reduceIte, ready, Execution.release, Execution.Valid]
              exact ⟨valid.1, fun _ => cleared, fun _ => cleared⟩
          | false =>
              simp only [Execution.step, owner, begun, Bool.not_true, Bool.false_eq_true,
                ↓reduceIte, ready, Execution.Valid]
              refine ⟨Normalizer.callback_valid tail permission state.work valid.1, ?_, ?_⟩
              · intro marked
                have complete : (Normalizer.callback tail permission state.work).status = .complete := by
                  simpa using marked
                exact Normalizer.completed_callback_clears_child tail permission state.work complete
              · intro absent
                cases absent

theorem Execution.normalizer_prefix_valid (tail : AtomicTail Token Context Service)
    (permission : Bool) (state : Execution Owner (Normalizer Token Context Service) Loan Context)
    (valid : state.Valid) (fuel : Nat) :
    (Execution.outcomeState (Normalizer.callback tail) permission
      (state.run (Normalizer.callback tail) permission fuel).2).Valid :=
  Execution.prefix_invariant (Normalizer.callback tail) permission Execution.Valid
    (fun next => next.normalizer_step_valid tail permission) fuel none state valid

/-- A fresh held child has no completed-phase shortcuts. Initialized frame
validity is the sole structural premise; no desired execution equality is an input. -/
theorem Execution.fresh_valid (outer : Owner) (child : Token) (drain : Drain Token Context)
    (service : Service) (loan : Option Loan) (context : Context) (relocatable : Bool)
    (drainValid : drain.Valid) :
    (Execution.mk (some outer) (Normalizer.mk (some child) false drain service 0 [])
      loan context 0 false false relocatable []).Valid := by
  exact ⟨⟨drainValid, by simp⟩, by simp, by simp⟩

/-- These are the still-held modeled allocation tickets. Opaque tail services
and external borrowed-context lifetime are not represented as extra tickets. -/
def Normalizer.pendingResources (state : Normalizer Token Context Service) : List Token :=
  state.owner.toList ++ state.drain.remaining

def Execution.pendingResources
    (state : Execution Token (Normalizer Token Context Service) Loan Context) : List Token :=
  state.owner.toList ++ state.work.pendingResources

theorem Execution.valid_released_child_and_drain
    (state : Execution Owner (Normalizer Token Context Service) Loan Context)
    (valid : state.Valid) (released : state.owner = none) :
    state.work.owner = none ∧ state.work.drain.ready = true ∧ state.work.drain.remaining = [] := by
  have child := valid.2.2 released
  have ready := valid.1.2 child
  exact ⟨child, ready, state.work.drain.ready_remaining ready⟩

/-- The valid finite endpoint strengthens the boundary-only completion law:
actual preserved phase consistency forces the child clear and every converted
ticket visited. Malformed release-ready metadata has no such conclusion. -/
theorem Execution.normalizer_valid_finite_completion (tail : AtomicTail Token Context Service)
    (state : Execution Owner (Normalizer Token Context Service) Loan Context) (valid : state.Valid)
    (fuel : Nat) (enough : state.normalizerRank + 2 ≤ fuel) :
    ∃ final, state.run (Normalizer.callback tail) true fuel =
      (state.normalizerRemaining, .done ⟨(), .complete, final⟩) ∧
      final.Valid ∧ final.owner = none ∧ final.work.owner = none ∧
      final.work.drain.ready = true ∧ final.work.drain.remaining = [] := by
  obtain ⟨final, done, released⟩ := state.normalizer_finite_completion tail fuel enough
  have kept := state.normalizer_prefix_valid tail true valid fuel
  rw [done] at kept
  change final.Valid at kept
  obtain ⟨child, ready, empty⟩ := final.valid_released_child_and_drain kept released
  exact ⟨final, done, kept, released, child, ready, empty⟩

theorem Execution.cleared_inventory_readback
    (state : Execution Token (Normalizer Token Context Service) Loan Context)
    (outer : state.owner = none) (child : state.work.owner = none)
    (drained : state.work.drain.remaining = []) :
    state.pendingResources = [] ∧ state.normalizerInventory =
      state.releasedRev ++ state.work.releasedRev ++ state.work.drain.releasedRev.reverse := by
  simp [Execution.pendingResources, Normalizer.pendingResources, Execution.normalizerInventory,
    Execution.inventory, Normalizer.inventory, Drain.whole, outer, child, drained, List.append_assoc]

/-- The completed release logs account for the actual initial ticket inventory.
This is derived from the proved concrete prefix partition and phase invariant,
not from an assumed correct final destination or an assumed complete invoice. -/
theorem Execution.normalizer_valid_complete_inventory (tail : AtomicTail Token Context Service)
    (state : Execution Token (Normalizer Token Context Service) Loan Context) (valid : state.Valid)
    (fuel : Nat) (enough : state.normalizerRank + 2 ≤ fuel) :
    ∃ final, state.run (Normalizer.callback tail) true fuel =
      (state.normalizerRemaining, .done ⟨(), .complete, final⟩) ∧ final.Valid ∧
      final.owner = none ∧ final.work.owner = none ∧ final.work.drain.remaining = [] ∧
      final.pendingResources = [] ∧
      (final.releasedRev ++ final.work.releasedRev ++ final.work.drain.releasedRev.reverse).Perm
        state.normalizerInventory := by
  obtain ⟨final, done, kept, outer, child, _ready, drained⟩ :=
    state.normalizer_valid_finite_completion tail valid fuel enough
  have readback := final.cleared_inventory_readback outer child drained
  have partition := state.normalizer_prefix_partition tail true fuel
  rw [done] at partition
  change final.normalizerInventory.Perm state.normalizerInventory at partition
  rw [readback.2] at partition
  exact ⟨final, done, kept, outer, child, drained, readback.1, partition⟩

theorem Execution.regrant_valid (tail : AtomicTail Token Context Service)
    (oldPermission newPermission : Bool)
    (state : Execution Owner (Normalizer Token Context Service) Loan Context) (valid : state.Valid)
    (first later : Nat) :
    (Execution.outcomeState (Normalizer.callback tail) newPermission
      (Execution.regrant (Normalizer.callback tail) oldPermission newPermission later
        (state.run (Normalizer.callback tail) oldPermission first)).2).Valid := by
  exact (Execution.outcomeState (Normalizer.callback tail) oldPermission
    (state.run (Normalizer.callback tail) oldPermission first).2).normalizer_prefix_valid tail newPermission
      (state.normalizer_prefix_valid tail oldPermission valid first) later

namespace Controls

theorem mixed_initial_phase_valid : mixedExecution.Valid := by
  apply Execution.fresh_valid
  intro frame member
  have same : frame = mixedFrame := by simpa [mixedDrain] using member
  subst frame
  exact initialized_extent_and_distinct_ownership.1

theorem wide_initial_phase_valid (width : Nat) : (wideExecution width).Valid := by
  apply Execution.fresh_valid
  intro frame member
  have same : frame = wideFrame width := by simpa [wideExecution] using member
  subst frame
  constructor
  · exact Nat.le_refl _
  · intro i beyond inside
    change width ≤ i at beyond
    change i < width at inside
    omega

theorem arbitrary_width_disposes_all_modeled_resources (width : Nat) :
    ∃ final, (wideExecution width).run (Normalizer.callback tail) true (width + 9) =
      (width + 6, .done ⟨(), .complete, final⟩) ∧ final.Valid ∧
      final.owner = none ∧ final.work.owner = none ∧ final.work.drain.remaining = [] ∧
      final.pendingResources = [] := by
  have remaining : (wideExecution width).normalizerRemaining = width + 6 := by
    simp [wideExecution, wideFrame, Execution.normalizerRemaining, Normalizer.rank, Drain.potential]
    omega
  have rank : (wideExecution width).normalizerRank + 2 ≤ width + 9 := by
    simp [wideExecution, wideFrame, Execution.normalizerRank, Normalizer.rank, Drain.potential]
    omega
  obtain ⟨final, done, kept, outer, child, drained, empty, _partition⟩ :=
    (wideExecution width).normalizer_valid_complete_inventory tail (wide_initial_phase_valid width) (width + 9) rank
  exact ⟨final, by simpa only [remaining] using done, kept, outer, child, drained, empty⟩

def forgedReady : Execution Nat (Normalizer Nat Nat Nat) Nat Nat :=
  { mixedExecution with retiring := true, releaseReady := true, loan := none }

theorem forged_ready_rejects_phase_invariant : ¬ forgedReady.Valid := by
  intro valid
  have child := valid.2.1 (by rfl)
  simp [forgedReady, mixedExecution, mixedChild] at child

/-- Boundary release on malformed metadata does not establish child disposal. -/
theorem forged_ready_clears_outer_but_abandons_child :
    let final := Execution.outcomeState (Normalizer.callback tail) true
      (forgedReady.run (Normalizer.callback tail) true 3).2
    final.owner = none ∧ final.work.owner = some 200 ∧ final.work.drain.remaining ≠ [] := by
  simp [Execution.run, Execution.packet, Execution.advance_poll, Execution.advance_stopped,
    Execution.step, Execution.release, Execution.outcomeState, forgedReady, mixedExecution,
    mixedChild, mixedDrain, Drain.remaining, mixedFrame, Frame.inventory, Frame.keys, Header.inventory]

theorem completed_child_with_pending_slots_rejects_phase_invariant :
    ¬ ({ mixedChild with owner := none } : Normalizer Nat Nat Nat).Valid := by
  intro valid
  have ready := valid.2 rfl
  simp [mixedChild, mixedDrain, Drain.ready] at ready

theorem actual_pause_and_atomic_regrant_preserve_phase :
    (Execution.outcomeState (Normalizer.callback tail) true
      (mixedExecution.run (Normalizer.callback tail) true 8).2).Valid ∧
    (Execution.outcomeState (Normalizer.callback tail) true
      (Execution.regrant (Normalizer.callback tail) false true 3
        (mixedExecution.run (Normalizer.callback tail) false 10)).2).Valid :=
  ⟨mixedExecution.normalizer_prefix_valid tail true mixed_initial_phase_valid 8,
    mixedExecution.regrant_valid tail false true mixed_initial_phase_valid 10 3⟩

end Controls

end Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement

/-!
Task and host cancellation compose the retained execution protocol with the
existing ready queue and a source-dependent destination-copy owner. Each
positive model action is a single phase transition. Cursor inspection fuel,
cleanup-provider requests, settled service units, producer membership and
host atomic tails are separate observations. Native multi-unit batching and
physical bookkeeping/provider prices require their own realization.

Captured source work and caller credit remain retained context, not funding
for cleanup. Preserving that context's identity does not establish its
external lifetime. Atomic permission grants work placement only; resource,
effect and lifetime authority remain independent premises.
-/

namespace Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.TaskHost

open Mettapedia.TypeTheory

variable {Token Work Loan Context Capture : Type}

/-- Queue membership denotes production eligibility only. The task object and
its callback captures remain owned independently while cleanup is scheduled. -/
structure Task (Token Work Loan Context Capture : Type) where
  identity : Nat
  queue : Mettapedia.Machines.ReadyQueue.State
  execution : Execution Token Work Loan Context
  capture : Capture

/-- One positive model action, using the existing removal and cleanup steps.
Queue removal is outside cleanup service units. An empty execution makes no
cleanup-provider request, although its queue membership can still be removed. -/
def Task.step (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) : Reply (Task Token Work Loan Context Capture) :=
  let removed := (Mettapedia.Machines.ReadyQueue.step state.queue (.remove state.identity)).2
  match state.execution.owner with
  | none => ⟨.complete, 0, { state with queue := removed }⟩
  | some _ =>
      let result := state.execution.step callback permission
      ⟨result.status, result.used, { state with queue := removed, execution := result.next }⟩

/-- A zero grant observes only whether this task is already empty. It does
not remove membership, clear a loan, invoke a provider or change captures.
A positive grant selects one model action; native batching is separate. -/
def Task.pollOne (callback : Callback Work) (permission : Bool) (grant : Nat)
    (state : Task Token Work Loan Context Capture) : Reply (Task Token Work Loan Context Capture) :=
  if grant = 0 then
    ⟨(if state.identity ∈ state.queue.tasks ∨ state.execution.owner.isSome then .pending else .complete), 0, state⟩
  else state.step callback permission

inductive Event (Token : Type) where
  | membership (task : Nat)
  | cleanupWork (units : Nat)
  | cleanupPoll
  | returnCopy (ticket : Token)
  | decision (ticket : Token)
  deriving DecidableEq, Repr

/-- The callback-completion order is service settlement before its request
account. This word is a semantic observation, not a required runtime log. -/
def Task.events (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) : List (Event Token) :=
  (if state.identity ∈ state.queue.tasks then [.membership state.identity] else []) ++
    (if state.execution.owner.isSome then
      (if (state.execution.step callback permission).used = 0 then []
       else [.cleanupWork (state.execution.step callback permission).used]) ++ [.cleanupPoll] else [])

def Event.units : Event Token → Nat
  | .cleanupWork units => units
  | .returnCopy _ | .decision _ => 1
  | .membership _ | .cleanupPoll => 0

def Event.requests : Event Token → Nat
  | .cleanupPoll => 1
  | _ => 0

def Event.removals : Event Token → Nat
  | .membership _ => 1
  | _ => 0

def weighted (price : Event Token → Nat) (word : List (Event Token)) : Nat := (word.map price).sum

theorem Task.zero_inert (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) :
    (state.pollOne callback permission 0).next = state ∧ (state.pollOne callback permission 0).used = 0 := by
  simp [Task.pollOne]

theorem Task.actual_execution_step (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) :
    (state.step callback permission).status = (state.execution.step callback permission).status ∧
      (state.step callback permission).used = (state.execution.step callback permission).used ∧
      (state.step callback permission).next.execution = (state.execution.step callback permission).next := by
  cases owner : state.execution.owner with
  | none => simp [Task.step, owner, Execution.step]
  | some owner => simp [Task.step, owner]

theorem Task.step_capture (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) :
    (state.step callback permission).next.capture = state.capture ∧
      (state.step callback permission).next.identity = state.identity := by
  cases owner : state.execution.owner <;> simp [Task.step, owner]

theorem Task.step_removes_producer (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) :
    state.identity ∉ (state.step callback permission).next.queue.tasks := by
  cases owner : state.execution.owner <;>
    simp [Task.step, owner, Mettapedia.Machines.ReadyQueue.step]

theorem Task.step_keeps_other_members (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) (other : Nat) (different : other ≠ state.identity) :
    other ∈ (state.step callback permission).next.queue.tasks ↔ other ∈ state.queue.tasks := by
  cases owner : state.execution.owner <;>
    simpa [Task.step, owner] using
      Mettapedia.Machines.ReadyQueue.removal_preserves_other_members state.queue state.identity other different

theorem Task.service_projection (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) :
    weighted Event.units (state.events callback permission) = (state.step callback permission).used := by
  cases owner : state.execution.owner with
  | none =>
      by_cases queued : state.identity ∈ state.queue.tasks <;>
        simp [Task.events, Task.step, owner, queued, weighted, Event.units]
  | some owner =>
      by_cases queued : state.identity ∈ state.queue.tasks <;>
        by_cases zero : (state.execution.step callback permission).used = 0 <;>
        simp [Task.events, Task.step, owner, queued, zero, weighted, Event.units]

theorem Task.request_projection (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) :
    weighted Event.requests (state.events callback permission) = if state.execution.owner.isSome then 1 else 0 := by
  cases owner : state.execution.owner with
  | none =>
      by_cases queued : state.identity ∈ state.queue.tasks <;>
        simp [Task.events, owner, queued, weighted, Event.requests]
  | some owner =>
      by_cases queued : state.identity ∈ state.queue.tasks <;>
        by_cases zero : (state.execution.step callback permission).used = 0 <;>
        simp [Task.events, owner, queued, zero, weighted, Event.requests]

theorem Task.removal_projection (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) :
    weighted Event.removals (state.events callback permission) = if state.identity ∈ state.queue.tasks then 1 else 0 := by
  cases owner : state.execution.owner with
  | none =>
      by_cases queued : state.identity ∈ state.queue.tasks <;>
        simp [Task.events, owner, queued, weighted, Event.removals]
  | some owner =>
      by_cases queued : state.identity ∈ state.queue.tasks <;>
        by_cases zero : (state.execution.step callback permission).used = 0 <;>
        simp [Task.events, owner, queued, zero, weighted, Event.removals]

def Task.provider (callback : Callback Work) : Provider protocol where
  State _ _ := Task Token Work Loan Context Capture
  step state permission := ⟨(state.step callback permission).status, (state.step callback permission).next⟩

def Task.executionHom (callback : Callback Work) :
    Hom (Task.provider (Token := Token) (Loan := Loan) (Context := Context) (Capture := Capture) callback)
      (Execution.provider (Owner := Token) (Loan := Loan) (Context := Context) callback) where
  map state := state.execution
  step state permission := by
    have actual := state.actual_execution_step callback permission
    exact Sigma.ext actual.1 (heq_of_eq actual.2.2)

def Task.charge (callback : Callback Work) : Charge
    (Task.provider (Token := Token) (Loan := Loan) (Context := Context) (Capture := Capture) callback) :=
  fun state permission => (state.step callback permission).used

def Task.packet (callback : Callback Work) (permission : Bool) (state : Task Token Work Loan Context Capture) :
    Packet (Task.provider (Token := Token) (Loan := Loan) (Context := Context) (Capture := Capture) callback)
      (Execution.client permission) () := ⟨(), none, state⟩

def Task.run (callback : Callback Work) (permission : Bool) (fuel : Nat)
    (state : Task Token Work Loan Context Capture) :=
  advance (Task.provider callback) (Execution.client permission) (Task.charge callback) fuel
    (state.packet callback permission)

theorem Task.execution_account (callback : Callback Work) (permission : Bool) (fuel : Nat)
    (state : Task Token Work Loan Context Capture) :
    ((state.run callback permission fuel).1,
      (Task.executionHom callback).outcome (Execution.client permission) (state.run callback permission fuel).2) =
      state.execution.run callback permission fuel := by
  exact (Task.executionHom callback).advance_account (Execution.client permission) (Task.charge callback)
    (Execution.charge callback) (by intro _ _ next permission; exact (next.actual_execution_step callback permission).2.1)
    fuel (state.packet callback permission)

theorem Task.run_zero (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) :
    state.run callback permission 0 = (0, .paused (state.packet callback permission)) := rfl

/-- This split composes protocol inspection fuel. It does not identify a
native multi-unit grant with a count of callback requests. -/
theorem Task.split (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) (first later : Nat) :
    state.run callback permission (first + later) =
      resume (Task.provider callback) (Execution.client permission) (Task.charge callback) later
        (state.run callback permission first) := advance_add _ _ _ first later (state.packet callback permission)

private def stateOf (machine : Provider protocol) (permission : Bool) :
    Outcome machine (Execution.client permission) () → machine.State () ()
  | .paused ⟨(), _, state⟩ => state
  | .done ⟨(), _, state⟩ => state

private theorem client_poll (permission : Bool) :
    (Execution.client permission).str () () none =
      ⟨.inr permission, fun (status : Status) => if status = .pending then none else some status⟩ := by
  unfold Execution.client
  dsimp only
  simp only [TypeCat.ofHom, CategoryTheory.ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
  rfl

private theorem client_stopped (permission : Bool) (status : Status) :
    (Execution.client permission).str () () (some status) =
      ⟨.inl status, fun impossible => nomatch impossible⟩ := by
  unfold Execution.client
  dsimp only
  simp only [TypeCat.ofHom, CategoryTheory.ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
  congr 1
  funext impossible
  cases impossible

private def followingControl (status : Status) : Option Status :=
  if status = .pending then none else some status

private theorem advance_poll (machine : Provider protocol) (charge : Charge machine)
    (permission : Bool) (fuel : Nat) (state : machine.State () ()) :
    advance machine (Execution.client permission) charge (fuel + 1) (base := ()) ⟨(), none, state⟩ =
      let response := machine.step state permission
      let rest := advance machine (Execution.client permission) charge fuel (base := ())
        ⟨(), followingControl response.1, response.2⟩
      (charge state permission + rest.1, rest.2) := by
  simp only [advance, client_poll]
  rfl

private theorem advance_stopped (machine : Provider protocol) (charge : Charge machine)
    (permission : Bool) (fuel : Nat) (status : Status) (state : machine.State () ()) :
    advance machine (Execution.client permission) charge (fuel + 1) (base := ())
      ⟨(), some status, state⟩ = (0, .done ⟨(), status, state⟩) := by
  simp only [advance, client_stopped]

/-- A shared proof about the existing cursor, used by both wrappers. It adds
no traversal, scheduler or evaluation algorithm. -/
private theorem prefix_invariant (machine : Provider protocol) (charge : Charge machine)
    (permission : Bool) (invariant : machine.State () () → Prop)
    (kept : ∀ state, invariant state → invariant (machine.step state permission).2)
    (fuel : Nat) (control : Option Status) (state : machine.State () ()) (valid : invariant state) :
    invariant (stateOf machine permission (advance machine (Execution.client permission) charge fuel
      (base := ()) ⟨(), control, state⟩).2) := by
  induction fuel generalizing control state with
  | zero => exact valid
  | succ fuel ih =>
      cases control with
      | some status => rw [advance_stopped]; exact valid
      | none =>
          rw [advance_poll]
          exact ih _ _ (kept state valid)

def Task.outcomeState (callback : Callback Work) (permission : Bool) :
    Outcome (Task.provider (Token := Token) (Loan := Loan) (Context := Context) (Capture := Capture) callback)
      (Execution.client permission) () → Task Token Work Loan Context Capture := stateOf _ permission

variable {Service : Type}

def Task.Valid (state : Task Token (Normalizer Token Context Service) Loan Context Capture) : Prop :=
  Mettapedia.Machines.ReadyQueue.invariant state.queue ∧ state.execution.Valid

theorem Task.step_valid (tail : AtomicTail Token Context Service) (permission : Bool)
    (state : Task Token (Normalizer Token Context Service) Loan Context Capture) (valid : state.Valid) :
    (state.step (Normalizer.callback tail) permission).next.Valid := by
  have queue := Mettapedia.Machines.ReadyQueue.step_preserves_invariant
    state.queue (.remove state.identity) valid.1
  have execution := state.execution.normalizer_step_valid tail permission valid.2
  cases owner : state.execution.owner with
  | none => simpa [Task.step, Task.Valid, owner] using And.intro queue valid.2
  | some owner => simpa [Task.step, Task.Valid, owner] using And.intro queue execution

theorem Task.prefix_valid (tail : AtomicTail Token Context Service) (permission : Bool)
    (state : Task Token (Normalizer Token Context Service) Loan Context Capture) (valid : state.Valid)
    (fuel : Nat) :
    (Task.outcomeState (Normalizer.callback tail) permission
      (state.run (Normalizer.callback tail) permission fuel).2).Valid :=
  prefix_invariant (Task.provider (Normalizer.callback tail)) (Task.charge (Normalizer.callback tail))
    permission Task.Valid (fun next => next.step_valid tail permission) fuel none state valid

theorem Task.prefix_capture_and_acceptance (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) (fuel : Nat) :
    let final := Task.outcomeState callback permission (state.run callback permission fuel).2
    final.capture = state.capture ∧ final.execution.accepted = state.execution.accepted ∧
      final.execution.context = state.execution.context := by
  refine prefix_invariant (Task.provider callback) (Task.charge callback) permission
    (fun next => next.capture = state.capture ∧ next.execution.accepted = state.execution.accepted ∧
      next.execution.context = state.execution.context) ?_ fuel none state ?_
  · intro next previous
    have actual := next.actual_execution_step callback permission
    have kept := next.execution.step_context callback permission
    exact ⟨(next.step_capture callback permission).1.trans previous.1,
      (congrArg Execution.accepted actual.2.2).trans (kept.2.trans previous.2.1),
      (congrArg Execution.context actual.2.2).trans (kept.1.trans previous.2.2)⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem Task.positive_blocks_answers (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) :
    (state.step callback permission).next.execution.answerAdmission ≠ .available := by
  rw [(state.actual_execution_step callback permission).2.2]
  cases owner : state.execution.owner with
  | none => simp [Execution.step, owner, Execution.answerAdmission]
  | some owner =>
      cases begun : state.execution.retiring <;> cases ready : state.execution.releaseReady <;>
        simp [Execution.step, owner, begun, ready, Execution.begin, Execution.release, Execution.answerAdmission]

set_option backward.isDefEq.respectTransparency false in
theorem Task.positive_prefix_not_queued (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) (fuel : Nat) :
    let final := Task.outcomeState callback permission (state.run callback permission (fuel + 1)).2
    final.identity ∉ final.queue.tasks := by
  unfold Task.run Task.packet
  dsimp only
  rw [advance_poll]
  refine prefix_invariant (Task.provider callback) (Task.charge callback) permission
    (fun next => next.identity ∉ next.queue.tasks) ?_ fuel _ _ ?_
  · intro next _previous
    change (next.step callback permission).next.identity ∉ (next.step callback permission).next.queue.tasks
    rw [(next.step_capture callback permission).2]
    exact next.step_removes_producer callback permission
  · change (state.step callback permission).next.identity ∉ (state.step callback permission).next.queue.tasks
    rw [(state.step_capture callback permission).2]
    exact state.step_removes_producer callback permission

/-- The actual provider hom transports finite service execution; the queue
and capture invariants are then derived on its retained source residual. -/
theorem Task.valid_finite_completion (tail : AtomicTail Token Context Service)
    (state : Task Token (Normalizer Token Context Service) Loan Context Capture) (valid : state.Valid)
    (fuel : Nat) (enough : state.execution.normalizerRank + 2 ≤ fuel) :
    ∃ final, state.run (Normalizer.callback tail) true fuel =
      (state.execution.normalizerRemaining, .done ⟨(), .complete, final⟩) ∧ final.Valid ∧
      final.identity ∉ final.queue.tasks ∧ final.execution.owner = none ∧
      final.execution.work.owner = none ∧ final.execution.work.drain.remaining = [] := by
  obtain ⟨target, finished, targetValid, outer, child, _ready, drained⟩ :=
    state.execution.normalizer_valid_finite_completion tail valid.2 fuel enough
  have actual := state.execution_account (Normalizer.callback tail) true fuel
  rw [finished] at actual
  cases result : state.run (Normalizer.callback tail) true fuel with
  | mk paid outcome =>
      rw [result] at actual
      have billed : paid = state.execution.normalizerRemaining := congrArg Prod.fst actual
      cases outcome with
      | paused packet =>
          have observed := congrArg Prod.snd actual
          simp [Hom.outcome, Outcome.mapState] at observed
      | done record =>
          rcases record with ⟨index, status, final⟩
          cases index
          have observed := congrArg Prod.snd actual
          have same : status = .complete ∧ final.execution = target := by
            simp only [Hom.outcome, Outcome.mapState] at observed
            have result := Outcome.done.inj observed
            have pair := congrArg (fun value : Finished
              (Execution.provider (Owner := Token) (Loan := Loan) (Context := Context) (Normalizer.callback tail))
              (Return := fun _ _ => Status) () =>
                ((value.2.1, value.2.2) : Status × Execution Token (Normalizer Token Context Service) Loan Context)) result
            exact Prod.mk.inj pair
          have kept := state.prefix_valid tail true valid fuel
          rw [result] at kept
          change final.Valid at kept
          have queued : final.identity ∉ final.queue.tasks := by
            cases fuel with
            | zero => omega
            | succ rest =>
                have absent := state.positive_prefix_not_queued (Normalizer.callback tail) true rest
                simpa [result, Task.outcomeState, stateOf] using absent
          refine ⟨final, ?_, kept, queued, ?_, ?_, ?_⟩
          · exact Prod.ext billed (by rw [same.1])
          · simpa [same.2] using outer
          · simpa [same.2] using child
          · simpa [same.2] using drained

def Task.pending (state : Task Token Work Loan Context Capture) : Bool :=
  decide (state.identity ∈ state.queue.tasks) || state.execution.owner.isSome

theorem Task.not_pending (state : Task Token Work Loan Context Capture) :
    state.pending = false ↔ state.identity ∉ state.queue.tasks ∧ state.execution.owner = none := by
  cases owner : state.execution.owner <;> simp [Task.pending, owner]

/-- A retained destination continuation names the exact source owner it may
still consult. Its private cursor/arena marks are retained in `residual`. -/
structure DependentCopy (Token Residual : Type) where
  ticket : Token
  sourceOwner : Token
  residual : Residual
  deriving DecidableEq, Repr

/-- `Output` denotes retained completed data, not the completion verdict.
Cancellation changes that separate verdict while data inspection remains
available until its decision owner is actually released. -/
structure Host (Token Work Loan Context Capture Residual Snapshot Output Service : Type) where
  owner : Option Token
  task : Task Token Work Loan Context Capture
  copy : Option (DependentCopy Token Residual)
  snapshot : Option Snapshot
  cancelled : Bool
  outcome : Output
  service : Service
  releasedCopiesRev : List Token
  releasedDecisionsRev : List Token

variable {Residual Snapshot Output HostService : Type}

def Host.mark (observe : Execution Token Work Loan Context → Snapshot)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :=
  { state with cancelled := true
               snapshot := if state.cancelled then state.snapshot else some (observe state.task.execution) }

/-- One actual cleanup phase. With a dependent copy, the first positive
action overrides atomic permission and performs only source cancellation-begin.
The copy is then disposed before further source cleanup. Decision metadata is
a separately admitted final tail. No ordinary plan/delivery callback occurs. -/
def Host.step (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :
    Reply (Host Token Work Loan Context Capture Residual Snapshot Output HostService) :=
  match state.owner with
  | none => ⟨.complete, 0, state⟩
  | some owner =>
      let marked := state.mark observe
      if !state.cancelled && state.copy.isSome then
        let stopped := state.task.step callback false
        ⟨.pending, stopped.used, { marked with task := stopped.next }⟩
      else match state.copy with
      | some copy =>
          if permission then
            ⟨.pending, 1, { marked with
              copy := none
              service := copyTail copy state.task.capture state.service
              releasedCopiesRev := copy.ticket :: state.releasedCopiesRev }⟩
          else ⟨.atomic, 0, marked⟩
      | none =>
          if state.task.pending then
            let result := state.task.step callback permission
            ⟨(if result.status = .complete ∧ releaseDecision then .pending else result.status),
              result.used, { marked with task := result.next }⟩
          else if releaseDecision then
            if permission then
              ⟨.complete, 1, { marked with
                owner := none
                service := decisionTail owner state.task.capture state.service
                releasedDecisionsRev := owner :: state.releasedDecisionsRev }⟩
            else ⟨.atomic, 0, marked⟩
          else ⟨.complete, 0, marked⟩

def Host.events (callback : Callback Work) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) : List (Event Token) :=
  match state.owner with
  | none => []
  | some owner =>
      if !state.cancelled && state.copy.isSome then state.task.events callback false
      else match state.copy with
      | some copy => if permission then [.returnCopy copy.ticket] else []
      | none =>
          if state.task.pending then state.task.events callback permission
          else if releaseDecision && permission then [.decision owner] else []

def Host.pollOne (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool) (grant : Nat)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :=
  if grant = 0 then
    (⟨(if state.owner.isNone || (!releaseDecision && !state.task.pending && state.copy.isNone)
       then .complete else .pending), 0, state⟩ : Reply _)
  else state.step callback observe copyTail decisionTail releaseDecision permission

/-- Source identity/lifetime is not replaced by snapshot equality. The first
copy-dependent cancellation starts from an unretired source; later phases keep
that same owner until the dependent copy is gone. -/
def Host.Valid (state : Host Token (Normalizer Token Context Service) Loan Context Capture
    Residual Snapshot Output HostService) : Prop :=
  state.task.Valid ∧
    (∀ copy, state.copy = some copy → state.task.execution.owner = some copy.sourceOwner) ∧
    (state.cancelled = false → state.copy.isSome = true → state.task.execution.retiring = false) ∧
    (state.owner = none → state.task.pending = false ∧ state.copy = none)

theorem Host.zero_inert (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :
    (state.pollOne callback observe copyTail decisionTail releaseDecision permission 0).next = state ∧
      (state.pollOne callback observe copyTail decisionTail releaseDecision permission 0).used = 0 := by
  simp [Host.pollOne]

theorem Host.mark_cancelled (observe : Execution Token Work Loan Context → Snapshot)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :
    (state.mark observe).cancelled = true := by
  cases marked : state.cancelled <;> simp [Host.mark, marked]

theorem Host.mark_snapshot (observe : Execution Token Work Loan Context → Snapshot)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService)
    (fresh : state.cancelled = false) :
    (state.mark observe).snapshot = some (observe state.task.execution) := by
  simp [Host.mark, fresh]

theorem Host.source_stop_before_copy (callback : Callback Work)
    (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService)
    (owner : Token) (copy : DependentCopy Token Residual) (held : state.owner = some owner)
    (pending : state.copy = some copy) (fresh : state.cancelled = false)
    (source : state.task.execution.owner = some copy.sourceOwner)
    (unretired : state.task.execution.retiring = false) :
    let result := state.step callback observe copyTail decisionTail releaseDecision permission
    result.status = .pending ∧ result.used = 1 ∧ result.next.cancelled = true ∧
      result.next.copy = some copy ∧ result.next.task.execution.owner = some copy.sourceOwner ∧
      result.next.task.execution.retiring = true ∧ result.next.task.execution.loan = none ∧
      result.next.snapshot = some (observe state.task.execution) ∧ result.next.service = state.service := by
  simp [Host.step, held, pending, fresh, Host.mark, Task.step, source, Execution.step,
    unretired, Execution.begin]

theorem Host.service_projection (callback : Callback Work)
    (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :
    weighted Event.units (state.events callback releaseDecision permission) =
      (state.step callback observe copyTail decisionTail releaseDecision permission).used := by
  cases owner : state.owner with
  | none => simp [Host.step, Host.events, owner, weighted]
  | some owner =>
      cases cancelled : state.cancelled with
      | false =>
          cases copy : state.copy with
          | some dependent =>
              simpa [Host.step, Host.events, owner, cancelled, copy] using state.task.service_projection callback false
          | none =>
              cases ready : state.task.pending with
              | true => simpa [Host.step, Host.events, owner, cancelled, copy, ready] using
                  state.task.service_projection callback permission
              | false =>
                  cases releaseDecision <;> cases permission <;>
                    simp [Host.step, Host.events, owner, cancelled, copy, ready, weighted, Event.units]
      | true =>
          cases copy : state.copy with
          | some dependent =>
              cases permission <;> simp [Host.step, Host.events, owner, cancelled, copy, weighted, Event.units]
          | none =>
              cases ready : state.task.pending with
              | true => simpa [Host.step, Host.events, owner, cancelled, copy, ready] using
                  state.task.service_projection callback permission
              | false =>
                  cases releaseDecision <;> cases permission <;>
                    simp [Host.step, Host.events, owner, cancelled, copy, ready, weighted, Event.units]

/-- Gate for active planning, delivery and publication. It does not govern
read-only inspection of retained completed data. This is a model interface,
not a C conformance theorem for every consumer. -/
def Host.tryActiveAction {Result : Type}
    (operation : Output → Capture → Result)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) : Option Result :=
  if state.owner.isSome && !state.cancelled then some (operation state.outcome state.task.capture) else none

theorem Host.cancelled_refuses_active_actions {Result : Type} (operation : Output → Capture → Result)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService)
    (cancelled : state.cancelled = true) : state.tryActiveAction operation = none := by
  simp [Host.tryActiveAction, cancelled]

theorem Task.unretired_permission_irrelevant (callback : Callback Work) (left right : Bool)
    (state : Task Token Work Loan Context Capture) (unretired : state.execution.retiring = false) :
    state.step callback left = state.step callback right := by
  cases owner : state.execution.owner <;>
    simp [Task.step, owner, Execution.step, unretired, Execution.begin]

theorem Task.completed_is_empty (callback : Callback Work) (permission : Bool)
    (state : Task Token Work Loan Context Capture) (complete : (state.step callback permission).status = .complete) :
    (state.step callback permission).next.pending = false := by
  apply (Task.not_pending _).mpr
  constructor
  · rw [(state.step_capture callback permission).2]
    exact state.step_removes_producer callback permission
  · have actual := state.actual_execution_step callback permission
    have executionComplete := actual.1.symm.trans complete
    rw [actual.2.2]
    cases owner : state.execution.owner with
    | none => simp [Execution.step, owner]
    | some owner =>
        cases begun : state.execution.retiring <;> cases ready : state.execution.releaseReady <;>
          cases reply : (callback permission state.execution.work).status <;>
          simp [Execution.step, owner, begun, ready, reply, Execution.release] at executionComplete ⊢

theorem Host.mark_fields (observe : Execution Token Work Loan Context → Snapshot)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :
    (state.mark observe).task = state.task ∧ (state.mark observe).owner = state.owner ∧
      (state.mark observe).copy = state.copy ∧ (state.mark observe).outcome = state.outcome := by
  cases cancelled : state.cancelled <;> simp [Host.mark, cancelled]

theorem Host.mark_valid (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService)
    (valid : state.Valid) : (state.mark observe).Valid := by
  exact ⟨valid.1, valid.2.1, by simp [Host.mark], valid.2.2.2⟩

theorem Host.step_valid (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService)
    (valid : state.Valid) :
    (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission).next.Valid := by
  cases owner : state.owner with
  | none => simpa [Host.step, owner] using valid
  | some outer =>
      by_cases first : (!state.cancelled && state.copy.isSome) = true
      · have parts : state.cancelled = false ∧ state.copy.isSome = true := by simpa using first
        have unretired := valid.2.2.1 parts.1 parts.2
        have next := state.task.step_valid tail false valid.1
        have unchanged : (state.task.step (Normalizer.callback tail) false).next.execution.owner =
            state.task.execution.owner := by
          rw [(state.task.actual_execution_step (Normalizer.callback tail) false).2.2]
          cases source : state.task.execution.owner <;>
            simp [Execution.step, source, unretired, Execution.begin]
        simp only [Host.step, owner, first, ↓reduceIte]
        refine ⟨next, ?_, by simp [Host.mark], by simp [Host.mark, owner]⟩
        intro copy present
        change state.copy = some copy at present
        change (state.task.step (Normalizer.callback tail) false).next.execution.owner = some copy.sourceOwner
        rw [unchanged]
        exact valid.2.1 copy present
      · simp only [Host.step, owner, first, Bool.false_eq_true, ↓reduceIte]
        cases copy : state.copy with
        | some dependent =>
            cases permission with
            | false => exact state.mark_valid observe valid
            | true =>
                exact ⟨valid.1, by simp, by simp [Host.mark], by simp [Host.mark, owner]⟩
        | none =>
            cases pending : state.task.pending with
            | true =>
                exact ⟨state.task.step_valid tail permission valid.1,
                  by simp [Host.mark, copy], by simp [Host.mark], by simp [Host.mark, owner]⟩
            | false =>
                cases releaseDecision with
                | false => exact state.mark_valid observe valid
                | true =>
                    cases permission with
                    | false => exact state.mark_valid observe valid
                    | true => exact ⟨valid.1, by simp [Host.mark, copy], by simp [Host.mark],
                        fun _ => ⟨pending, copy⟩⟩

def Host.provider (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision : Bool) : Provider protocol where
  State _ _ := Host Token Work Loan Context Capture Residual Snapshot Output HostService
  step state permission :=
    ⟨(state.step callback observe copyTail decisionTail releaseDecision permission).status,
      (state.step callback observe copyTail decisionTail releaseDecision permission).next⟩

def Host.charge (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision : Bool) : Charge
    (Host.provider (Loan := Loan) (Output := Output) callback observe copyTail decisionTail releaseDecision) :=
  fun state permission => (state.step callback observe copyTail decisionTail releaseDecision permission).used

def Host.packet (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :
    Packet (Host.provider (Output := Output) callback observe copyTail decisionTail releaseDecision)
      (Execution.client permission) () := ⟨(), none, state⟩

def Host.run (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool) (fuel : Nat)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :=
  advance (Host.provider callback observe copyTail decisionTail releaseDecision) (Execution.client permission)
    (Host.charge callback observe copyTail decisionTail releaseDecision) fuel
    (state.packet callback observe copyTail decisionTail releaseDecision permission)

def Host.outcomeState (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool) :
    Outcome (Host.provider (Output := Output) callback observe copyTail decisionTail releaseDecision)
      (Execution.client permission) () → Host Token Work Loan Context Capture Residual Snapshot Output HostService :=
  stateOf _ permission

theorem Host.run_zero (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :
    state.run callback observe copyTail decisionTail releaseDecision permission 0 =
      (0, .paused (state.packet callback observe copyTail decisionTail releaseDecision permission)) := rfl

theorem Host.split (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) (first later : Nat) :
    state.run callback observe copyTail decisionTail releaseDecision permission (first + later) =
      resume (Host.provider callback observe copyTail decisionTail releaseDecision) (Execution.client permission)
        (Host.charge callback observe copyTail decisionTail releaseDecision) later
        (state.run callback observe copyTail decisionTail releaseDecision permission first) :=
  advance_add _ _ _ first later (state.packet callback observe copyTail decisionTail releaseDecision permission)

theorem Host.prefix_valid (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService)
    (valid : state.Valid) (fuel : Nat) :
    (Host.outcomeState (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission
      (state.run (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission fuel).2).Valid :=
  prefix_invariant (Host.provider (Normalizer.callback tail) observe copyTail decisionTail releaseDecision)
    (Host.charge (Normalizer.callback tail) observe copyTail decisionTail releaseDecision) permission Host.Valid
    (fun next => next.step_valid tail observe copyTail decisionTail releaseDecision permission) fuel none state valid

theorem Host.valid_copy_holds_source
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService)
    (valid : state.Valid) (copy : DependentCopy Token Residual) (pending : state.copy = some copy) :
    state.task.execution.owner = some copy.sourceOwner := valid.2.1 copy pending

theorem Host.prefix_copy_holds_source (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService)
    (valid : state.Valid) (fuel : Nat) (copy : DependentCopy Token Residual) :
    let final := Host.outcomeState (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission
      (state.run (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission fuel).2
    final.copy = some copy → final.task.execution.owner = some copy.sourceOwner :=
  (state.prefix_valid tail observe copyTail decisionTail releaseDecision permission valid fuel).2.1 copy

def Host.inspectCompletedData
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) : Option (Bool × Output) :=
  state.owner.map fun _ => (state.cancelled, state.outcome)

theorem Host.cancelled_data_remains_inspectable
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService)
    (owner : Token) (held : state.owner = some owner) (cancelled : state.cancelled = true) :
    state.inspectCompletedData = some (true, state.outcome) := by
  simp [Host.inspectCompletedData, held, cancelled]

def Task.rank (state : Task Token (Normalizer Token Context Service) Loan Context Capture) : Nat :=
  state.execution.normalizerRank + if state.identity ∈ state.queue.tasks then 1 else 0

theorem Task.rank_decreases (tail : AtomicTail Token Context Service)
    (state : Task Token (Normalizer Token Context Service) Loan Context Capture) (pending : state.pending = true) :
    (state.step (Normalizer.callback tail) true).next.rank < state.rank := by
  have absent := state.step_removes_producer (Normalizer.callback tail) true
  have identity := (state.step_capture (Normalizer.callback tail) true).2
  have zero : (if (state.step (Normalizer.callback tail) true).next.identity ∈
      (state.step (Normalizer.callback tail) true).next.queue.tasks then 1 else 0) = 0 := by
    rw [identity]
    simp [absent]
  simp only [Task.rank, zero]
  rw [(state.actual_execution_step (Normalizer.callback tail) true).2.2]
  cases owner : state.execution.owner with
  | none =>
      have queued : state.identity ∈ state.queue.tasks := by simpa [Task.pending, owner] using pending
      simp [Execution.step, owner, Execution.normalizerRank, queued]
  | some source =>
      have decrease := state.execution.normalizer_rank_decreases tail source owner
      split <;> omega

def Host.rank (releaseDecision : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService) : Nat :=
  if state.owner.isNone then 0 else state.task.rank + state.copy.toList.length +
    (if releaseDecision then 1 else 0) + if state.cancelled then 0 else 1

def Host.remaining (releaseDecision : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService) : Nat :=
  if state.owner.isNone then 0 else state.task.execution.normalizerRemaining + state.copy.toList.length +
    if releaseDecision then 1 else 0

theorem Task.remaining_balance (tail : AtomicTail Token Context Service)
    (state : Task Token (Normalizer Token Context Service) Loan Context Capture) :
    (state.step (Normalizer.callback tail) true).next.execution.normalizerRemaining +
      (state.step (Normalizer.callback tail) true).used = state.execution.normalizerRemaining := by
  rw [(state.actual_execution_step (Normalizer.callback tail) true).2.2,
    (state.actual_execution_step (Normalizer.callback tail) true).2.1]
  exact state.execution.normalizer_work_balance tail

theorem Host.remaining_balance (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService)
    (valid : state.Valid) :
    (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true).next.remaining releaseDecision +
      (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true).used =
        state.remaining releaseDecision := by
  cases owner : state.owner with
  | none => simp [Host.step, owner]
  | some outer =>
      have balance := state.task.remaining_balance tail
      by_cases first : (!state.cancelled && state.copy.isSome) = true
      · have parts : state.cancelled = false ∧ state.copy.isSome = true := by simpa using first
        have same := state.task.unretired_permission_irrelevant (Normalizer.callback tail) false true
          (valid.2.2.1 parts.1 parts.2)
        simp only [Host.step, owner, first, ↓reduceIte, same, Host.remaining, Host.mark, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte]
        omega
      · simp only [Host.step, owner, first, Bool.false_eq_true, ↓reduceIte]
        cases copy : state.copy with
        | some dependent =>
            simp [Host.remaining, Host.mark, owner, copy]
            omega
        | none =>
            cases pending : state.task.pending with
            | true =>
                simp only [Host.remaining, Host.mark, owner, copy, Option.isNone_some,
                  Bool.false_eq_true, ↓reduceIte, Option.toList_none, List.length_nil, Nat.add_zero]
                omega
            | false =>
                have source := ((Task.not_pending state.task).mp pending).2
                have empty : state.task.execution.normalizerRemaining = 0 := by
                  simp [Execution.normalizerRemaining, source]
                cases releaseDecision <;>
                  simp [Host.remaining, Host.mark, owner, copy, empty]

theorem Host.true_not_atomic (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService) :
    (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true).status ≠ .atomic := by
  cases owner : state.owner with
  | none => simp [Host.step, owner]
  | some outer =>
      have safe : (state.task.step (Normalizer.callback tail) true).status ≠ .atomic := by
        rw [(state.task.actual_execution_step (Normalizer.callback tail) true).1]
        exact state.task.execution.normalizer_not_atomic tail
      simp only [Host.step, owner]
      split
      · simp
      · cases copy : state.copy with
        | some dependent => simp
        | none =>
            cases pending : state.task.pending with
            | true =>
                cases result : (state.task.step (Normalizer.callback tail) true).status <;>
                  cases releaseDecision <;> simp_all
            | false => cases releaseDecision <;> simp

theorem Host.rank_decreases (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService)
    (valid : state.Valid) (owner : Token) (held : state.owner = some owner)
    (pendingReply : (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true).status = .pending) :
    (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true).next.rank releaseDecision <
      state.rank releaseDecision := by
  by_cases first : (!state.cancelled && state.copy.isSome) = true
  · have parts : state.cancelled = false ∧ state.copy.isSome = true := by simpa using first
    obtain ⟨copy, present⟩ := Option.isSome_iff_exists.mp parts.2
    have source := valid.2.1 copy present
    have taskPending : state.task.pending = true := by simp [Task.pending, source]
    have decrease := state.task.rank_decreases tail taskPending
    have same := state.task.unretired_permission_irrelevant (Normalizer.callback tail) false true
      (valid.2.2.1 parts.1 parts.2)
    simp only [Host.step, held, parts.1, present, Option.isSome_some, Bool.not_false, Bool.true_and,
      ↓reduceIte, same, Host.rank, Host.mark, Option.isNone_some, Bool.false_eq_true,
      Option.toList_some, List.length_singleton]
    omega
  · simp only [Host.step, held, first, Bool.false_eq_true, ↓reduceIte] at pendingReply ⊢
    cases copy : state.copy with
    | some dependent =>
        simp [Host.rank, Host.mark, held, copy]
        split <;> omega
    | none =>
        cases pending : state.task.pending with
        | true =>
            have decrease := state.task.rank_decreases tail pending
            simp only [Host.rank, Host.mark, held, copy, Option.isNone_some,
              Bool.false_eq_true, ↓reduceIte, Option.toList_none, List.length_nil, Nat.add_zero]
            split <;> omega
        | false => cases releaseDecision <;> simp [copy, pending] at pendingReply


/-- Completion is obtained from the actual phase cases. Plan completion may
retain decision metadata; decision completion additionally clears that owner. -/
theorem Host.completed_empty (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService)
    (valid : state.Valid)
    (complete : (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission).status = .complete) :
    let final := (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission).next
    final.task.pending = false ∧ final.copy = none ∧ (releaseDecision = true → final.owner = none) := by
  cases owner : state.owner with
  | none =>
      simp only [Host.step, owner]
      exact ⟨(valid.2.2.2 owner).1, (valid.2.2.2 owner).2, by simp⟩
  | some outer =>
      by_cases first : (!state.cancelled && state.copy.isSome) = true
      · simp [Host.step, owner, first] at complete
      · simp only [Host.step, owner, first, Bool.false_eq_true, ↓reduceIte] at complete ⊢
        cases copy : state.copy with
        | some dependent => cases permission <;> simp [copy] at complete
        | none =>
            cases pending : state.task.pending with
            | true =>
                have taskComplete : (state.task.step (Normalizer.callback tail) permission).status = .complete := by
                  cases result : (state.task.step (Normalizer.callback tail) permission).status <;>
                    cases releaseDecision <;> simp_all
                have mode : releaseDecision = false := by
                  cases releaseDecision <;> simp_all
                simpa [copy, pending, Host.mark, mode] using
                  state.task.completed_is_empty (Normalizer.callback tail) permission taskComplete
            | false =>
                cases releaseDecision <;> cases permission <;>
                  simp_all [Host.mark]

theorem Host.complete_remaining_zero (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService)
    (valid : state.Valid)
    (complete : (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission).status = .complete) :
    (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission).next.remaining releaseDecision = 0 := by
  have empty := state.completed_empty tail observe copyTail decisionTail releaseDecision permission valid complete
  have source := ((Task.not_pending _).mp empty.1).2
  cases releaseDecision with
  | false => simp [Host.remaining, source, empty.2.1, Execution.normalizerRemaining]
  | true => simp [Host.remaining, empty.2.2 rfl]

private theorem Host.advance_actual (callback : Callback Work)
    (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (fuel : Nat) (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :
    advance (Host.provider callback observe copyTail decisionTail releaseDecision) (Execution.client permission)
      (Host.charge callback observe copyTail decisionTail releaseDecision) (fuel + 1) (base := ()) ⟨(), none, state⟩ =
      let response := state.step callback observe copyTail decisionTail releaseDecision permission
      let rest := advance (Host.provider callback observe copyTail decisionTail releaseDecision) (Execution.client permission)
        (Host.charge callback observe copyTail decisionTail releaseDecision) fuel (base := ())
          ⟨(), followingControl response.status, response.next⟩
      (response.used + rest.1, rest.2) := by
  simp only [advance, client_poll]
  rfl

private theorem Host.advance_terminal (callback : Callback Work)
    (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (fuel : Nat) (status : Status)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :
    advance (Host.provider callback observe copyTail decisionTail releaseDecision) (Execution.client permission)
      (Host.charge callback observe copyTail decisionTail releaseDecision) (fuel + 1) (base := ())
        ⟨(), some status, state⟩ = (0, .done ⟨(), status, state⟩) := by
  simp only [advance, client_stopped]

/-- This finite completion theorem counts this cursor's inspection fuel.
It follows the actual task/host phases and their valid-state coupling; it
assumes neither a complete invoice nor a disposed child as an input. -/
theorem Host.finite_completion (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService)
    (valid : state.Valid) (fuel : Nat) (enough : state.rank releaseDecision + 2 ≤ fuel) :
    ∃ final, state.run (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true fuel =
      (state.remaining releaseDecision, .done ⟨(), .complete, final⟩) ∧ final.Valid ∧
      final.task.pending = false ∧ final.copy = none ∧ (releaseDecision = true → final.owner = none) := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      have positive : 0 < fuel := by omega
      have notAtomic := state.true_not_atomic tail observe copyTail decisionTail releaseDecision
      have nextValid := state.step_valid tail observe copyTail decisionTail releaseDecision true valid
      have balance := state.remaining_balance tail observe copyTail decisionTail releaseDecision valid
      cases reply : (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true).status with
      | atomic => exact False.elim (notAtomic reply)
      | pending =>
          have smaller : (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true).next.rank
              releaseDecision < state.rank releaseDecision := by
            cases owner : state.owner with
            | none => simp [Host.step, owner] at reply
            | some outer => exact state.rank_decreases tail observe copyTail decisionTail releaseDecision valid outer owner reply
          have room : (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true).next.rank
              releaseDecision + 2 ≤ fuel := by omega
          obtain ⟨final, finished, finalValid⟩ := ih _ nextValid room
          refine ⟨final, ?_, finalValid⟩
          simp only [Host.run, Host.packet, Host.advance_actual, followingControl, reply, ↓reduceIte]
          change ((state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true).used +
            ((state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true).next.run
              (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true fuel).1,
            ((state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true).next.run
              (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true fuel).2) = _
          rw [finished]
          exact Prod.ext (by omega) rfl
      | complete =>
          have empty := state.complete_remaining_zero tail observe copyTail decisionTail releaseDecision true valid reply
          refine ⟨(state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true).next, ?_, nextValid,
            state.completed_empty tail observe copyTail decisionTail releaseDecision true valid reply⟩
          cases fuel with
          | zero => omega
          | succ rest =>
              simp only [Host.run, Host.packet, Host.advance_actual, followingControl, reply, reduceCtorEq,
                ↓reduceIte, Host.advance_terminal, Nat.add_zero]
              exact Prod.ext (by omega) rfl


/-- The task wrapper projects to the same source execution and its concrete
normalizer ticket partition, regardless of the separately observed queue event. -/
theorem Task.inventory_partition (tail : AtomicTail Token Context Service) (permission : Bool)
    (state : Task Token (Normalizer Token Context Service) Loan Context Capture) :
    (state.step (Normalizer.callback tail) permission).next.execution.normalizerInventory.Perm
      state.execution.normalizerInventory := by
  rw [(state.actual_execution_step (Normalizer.callback tail) permission).2.2]
  exact state.execution.normalizer_partition tail permission

theorem Host.source_inventory_partition (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService) :
    (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission).next.task.execution.normalizerInventory.Perm
      state.task.execution.normalizerInventory := by
  cases owner : state.owner with
  | none => simp [Host.step, owner]
  | some outer =>
      by_cases first : (!state.cancelled && state.copy.isSome) = true
      · simpa [Host.step, owner, first] using state.task.inventory_partition tail false
      · simp only [Host.step, owner, first, Bool.false_eq_true, ↓reduceIte]
        cases copy : state.copy with
        | some dependent => cases permission <;> exact List.Perm.refl _
        | none =>
            cases pending : state.task.pending with
            | true => exact state.task.inventory_partition tail permission
            | false => cases releaseDecision <;> cases permission <;> exact List.Perm.refl _

theorem Host.source_prefix_inventory (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService)
    (fuel : Nat) :
    (Host.outcomeState (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission
      (state.run (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission fuel).2).task.execution.normalizerInventory.Perm
        state.task.execution.normalizerInventory :=
  prefix_invariant (Host.provider (Normalizer.callback tail) observe copyTail decisionTail releaseDecision)
    (Host.charge (Normalizer.callback tail) observe copyTail decisionTail releaseDecision) permission
    (fun next : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService =>
      next.task.execution.normalizerInventory.Perm state.task.execution.normalizerInventory)
    (fun next previous => (next.source_inventory_partition tail observe copyTail decisionTail releaseDecision permission).trans previous)
    fuel none state (List.Perm.refl _)

/-- Full disposal is a consequence of actual finite execution and the
preserved child/copy/decision phase invariant. The opaque services and borrowed
lifetimes have not been converted into physical bounds by this theorem. -/
theorem Host.valid_finite_disposal (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService)
    (valid : state.Valid) (fuel : Nat) (enough : state.rank releaseDecision + 2 ≤ fuel) :
    ∃ final, state.run (Normalizer.callback tail) observe copyTail decisionTail releaseDecision true fuel =
      (state.remaining releaseDecision, .done ⟨(), .complete, final⟩) ∧ final.Valid ∧
      final.task.identity ∉ final.task.queue.tasks ∧ final.task.execution.owner = none ∧
      final.task.execution.work.owner = none ∧ final.task.execution.work.drain.remaining = [] ∧
      final.copy = none ∧ (releaseDecision = true → final.owner = none) ∧
      final.task.execution.pendingResources = [] ∧
      (final.task.execution.releasedRev ++ final.task.execution.work.releasedRev ++
        final.task.execution.work.drain.releasedRev.reverse).Perm state.task.execution.normalizerInventory := by
  obtain ⟨final, finished, kept, stopped, copy, decision⟩ :=
    state.finite_completion tail observe copyTail decisionTail releaseDecision valid fuel enough
  obtain ⟨queued, outer⟩ := (Task.not_pending _).mp stopped
  obtain ⟨child, _ready, drained⟩ := final.task.execution.valid_released_child_and_drain kept.1.2 outer
  have inventory := state.source_prefix_inventory tail observe copyTail decisionTail releaseDecision true fuel
  rw [finished] at inventory
  change final.task.execution.normalizerInventory.Perm state.task.execution.normalizerInventory at inventory
  have readback := final.task.execution.cleared_inventory_readback outer child drained
  rw [readback.2] at inventory
  exact ⟨final, finished, kept, queued, outer, child, drained, copy, decision, readback.1, inventory⟩


open _root_.CategoryTheory Mettapedia.Effects

/-- Pricing is a projection of the ordered event account. In particular,
queue removal, service settlements and cleanup requests remain separate. -/
def Event.priceHom (price : Event Token → Nat) : FreeMonoid (Event Token) →* Multiplicative Nat :=
  FreeMonoid.lift fun event => Multiplicative.ofAdd (price event)

theorem Event.price_word (price : Event Token → Nat) (word : List (Event Token)) :
    Multiplicative.toAdd (Event.priceHom price (FreeMonoid.ofList word)) = weighted price word := by
  induction word with
  | nil => simp [Event.priceHom, weighted]
  | cons event rest ih =>
      simp only [FreeMonoid.ofList_cons, map_mul]
      simpa [Event.priceHom, weighted] using congrArg (price event + ·) ih

/-- This graph contains exactly the existing task actions, not another
cancellation interpreter. An edge supplies only its actual residual equation. -/
abbrev Task.stepGraph (callback : Callback Work) : Quiver (Task Token Work Loan Context Capture) where
  Hom before after := Σ permission : Bool, PLift ((before.step callback permission).next = after)

def Task.actionAccount (callback : Callback Work) :
    letI := Task.stepGraph (Token := Token) (Loan := Loan) (Context := Context) (Capture := Capture) callback
    RunAccount (Paths (Task Token Work Loan Context Capture)) (FreeMonoid (Event Token)) := by
  letI := Task.stepGraph (Token := Token) (Loan := Loan) (Context := Context) (Capture := Capture) callback
  exact Mettapedia.GSLT.Contracts.Accounts.pathAccount
    (fun {before} {_after} edge => FreeMonoid.ofList (before.events callback edge.1))

def Task.pricedAccount (callback : Callback Work) (price : Event Token → Nat) :
    letI := Task.stepGraph (Token := Token) (Loan := Loan) (Context := Context) (Capture := Capture) callback
    RunAccount (Paths (Task Token Work Loan Context Capture)) (Multiplicative Nat) :=
  letI := Task.stepGraph (Token := Token) (Loan := Loan) (Context := Context) (Capture := Capture) callback
  (Task.actionAccount callback).map (Event.priceHom price)

private theorem Task.advance_actual (callback : Callback Work) (permission : Bool)
    (fuel : Nat) (state : Task Token Work Loan Context Capture) :
    advance (Task.provider callback) (Execution.client permission) (Task.charge callback) (fuel + 1)
      (base := ()) ⟨(), none, state⟩ =
      let response := state.step callback permission
      let rest := advance (Task.provider callback) (Execution.client permission) (Task.charge callback)
        fuel (base := ()) ⟨(), followingControl response.status, response.next⟩
      (response.used + rest.1, rest.2) := by
  simp only [advance, client_poll]
  rfl

private theorem Task.advance_terminal (callback : Callback Work) (permission : Bool)
    (fuel : Nat) (status : Status) (state : Task Token Work Loan Context Capture) :
    advance (Task.provider callback) (Execution.client permission) (Task.charge callback) (fuel + 1)
      (base := ()) ⟨(), some status, state⟩ = (0, .done ⟨(), status, state⟩) := by
  simp only [advance, client_stopped]

/-- The existing cursor prefix constructs a typed path with its exact event
account projected to the actual service settlement, including atomic cuts. -/
theorem Task.actual_path_account (callback : Callback Work) (permission : Bool)
    (fuel : Nat) (control : Option Status) (state : Task Token Work Loan Context Capture) :
    letI := Task.stepGraph (Token := Token) (Loan := Loan) (Context := Context) (Capture := Capture) callback
    ∃ path : Quiver.Path state (Task.outcomeState callback permission
      (advance (Task.provider callback) (Execution.client permission) (Task.charge callback)
        fuel (base := ()) ⟨(), control, state⟩).2),
      (Task.pricedAccount callback Event.units).of path = Multiplicative.ofAdd
        (advance (Task.provider callback) (Execution.client permission) (Task.charge callback)
          fuel (base := ()) ⟨(), control, state⟩).1 := by
  let _ := Task.stepGraph (Token := Token) (Loan := Loan) (Context := Context) (Capture := Capture) callback
  induction fuel generalizing control state with
  | zero => exact ⟨.nil, rfl⟩
  | succ fuel ih =>
      cases control with
      | some status => rw [Task.advance_terminal]; exact ⟨.nil, rfl⟩
      | none =>
          rw [Task.advance_actual]
          obtain ⟨path, accounted⟩ := ih (followingControl (state.step callback permission).status)
            (state.step callback permission).next
          let edge : state ⟶ (state.step callback permission).next := ⟨permission, ⟨rfl⟩⟩
          have head : (Task.pricedAccount callback Event.units).of edge.toPath =
              Multiplicative.ofAdd (state.step callback permission).used := by
            change Event.priceHom Event.units ((Mettapedia.GSLT.Contracts.Accounts.pathAccount
              (fun {before : Task Token Work Loan Context Capture} {_after} (edge : before ⟶ _after) =>
                FreeMonoid.ofList (before.events callback edge.1))).of
                  ((Quiver.Path.nil : Quiver.Path state state).cons edge)) = _
            rw [Mettapedia.GSLT.Contracts.Accounts.pathAccount_cons,
              Mettapedia.GSLT.Contracts.Accounts.pathAccount_nil]
            simp only [one_mul]
            exact congrArg Multiplicative.ofAdd
              ((Event.price_word Event.units (state.events callback permission)).trans
                (state.service_projection callback permission))
          refine ⟨edge.toPath.comp path, ?_⟩
          change (Task.pricedAccount callback Event.units).of (edge.toPath ≫ path) = _
          exact ((Task.pricedAccount callback Event.units).of_comp edge.toPath path).trans
            ((congrArg₂ (fun x y : Multiplicative Nat => x * y) head accounted).trans rfl)

abbrev Host.stepGraph (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision : Bool) :
    Quiver (Host Token Work Loan Context Capture Residual Snapshot Output HostService) where
  Hom before after := Σ permission : Bool,
    PLift ((before.step callback observe copyTail decisionTail releaseDecision permission).next = after)

def Host.actionAccount (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision : Bool) :
    letI := Host.stepGraph (Output := Output) callback observe copyTail decisionTail releaseDecision
    RunAccount (Paths (Host Token Work Loan Context Capture Residual Snapshot Output HostService)) (FreeMonoid (Event Token)) := by
  letI := Host.stepGraph (Output := Output) callback observe copyTail decisionTail releaseDecision
  exact Mettapedia.GSLT.Contracts.Accounts.pathAccount
    (fun {before} {_after} edge => FreeMonoid.ofList (before.events callback releaseDecision edge.1))

def Host.pricedAccount (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision : Bool) (price : Event Token → Nat) :
    letI := Host.stepGraph (Output := Output) callback observe copyTail decisionTail releaseDecision
    RunAccount (Paths (Host Token Work Loan Context Capture Residual Snapshot Output HostService)) (Multiplicative Nat) :=
  letI := Host.stepGraph (Output := Output) callback observe copyTail decisionTail releaseDecision
  (Host.actionAccount callback observe copyTail decisionTail releaseDecision).map (Event.priceHom price)

theorem Host.actual_path_account (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (fuel : Nat) (control : Option Status)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :
    letI := Host.stepGraph (Output := Output) callback observe copyTail decisionTail releaseDecision
    ∃ path : Quiver.Path state (Host.outcomeState callback observe copyTail decisionTail releaseDecision permission
      (advance (Host.provider callback observe copyTail decisionTail releaseDecision) (Execution.client permission)
        (Host.charge callback observe copyTail decisionTail releaseDecision) fuel (base := ()) ⟨(), control, state⟩).2),
      (Host.pricedAccount callback observe copyTail decisionTail releaseDecision Event.units).of path = Multiplicative.ofAdd
        (advance (Host.provider callback observe copyTail decisionTail releaseDecision) (Execution.client permission)
          (Host.charge callback observe copyTail decisionTail releaseDecision) fuel (base := ()) ⟨(), control, state⟩).1 := by
  let _ := Host.stepGraph (Output := Output) callback observe copyTail decisionTail releaseDecision
  induction fuel generalizing control state with
  | zero => exact ⟨.nil, rfl⟩
  | succ fuel ih =>
      cases control with
      | some status => rw [Host.advance_terminal]; exact ⟨.nil, rfl⟩
      | none =>
          rw [Host.advance_actual]
          obtain ⟨path, accounted⟩ := ih
            (followingControl (state.step callback observe copyTail decisionTail releaseDecision permission).status)
            (state.step callback observe copyTail decisionTail releaseDecision permission).next
          let edge : state ⟶ (state.step callback observe copyTail decisionTail releaseDecision permission).next :=
            ⟨permission, ⟨rfl⟩⟩
          have head : (Host.pricedAccount callback observe copyTail decisionTail releaseDecision Event.units).of edge.toPath =
              Multiplicative.ofAdd (state.step callback observe copyTail decisionTail releaseDecision permission).used := by
            change Event.priceHom Event.units ((Mettapedia.GSLT.Contracts.Accounts.pathAccount
              (fun {before : Host Token Work Loan Context Capture Residual Snapshot Output HostService} {_after}
                (edge : before ⟶ _after) => FreeMonoid.ofList (before.events callback releaseDecision edge.1))).of
                  ((Quiver.Path.nil : Quiver.Path state state).cons edge)) = _
            rw [Mettapedia.GSLT.Contracts.Accounts.pathAccount_cons,
              Mettapedia.GSLT.Contracts.Accounts.pathAccount_nil]
            simp only [one_mul]
            exact congrArg Multiplicative.ofAdd
              ((Event.price_word Event.units (state.events callback releaseDecision permission)).trans
                (state.service_projection callback observe copyTail decisionTail releaseDecision permission))
          refine ⟨edge.toPath.comp path, ?_⟩
          change (Host.pricedAccount callback observe copyTail decisionTail releaseDecision Event.units).of
            (edge.toPath ≫ path) = _
          exact ((Host.pricedAccount callback observe copyTail decisionTail releaseDecision Event.units).of_comp edge.toPath path).trans
            ((congrArg₂ (fun x y : Multiplicative Nat => x * y) head accounted).trans rfl)


/-- The host either retains the exact source residual or takes one actual
task cleanup action. It never resumes an ordinary producer/consumer here. -/
theorem Host.source_residual (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :
    let final := (state.step callback observe copyTail decisionTail releaseDecision permission).next
    final.task = state.task ∨ final.task = (state.task.step callback false).next ∨
      final.task = (state.task.step callback permission).next := by
  cases owner : state.owner with
  | none => simp [Host.step, owner]
  | some outer =>
      by_cases first : (!state.cancelled && state.copy.isSome) = true
      · simp [Host.step, owner, first]
      · simp only [Host.step, owner, first, Bool.false_eq_true, ↓reduceIte]
        cases copy : state.copy with
        | some dependent => cases permission <;> exact Or.inl rfl
        | none =>
            cases pending : state.task.pending with
            | true => exact Or.inr (Or.inr rfl)
            | false => cases releaseDecision <;> cases permission <;> exact Or.inl rfl

theorem Host.step_capture_and_data (callback : Callback Work)
    (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :
    let final := (state.step callback observe copyTail decisionTail releaseDecision permission).next
    final.task.capture = state.task.capture ∧ final.task.execution.accepted = state.task.execution.accepted ∧
      final.task.execution.context = state.task.execution.context ∧ final.outcome = state.outcome := by
  have retained := state.source_residual callback observe copyTail decisionTail releaseDecision permission
  have taskFields : ∀ permission, (state.task.step callback permission).next.capture = state.task.capture ∧
      (state.task.step callback permission).next.execution.accepted = state.task.execution.accepted ∧
      (state.task.step callback permission).next.execution.context = state.task.execution.context := by
    intro permission
    have actual := state.task.actual_execution_step callback permission
    have kept := state.task.execution.step_context callback permission
    exact ⟨(state.task.step_capture callback permission).1,
      (congrArg Execution.accepted actual.2.2).trans kept.2,
      (congrArg Execution.context actual.2.2).trans kept.1⟩
  have data : (state.step callback observe copyTail decisionTail releaseDecision permission).next.outcome = state.outcome := by
    cases owner : state.owner with
    | none => simp [Host.step, owner]
    | some outer =>
        by_cases first : (!state.cancelled && state.copy.isSome) = true
        · simp [Host.step, owner, first, Host.mark]
        · simp only [Host.step, owner, first, Bool.false_eq_true, ↓reduceIte]
          cases copy : state.copy with
          | some dependent => cases permission <;> rfl
          | none => cases pending : state.task.pending <;> cases releaseDecision <;> cases permission <;> rfl
  rcases retained with same | same | same
  · exact ⟨congrArg Task.capture same, congrArg (fun task => task.execution.accepted) same,
      congrArg (fun task => task.execution.context) same, data⟩
  · exact ⟨(congrArg Task.capture same).trans (taskFields false).1,
      (congrArg (fun task => task.execution.accepted) same).trans (taskFields false).2.1,
      (congrArg (fun task => task.execution.context) same).trans (taskFields false).2.2, data⟩
  · exact ⟨(congrArg Task.capture same).trans (taskFields permission).1,
      (congrArg (fun task => task.execution.accepted) same).trans (taskFields permission).2.1,
      (congrArg (fun task => task.execution.context) same).trans (taskFields permission).2.2, data⟩

theorem Host.prefix_capture_and_data (callback : Callback Work)
    (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) (fuel : Nat) :
    let final := Host.outcomeState callback observe copyTail decisionTail releaseDecision permission
      (state.run callback observe copyTail decisionTail releaseDecision permission fuel).2
    final.task.capture = state.task.capture ∧ final.task.execution.accepted = state.task.execution.accepted ∧
      final.task.execution.context = state.task.execution.context ∧ final.outcome = state.outcome := by
  refine prefix_invariant (Host.provider callback observe copyTail decisionTail releaseDecision)
    (Host.charge callback observe copyTail decisionTail releaseDecision) permission
    (fun next => next.task.capture = state.task.capture ∧ next.task.execution.accepted = state.task.execution.accepted ∧
      next.task.execution.context = state.task.execution.context ∧ next.outcome = state.outcome) ?_ fuel none state ?_
  · intro next previous
    have kept := next.step_capture_and_data callback observe copyTail decisionTail releaseDecision permission
    exact ⟨kept.1.trans previous.1, kept.2.1.trans previous.2.1,
      kept.2.2.1.trans previous.2.2.1, kept.2.2.2.trans previous.2.2.2⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- New atomic permission starts a new cancellation invocation on the exact
retained residual and paid account. It does not resume a done ATOMIC client. -/
def Host.regrant (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision oldPermission newPermission : Bool) (fuel : Nat)
    (previous : Nat × Outcome (Host.provider (Output := Output) callback observe copyTail decisionTail releaseDecision)
      (Execution.client oldPermission) ()) :=
  let next := (Host.outcomeState callback observe copyTail decisionTail releaseDecision oldPermission previous.2).run
    callback observe copyTail decisionTail releaseDecision newPermission fuel
  (previous.1 + next.1, next.2)

theorem Host.regrant_zero (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision oldPermission newPermission : Bool)
    (previous : Nat × Outcome (Host.provider (Output := Output) callback observe copyTail decisionTail releaseDecision)
      (Execution.client oldPermission) ()) :
    Host.regrant callback observe copyTail decisionTail releaseDecision oldPermission newPermission 0 previous =
      (previous.1, .paused ((Host.outcomeState callback observe copyTail decisionTail releaseDecision oldPermission previous.2).packet
        callback observe copyTail decisionTail releaseDecision newPermission)) := by
  simp [Host.regrant, Host.run, advance]

theorem Host.atomic_done_resume_inert (callback : Callback Work)
    (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool) (paid fuel : Nat)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :
    resume (Host.provider callback observe copyTail decisionTail releaseDecision) (Execution.client permission)
      (Host.charge callback observe copyTail decisionTail releaseDecision) fuel (base := ())
      (paid, .done ⟨(), .atomic, state⟩) = (paid, .done ⟨(), .atomic, state⟩) := rfl


/-- A pending copy may use its borrowed source when its own destructor runs.
Atomic permission admits placement only; it supplies no new resource authority. -/
theorem Host.copy_atomic_refusal (callback : Callback Work)
    (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService)
    (owner : Token) (copy : DependentCopy Token Residual) (held : state.owner = some owner)
    (pending : state.copy = some copy) (cancelled : state.cancelled = true) :
    state.step callback observe copyTail decisionTail releaseDecision false = ⟨.atomic, 0, state.mark observe⟩ := by
  simp [Host.step, held, pending, cancelled]

theorem Host.copy_atomic_granted (callback : Callback Work)
    (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService)
    (owner : Token) (copy : DependentCopy Token Residual) (held : state.owner = some owner)
    (pending : state.copy = some copy) (cancelled : state.cancelled = true) :
    let result := state.step callback observe copyTail decisionTail releaseDecision true
    result.status = .pending ∧ result.used = 1 ∧ result.next.copy = none ∧ result.next.task = state.task ∧
      result.next.service = copyTail copy state.task.capture state.service ∧
      result.next.releasedCopiesRev = copy.ticket :: state.releasedCopiesRev := by
  simp [Host.step, held, pending, cancelled, Host.mark]

theorem Host.copy_after_source_release_invalid
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService)
    (copy : DependentCopy Token Residual) (pending : state.copy = some copy)
    (released : state.task.execution.owner = none) : ¬state.Valid := by
  intro valid
  have held := state.valid_copy_holds_source valid copy pending
  rw [released] at held
  cases held

namespace Controls

abbrev old := Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.Controls.mixedExecution
abbrev tail := Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.Controls.tail

def task : Task Nat (Normalizer Nat Nat Nat) Nat Nat (Nat × Nat) :=
  ⟨3, ⟨4, [3, 8]⟩, old, (50, 7)⟩

def copy : DependentCopy Nat (List Nat) := ⟨300, 100, [41, 42]⟩

def host : Host Nat (Normalizer Nat Nat Nat) Nat Nat (Nat × Nat) (List Nat) Nat (List Nat) Nat :=
  ⟨some 400, task, some copy, none, false, [11, 12], 0, [], []⟩

def observe (source : Execution Nat (Normalizer Nat Nat Nat) Nat Nat) : Nat := source.accepted

def copyTail : AtomicTail (DependentCopy Nat (List Nat)) (Nat × Nat) Nat :=
  fun copy capture service => service + copy.ticket + capture.2

def decisionTail : AtomicTail Nat (Nat × Nat) Nat := fun owner capture service => service + owner + capture.1

def stop := (host.step (Normalizer.callback tail) observe copyTail decisionTail true true).next

def cleared := (stop.step (Normalizer.callback tail) observe copyTail decisionTail true true).next

def denied := host.run (Normalizer.callback tail) observe copyTail decisionTail true false 3

def emptyTask : Task Nat (Normalizer Nat Nat Nat) Nat Nat (Nat × Nat) :=
  { task with execution := { old with owner := none } }

def emptyPlan : Host Nat (Normalizer Nat Nat Nat) Nat Nat (Nat × Nat) (List Nat) Nat (List Nat) Nat :=
  { host with task := { emptyTask with queue := ⟨4, [8]⟩ }, copy := none, cancelled := true }

theorem initial_valid : host.Valid := by
  refine ⟨⟨by change [3, 8].Nodup ∧ 2 ≤ 4; decide, ?_⟩, ?_, ?_, ?_⟩
  · exact Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.Controls.mixed_initial_phase_valid
  · intro pending same
    have equal : copy = pending := Option.some.inj same
    cases equal
    rfl
  · intro _ _
    rfl
  · simp [host]

theorem zero_preserves_membership_and_loan :
    (task.pollOne (Normalizer.callback tail) true 0).next.queue.tasks = [3, 8] ∧
      (task.pollOne (Normalizer.callback tail) true 0).next.execution.loan = some 77 ∧
      (task.pollOne (Normalizer.callback tail) true 0).used = 0 := by decide

theorem empty_task_removes_without_provider_request :
    (emptyTask.step (Normalizer.callback tail) false).next.queue.tasks = [8] ∧
      (emptyTask.step (Normalizer.callback tail) false).used = 0 ∧
      emptyTask.events (Normalizer.callback tail) false = [.membership 3] := by decide

theorem first_stop_exact_event_order :
    host.events (Normalizer.callback tail) true true = [.membership 3, .cleanupWork 1, .cleanupPoll] ∧
      stop.task.queue.tasks = [8] ∧ stop.task.execution.loan = none ∧
      stop.task.execution.owner = some 100 ∧ stop.copy.map DependentCopy.ticket = some 300 ∧
      stop.cancelled = true ∧ stop.snapshot = some 0 ∧ stop.service = 0 := by decide

theorem copy_denied_keeps_both_owners :
    (stop.step (Normalizer.callback tail) observe copyTail decisionTail true false).status = .atomic ∧
      (stop.step (Normalizer.callback tail) observe copyTail decisionTail true false).used = 0 ∧
      (stop.step (Normalizer.callback tail) observe copyTail decisionTail true false).next.task.execution.owner = some 100 ∧
      (stop.step (Normalizer.callback tail) observe copyTail decisionTail true false).next.copy.map DependentCopy.ticket = some 300 := by decide

theorem copy_before_source_and_credit_separate :
    cleared.copy = none ∧ cleared.task.execution.owner = some 100 ∧ cleared.task.execution.work.owner = some 200 ∧
      cleared.task.capture = (50, 7) ∧ cleared.snapshot = some 0 ∧ cleared.service = 307 ∧
      cleared.releasedCopiesRev = [300] ∧ cleared.task.execution.accepted = 0 := by decide

theorem zero_plan_done_but_decision_held :
    (emptyPlan.pollOne (Normalizer.callback tail) observe copyTail decisionTail false false 0).status = .complete ∧
      (emptyPlan.pollOne (Normalizer.callback tail) observe copyTail decisionTail true true 0).status = .pending ∧
      (emptyPlan.pollOne (Normalizer.callback tail) observe copyTail decisionTail false false 0).next.owner = some 400 ∧
      (emptyPlan.pollOne (Normalizer.callback tail) observe copyTail decisionTail true true 0).used = 0 := by decide

theorem decision_needs_separate_atomic_action :
    (emptyPlan.step (Normalizer.callback tail) observe copyTail decisionTail true false).status = .atomic ∧
      (emptyPlan.step (Normalizer.callback tail) observe copyTail decisionTail true false).next.owner = some 400 ∧
      (emptyPlan.step (Normalizer.callback tail) observe copyTail decisionTail true true).used = 1 ∧
      (emptyPlan.step (Normalizer.callback tail) observe copyTail decisionTail true true).next.owner = none ∧
      (emptyPlan.step (Normalizer.callback tail) observe copyTail decisionTail true true).next.service = 450 := by decide

theorem cancelled_data_inspection_differs_from_active_use :
    stop.inspectCompletedData = some (true, [11, 12]) ∧
      stop.tryActiveAction (fun output capture => output.length + capture.1) = none := by decide

def completedSource := Execution.outcomeState (Normalizer.callback tail) true
  (old.run (Normalizer.callback tail) true 20).2

def sourceFirst := { host with task := { task with execution := completedSource } }

theorem source_before_copy_breaks_dependency :
    completedSource.owner = none ∧ sourceFirst.copy.map DependentCopy.ticket = some 300 ∧ ¬sourceFirst.Valid := by
  refine ⟨by decide, by decide, ?_⟩
  exact sourceFirst.copy_after_source_release_invalid copy rfl (by decide)

def wrongOrigin := { host with copy := some { copy with sourceOwner := 999 } }

theorem wrong_source_identity_refused : ¬wrongOrigin.Valid := by
  intro valid
  have held := wrongOrigin.valid_copy_holds_source valid { copy with sourceOwner := 999 } rfl
  cases held

theorem atomic_cut_omits_zero_settlement :
    stop.events (Normalizer.callback tail) true false = [] ∧
      (Task.mk 3 ⟨4, [3]⟩
        { old with retiring := true, work := { old.work with retiring := true, drain := { old.work.drain with frames := [], header := none } } }
        (50, 7)).events (Normalizer.callback tail) false = [.membership 3, .cleanupPoll] := by decide

theorem resume_atomic_does_not_regrant :
    (resume (Host.provider (Normalizer.callback tail) observe copyTail decisionTail true) (Execution.client false)
      (Host.charge (Normalizer.callback tail) observe copyTail decisionTail true) 100 denied).1 = 1 ∧
      (Host.outcomeState (Normalizer.callback tail) observe copyTail decisionTail true false
        (resume (Host.provider (Normalizer.callback tail) observe copyTail decisionTail true) (Execution.client false)
          (Host.charge (Normalizer.callback tail) observe copyTail decisionTail true) 100 denied).2).copy.map DependentCopy.ticket = some 300 := by decide

theorem regrant_retains_prefix_and_avoids_restart :
    let result := Host.regrant (Normalizer.callback tail) observe copyTail decisionTail true false true 2 denied
    result.1 = 3 ∧
      (Host.outcomeState (Normalizer.callback tail) observe copyTail decisionTail true true result.2).copy = none ∧
      (Host.outcomeState (Normalizer.callback tail) observe copyTail decisionTail true true result.2).task.execution.owner = some 100 ∧
      (Host.outcomeState (Normalizer.callback tail) observe copyTail decisionTail true true result.2).task.execution.work.retiring = true ∧
      (Host.outcomeState (Normalizer.callback tail) observe copyTail decisionTail true true result.2).snapshot = some 0 := by decide


def wideHost (width : Nat) :=
  { host with task := { task with execution :=
    Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.Controls.wideExecution width } }

theorem wide_valid (width : Nat) : (wideHost width).Valid := by
  refine ⟨⟨by change [3, 8].Nodup ∧ 2 ≤ 4; decide, ?_⟩, ?_, ?_, ?_⟩
  · exact Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.Controls.wide_initial_phase_valid width
  · intro pending same
    have equal : copy = pending := Option.some.inj same
    cases equal
    rfl
  · intro _ _
    rfl
  · simp [wideHost, host]

/-- Arbitrary initialized width, not merely a finite census, has the exact
composed model service invoice. Queue operations and request observations are
separate, and no source-credit payment for cleanup is asserted. -/
theorem arbitrary_width_host_complete_invoice (width : Nat) :
    ∃ final, (wideHost width).run (Normalizer.callback tail) observe copyTail decisionTail true true (width + 13) =
      (width + 8, .done ⟨(), .complete, final⟩) ∧ final.Valid ∧
      final.task.identity ∉ final.task.queue.tasks ∧ final.task.execution.owner = none ∧
      final.task.execution.work.owner = none ∧ final.task.execution.work.drain.remaining = [] ∧
      final.copy = none ∧ final.owner = none ∧ final.task.execution.pendingResources = [] := by
  have remaining : (wideHost width).remaining true = width + 8 := by
    simp [wideHost, host, task, copy, Host.remaining,
      Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.Controls.wideExecution,
      Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.Controls.wideFrame,
      Execution.normalizerRemaining, Normalizer.rank, Drain.potential]
    omega
  have rank : (wideHost width).rank true + 2 ≤ width + 13 := by
    simp [wideHost, host, task, copy, Host.rank, Task.rank,
      Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.Controls.wideExecution,
      Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.Controls.wideFrame,
      Execution.normalizerRank, Normalizer.rank, Drain.potential]
    omega
  obtain ⟨final, done, valid, queued, source, child, drained, copied, decision, empty, _partition⟩ :=
    (wideHost width).valid_finite_disposal tail observe copyTail decisionTail true (wide_valid width) (width + 13) rank
  exact ⟨final, by simpa only [remaining] using done, valid, queued, source, child, drained, copied, decision rfl, empty⟩

theorem declared_unit_does_not_bound_copy_service :
    let result := stop.step (Normalizer.callback tail) observe
      (fun _ _ service => service + 1000) decisionTail true true
    result.used = 1 ∧ result.next.service = 1000 ∧ result.next.task.execution.owner = some 100 := by decide

end Controls


/-- Only owned decision and dependent-copy tickets occur here; borrowed
source identities and output values are not additional owned allocations. -/
def Host.wrapperInventory (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) : List Token :=
  state.owner.toList ++ state.releasedDecisionsRev ++ (state.copy.toList.map DependentCopy.ticket) ++ state.releasedCopiesRev

def Host.inventory
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService) : List Token :=
  state.wrapperInventory ++ state.task.execution.normalizerInventory

theorem Host.wrapper_partition (callback : Callback Work) (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService) :
    (state.step callback observe copyTail decisionTail releaseDecision permission).next.wrapperInventory = state.wrapperInventory := by
  cases owner : state.owner with
  | none => simp [Host.step, owner]
  | some outer =>
      by_cases first : (!state.cancelled && state.copy.isSome) = true
      · simp [Host.step, owner, first, Host.mark, Host.wrapperInventory]
      · simp only [Host.step, owner, first, Bool.false_eq_true, ↓reduceIte]
        cases copy : state.copy with
        | some dependent => cases permission <;> simp [Host.wrapperInventory, Host.mark, owner, copy]
        | none =>
            cases pending : state.task.pending <;> cases releaseDecision <;> cases permission <;>
              simp [Host.wrapperInventory, Host.mark, owner, copy]

theorem Host.inventory_partition (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService) :
    (state.step (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission).next.inventory.Perm state.inventory := by
  unfold Host.inventory
  rw [state.wrapper_partition (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission]
  exact (state.source_inventory_partition tail observe copyTail decisionTail releaseDecision permission).append_left _

theorem Host.prefix_inventory (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService) (fuel : Nat) :
    (Host.outcomeState (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission
      (state.run (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission fuel).2).inventory.Perm state.inventory :=
  prefix_invariant (Host.provider (Normalizer.callback tail) observe copyTail decisionTail releaseDecision)
    (Host.charge (Normalizer.callback tail) observe copyTail decisionTail releaseDecision) permission
    (fun next => next.inventory.Perm state.inventory)
    (fun next previous => (next.inventory_partition tail observe copyTail decisionTail releaseDecision permission).trans previous)
    fuel none state (List.Perm.refl _)

/-- Ticket uniqueness is a separate allocation/ownership premise. Actual
retirement preserves it, so a ticket cannot be released twice in this model. -/
theorem Host.prefix_unique (tail : AtomicTail Token Context Service)
    (observe : Execution Token (Normalizer Token Context Service) Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token (Normalizer Token Context Service) Loan Context Capture Residual Snapshot Output HostService)
    (unique : state.inventory.Nodup) (fuel : Nat) :
    (Host.outcomeState (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission
      (state.run (Normalizer.callback tail) observe copyTail decisionTail releaseDecision permission fuel).2).inventory.Nodup :=
  ((state.prefix_inventory tail observe copyTail decisionTail releaseDecision permission fuel).nodup_iff).mpr unique

namespace Controls

theorem initial_tickets_unique : host.inventory.Nodup := by decide

theorem copy_ticket_cannot_be_released_twice (fuel : Nat) :
    (Host.outcomeState (Normalizer.callback tail) observe copyTail decisionTail true true
      (host.run (Normalizer.callback tail) observe copyTail decisionTail true true fuel).2).inventory.Nodup :=
  host.prefix_unique tail observe copyTail decisionTail true true initial_tickets_unique fuel

end Controls


/-- Every held positive cancellation records the verdict before the next
phase can plan, deliver or publish. Completed-data inspection is separate. -/
theorem Host.positive_marks_cancelled (callback : Callback Work)
    (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService)
    (outer : Token) (held : state.owner = some outer) :
    (state.step callback observe copyTail decisionTail releaseDecision permission).next.cancelled = true := by
  simp only [Host.step, held]
  split
  · rfl
  · cases copy : state.copy with
    | some dependent => cases permission <;> rfl
    | none => cases pending : state.task.pending <;> cases releaseDecision <;> cases permission <;> rfl

theorem Host.cancelled_snapshot_step (callback : Callback Work)
    (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService)
    (cancelled : state.cancelled = true) :
    let final := (state.step callback observe copyTail decisionTail releaseDecision permission).next
    final.cancelled = true ∧ final.snapshot = state.snapshot := by
  cases owner : state.owner with
  | none => simp [Host.step, owner, cancelled]
  | some outer =>
      simp only [Host.step, owner, cancelled, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      cases copy : state.copy with
      | some dependent => cases permission <;> simp [Host.mark, cancelled]
      | none =>
          cases pending : state.task.pending <;> cases releaseDecision <;> cases permission <;>
            simp [Host.mark, cancelled]

theorem Host.cancelled_snapshot_prefix (callback : Callback Work)
    (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService)
    (cancelled : state.cancelled = true) (fuel : Nat) :
    let final := Host.outcomeState callback observe copyTail decisionTail releaseDecision permission
      (state.run callback observe copyTail decisionTail releaseDecision permission fuel).2
    final.cancelled = true ∧ final.snapshot = state.snapshot :=
  prefix_invariant (Host.provider callback observe copyTail decisionTail releaseDecision)
    (Host.charge callback observe copyTail decisionTail releaseDecision) permission
    (fun next => next.cancelled = true ∧ next.snapshot = state.snapshot)
    (fun next previous => by
      have kept := next.cancelled_snapshot_step callback observe copyTail decisionTail releaseDecision permission previous.1
      exact ⟨kept.1, kept.2.trans previous.2⟩)
    fuel none state ⟨cancelled, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem Host.positive_prefix_cancelled (callback : Callback Work)
    (observe : Execution Token Work Loan Context → Snapshot)
    (copyTail : AtomicTail (DependentCopy Token Residual) Capture HostService)
    (decisionTail : AtomicTail Token Capture HostService) (releaseDecision permission : Bool)
    (state : Host Token Work Loan Context Capture Residual Snapshot Output HostService)
    (outer : Token) (held : state.owner = some outer) (fuel : Nat) :
    (Host.outcomeState callback observe copyTail decisionTail releaseDecision permission
      (state.run callback observe copyTail decisionTail releaseDecision permission (fuel + 1)).2).cancelled = true := by
  unfold Host.run Host.packet
  dsimp only
  rw [Host.advance_actual]
  refine prefix_invariant (Host.provider callback observe copyTail decisionTail releaseDecision)
    (Host.charge callback observe copyTail decisionTail releaseDecision) permission
    (fun next => next.cancelled = true) ?_ fuel _ _ ?_
  · intro next previous
    exact (next.cancelled_snapshot_step callback observe copyTail decisionTail releaseDecision permission previous).1
  · exact state.positive_marks_cancelled callback observe copyTail decisionTail releaseDecision permission outer held

end Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.TaskHost

namespace Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.PagedStorage

open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ExecutableStorage.BoundedIndexed

variable {Value Key : Type}

/-- Only the initialized row extent participates in the key view. Backing
page/directory blocks belong to the lower storage chain, not these key slots. -/
def keySlots (primary : ExecutableStorage.BoundedIndexed.Array (Row Value Key)) (extent index : Nat) : Option Key :=
  if index < extent then (primary.read index).bind Row.key else none

/-- Key-slot projection into the existing frame owner. Fixed frame/header
resources are outside this projection and are not claimed disposed by it. -/
def keyFrame (identity extent length : Nat) (primary : ExecutableStorage.BoundedIndexed.Array (Row Value Key)) : Frame Key :=
  ⟨identity, extent, length, keySlots primary extent, none, none, none, none⟩

theorem initialized_key_frame_valid (identity extent : Nat) (primary : ExecutableStorage.BoundedIndexed.Array (Row Value Key)) :
    (keyFrame identity extent extent primary).Valid := by
  constructor
  · exact Nat.le_refl _
  · intro index beyond inside
    change extent ≤ index at beyond
    change index < extent at inside
    omega

/-- One real paged-row write, preserving ordinal/value and nulling only its
key, realizes the preexisting `Frame.pop`. Typed row-cell and index separation
are local memory admission, not a final disposal or permutation assumption. -/
theorem actual_key_pop (identity extent length : Nat) (primary next : ExecutableStorage.BoundedIndexed.Array (Row Value Key))
    (positive : 0 < length) (inside : length ≤ extent) (row : Row Value Key)
    (read : primary.read (length - 1) = some row) (address : Ptr)
    (location : primary.at (length - 1) = some address) (typed : DataCell primary.memory address)
    (written : primary.write (length - 1) { row with key := none } = some next)
    (separate : ∀ index < extent, index ≠ length - 1 →
      ∃ other, primary.at index = some other ∧ other ≠ address) :
    keyFrame identity extent (length - 1) next = (keyFrame identity extent length primary).pop ∧
      (primary.read (length - 1)).map (fun row => (row.ordinal, row.value)) =
        (next.read (length - 1)).map (fun row => (row.ordinal, row.value)) := by
  have lastInside : length - 1 < extent := by omega
  have lastRead := primary.write_read_same next (length - 1) { row with key := none } address location typed written
  constructor
  · unfold keyFrame Frame.pop
    congr 1
    funext index
    by_cases last : index = length - 1
    · subst index
      simp [keySlots, lastInside, lastRead]
    · by_cases bounded : index < extent
      · obtain ⟨other, before, different⟩ := separate index bounded last
        have kept := primary.write_read_other next (length - 1) { row with key := none }
          address location typed written index other before different
        simp [keySlots, bounded, Function.update_of_ne last, kept]
      · simp [keySlots, bounded, Function.update_of_ne last]
  · simp [read, lastRead]

theorem actual_key_pop_valid (identity extent length : Nat) (primary next : ExecutableStorage.BoundedIndexed.Array (Row Value Key))
    (valid : (keyFrame identity extent length primary).Valid) (positive : 0 < length)
    (row : Row Value Key) (read : primary.read (length - 1) = some row) (address : Ptr)
    (location : primary.at (length - 1) = some address) (typed : DataCell primary.memory address)
    (written : primary.write (length - 1) { row with key := none } = some next)
    (separate : ∀ index < extent, index ≠ length - 1 →
      ∃ other, primary.at index = some other ∧ other ≠ address) :
    (keyFrame identity extent (length - 1) next).Valid := by
  rw [(actual_key_pop identity extent length primary next positive valid.1 row read address location typed written separate).1]
  exact Frame.pop_valid _ valid positive

theorem actual_key_pop_inventory (identity extent length : Nat) (primary next : ExecutableStorage.BoundedIndexed.Array (Row Value Key))
    (positive : 0 < length) (inside : length ≤ extent) (row : Row Value Key)
    (read : primary.read (length - 1) = some row) (address : Ptr)
    (location : primary.at (length - 1) = some address) (typed : DataCell primary.memory address)
    (written : primary.write (length - 1) { row with key := none } = some next)
    (separate : ∀ index < extent, index ≠ length - 1 →
      ∃ other, primary.at index = some other ∧ other ≠ address) :
    (keyFrame identity extent length primary).inventory.Perm
      (row.key.toList ++ (keyFrame identity extent (length - 1) next).inventory) := by
  have partition := Frame.pop_inventory (keyFrame identity extent length primary) positive
  rw [← (actual_key_pop identity extent length primary next positive inside row read address location typed written separate).1] at partition
  simpa [keyFrame, keySlots, show length - 1 < extent by omega, read] using partition

/-- Phase consistency says every initialized slot outside the remaining
owned prefix is actually nulled. A forged zero count has no such grant. -/
theorem cleared_valid_view_has_no_keys (identity extent : Nat) (primary : ExecutableStorage.BoundedIndexed.Array (Row Value Key))
    (valid : (keyFrame identity extent 0 primary).Valid) :
    ∀ index < extent, (primary.read index).bind Row.key = none := by
  intro index inside
  have empty := valid.2 index (Nat.zero_le _) inside
  simpa [keyFrame, keySlots, inside] using empty

def releaseBackingIfCleared (length : Nat) (primary : ExecutableStorage.BoundedIndexed.Array (Row Value Key)) :
    Option (Mettapedia.Machines.CMemory.ExecutableStorage.BoundedIndexed.Released (Row Value Key)) :=
  if length = 0 then some primary.releaseOne else none

theorem pending_keys_keep_backing (length : Nat) (primary : ExecutableStorage.BoundedIndexed.Array (Row Value Key)) (positive : 0 < length) :
    releaseBackingIfCleared length primary = none := by
  have nonzero : length ≠ 0 := by omega
  rw [releaseBackingIfCleared, if_neg nonzero]

theorem admitted_backing_release_has_no_owned_primary_keys (identity extent length : Nat)
    (primary : ExecutableStorage.BoundedIndexed.Array (Row Value Key)) (valid : (keyFrame identity extent length primary).Valid)
    (reply : Mettapedia.Machines.CMemory.ExecutableStorage.BoundedIndexed.Released (Row Value Key))
    (admitted : releaseBackingIfCleared length primary = some reply) :
    ∀ index < extent, (primary.read index).bind Row.key = none := by
  by_cases zero : length = 0
  · subst length
    exact cleared_valid_view_has_no_keys identity extent primary valid
  · simp [releaseBackingIfCleared, zero] at admitted

/-- A completed actual pass may change the complete primary owner. The
partial scratch view contributes no owned key tickets before that handoff. -/
theorem completed_primary_key_permutation (choose : Pass Value Key → Mettapedia.Machines.CMemory.ExecutableStorage.AllocationChoice)
    (rows : List (Row Value Key)) (order : List Nat) (legal : order.Perm (List.range rows.length))
    (state : Pass Value Key) (valid : state.Valid rows order) (fuel paid : Nat)
    (admitted : Pass.AdmittedPrefix choose fuel none state) (final : Pass Value Key)
    (finished : state.run choose fuel = (paid, .done ⟨(), .ready, final⟩)) :
    (ownedKeys (observed final.scratch final.expected)).Perm (rows.filterMap Row.key) ∧
      final.swap = some ⟨final.scratch, final.primary⟩ :=
  (state.completed_cursor_permutation choose rows order legal valid fuel paid admitted final finished).2

theorem completed_primary_keys_unique (choose : Pass Value Key → Mettapedia.Machines.CMemory.ExecutableStorage.AllocationChoice)
    (rows : List (Row Value Key)) (order : List Nat) (legal : order.Perm (List.range rows.length))
    (state : Pass Value Key) (valid : state.Valid rows order) (fuel paid : Nat)
    (admitted : Pass.AdmittedPrefix choose fuel none state) (final : Pass Value Key)
    (finished : state.run choose fuel = (paid, .done ⟨(), .ready, final⟩)) (unique : (rows.filterMap Row.key).Nodup) :
    (ownedKeys (observed final.scratch final.expected)).Nodup :=
  ((completed_primary_key_permutation choose rows order legal state valid fuel paid admitted final finished).1.nodup_iff).mpr unique


/-- The existing frame inventory is exactly the lower storage observer's
primary key inventory over the initialized prefix, with order/multiplicity. -/
theorem frame_inventory_eq_keys (identity extent length : Nat)
    (primary : ExecutableStorage.BoundedIndexed.Array (Row Value Key)) (bounded : length ≤ extent) :
    (keyFrame identity extent length primary).inventory = ownedKeys (observed primary length) := by
  simp only [keyFrame, Frame.inventory, Frame.keys, Frame.fixed, Option.toList_none,
    List.flatMap_nil, List.append_nil, ownedKeys, observed, List.filterMap_map]
  apply List.filterMap_congr
  intro index member
  have inside : index < extent := by have before := List.mem_range.mp member; omega
  simp [keySlots, inside]

theorem completed_primary_frame_inventory (identity : Nat)
    (choose : Pass Value Key → Mettapedia.Machines.CMemory.ExecutableStorage.AllocationChoice)
    (rows : List (Row Value Key)) (order : List Nat) (legal : order.Perm (List.range rows.length))
    (state : Pass Value Key) (valid : state.Valid rows order) (fuel paid : Nat)
    (admitted : Pass.AdmittedPrefix choose fuel none state) (final : Pass Value Key)
    (finished : state.run choose fuel = (paid, .done ⟨(), .ready, final⟩)) :
    (keyFrame identity final.expected final.expected final.scratch).inventory.Perm (rows.filterMap Row.key) := by
  rw [frame_inventory_eq_keys identity final.expected final.expected final.scratch (Nat.le_refl _)]
  exact (completed_primary_key_permutation choose rows order legal state valid fuel paid admitted final finished).1

namespace Controls

set_option maxRecDepth 16384

abbrev complete := Mettapedia.Machines.CMemory.ExecutableStorage.BoundedIndexed.Controls.copied.scratch
abbrev first := Mettapedia.Machines.CMemory.ExecutableStorage.BoundedIndexed.Controls.first
abbrev second := Mettapedia.Machines.CMemory.ExecutableStorage.BoundedIndexed.Controls.second

def afterOne := (complete.write 1 { first with key := none }).getD complete

def afterBoth := (afterOne.write 0 { second with key := none }).getD afterOne

theorem first_null_write : complete.write 1 { first with key := none } = some afterOne := by decide

theorem second_null_write : afterOne.write 0 { second with key := none } = some afterBoth := by decide

theorem actual_first_paged_pop :
    keyFrame 9 2 1 afterOne = (keyFrame 9 2 2 complete).pop ∧
      (complete.read 1).map (fun row => (row.ordinal, row.value)) =
        (afterOne.read 1).map (fun row => (row.ordinal, row.value)) := by
  apply actual_key_pop 9 2 2 complete afterOne (by decide) (by decide) first (by decide) ⟨24, 1⟩ (by decide)
    (DataCell.of_value _ _ first (by decide)) first_null_write
  intro index inside different
  have zero : index = 0 := by omega
  subst index
  exact ⟨⟨24, 0⟩, by decide, by decide⟩

theorem first_paged_pop_valid : (keyFrame 9 2 1 afterOne).Valid := by
  rw [actual_first_paged_pop.1]
  exact Frame.pop_valid _ (initialized_key_frame_valid 9 2 complete) (by decide)

theorem actual_second_paged_pop :
    keyFrame 9 2 0 afterBoth = (keyFrame 9 2 1 afterOne).pop ∧
      (afterOne.read 0).map (fun row => (row.ordinal, row.value)) =
        (afterBoth.read 0).map (fun row => (row.ordinal, row.value)) := by
  apply actual_key_pop 9 2 1 afterOne afterBoth (by decide) (by decide) second (by decide) ⟨24, 0⟩ (by decide)
    (DataCell.of_value _ _ second (by decide)) second_null_write
  intro index inside different
  have one : index = 1 := by omega
  subst index
  exact ⟨⟨24, 1⟩, by decide, by decide⟩

theorem all_paged_keys_nulled_by_actual_writes :
    (keyFrame 9 2 0 afterBoth).Valid ∧ (afterBoth.read 0).bind Row.key = none ∧
      (afterBoth.read 1).bind Row.key = none := by
  have valid : (keyFrame 9 2 0 afterBoth).Valid := by
    rw [actual_second_paged_pop.1]
    exact Frame.pop_valid _ first_paged_pop_valid (by decide)
  exact ⟨valid, cleared_valid_view_has_no_keys 9 2 afterBoth valid 0 (by decide),
    cleared_valid_view_has_no_keys 9 2 afterBoth valid 1 (by decide)⟩

theorem key_pop_removes_only_complete_primary_ticket :
    (keyFrame 9 2 2 complete).inventory = [1001, 1000] ∧
      (keyFrame 9 2 1 afterOne).inventory = [1001] ∧
      (keyFrame 9 2 0 afterBoth).inventory = [] ∧
      (keyFrame 9 2 2 complete).inventory.Nodup := by decide

theorem forged_zero_prefix_abandons_real_keys : ¬(keyFrame 9 2 0 complete).Valid := by
  intro valid
  have empty := cleared_valid_view_has_no_keys 9 2 complete valid 0 (by decide)
  have held : (complete.read 0).bind Row.key = some 1001 := by decide
  rw [held] at empty
  cases empty

theorem key_phase_keeps_backing : releaseBackingIfCleared 1 afterOne = none := pending_keys_keep_backing 1 afterOne (by decide)

theorem admitted_block_retirement_revokes_row_access :
    (afterBoth.releaseOne).freed = some 24 ∧ afterBoth.releaseOne.next.at 0 = none ∧
      afterBoth.releaseOne.next.chain.length = 4 := by decide

theorem actual_null_writes_keep_live_backing : afterBoth.Valid := by
  have initial := Mettapedia.Machines.CMemory.ExecutableStorage.BoundedIndexed.Controls.complete_primary_storage_valid
  have next := complete.write_valid afterOne 1 { first with key := none } initial first_null_write
  exact afterOne.write_valid afterBoth 0 { second with key := none } next second_null_write

theorem empty_key_view_then_finite_block_disposal :
    ∃ final, afterBoth.releaseRun 7 = (5, .done ⟨(), .ready, final⟩) ∧
      final.Valid ∧ final.chain = [] ∧ final.root = none ∧ final.elementSize = 0 ∧
      final.releasedRev.reverse = afterBoth.retirementWord := by
  simpa only [show afterBoth.chain.length = 5 by decide] using
    afterBoth.release_finite actual_null_writes_keep_live_backing 7 (by decide)


def nullAgain := (afterOne.write 1 { first with key := none }).getD afterOne

theorem null_slot_actual_pop :
    keyFrame 9 2 1 nullAgain = (keyFrame 9 2 2 afterOne).pop ∧
      (afterOne.read 1).map (fun row => (row.ordinal, row.value)) =
        (nullAgain.read 1).map (fun row => (row.ordinal, row.value)) := by
  apply actual_key_pop 9 2 2 afterOne nullAgain (by decide) (by decide) { first with key := none }
    (by decide) ⟨24, 1⟩ (by decide) (DataCell.of_value _ _ { first with key := none } (by decide)) (by decide)
  intro index inside different
  have zero : index = 0 := by omega
  subst index
  exact ⟨⟨24, 0⟩, by decide, by decide⟩

theorem null_scan_advances_without_owning_a_key :
    (keyFrame 9 2 2 afterOne).slots 1 = none ∧
      (keyFrame 9 2 1 nullAgain).inventory = [1001] ∧
      (keyFrame 9 2 1 nullAgain).Valid := by
  refine ⟨by decide, by decide, ?_⟩
  rw [null_slot_actual_pop.1]
  exact Frame.pop_valid _ (initialized_key_frame_valid 9 2 afterOne) (by decide)

end Controls

end Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.PagedStorage

namespace Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.FrameRecords

open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ExecutableStorage
open Mettapedia.Machines.CMemory.ExecutableStorage.BoundedIndexed

variable {Token : Type}

/-- Constant header admission for the existing initialized-frame invariant.
It is not a scan of the frame's slots or a grant to dispose borrowed sources. -/
def clear (frame : Frame Token) : Bool :=
  frame.length == 0 && frame.key.isNone && frame.scratch.isNone && frame.assembly.isNone && frame.items.isNone

theorem clear_fields (frame : Frame Token) (cleared : clear frame = true) :
    frame.length = 0 ∧ frame.key = none ∧ frame.scratch = none ∧ frame.assembly = none ∧ frame.items = none := by
  simpa [clear, and_assoc] using cleared

theorem clear_inventory (frame : Frame Token) (cleared : clear frame = true) : frame.inventory = [] := by
  obtain ⟨length, key, scratch, assembly, items⟩ := clear_fields frame cleared
  simp [Frame.inventory, Frame.keys, Frame.fixed, length, key, scratch, assembly, items]

/-- The phase invariant supplies initialized-slot closure that a forged zero
length alone would not supply. The extent counts initialized slots, not capacity. -/
theorem clear_initialized_slots (frame : Frame Token) (valid : frame.Valid) (cleared : clear frame = true) :
    frame.inventory = [] ∧ ∀ index < frame.extent, frame.slots index = none := by
  refine ⟨clear_inventory frame cleared, ?_⟩
  intro index inside
  exact valid.2 index (by rw [(clear_fields frame cleared).1]; exact Nat.zero_le _) inside

theorem nonempty_inventory_blocks (frame : Frame Token) (owned : frame.inventory ≠ []) : clear frame = false := by
  exact Bool.eq_false_iff.mpr (fun cleared => owned (clear_inventory frame cleared))

/-- The typed gate refuses before raw pop. Generic record pop itself retains
its caller-owned-contents precondition and authenticates no arbitrary claim. -/
theorem typed_pop_refuses_owned_contents (state : FrameStack.Stack (Frame Token)) (frame : Frame Token)
    (positive : 0 < state.depth) (top : state.top = some frame) (owned : frame.inventory ≠ []) :
    (state.cleanupStep clear).status = .refused ∧ (state.cleanupStep clear).next = state :=
  FrameStack.uncleared_refuses_pop clear state positive frame top (nonempty_inventory_blocks frame owned)

/-- An actual fixed-record store transports the preexisting owned-key pop
law. Record identity, source fields and the pointer slot remain unchanged. -/
theorem actual_tail_store (state : FrameStack.Stack (Frame Token)) (entries : List (Ptr × Frame Token))
    (pointer : Ptr) (frame : Frame Token) (represented : FrameStack.Represents state (entries ++ [(pointer, frame)]))
    (live : state.retiring = false) (pending : state.pending = none) (valid : frame.Valid) (positive : 0 < frame.length) :
    ∃ records,
      state.write (state.depth - 1) frame.pop = some { state with records := records } ∧
      FrameStack.Represents { state with records := records } (entries ++ [(pointer, frame.pop)]) ∧
      frame.pop.Valid ∧ frame.inventory.Perm ((frame.slots (frame.length - 1)).toList ++ frame.pop.inventory) := by
  obtain ⟨records, written, next, _⟩ := FrameStack.write_top_represents state entries pointer frame frame.pop
    represented live pending
  exact ⟨records, written, next, Frame.pop_valid frame valid positive, Frame.pop_inventory frame positive⟩

/-- One actual owned-key tail transition, stored in its fixed record, earns
the typed pop admission. The lower operations then null the slot and free
exactly that record; backing remains until the remaining frames are retired. -/
theorem one_key_then_record (state : FrameStack.Stack (Frame Token)) (entries : List (Ptr × Frame Token))
    (pointer : Ptr) (frame : Frame Token) (key : Token)
    (represented : FrameStack.Represents state (entries ++ [(pointer, frame)]))
    (live : state.retiring = false) (pending : state.pending = none) (admitted : state.WriteAdmission)
    (valid : frame.Valid) (length : frame.length = 1) (slot : frame.slots 0 = some key)
    (keyCursor : frame.key = none) (scratch : frame.scratch = none)
    (assembly : frame.assembly = none) (items : frame.items = none) :
    ∃ records next,
      state.write (state.depth - 1) frame.pop = some { state with records := records } ∧
      ({ state with records := records } : FrameStack.Stack (Frame Token)).cleanupStep clear =
        ⟨.pending, next, none, none⟩ ∧
      FrameStack.Represents next entries ∧ next.depth = state.depth - 1 ∧ next.pending = none ∧
      next.disposed = state.disposed + 1 ∧ next.backing.chain = state.backing.chain ∧
      load next.records pointer = none ∧ frame.inventory.Perm [key] := by
  obtain ⟨records, written, updatedRepresents, nextValid, partition⟩ :=
    actual_tail_store state entries pointer frame represented live pending valid (by omega)
  let updated := { state with records := records }
  have clean : clear frame.pop = true := by
    simp [clear, Frame.pop, length, keyCursor, scratch, assembly, items]
  have depth : state.depth = entries.length + 1 := by simpa [pending] using represented.depth
  have top : updated.top = some frame.pop := by
    simp only [FrameStack.Stack.top, show updated.depth ≠ 0 by dsimp [updated]; omega, ↓reduceIte]
    exact FrameStack.committed_read updated (entries ++ [(pointer, frame.pop)]) updatedRepresents live
      (state.depth - 1) pointer frame.pop (by simp [depth])
  obtain ⟨next, popped, nextRepresents, nextDepth, disposed, nextPending, nextLive, _, chain, dead, _⟩ :=
    FrameStack.committed_pop updated entries pointer frame.pop updatedRepresents live pending admitted
  refine ⟨records, next, written, ?_, nextRepresents, nextDepth, nextPending, disposed, chain, dead, ?_⟩
  · have nonzero : state.depth ≠ 0 := by omega
    have actualTop := top
    have actualPop := popped
    dsimp only [updated] at actualTop actualPop
    simp only [FrameStack.Stack.cleanupStep, if_neg nonzero, actualTop, clean, ↓reduceIte, actualPop]
  · simpa [length, slot, clear_inventory frame.pop clean] using partition

namespace Controls

set_option maxRecDepth 16384

def oneKey : Frame Nat := ⟨9, 1, 1, fun index => if index = 0 then some 42 else none, none, none, none, none⟩

theorem oneKey_valid : oneKey.Valid := by
  refine ⟨by decide, ?_⟩
  intro index beyond inside
  change 1 ≤ index at beyond
  change index < 1 at inside
  omega

theorem real_owned_key_and_clear_tail : oneKey.inventory = [42] ∧ clear oneKey = false ∧
    clear oneKey.pop = true ∧ oneKey.pop.inventory = [] := by
  simp [oneKey, Frame.inventory, Frame.keys, Frame.fixed, Frame.pop, clear]

def seed : FrameStack.Stack (Frame Nat) :=
  ⟨FrameStack.Controls.prepared.backing, [], 1, some oneKey, 352, false, 0⟩

def pages (state : FrameStack.Stack (Frame Nat)) : BlockId := FrameStack.freshIdentity state.backing.memory
def records (state : FrameStack.Stack (Frame Nat)) : BlockId := FrameStack.freshIdentity state.records + 2000

theorem pages_fresh (state : FrameStack.Stack (Frame Nat)) : state.backing.memory.lookup (pages state) = none :=
  FrameStack.freshIdentity_absent _ _ (Nat.le_refl _)

theorem records_fresh (state : FrameStack.Stack (Frame Nat)) : state.records.lookup (records state) = none :=
  FrameStack.freshIdentity_absent _ _ (by simp [records])

theorem seed_represents : FrameStack.Represents seed [] := by
  refine ⟨rfl, by decide, FrameStack.Controls.prepared_backing_valid, ?_, by simp, ?_⟩
  · intro index pointer frame found; simp at found
  · intro identity block found; simp [seed] at found

theorem seed_admission : seed.PublishAdmission := FrameStack.Controls.prepared_local_publication_admission

/-- A nonempty key lifecycle uses the actual fixed-record store before record
free, then the existing backing provider. No payload finalizer price is inferred. -/
theorem actual_nonempty_key_record_backing_lifecycle :
    ∃ (pointer : Ptr) (state next final : FrameStack.Stack (Frame Nat)) (recordMemory : Storage (Frame Nat)) (fuel paid : Nat),
      seed.pushRun (FrameStack.freshChoice pages) (FrameStack.freshChoice records) 3 =
        (2, .done ⟨(), .ready, state⟩) ∧
      (state.cleanupStep clear).status = .refused ∧
      state.write (state.depth - 1) oneKey.pop = some { state with records := recordMemory } ∧
      ({ state with records := recordMemory } : FrameStack.Stack (Frame Nat)).cleanupStep clear =
        ⟨.pending, next, none, none⟩ ∧
      next.cleanupRun clear fuel = (paid, .done ⟨(), .ready, final⟩) ∧
      final.depth = 0 ∧ final.pending = none ∧ final.backing.chain = [] ∧ final.backing.root = none ∧
      final.disposed = state.disposed + 1 ∧ load final.records pointer = none ∧ oneKey.inventory.Perm [42] := by
  obtain ⟨pointer, state, ran, represented, pending, depth, size, live, chain⟩ :=
    FrameStack.push_finite pages records pages_fresh records_fresh seed [] seed_represents rfl (by decide) rfl
      oneKey rfl 0 (by decide) seed_admission
  have stateDepth : state.depth = 1 := depth
  have top : state.top = some oneKey := by
    simp only [FrameStack.Stack.top, stateDepth, Nat.one_ne_zero, ↓reduceIte, Nat.sub_self]
    exact FrameStack.committed_read state [(pointer, oneKey)] represented live 0 pointer oneKey (by simp)
  have refused := typed_pop_refuses_owned_contents state oneKey (by omega) top (by
    simp [real_owned_key_and_clear_tail.1])
  have location := (represented.records_live 0 pointer oneKey (by simp)).1
  have admission : state.WriteAdmission := by
    intro address located
    have atZero : state.backing.at 0 = some address := by simpa only [stateDepth, Nat.sub_self] using located
    have loaded := FrameStack.read_load state.backing 0 (some pointer) location address atZero
    obtain ⟨block, found, blockLive, inside⟩ := load_present _ _ _ loaded
    refine ⟨⟨block, found, blockLive, inside⟩, DataCell.of_value _ _ _ loaded, ?_⟩
    intro index bounded
    omega
  obtain ⟨memory, next, written, popped, nextRepresents, nextDepth, noPending, disposed, nextChain, dead, inventory⟩ :=
    one_key_then_record state [] pointer oneKey 42 represented live pending admission oneKey_valid rfl rfl rfl rfl rfl rfl
  have zero : next.depth = 0 := by omega
  obtain ⟨fuel, paid, final, finished, finalDepth, finalPending, finalRecords, finalDisposed,
    _, finalChain, finalRoot, _, _⟩ := FrameStack.backing_finite clear next zero noPending nextRepresents.backing_valid
  refine ⟨pointer, state, next, final, memory, fuel, paid, ran, refused.1, written, popped, finished,
    finalDepth, finalPending, finalChain, finalRoot, finalDisposed.trans disposed, ?_, inventory⟩
  simpa only [finalRecords] using dead

def forged : Frame Nat := { oneKey with length := 0 }

theorem zero_header_needs_initialized_slot_invariant : clear forged = true ∧ ¬forged.Valid := by
  refine ⟨rfl, ?_⟩
  intro valid
  have empty := valid.2 0 (by decide) (by decide)
  change some 42 = none at empty
  cases empty

end Controls

end Mettapedia.Machines.Cursor.OwnedLifecycle.RetainedRetirement.FrameRecords
