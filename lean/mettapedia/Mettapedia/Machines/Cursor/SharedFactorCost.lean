import Mettapedia.Machines.Cursor.SharedFactor
import Mettapedia.Machines.ResourceOwnership
import Mettapedia.Machines.Cursor.OwnedLifecycle
import Mettapedia.Machines.Cursor.SuffixForwarding
import Mettapedia.Machines.Cursor.SharedFactorMachine

/-!
# Storage and operation accounts for suffix factors

The finite heap instance models atomic payloads, one backing allocation and
owner roots. It charges shared allocations once, regardless of reader count.
Structured payloads use the existing transitive heap footprint instead;
their descendants cannot be omitted from a native byte account.
The backing heap does not include the allocation graph of a structured caller
key; its owners must retain and charge that graph separately.

The operation account counts backing writes, view construction, admission
checks, indexed reads and deliveries separately. Translating these counts to
time requires bounds for the corresponding primitives. In particular an
arbitrary collapse algebra's `combine` does not have unit physical cost.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.SharedFactorCost

open Mettapedia.Machines.ResourceOwnership
open Mettapedia.GSLT.Distinction.ProductiveBlocks

variable {Value : Type}

/-- Each active reader retains the backing allocation in its own owner scope.
Acknowledged payloads may still be inspected until that reader is cancelled. -/
def readerRoots {Input : Type} {clients : Nat} (state : SharedFactor.State Input Value clients) :
    Roots Nat (Fin (state.backing.size + 1)) :=
  Finset.univ.biUnion fun client =>
    if (state.positions client).isSome then {(client.val + 2, 0)} else ∅

theorem reader_holds_backing {Input : Type} {clients : Nat}
    (state : SharedFactor.State Input Value clients) (client : Fin clients) (position : Nat)
    (present : state.positions client = some position) :
    (client.val + 2, 0) ∈ readerRoots state := by
  apply Finset.mem_biUnion.mpr
  exact ⟨client, Finset.mem_univ _, by simp [present]⟩

/-- Address zero is the backing allocation; the remaining addresses hold
the indexed atomic payloads and have no outgoing resource references. -/
def cell (backing : Array Value) (headerBytes : Nat) (payloadBytes : Value → Nat)
    (address : Fin (backing.size + 1)) : Cell (Fin (backing.size + 1)) (Option Value) where
  value := if address = 0 then none else backing[address.val - 1]?
  references := if address = 0 then Finset.univ.erase 0 else ∅
  bytes := if address = 0 then headerBytes
    else ((backing[address.val - 1]?).map payloadBytes).getD 0

def heap (backing : Array Value) (headerBytes : Nat) (payloadBytes : Value → Nat) :
    Heap (Fin (backing.size + 1)) (Option Value) where
  lookup address := some (cell backing headerBytes payloadBytes address)
  allocated := Finset.univ
  allocated_iff := by intro address; simp
  closed := by intro address found present other reference; exact Finset.mem_univ _

/-- A reader holding the backing allocation protects every payload cell. -/
theorem backing_root_keeps_payloads (backing : Array Value) (headerBytes : Nat)
    (payloadBytes : Value → Nat) (roots : Roots Nat (Fin (backing.size + 1)))
    (reader : Nat) (held : (reader, 0) ∈ roots) (address : Fin (backing.size + 1)) :
    Live (heap backing headerBytes payloadBytes) roots address := by
  have backingLive : Live (heap backing headerBytes payloadBytes) roots 0 :=
    live_of_root _ _ held (Finset.mem_univ _)
  by_cases same : address = 0
  · simpa only [same] using backingLive
  · apply live_step _ _ backingLive rfl
    simp [cell, same]

/-- Actual indexed cells survive collection while any reader retains backing
ownership. Store eviction may release its own root independently. -/
theorem lookup_after_collection (backing : Array Value) (headerBytes : Nat)
    (payloadBytes : Value → Nat) (roots : Roots Nat (Fin (backing.size + 1)))
    (reader : Nat) (held : (reader, 0) ∈ roots) (address : Fin (backing.size + 1)) :
    (collect (heap backing headerBytes payloadBytes) roots).lookup address =
      some (cell backing headerBytes payloadBytes address) :=
  lookup_collect_of_live _ _ (backing_root_keeps_payloads _ _ _ roots reader held address)

theorem eviction_preserves_live_reader (backing : Array Value) (headerBytes : Nat)
    (payloadBytes : Value → Nat) (roots : Roots Nat (Fin (backing.size + 1)))
    (store reader : Nat) (different : reader ≠ store) (held : (reader, 0) ∈ roots)
    (address : Fin (backing.size + 1)) :
    (collect (heap backing headerBytes payloadBytes) (release roots store)).lookup address =
      some (cell backing headerBytes payloadBytes address) := by
  apply lookup_after_collection _ _ _ _ reader _ address
  exact (mem_release roots store (reader, 0)).mpr ⟨held, different⟩

/-- This is the actual factor state, with roots derived from its independent
positions. Cancelling another reader cannot reclaim its backing payloads. -/
theorem cancellation_keeps_other_reader {Input : Type} {clients : Nat}
    (state : SharedFactor.State Input Value clients) (cancelled reader : Fin clients)
    (distinct : reader ≠ cancelled) (position : Nat)
    (present : state.positions reader = some position)
    (headerBytes : Nat) (payloadBytes : Value → Nat) (address : Fin (state.backing.size + 1)) :
    (collect (heap state.backing headerBytes payloadBytes)
      (readerRoots (SharedFactor.cancel state cancelled))).lookup address =
      some (cell state.backing headerBytes payloadBytes address) := by
  apply lookup_after_collection _ _ _ _ (reader.val + 2) _ address
  apply reader_holds_backing (SharedFactor.cancel state cancelled) reader position
  simp only [SharedFactor.cancel, SharedFactor.setPosition, Function.update_of_ne distinct]
  exact present

/-- Publication retains the backing root under the caller's independent
ownership before acknowledging the selected occurrence. The caller survives
release of the delivering reader's owner and all its transitive payloads stay. -/
theorem publication_before_acknowledgment {Input : Type} {clients : Nat}
    (state : SharedFactor.State Input Value clients) (client : Fin clients) (output : Nat)
    (outside : output ≠ client.val + 2) (headerBytes : Nat) (payloadBytes : Value → Nat)
    (address : Fin (state.backing.size + 1)) :
    (collect (heap state.backing headerBytes payloadBytes)
      (release (OwnedLifecycle.publish (readerRoots state) output [0]) (client.val + 2))).lookup
        address = some (cell state.backing headerBytes payloadBytes address) := by
  apply lookup_after_collection _ _ _ _ output _ address
  apply (mem_release _ _ _).mpr
  refine ⟨?_, outside⟩
  apply Finset.mem_union_right
  exact (OwnedLifecycle.mem_answerRoots output output [0] 0).mpr ⟨rfl, by simp⟩

/-- Bounds include the backing allocation and each reachable payload once.
No bound on the number of readers is needed for the shared payload graph. -/
theorem retained_payload_bytes_le (backing : Array Value) (headerBytes : Nat)
    (payloadBytes : Value → Nat) (roots : Roots Nat (Fin (backing.size + 1)))
    (bound : Nat) (bounded : ∀ value, payloadBytes value ≤ bound) :
    retainedBytes (heap backing headerBytes payloadBytes) roots ≤
      (backing.size + 1) * max headerBytes bound := by
  apply retainedBytes_le _ _ (backing.size + 1) (max headerBytes bound)
  · exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  · intro address live
    simp only [cellBytes, heap, Option.map_some, Option.getD_some, cell]
    split
    · exact Nat.le_max_left _ _
    · cases present : backing[address.val - 1]? with
      | none => simp
      | some value => exact (bounded value).trans (Nat.le_max_right _ _)

/-- After the ownership handoff, the compact allocation's byte bound uses
only its retained suffix. Old pinned generations have their own heap account
until release; they cannot be subtracted while a reader still owns them. -/
theorem compact_retained_bytes_le {Input : Type} {clients : Nat}
    (lower : Nat) (state : SharedFactor.State Input Value clients)
    (headerBytes : Nat) (payloadBytes : Value → Nat)
    (roots : Roots Nat (Fin ((SharedFactor.trimBefore lower state).backing.size + 1)))
    (bound : Nat) (bounded : ∀ value, payloadBytes value ≤ bound) :
    retainedBytes (heap (SharedFactor.trimBefore lower state).backing headerBytes payloadBytes) roots ≤
      (state.backing.size - lower + 1) * max headerBytes bound := by
  simpa only [SharedFactor.compact_backing_size] using
    retained_payload_bytes_le (SharedFactor.trimBefore lower state).backing
      headerBytes payloadBytes roots bound bounded

/-- Word metadata is separate from payload retention: four words per view
and two per maximum live consumer, under the stated layout contract. -/
theorem retained_with_metadata_le (backing : Array Value) (headerBytes : Nat)
    (payloadBytes : Value → Nat) (roots : Roots Nat (Fin (backing.size + 1)))
    (bound wordBytes views readers : Nat) (bounded : ∀ value, payloadBytes value ≤ bound) :
    retainedBytes (heap backing headerBytes payloadBytes) roots + wordBytes * (4 * views + 2 * readers) ≤
      (backing.size + 1) * max headerBytes bound + wordBytes * (4 * views + 2 * readers) :=
  Nat.add_le_add_right (retained_payload_bytes_le _ _ _ roots bound bounded) _

/-- Four independent accounts. Retained bytes are a state quantity; the first
three are cumulative operation counts. -/
structure Account where
  backend : Nat
  upkeep : Nat
  deliveries : Nat
  retainedBytes : Nat
  deriving DecidableEq, Repr

/-- Metadata allocations for materialized delivery records. Referenced
payloads remain in the backing heap under publication roots. The declared
record size includes its allocation header and fields. -/
def deliveryHeap {Event : Type} (events : List Event) (recordBytes : Nat) :
    Heap (Fin events.length) Event where
  lookup address := some ⟨events[address.val], ∅, recordBytes⟩
  allocated := Finset.univ
  allocated_iff := by intro address; simp
  closed := by intro address found present other reference; exact Finset.mem_univ _

/-- A caller retaining the materialized stream owns every record allocation,
even when several records refer to the same shared payload. -/
def deliveryRoots {Event : Type} (events : List Event) : Roots Nat (Fin events.length) :=
  Finset.univ.image fun address => (0, address)

theorem delivery_census_bytes {Event : Type} (events : List Event) (recordBytes : Nat) :
    censusBytes (deliveryHeap events recordBytes) (deliveryRoots events) =
      events.length * recordBytes := by
  have whole : footprint (deliveryHeap events recordBytes) (deliveryRoots events) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro address
    apply (mem_footprint _ _ _).mpr
    apply live_of_root _ _ (owner := 0)
    · exact Finset.mem_image.mpr ⟨address, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_univ _
  rw [censusBytes, census_eq_footprint _ _ (by intro pair member; exact Finset.mem_univ _), whole]
  simp [cellBytes, deliveryHeap]

/-- Repeated equal payloads still require separate materialized occurrence
records. Their backing payload storage and record storage are different sums. -/
theorem duplicate_deliveries_have_record_storage :
    censusBytes (deliveryHeap [(0, (41, 7)), (1, (41, 7))] 16)
      (deliveryRoots [(0, (41, 7)), (1, (41, 7))]) = 32 := by
  rw [delivery_census_bytes]
  decide

theorem forgetting_delivery_records_understates_storage :
    censusBytes (deliveryHeap [(0, (41, 7)), (1, (41, 7))] 16)
      (deliveryRoots [(0, (41, 7)), (1, (41, 7))]) > 0 := by
  rw [duplicate_deliveries_have_record_storage]
  decide

/-- Retaining any materialized delivery also publishes the backing under
the output owner. Record retention cannot be paired with an empty payload
root set. Owner one is separate from store zero and reader owners two onward. -/
def deliveryBackingRoots {Event : Type} {addresses : Nat} (events : List Event)
    (roots : Roots Nat (Fin (addresses + 1))) : Roots Nat (Fin (addresses + 1)) :=
  if events.isEmpty then roots else OwnedLifecycle.publish roots 1 [0]

theorem retained_delivery_keeps_payloads {Event : Type} (events : List Event)
    (nonempty : events ≠ []) (backing : Array Value) (headerBytes : Nat)
    (payloadBytes : Value → Nat) (roots : Roots Nat (Fin (backing.size + 1)))
    (address : Fin (backing.size + 1)) :
    (collect (heap backing headerBytes payloadBytes) (deliveryBackingRoots events roots)).lookup
      address = some (cell backing headerBytes payloadBytes address) := by
  apply lookup_after_collection _ _ _ _ 1 _ address
  simp only [deliveryBackingRoots, List.isEmpty_iff, nonempty, if_false]
  apply Finset.mem_union_right
  exact (OwnedLifecycle.mem_answerRoots 1 1 [0] 0).mpr ⟨rfl, by simp⟩

/-- One admitted cursor delivery uses one bounds check, one indexed read,
one publication and one cursor acknowledgment. Each is an explicit primitive. -/
def deliveryWork : Nat → Nat
  | 0 => 0
  | count + 1 => 4 + deliveryWork count

theorem deliveryWork_eq (count : Nat) : deliveryWork count = 4 * count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [deliveryWork, ih]; omega

/-- Actual shared-prefix construction supplies its amortized write account.
This combines storage upkeep with four metadata writes for each table view. -/
def constructionUpkeep (source : List Value) : Nat :=
  (PrefixBuffer.run PrefixBuffer.emptyHeap PrefixBuffer.emptyView [] source).2.2 + 4 * source.length

theorem constructionUpkeep_le (source : List Value) : constructionUpkeep source ≤ 7 * source.length := by
  have writes := (PrefixBuffer.chain_tables source).2.1
  unfold constructionUpkeep
  omega

private theorem install_sum_le {Input : Type} [DecidableEq Value]
    (backing : Array Value) (programs : List (SuffixForwarding.Program Input Value)) :
    (programs.map (fun program => (SuffixForwarding.installWithWork backing program).2)).sum ≤
      10 * programs.length := by
  induction programs with
  | nil => simp
  | cons program rest ih =>
      have step := SuffixForwarding.installWithWork_bound backing program
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- A counted buffer traversal. Each nonempty step charges a slot read and
one temporary list-node construction; the final inspection costs one. -/
def readWithWork (buffer : PrefixBuffer.Buffer Value) :
    Nat → Nat → Option (List Value) × Nat
  | _, 0 => (some [], 1)
  | start, count + 1 =>
      let rest := readWithWork buffer (start + 1) count
      let answer := match buffer.cell start, rest.1 with
        | some value, some values => some (value :: values)
        | _, _ => none
      (answer, rest.2 + 2)

theorem readWithWork_result (buffer : PrefixBuffer.Buffer Value) (start count : Nat) :
    (readWithWork buffer start count).1 = PrefixBuffer.readFrom buffer start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [readWithWork, PrefixBuffer.readFrom, ih]
      rfl

theorem readWithWork_cost (buffer : PrefixBuffer.Buffer Value) (start count : Nat) :
    (readWithWork buffer start count).2 = 2 * count + 1 := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp only [readWithWork, ih]; omega

/-- Build the ordered backing from actual online prepends, then traverse and
freeze the returned buffer. Reversing the input and writing the final array
each charge one node or slot per payload. This charges the conversion, rather
than assuming that the builder already returned the desired array. -/
def buildWithWork (source : List Value) : Option (Array Value) × Nat :=
  let built := PrefixBuffer.run PrefixBuffer.emptyHeap PrefixBuffer.emptyView [] source.reverse
  let scanned := readWithWork (built.1.buf built.2.1.addr) built.2.1.start built.2.1.len
  (scanned.1.map List.toArray, built.2.2 + source.length + scanned.2 + source.length)

theorem buildWithWork_result (source : List Value) :
    (buildWithWork source).1 = some source.toArray := by
  have readout := PrefixBuffer.read_run source.reverse
    (PrefixBuffer.read_emptyView (α := Value))
  simp only [List.reverse_reverse, List.append_nil, PrefixBuffer.read] at readout
  dsimp only [buildWithWork]
  rw [readWithWork_result, readout]
  rfl

theorem buildWithWork_bound (source : List Value) :
    (buildWithWork source).2 ≤ 7 * source.length + 1 := by
  have writes := (PrefixBuffer.chain_tables source.reverse).2.1
  simp only [List.length_reverse] at writes
  have readout := PrefixBuffer.read_run source.reverse
    (PrefixBuffer.read_emptyView (α := Value))
  simp only [List.reverse_reverse, List.append_nil, PrefixBuffer.read] at readout
  have length := PrefixBuffer.read_prepend.readFrom_length _ _ _ source readout
  dsimp only [buildWithWork]
  rw [readWithWork_cost, ← length]
  omega

theorem constructed_chain_backing (size : Nat) :
    (buildWithWork (List.range size)).1 = some (SuffixForwarding.backing size) :=
  buildWithWork_result _

theorem unreversed_prepends_change_order :
    PrefixBuffer.read
      (PrefixBuffer.run PrefixBuffer.emptyHeap PrefixBuffer.emptyView [] [0, 1, 2]).1
      (PrefixBuffer.run PrefixBuffer.emptyHeap PrefixBuffer.emptyView [] [0, 1, 2]).2.1 ≠
        some ([0, 1, 2] : List Nat) := by decide

/-- The actual backing builder is evaluated once. Each admitted view then
performs its bounded checks and four field writes. No membership index is
rebuilt: the dense interval index is implicit in each admitted view. -/
def chainUpkeep (size : Nat) : Nat :=
  let built := buildWithWork (List.range size)
  let heldBacking := built.1.getD #[]
  built.2 +
    ((List.range size).map (fun caller =>
      (SuffixForwarding.installWithWork heldBacking
        (SuffixForwarding.chainProgram size caller)).2)).sum

theorem chainUpkeep_le (size : Nat) : chainUpkeep size ≤ 17 * size + 1 := by
  have construction := buildWithWork_bound (List.range size)
  have admission := install_sum_le (SuffixForwarding.backing size)
    ((List.range size).map (SuffixForwarding.chainProgram size))
  simp only [List.length_map, List.length_range, List.map_map, Function.comp_def] at admission
  simp only [List.length_range] at construction
  dsimp only [chainUpkeep]
  rw [constructed_chain_backing, Option.getD_some]
  omega

def chainReader (size : Nat) (caller : Fin (size + 1)) : SharedFactorMachine.Checked Nat Nat 1 :=
  ⟨⟨SuffixForwarding.backing size, SuffixForwarding.view size caller.val,
      fun _ => some 0⟩, SuffixForwarding.chain_valid size caller.val (by omega)⟩

/-- Each completed suffix has exactly its source number of occurrences.
Every suffix can be requested without retaining another payload copy. -/
theorem suffix_deliveries (size : Nat) (caller : Fin (size + 1)) :
    ((SharedFactorMachine.indexed 0).run (size + 1) (chainReader size caller)).1.length =
      size - caller.val := by
  rw [SharedFactorMachine.delivery_count _ _ 0 0 rfl]
  simp only [chainReader, SuffixForwarding.view, Nat.sub_zero]
  apply Nat.min_eq_right
  omega

theorem root_deliveries (size fuel : Nat) :
    ((SharedFactorMachine.indexed 0).run fuel (chainReader size 0)).1.length = min fuel size := by
  rw [SharedFactorMachine.delivery_count _ _ 0 0 rfl]
  rfl

theorem root_work_le (size : Nat) :
    (SharedFactorMachine.indexed 0).spent (SharedFactorMachine.price 0) (size + 1)
      (chainReader size 0) ≤ 4 * size + 1 := by
  have bound := SharedFactorMachine.spent_le_deliveries (size + 1) (chainReader size 0) 0
  rw [suffix_deliveries] at bound
  simpa using bound

/-- Root enumeration is within factor four plus one terminal inspection of
any explicit-output implementation returning the same number of answers,
under accounts that charge at least one unit per published answer. This
comparison says nothing about compressed readouts or minimum retained bytes. -/
theorem root_stream_work_competitive {State Event Verdict Request : Type}
    (size : Nat) (machine : Machine State Event Verdict Request) (price : State → Nat)
    (publishes : ∀ state events next, machine.step state = some (.publish events next) →
      events.length ≤ price state)
    (fails : ∀ state events, machine.step state = some (.fail events) →
      events.length ≤ price state)
    (fuel : Nat) (state : State) (answers : (machine.run fuel state).1.length = size) :
    (SharedFactorMachine.indexed 0).spent (SharedFactorMachine.price 0) (size + 1)
        (chainReader size 0) ≤ 4 * machine.spent price fuel state + 1 := by
  have lower := machine.output_length_le_spent price publishes fails fuel state
  rw [answers] at lower
  exact (root_work_le size).trans (by omega)

/-- Root enumeration is linear above and below in the declared delivery
primitive model. This is not a claim about minimum representation bytes or
the best constant on a physical backend. -/
theorem root_work_linear (size : Nat) :
    4 * size ≤ (SharedFactorMachine.indexed 0).spent (SharedFactorMachine.price 0)
        (size + 1) (chainReader size 0) ∧
      (SharedFactorMachine.indexed 0).spent (SharedFactorMachine.price 0)
        (size + 1) (chainReader size 0) ≤ 4 * size + 1 := by
  refine ⟨?_, root_work_le size⟩
  have bound := SharedFactorMachine.deliveries_le_spent (size + 1) (chainReader size 0) 0
  rw [suffix_deliveries] at bound
  simpa using bound

theorem root_construction_and_delivery_le (size : Nat) :
    chainUpkeep size +
      (SharedFactorMachine.indexed 0).spent (SharedFactorMachine.price 0) (size + 1)
        (chainReader size 0) ≤ 21 * size + 2 := by
  have upkeep := chainUpkeep_le size
  have delivery := root_work_le size
  omega

/-- Including construction and admission still gives an output-sensitive
regional bound. The competitor must publish the same explicit number of
answers and charge each; its native representation and constants may differ. -/
theorem root_region_work_competitive {State Event Verdict Request : Type}
    (size : Nat) (machine : Machine State Event Verdict Request) (price : State → Nat)
    (publishes : ∀ state events next, machine.step state = some (.publish events next) →
      events.length ≤ price state)
    (fails : ∀ state events, machine.step state = some (.fail events) →
      events.length ≤ price state)
    (fuel : Nat) (state : State) (answers : (machine.run fuel state).1.length = size) :
    chainUpkeep size +
      (SharedFactorMachine.indexed 0).spent (SharedFactorMachine.price 0) (size + 1)
        (chainReader size 0) ≤ 21 * machine.spent price fuel state + 2 := by
  have lower := machine.output_length_le_spent price publishes fails fuel state
  rw [answers] at lower
  exact (root_construction_and_delivery_le size).trans (by omega)

/-- Observing all suffixes through the actual common runner necessarily
publishes the triangular output size, even with linear backing storage. -/
theorem all_suffix_deliveries (size : Nat) :
    2 * (∑ caller : Fin (size + 1),
      ((SharedFactorMachine.indexed 0).run (size + 1) (chainReader size caller)).1.length) =
      size * (size + 1) := by
  have total : (∑ caller : Fin (size + 1),
      ((SharedFactorMachine.indexed 0).run (size + 1) (chainReader size caller)).1.length) =
      ((List.range size).tails.map List.length).sum := by
    have tails : (List.range size).tails =
        List.ofFn (fun caller : Fin (size + 1) => (List.range size).drop caller.val) := by
      apply List.ext_getElem
      · simp
      · intro index _ _
        simp only [List.getElem_tails, List.getElem_ofFn]
    rw [tails]
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, List.length_drop, List.length_range]
    apply Finset.sum_congr rfl
    intro caller _
    exact suffix_deliveries size caller
  rw [total, ← SuffixForwarding.allDeliveries_source, List.length_range]
  exact SuffixForwarding.allDeliveries_triangular size

/-- All requested suffix outputs, as materialized by the common runner. -/
def allSuffixEvents (size : Nat) : List (Nat × (Nat × Nat)) :=
  (List.ofFn fun caller : Fin (size + 1) =>
    ((SharedFactorMachine.indexed 0).run (size + 1) (chainReader size caller)).1).flatten

/-- Retaining every materialized suffix stream requires triangular record
storage despite linear backing storage. Streaming or compressed observers
have a different retention contract. -/
theorem all_suffix_record_bytes (size recordBytes : Nat) :
    2 * censusBytes (deliveryHeap (allSuffixEvents size) recordBytes)
      (deliveryRoots (allSuffixEvents size)) = size * (size + 1) * recordBytes := by
  rw [delivery_census_bytes]
  have length : (allSuffixEvents size).length =
      ∑ caller : Fin (size + 1),
        ((SharedFactorMachine.indexed 0).run (size + 1) (chainReader size caller)).1.length := by
    simp only [allSuffixEvents, List.length_flatten, List.map_ofFn, List.sum_ofFn,
      Function.comp_apply]
  rw [length, ← Nat.mul_assoc, all_suffix_deliveries]

/-- The fourth account bounds the actual reachable atomic backing heap and
the declared metadata layout. Caller handles occupy one metadata word.
Structured payloads additionally charge their transitive resource graphs. -/
theorem chain_retained_bytes_le (size headerBytes wordBytes bound readers : Nat)
    (payloadBytes : Nat → Nat) (bounded : ∀ payload, payloadBytes payload ≤ bound)
    (roots : Roots Nat (Fin ((SuffixForwarding.backing size).size + 1))) :
    retainedBytes (heap (SuffixForwarding.backing size) headerBytes payloadBytes) roots +
      wordBytes * (4 * size + 2 * readers) ≤
        (size + 1) * max headerBytes bound + wordBytes * (4 * size + 2 * readers) := by
  simpa only [SuffixForwarding.shared_payload_count] using
    retained_with_metadata_le (SuffixForwarding.backing size) headerBytes payloadBytes roots
      bound wordBytes size readers bounded

/-- A constructed regional account, using the actual common-machine run,
counted admission path and reachable heap. Producer work before this delivery
region and native allocation/copy primitives have their own accounts. -/
def chainAccount (size headerBytes wordBytes readers recordBytes : Nat) (payloadBytes : Nat → Nat)
    (roots : Roots Nat (Fin ((SuffixForwarding.backing size).size + 1))) : Account where
  backend := (SharedFactorMachine.indexed 0).spent (SharedFactorMachine.price 0) (size + 1)
    (chainReader size 0)
  upkeep := chainUpkeep size
  deliveries := ((SharedFactorMachine.indexed 0).run (size + 1) (chainReader size 0)).1.length
  retainedBytes := censusBytes (heap (SuffixForwarding.backing size) headerBytes payloadBytes)
    (deliveryBackingRoots
      ((SharedFactorMachine.indexed 0).run (size + 1) (chainReader size 0)).1 roots) +
    wordBytes * (4 * size + 2 * readers) +
    censusBytes (deliveryHeap
      ((SharedFactorMachine.indexed 0).run (size + 1) (chainReader size 0)).1 recordBytes)
      (deliveryRoots ((SharedFactorMachine.indexed 0).run (size + 1) (chainReader size 0)).1)

theorem chainAccount_bounds (size headerBytes wordBytes bound readers recordBytes : Nat)
    (payloadBytes : Nat → Nat) (bounded : ∀ payload, payloadBytes payload ≤ bound)
    (roots : Roots Nat (Fin ((SuffixForwarding.backing size).size + 1))) :
    (chainAccount size headerBytes wordBytes readers recordBytes payloadBytes roots).backend ≤ 4 * size + 1 ∧
    (chainAccount size headerBytes wordBytes readers recordBytes payloadBytes roots).upkeep ≤ 17 * size + 1 ∧
    (chainAccount size headerBytes wordBytes readers recordBytes payloadBytes roots).deliveries = size ∧
    (chainAccount size headerBytes wordBytes readers recordBytes payloadBytes roots).retainedBytes ≤
      (size + 1) * max headerBytes bound + wordBytes * (4 * size + 2 * readers) + size * recordBytes := by
  let retainedRoots := deliveryBackingRoots
    ((SharedFactorMachine.indexed 0).run (size + 1) (chainReader size 0)).1 roots
  have bytes := censusBytes_eq_retainedBytes
    (heap (SuffixForwarding.backing size) headerBytes payloadBytes) retainedRoots
    (by intro pair member; exact Finset.mem_univ _)
  dsimp only [chainAccount]
  refine ⟨root_work_le size, chainUpkeep_le size, ?_, ?_⟩
  · exact suffix_deliveries size 0
  · rw [bytes, delivery_census_bytes, suffix_deliveries]
    simpa only [Fin.val_zero, Nat.sub_zero] using
      Nat.add_le_add_right (chain_retained_bytes_le _ _ _ _ _ _ bounded retainedRoots)
        (size * recordBytes)

private abbrev sample : Array Nat := #[7, 7, 9]

/-- Retaining every element does not retain the allocation containing their
slots. A view must also own that backing allocation. -/
theorem payload_roots_do_not_keep_backing :
    (collect (heap sample 16 (fun _ => 8))
      ({(1, 1), (1, 2), (1, 3)} : Roots Nat (Fin 4))).lookup 0 = none ∧
    ∀ address : Fin 4, address ≠ 0 →
      (collect (heap sample 16 (fun _ => 8))
        ({(1, 1), (1, 2), (1, 3)} : Roots Nat (Fin 4))).lookup address =
          some (cell sample 16 (fun _ => 8) address) := by
  constructor
  · apply lookup_collect_of_not_live
    intro live
    cases live with
    | root present => simpa [Heap.toStore, rootAddresses] using present.2
    | step previous edge =>
        obtain ⟨stored, found, reference⟩ := edge
        simp only [heap] at found
        cases Option.some.inj found
        simp only [cell] at reference
        split_ifs at reference <;> simp_all
  · intro address nonzero
    apply lookup_collect_of_live
    apply live_of_root _ _ (owner := 1)
    · fin_cases address <;> simp_all
    · exact Finset.mem_univ _

theorem premature_release_changes_payload :
    (collect (heap sample 16 (fun _ => 8)) (∅ : Roots Nat (Fin 4))).lookup 1 = none ∧
    (heap sample 16 (fun _ => 8)).lookup 1 ≠ none := by
  constructor
  · exact lookup_collect_of_not_live _ _ (not_live_empty _ _)
  · decide

theorem one_reader_survives_store_eviction :
    (collect (heap sample 16 (fun _ => 8))
      (release ({(0, 0), (1, 0)} : Roots Nat (Fin 4)) 0)).lookup 2 =
      some (cell sample 16 (fun _ => 8) 2) := by
  exact eviction_preserves_live_reader sample 16 (fun _ => 8)
    ({(0, 0), (1, 0)} : Roots Nat (Fin 4)) 0 1 (by decide) (by simp) 2

end Mettapedia.Machines.Cursor.SharedFactorCost
