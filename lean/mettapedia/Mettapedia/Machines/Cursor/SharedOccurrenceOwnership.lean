import Mettapedia.Machines.Cursor.SharedOccurrenceLog
import Mettapedia.Machines.Cursor.OwnedLifecycle

/-!
# Owned delivery from a shared occurrence log

Unread log addresses protect their complete resource graphs. Delivery prepares
publication under a caller owner before acknowledging the occurrence. Both
intermediate configurations protect the answer graph. Cancelling one consumer
removes only that consumer's log roots;
published answers and other consumers' unread graphs survive collection.

The construction combines the actual cursor operations with the existing finite
resource heap and transitive reachability. It does not discover native roots,
qualify a producer, execute foreign finalizers, or prove a concurrent allocator.
Row retention and byte retention remain separate quantities.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.SharedOccurrenceOwnership

open Mettapedia.Machines.ResourceOwnership (Roots Heap Live ValidRoots collect live_mono
  live_of_root lookup_collect_of_live)
open Mettapedia.Machines.Cursor.SharedOccurrenceLog (State Valid Reply peek pull unread trim)
open Mettapedia.Machines.Cursor.OwnedLifecycle (answerRoots publish)

variable {Address Value Output : Type} {clients : Nat}
  [DecidableEq Address] [DecidableEq Output]

/-- Consumer log roots and caller publication roots occupy disjoint owner scopes. -/
def logRoots (Output : Type) (state : State Address clients) [DecidableEq Output] :
    Roots (Sum (Fin clients) Output) Address :=
  Finset.univ.biUnion (fun client => answerRoots (Sum.inl client) (unread state client))

@[simp] theorem mem_logRoots_consumer (state : State Address clients)
    (client : Fin clients) (address : Address) :
    (Sum.inl client, address) ∈ logRoots Output state ↔ address ∈ unread state client := by
  simp [logRoots]

@[simp] theorem caller_not_in_logRoots (state : State Address clients)
    (output : Output) (address : Address) : (Sum.inr output, address) ∉ logRoots Output state := by
  simp [logRoots]

def publishedRoots (published : Roots Output Address) : Roots (Sum (Fin clients) Output) Address :=
  published.image (fun pair => (Sum.inr pair.1, pair.2))

@[simp] theorem mem_publishedRoots_caller (published : Roots Output Address)
    (output : Output) (address : Address) :
    (Sum.inr output, address) ∈ publishedRoots (clients := clients) published ↔
      (output, address) ∈ published := by
  simp [publishedRoots]

@[simp] theorem consumer_not_in_publishedRoots (published : Roots Output Address)
    (client : Fin clients) (address : Address) :
    (Sum.inl client, address) ∉ publishedRoots published := by
  simp [publishedRoots]

structure Configuration (Address Output : Type) (clients : Nat) where
  log : State Address clients
  published : Roots Output Address

def roots (state : Configuration Address Output clients) : Roots (Sum (Fin clients) Output) Address :=
  logRoots Output state.log ∪ publishedRoots state.published

/-- Publication leaves every consumer position unchanged. The caller owns the
exported graph independently of log storage. -/
def prepare (state : Configuration Address Output clients) (client : Fin clients) (output : Output) :
    Configuration Address Output clients :=
  let published := match peek state.log client with
    | .answer _ address => publish state.published output [address]
    | _ => state.published
  ⟨state.log, published⟩

def acknowledge (state : Configuration Address Output clients) (client : Fin clients) :
    Reply Address × Configuration Address Output clients :=
  let received := pull state.log client
  (received.1, ⟨received.2, state.published⟩)

/-- This ordered composition admits collection between preparation and
acknowledgment. Native temporal refinement and failure handling are separate. -/
def advance (state : Configuration Address Output clients) (client : Fin clients) (output : Output) :
    Reply Address × Configuration Address Output clients :=
  acknowledge (prepare state client output) client

theorem prepare_answer (state : Configuration Address Output clients) (client : Fin clients)
    (output : Output) (position : Nat) (address : Address)
    (answer : peek state.log client = .answer position address) :
    prepare state client output = ⟨state.log, publish state.published output [address]⟩ := by
  simp only [prepare, answer]

theorem advance_answer (state : Configuration Address Output clients) (client : Fin clients)
    (output : Output) (position : Nat) (address : Address)
    (answer : peek state.log client = .answer position address) :
    advance state client output = (.answer position address,
      ⟨SharedOccurrenceLog.setPosition state.log client (some (position + 1)),
        publish state.published output [address]⟩) := by
  simp only [advance, prepare, acknowledge, pull, answer]

/-- Distinct consumers may publish and acknowledge in either order. Each
reply remains attached to its requesting consumer, and all caller roots agree.
This law concerns atomic owned delivery from a fixed log; it does not license
unsynchronized mutation of the native publication-root representation. -/
theorem advance_commute (state : Configuration Address Output clients)
    (left right : Fin clients) (leftOutput rightOutput : Output) (distinct : left ≠ right) :
    (let first := advance state left leftOutput
     let second := advance first.2 right rightOutput
     (first.1, second.1, second.2)) =
      (let second := advance state right rightOutput
       let first := advance second.2 left leftOutput
       (first.1, second.1, first.2)) := by
  have logs := SharedOccurrenceLog.pull_commute state.log left right distinct
  have leftRead := SharedOccurrenceLog.pull_preserves_other state.log right left distinct
  have rightRead := SharedOccurrenceLog.pull_preserves_other state.log left right distinct.symm
  simp only [advance, prepare, acknowledge, leftRead, rightRead]
  simp only at logs
  obtain ⟨leftAnswer, rest⟩ := Prod.mk.inj logs
  obtain ⟨rightAnswer, residual⟩ := Prod.mk.inj rest
  rw [leftAnswer, rightAnswer, residual]
  cases leftReply : peek state.log left <;> cases rightReply : peek state.log right <;>
    simp only [OwnedLifecycle.publish, Finset.union_assoc, Finset.union_left_comm,
      Finset.union_comm]

def WellFormed (heap : Heap Address Value) (state : Configuration Address Output clients) : Prop :=
  Valid state.log ∧ ValidRoots heap (roots state)

theorem delivered_address_is_allocated (heap : Heap Address Value)
    (state : Configuration Address Output clients) (client : Fin clients)
    (position : Nat) (address : Address) (valid : ValidRoots heap (roots state))
    (answer : peek state.log client = .answer position address) : address ∈ heap.allocated := by
  apply valid (Sum.inl client, address)
  apply Finset.mem_union_left
  rw [mem_logRoots_consumer, SharedOccurrenceLog.answer_unread state.log client position address answer]
  exact List.mem_cons_self

theorem prepare_wellFormed (heap : Heap Address Value)
    (state : Configuration Address Output clients) (client : Fin clients) (output : Output)
    (valid : WellFormed heap state) : WellFormed heap (prepare state client output) := by
  cases reply : peek state.log client with
  | answer position address =>
      have allocated := delivered_address_is_allocated heap state client position address valid.2 reply
      rw [prepare_answer state client output position address reply]
      refine ⟨valid.1, ?_⟩
      intro pair member
      rcases pair with ⟨owner, location⟩
      cases owner with
      | inl consumer =>
          have old : (Sum.inl consumer, location) ∈ roots state := by
            simpa [roots] using member
          exact valid.2 _ old
      | inr caller =>
          have published : (caller, location) ∈ publish state.published output [address] := by
            simpa [roots] using member
          rcases Finset.mem_union.mp published with old | fresh
          · apply valid.2 (Sum.inr caller, location)
            exact Finset.mem_union_right _ ((mem_publishedRoots_caller _ _ _).mpr old)
          · obtain ⟨_, selected⟩ := (OwnedLifecycle.mem_answerRoots _ _ _ _).mp fresh
            have same : location = address := by simpa using selected
            exact same ▸ allocated
  | paused => simpa only [prepare, reply] using valid
  | completed => simpa only [prepare, reply] using valid
  | cancelled => simpa only [prepare, reply] using valid
  | invalid => simpa only [prepare, reply] using valid

theorem acknowledge_wellFormed (heap : Heap Address Value)
    (state : Configuration Address Output clients) (client : Fin clients)
    (valid : WellFormed heap state) : WellFormed heap (acknowledge state client).2 := by
  refine ⟨SharedOccurrenceLog.pull_valid state.log client valid.1, ?_⟩
  intro pair member
  rcases pair with ⟨owner, address⟩
  apply valid.2 (owner, address)
  cases owner with
  | inl other =>
      have remaining : address ∈ unread (pull state.log client).2 other := by
        simpa [roots, acknowledge] using member
      apply Finset.mem_union_left
      rw [mem_logRoots_consumer]
      exact SharedOccurrenceLog.pull_unread_subset state.log client other remaining
  | inr output => simpa [roots, acknowledge] using member

theorem advance_wellFormed (heap : Heap Address Value)
    (state : Configuration Address Output clients) (client : Fin clients) (output : Output)
    (valid : WellFormed heap state) : WellFormed heap (advance state client output).2 :=
  acknowledge_wellFormed heap (prepare state client output) client
    (prepare_wellFormed heap state client output valid)

theorem collection_wellFormed (heap : Heap Address Value)
    (state : Configuration Address Output clients) (valid : WellFormed heap state) :
    WellFormed (collect heap (roots state)) state := by
  refine ⟨valid.1, ?_⟩
  intro pair member
  change pair.2 ∈ ResourceOwnership.footprint heap (roots state)
  apply (ResourceOwnership.mem_footprint heap (roots state) pair.2).mpr
  exact live_of_root heap (roots state) member (valid.2 pair member)

theorem collection_between_publication_and_acknowledgment
    (heap : Heap Address Value) (state : Configuration Address Output clients)
    (client : Fin clients) (output : Output) (valid : WellFormed heap state) :
    WellFormed (collect heap (roots (prepare state client output)))
      (advance state client output).2 :=
  acknowledge_wellFormed _ (prepare state client output) client
    (collection_wellFormed heap _ (prepare_wellFormed heap state client output valid))

theorem prepare_retains_selected_graph (heap : Heap Address Value)
    (state : Configuration Address Output clients) (client : Fin clients) (output : Output)
    (position : Nat) (address location : Address)
    (answer : peek state.log client = .answer position address)
    (live : Live heap (answerRoots (Sum.inr output : Sum (Fin clients) Output) [address]) location) :
    (collect heap (roots (prepare state client output))).lookup location = heap.lookup location := by
  apply lookup_collect_of_live
  apply live_mono heap _ live
  intro pair member
  rcases pair with ⟨owner, root⟩
  obtain ⟨same, selected⟩ := (OwnedLifecycle.mem_answerRoots _ _ _ _).mp member
  subst owner
  rw [prepare_answer state client output position address answer]
  apply Finset.mem_union_right
  rw [mem_publishedRoots_caller]
  exact Finset.mem_union_right _
    ((OwnedLifecycle.mem_answerRoots output output [address] root).mpr ⟨rfl, selected⟩)

theorem advance_retains_published_graph (heap : Heap Address Value)
    (state : Configuration Address Output clients) (client : Fin clients) (output : Output)
    (position : Nat) (address location : Address)
    (answer : peek state.log client = .answer position address)
    (live : Live heap (answerRoots (Sum.inr output : Sum (Fin clients) Output) [address]) location) :
    (collect heap (roots (advance state client output).2)).lookup location = heap.lookup location := by
  apply lookup_collect_of_live
  apply live_mono heap (roots := answerRoots (Sum.inr output : Sum (Fin clients) Output) [address]) _ live
  intro pair member
  rcases pair with ⟨owner, root⟩
  obtain ⟨same, selected⟩ := (OwnedLifecycle.mem_answerRoots _ _ _ _).mp member
  subst owner
  rw [advance_answer state client output position address answer]
  apply Finset.mem_union_right
  rw [mem_publishedRoots_caller]
  exact Finset.mem_union_right _
    ((OwnedLifecycle.mem_answerRoots output output [address] root).mpr ⟨rfl, selected⟩)

theorem advance_retains_prior_published_graph (heap : Heap Address Value)
    (state : Configuration Address Output clients) (client : Fin clients) (output : Output)
    (location : Address) (live : Live heap (publishedRoots (clients := clients) state.published) location) :
    (collect heap (roots (advance state client output).2)).lookup location = heap.lookup location := by
  apply lookup_collect_of_live
  apply live_mono heap _ live
  intro pair member
  apply Finset.mem_union_right
  obtain ⟨old, present, same⟩ := Finset.mem_image.mp member
  apply Finset.mem_image.mpr
  refine ⟨old, ?_, same⟩
  change old ∈ (match peek state.log client with
    | .answer _ address => publish state.published output [address]
    | _ => state.published)
  cases peek state.log client <;> simp only
  · exact OwnedLifecycle.publish_mono state.published output _ present
  all_goals exact present

def cancelConsumer (state : Configuration Address Output clients) (client : Fin clients) :
    Configuration Address Output clients :=
  ⟨SharedOccurrenceLog.cancel state.log client, state.published⟩

omit [DecidableEq Address] in
theorem unread_cancel_self (state : State Address clients) (client : Fin clients) :
    unread (SharedOccurrenceLog.cancel state client) client = [] := by
  simp [unread, SharedOccurrenceLog.cancel]

omit [DecidableEq Address] in
theorem unread_cancel_other (state : State Address clients) (client other : Fin clients)
    (distinct : other ≠ client) :
    unread (SharedOccurrenceLog.cancel state client) other = unread state other := by
  unfold unread SharedOccurrenceLog.cancel
  rw [SharedOccurrenceLog.setPosition_other state client other none distinct]
  rfl

theorem cancellation_removes_only_the_consumer_roots
    (state : Configuration Address Output clients) (client : Fin clients) :
    roots (cancelConsumer state client) =
      ResourceOwnership.cancel (roots state) {Sum.inl client} := by
  ext pair
  rcases pair with ⟨owner, address⟩
  cases owner with
  | inl other =>
      by_cases same : other = client
      · subst other
        simp [roots, cancelConsumer, unread_cancel_self]
      · simp [roots, cancelConsumer, unread_cancel_other _ _ _ same, same]
  | inr output => simp [roots, cancelConsumer]

theorem cancel_wellFormed (heap : Heap Address Value)
    (state : Configuration Address Output clients) (client : Fin clients)
    (valid : WellFormed heap state) : WellFormed heap (cancelConsumer state client) := by
  refine ⟨SharedOccurrenceLog.cancel_valid state.log client valid.1, ?_⟩
  rw [cancellation_removes_only_the_consumer_roots]
  intro pair member
  exact valid.2 pair (ResourceOwnership.cancel_subset (roots state) {Sum.inl client} member)

/-- Releasing a caller handle removes its publications, while all log consumers
keep their own independently owned unread graphs. -/
def releaseCaller (state : Configuration Address Output clients) (output : Output) :
    Configuration Address Output clients :=
  ⟨state.log, ResourceOwnership.release state.published output⟩

theorem releaseCaller_roots (state : Configuration Address Output clients) (output : Output) :
    roots (releaseCaller state output) = ResourceOwnership.release (roots state) (Sum.inr output) := by
  ext pair
  rcases pair with ⟨owner, address⟩
  cases owner with
  | inl client => simp [roots, releaseCaller]
  | inr caller => simp [roots, releaseCaller]

def trimLog (state : Configuration Address Output clients) : Configuration Address Output clients :=
  ⟨trim state.log, state.published⟩

theorem advance_valid (state : Configuration Address Output clients) (client : Fin clients)
    (output : Output) (valid : Valid state.log) : Valid (advance state client output).2.log :=
  SharedOccurrenceLog.pull_valid state.log client valid

theorem trimming_preserves_resource_roots (state : Configuration Address Output clients)
    (valid : Valid state.log) : roots (trimLog state) = roots state := by
  unfold roots trimLog logRoots
  congr 1
  congr 1
  funext client
  rw [SharedOccurrenceLog.trim_preserves_unread state.log client valid]

theorem cancel_trim_retains_other_unread_graph (heap : Heap Address Value)
    (state : Configuration Address Output clients) (client other : Fin clients)
    (valid : Valid state.log) (distinct : other ≠ client) (location : Address)
    (live : Live heap (answerRoots (Sum.inl other : Sum (Fin clients) Output)
      (unread state.log other)) location) :
    (collect heap (roots (trimLog (cancelConsumer state client)))).lookup location =
      heap.lookup location := by
  rw [trimming_preserves_resource_roots _ (SharedOccurrenceLog.cancel_valid _ _ valid)]
  apply lookup_collect_of_live
  apply live_mono heap _ live
  intro pair member
  rcases pair with ⟨owner, address⟩
  obtain ⟨same, selected⟩ := (OwnedLifecycle.mem_answerRoots _ _ _ _).mp member
  subst owner
  apply Finset.mem_union_left
  rw [mem_logRoots_consumer]
  exact (unread_cancel_other state.log client other distinct).symm ▸ selected

theorem cancel_trim_retains_published_graph (heap : Heap Address Value)
    (state : Configuration Address Output clients) (client : Fin clients)
    (valid : Valid state.log) (location : Address)
    (live : Live heap (publishedRoots (clients := clients) state.published) location) :
    (collect heap (roots (trimLog (cancelConsumer state client)))).lookup location =
      heap.lookup location := by
  rw [trimming_preserves_resource_roots _ (SharedOccurrenceLog.cancel_valid _ _ valid)]
  apply lookup_collect_of_live
  exact live_mono heap Finset.subset_union_right live

/-- Bounded owned observation includes the publication state in its residual. -/
def observe : Nat → Configuration Address Output clients → Fin clients → Output →
    List (Nat × Address) × Configuration Address Output clients
  | 0, state, _, _ => ([], state)
  | budget + 1, state, client, output =>
      match advance state client output with
      | (.answer position address, next) =>
          let rest := observe budget next client output
          ((position, address) :: rest.1, rest.2)
      | (_, next) => ([], next)

theorem observe_answer (budget : Nat) (state : Configuration Address Output clients)
    (client : Fin clients) (output : Output) (position : Nat) (address : Address)
    (answer : peek state.log client = .answer position address) :
    observe (budget + 1) state client output =
      (let rest := observe budget (advance state client output).2 client output
       ((position, address) :: rest.1, rest.2)) := by
  simp only [observe, advance_answer state client output position address answer]

theorem observe_stopped (budget : Nat) (state : Configuration Address Output clients)
    (client : Fin clients) (output : Output)
    (stopped : ∀ position address, peek state.log client ≠ .answer position address) :
    observe budget state client output = ([], state) := by
  cases budget with
  | zero => rfl
  | succ budget =>
      cases reply : peek state.log client with
      | answer position address => exact False.elim (stopped position address reply)
      | paused => simp only [observe, advance, prepare, acknowledge, pull, reply]
      | completed => simp only [observe, advance, prepare, acknowledge, pull, reply]
      | cancelled => simp only [observe, advance, prepare, acknowledge, pull, reply]
      | invalid => simp only [observe, advance, prepare, acknowledge, pull, reply]

theorem observe_wellFormed (budget : Nat) (heap : Heap Address Value)
    (state : Configuration Address Output clients) (client : Fin clients) (output : Output)
    (valid : WellFormed heap state) : WellFormed heap (observe budget state client output).2 := by
  induction budget generalizing state with
  | zero => exact valid
  | succ budget ih =>
      cases reply : peek state.log client with
      | answer position address =>
          rw [observe_answer budget state client output position address reply]
          exact ih _ (advance_wellFormed heap state client output valid)
      | paused =>
          rw [observe_stopped _ _ _ _ (by simp [reply])]
          exact valid
      | completed =>
          rw [observe_stopped _ _ _ _ (by simp [reply])]
          exact valid
      | cancelled =>
          rw [observe_stopped _ _ _ _ (by simp [reply])]
          exact valid
      | invalid =>
          rw [observe_stopped _ _ _ _ (by simp [reply])]
          exact valid

theorem observe_log (budget : Nat) (state : Configuration Address Output clients)
    (client : Fin clients) (output : Output) :
    (observe budget state client output).1 = (SharedOccurrenceLog.drain budget state.log client).1 ∧
      (observe budget state client output).2.log = (SharedOccurrenceLog.drain budget state.log client).2 := by
  induction budget generalizing state with
  | zero => exact ⟨rfl, rfl⟩
  | succ budget ih =>
      cases reply : peek state.log client with
      | answer position address =>
          rw [observe_answer budget state client output position address reply,
            SharedOccurrenceLog.drain_answer budget state.log client position address reply]
          have next := ih (advance state client output).2
          simp only [advance_answer state client output position address reply] at next ⊢
          exact ⟨congrArg (List.cons (position, address)) next.1, next.2⟩
      | paused =>
          rw [observe_stopped _ _ _ _ (by simp [reply]),
            SharedOccurrenceLog.drain_stopped _ _ _ (by simp [reply])]
          exact ⟨rfl, rfl⟩
      | completed =>
          rw [observe_stopped _ _ _ _ (by simp [reply]),
            SharedOccurrenceLog.drain_stopped _ _ _ (by simp [reply])]
          exact ⟨rfl, rfl⟩
      | cancelled =>
          rw [observe_stopped _ _ _ _ (by simp [reply]),
            SharedOccurrenceLog.drain_stopped _ _ _ (by simp [reply])]
          exact ⟨rfl, rfl⟩
      | invalid =>
          rw [observe_stopped _ _ _ _ (by simp [reply]),
            SharedOccurrenceLog.drain_stopped _ _ _ (by simp [reply])]
          exact ⟨rfl, rfl⟩

/-- Splitting preserves ordered occurrence delivery and the complete owned
residual, including every published caller root. -/
theorem observe_split (first second : Nat) (state : Configuration Address Output clients)
    (client : Fin clients) (output : Output) :
    observe (first + second) state client output =
      (let earlier := observe first state client output
       let later := observe second earlier.2 client output
       (earlier.1 ++ later.1, later.2)) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, observe, List.nil_append]
  | succ first ih =>
      cases reply : peek state.log client with
      | answer position address =>
          rw [Nat.succ_add, observe_answer _ state client output position address reply,
            observe_answer first state client output position address reply, ih]
          simp only [List.cons_append]
      | paused =>
          have stopped : ∀ p address, peek state.log client ≠ .answer p address := by simp [reply]
          simp only [observe_stopped _ _ _ _ stopped, List.nil_append]
      | completed =>
          have stopped : ∀ p address, peek state.log client ≠ .answer p address := by simp [reply]
          simp only [observe_stopped _ _ _ _ stopped, List.nil_append]
      | cancelled =>
          have stopped : ∀ p address, peek state.log client ≠ .answer p address := by simp [reply]
          simp only [observe_stopped _ _ _ _ stopped, List.nil_append]
      | invalid =>
          have stopped : ∀ p address, peek state.log client ≠ .answer p address := by simp [reply]
          simp only [observe_stopped _ _ _ _ stopped, List.nil_append]

/-- Send every log value and every publication address. Consumer and caller
identities stay, so an owning handle still names the same cursor. -/
def Configuration.map {DestinationAddress : Type} [DecidableEq DestinationAddress]
    (address : Address → DestinationAddress)
    (state : Configuration Address Output clients) :
    Configuration DestinationAddress Output clients :=
  ⟨state.log.map address,
    state.published.image (fun pair => (pair.1, address pair.2))⟩

omit [DecidableEq Address] in
theorem map_log {DestinationAddress : Type} [DecidableEq DestinationAddress]
    (address : Address → DestinationAddress)
    (state : Configuration Address Output clients) :
    (state.map address).log = state.log.map address := rfl

omit [DecidableEq Address] in
theorem map_published {DestinationAddress : Type} [DecidableEq DestinationAddress]
    (address : Address → DestinationAddress)
    (state : Configuration Address Output clients) :
    (state.map address).published =
      state.published.image (fun pair => (pair.1, address pair.2)) := rfl

theorem logRoots_map {DestinationAddress : Type} [DecidableEq DestinationAddress]
    (address : Address → DestinationAddress) (state : State Address clients) :
    logRoots Output (state.map address) =
      (logRoots Output state).image (fun pair => (pair.1, address pair.2)) := by
  ext pair
  rcases pair with ⟨owner, located⟩
  cases owner with
  | inl client =>
      simp only [Finset.mem_image, mem_logRoots_consumer, SharedOccurrenceLog.map_unread,
        List.mem_map]
      constructor
      · rintro ⟨value, held, rfl⟩
        exact ⟨(Sum.inl client, value), (mem_logRoots_consumer state client value).mpr held, rfl⟩
      · rintro ⟨⟨source, value⟩, held, same⟩
        cases source with
        | inl _ =>
            cases same
            exact ⟨value, (mem_logRoots_consumer state client value).mp held, rfl⟩
        | inr caller => exact absurd held (caller_not_in_logRoots state caller value)
  | inr caller =>
      apply iff_of_false
      · exact caller_not_in_logRoots (state.map address) caller located
      · intro held
        simp only [Finset.mem_image] at held
        rcases held with ⟨⟨source, value⟩, member, same⟩
        cases source with
        | inl _ => cases same
        | inr _ =>
            cases same
            exact caller_not_in_logRoots state caller value member

theorem publishedRoots_map {DestinationAddress : Type} [DecidableEq DestinationAddress]
    (address : Address → DestinationAddress) (published : Roots Output Address) :
    publishedRoots (published.image (fun pair => (pair.1, address pair.2))) =
      (publishedRoots (clients := clients) published).image
        (fun pair => (pair.1, address pair.2)) := by
  simp only [publishedRoots, Finset.image_image]
  rfl

/-- Mapped unread rows and mapped publication addresses are the image of the
old delivery roots. The carrier fields are the log and the publication set. -/
theorem map_roots {DestinationAddress : Type} [DecidableEq DestinationAddress]
    (address : Address → DestinationAddress)
    (state : Configuration Address Output clients) :
    roots (state.map address) =
      (roots state).image (fun pair => (pair.1, address pair.2)) := by
  simp only [roots, Configuration.map, Finset.image_union, logRoots_map, publishedRoots_map]

theorem map_id (state : Configuration Address Output clients) : state.map id = state := by
  cases state with
  | mk log published =>
      simp only [Configuration.map, SharedOccurrenceLog.map_id]
      congr 1
      ext pair
      simp only [Finset.mem_image, Prod.exists]
      constructor
      · rintro ⟨owner, located, member, rfl⟩
        exact member
      · intro member
        exact ⟨pair.1, pair.2, member, by cases pair; rfl⟩

namespace Controls

open Mettapedia.Machines.ResourceOwnership (rootAddresses census ValidRoots mem_census_iff_live
  lookup_collect_of_not_live not_live_empty)
open Mettapedia.Machines.ResourceOwnership.Examples (cyclicHeap cyclicCell)

/-- The two answer occurrences share node 0, which reaches the 1 -> 2 -> 1 cycle. -/
def sharedCycle : Configuration (Fin 3) Nat 2 :=
  ⟨⟨0, [0, 0], fun _ => some 0, false, 3⟩, ∅⟩

/-- Shared graph addresses do not couple distinct occurrence cursors. -/
theorem owned_deliveries_commute_with_shared_addresses :
    (let left := advance sharedCycle 0 7
     let right := advance left.2 1 8
     (left.1, right.1, right.2)) =
      (let right := advance sharedCycle 1 8
       let left := advance right.2 0 7
       (left.1, right.1, left.2)) :=
  advance_commute sharedCycle 0 1 7 8 (by decide)

/-- Equal payloads still have distinct delivery occurrences; sharing a cursor
does not satisfy the distinct-consumer commutation premise. -/
theorem one_cursor_cannot_reorder_equal_payload_occurrences :
    (advance sharedCycle 0 7).1 = .answer 0 0 ∧
      (advance (advance sharedCycle 0 8).2 0 7).1 = .answer 1 0 ∧
      (advance sharedCycle 0 7).1 ≠ (advance (advance sharedCycle 0 8).2 0 7).1 := by
  decide

theorem sharedCycle_valid : Valid sharedCycle.log := by
  simp [Valid, sharedCycle, SharedOccurrenceLog.pastEnd]

theorem duplicate_occurrences_share_one_resource_graph :
    rootAddresses (logRoots Nat sharedCycle.log) = {0} ∧
      (SharedOccurrenceLog.drain 2 sharedCycle.log 0).1 = [(0, 0), (1, 0)] := by decide

def delivered : Configuration (Fin 3) Nat 2 := (advance sharedCycle 0 7).2

theorem delivered_valid : Valid delivered.log := advance_valid sharedCycle 0 7 sharedCycle_valid

/-- Both consumers may disappear while the caller continues holding the exported answer. -/
def consumersGone : Configuration (Fin 3) Nat 2 :=
  trimLog (cancelConsumer (cancelConsumer delivered 0) 1)

theorem both_consumers_gone_caller_retains_the_cycle (location : Fin 3) :
    (collect cyclicHeap (roots consumersGone)).lookup location = cyclicHeap.lookup location := by
  have valid : ValidRoots cyclicHeap (publishedRoots (clients := 2) delivered.published) := by
    intro pair _
    exact Finset.mem_univ _
  have all : ∀ address : Fin 3,
      address ∈ census cyclicHeap (publishedRoots (clients := 2) delivered.published) := by decide
  have live := (mem_census_iff_live cyclicHeap _ valid location).mp (all location)
  exact cancel_trim_retains_published_graph cyclicHeap (cancelConsumer delivered 0) 1
    (SharedOccurrenceLog.cancel_valid delivered.log 0 delivered_valid) location live

theorem cancellation_keeps_the_other_consumers_cycle (location : Fin 3) :
    (collect cyclicHeap (roots (trimLog (cancelConsumer sharedCycle 0)))).lookup location =
      cyclicHeap.lookup location := by
  have valid : ValidRoots cyclicHeap
      (answerRoots (Sum.inl (1 : Fin 2) : Sum (Fin 2) Nat) (unread sharedCycle.log 1)) := by
    intro pair _
    exact Finset.mem_univ _
  have all : ∀ address : Fin 3, address ∈ census cyclicHeap
      (answerRoots (Sum.inl (1 : Fin 2) : Sum (Fin 2) Nat) (unread sharedCycle.log 1)) := by decide
  have live := (mem_census_iff_live cyclicHeap _ valid location).mp (all location)
  exact cancel_trim_retains_other_unread_graph cyclicHeap sharedCycle 0 1 sharedCycle_valid
    (by decide) location live

/-- Acknowledgment without publication leaves no owner after both consumers cancel. -/
def unpublished : Configuration (Fin 3) Nat 2 := ⟨(pull sharedCycle.log 0).2, ∅⟩

theorem acknowledgment_without_publication_loses_the_answer :
    (collect cyclicHeap (roots (trimLog (cancelConsumer (cancelConsumer unpublished 0) 1)))).lookup 0 ≠
      cyclicHeap.lookup 0 := by
  have empty : roots (trimLog (cancelConsumer (cancelConsumer unpublished 0) 1)) = ∅ := by decide
  rw [empty, lookup_collect_of_not_live cyclicHeap ∅ (not_live_empty cyclicHeap 0)]
  simp [cyclicHeap]

def singleConsumer : Configuration (Fin 3) Nat 1 :=
  ⟨⟨0, [0], fun _ => some 0, false, 1⟩, ∅⟩

theorem singleConsumer_wellFormed : WellFormed cyclicHeap singleConsumer := by
  constructor
  · simp [Valid, singleConsumer, SharedOccurrenceLog.pastEnd]
  · intro pair _
    exact Finset.mem_univ _

def dangling : Configuration Nat Nat 1 := ⟨⟨0, [1], fun _ => some 0, false, 1⟩, ∅⟩

theorem valid_cursor_does_not_certify_allocated_answers :
    Valid dangling.log ∧ ¬ WellFormed (ResourceOwnership.Examples.chainHeap 0) dangling := by
  constructor
  · simp [Valid, dangling, SharedOccurrenceLog.pastEnd]
  · intro valid
    have rooted : (Sum.inl (0 : Fin 1), (1 : Nat)) ∈ roots dangling := by decide
    have allocated := valid.2 _ rooted
    have absent : (1 : Nat) ∉ (ResourceOwnership.Examples.chainHeap 0).allocated := by decide
    exact absent allocated

theorem publishing_before_acknowledgment_allows_intermediate_collection :
    WellFormed (collect cyclicHeap (roots (prepare singleConsumer 0 7)))
      (advance singleConsumer 0 7).2 :=
  collection_between_publication_and_acknowledgment cyclicHeap singleConsumer 0 7
    singleConsumer_wellFormed

theorem acknowledging_first_exposes_the_answer_to_collection :
    (collect cyclicHeap (roots (acknowledge singleConsumer 0).2)).lookup 0 ≠
      cyclicHeap.lookup 0 := by
  have empty : roots (acknowledge singleConsumer 0).2 = ∅ := by decide
  rw [empty, lookup_collect_of_not_live cyclicHeap ∅ (not_live_empty cyclicHeap 0)]
  simp [cyclicHeap]

theorem releasing_the_final_caller_reclaims_the_cycle (location : Fin 3) :
    (collect cyclicHeap (roots (releaseCaller consumersGone 7))).lookup location = none := by
  have empty : roots (releaseCaller consumersGone 7) = ∅ := by decide
  rw [empty]
  exact lookup_collect_of_not_live cyclicHeap ∅ (not_live_empty cyclicHeap location)

theorem owned_split_retains_duplicate_delivery_and_publications :
    (observe 8 sharedCycle 0 7).1 = [(0, 0), (1, 0)] ∧
      (observe 8 sharedCycle 0 7).2.published = {(7, 0)} ∧
      observe 8 sharedCycle 0 7 =
        (let earlier := observe 1 sharedCycle 0 7
         let later := observe 7 earlier.2 0 7
         (earlier.1 ++ later.1, later.2)) := by
  exact ⟨by decide, by decide, observe_split 1 7 sharedCycle 0 7⟩

end Controls

end Mettapedia.Machines.Cursor.SharedOccurrenceOwnership
