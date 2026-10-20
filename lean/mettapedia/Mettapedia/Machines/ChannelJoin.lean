import Mettapedia.Machines.EventPump
import Mettapedia.Machines.RevisionedOccurrenceStore
import Mettapedia.GSLT.Causality.ResourceWaves
import Mettapedia.GSLT.Causality.ResourceRuns
import Mettapedia.GSLT.LanguageDef.NativeControlCursor
import Mettapedia.Machines.ResourceOwnership
import Mettapedia.Machines.Cursor.ReadOnlyQuery
import Mettapedia.GSLT.Contracts.IndexedAuthority

/-!
Adapted from godelclaw/MeTTapedia commit
562e3c8af4be9f2984bf7783eb71771ce9417d2a.

# Atomic channel joins over distinct message occurrences

RSpace separates stored data, stored receive continuations and runnable matched
work. This contract models that boundary: a candidate must provide one distinct
occurrence for each pattern, on the correct channel. Validation is independent
of the candidate finder. Successful commitment removes all selected data and
publishes the entire continuation/input tuple in one state transition.

Occurrence serials are unique within this store. Equal payloads are not equal
occurrences. A one-shot continuation is retired; a persistent continuation can
react again but must obtain fresh data. A nonempty join always spends at least
one occurrence. This is a semantic COMM contract, not a verification of a
particular tuple-space matcher, pattern language or storage implementation.

https://rholang.github.io/docs/rspace-intro/
-/

namespace Mettapedia.Machines.ChannelJoin

abbrev Occurrence := EventPump.Event

structure Pattern where
  channel : EventPump.Key
  accepts : Nat → Bool

def patternMatches (p : Pattern) (event : Occurrence) : Bool :=
  decide (p.channel = event.owner) && p.accepts event.payload

def matchesAll : List Pattern → List Occurrence → Bool
  | [], [] => true
  | p :: ps, e :: es => patternMatches p e && matchesAll ps es
  | _, _ => false

theorem matched_lists_have_equal_length (patterns : List Pattern) (events : List Occurrence)
    (h : matchesAll patterns events = true) : patterns.length = events.length := by
  induction patterns generalizing events with
  | nil => cases events <;> simp_all [matchesAll]
  | cons p ps ih =>
    cases events with
    | nil => simp [matchesAll] at h
    | cons e es =>
      have pair : patternMatches p e = true ∧ matchesAll ps es = true := by
        simpa only [matchesAll, Bool.and_eq_true_iff] using h
      simpa using ih es pair.2

theorem matched_inputs_obey_channels_and_filters (patterns : List Pattern)
    (events : List Occurrence) (h : matchesAll patterns events = true)
    (p : Pattern) (e : Occurrence) (paired : (p, e) ∈ patterns.zip events) :
    p.channel = e.owner ∧ p.accepts e.payload = true := by
  induction patterns generalizing events with
  | nil => simp at paired
  | cons head tail ih =>
    cases events with
    | nil => simp at paired
    | cons event rest =>
      have matched : patternMatches head event = true ∧ matchesAll tail rest = true := by
        simpa only [matchesAll, Bool.and_eq_true_iff] using h
      simp only [List.zip_cons_cons, List.mem_cons] at paired
      rcases paired with same | later
      · cases same
        simpa [patternMatches] using matched.1
      · exact ih rest matched.2 later

structure Continuation where
  patterns : List Pattern
  persistent : Bool := false

structure Reaction where
  continuation : Nat
  inputs : List Occurrence
  deriving DecidableEq, Repr

structure Space where
  produced : List Occurrence := []
  available : List Occurrence := []
  spent : List Nat := []
  receives : Nat → Option Continuation := fun _ => none
  registered : List Nat := []
  ready : List Reaction := []

def produce (s : Space) (e : Occurrence) : Space :=
  if e.serial ∈ s.produced.map EventPump.Event.serial then s
  else { s with produced := s.produced ++ [e], available := s.available ++ [e] }

def register (s : Space) (id : Nat) (continuation : Continuation) : Space :=
  if id ∈ s.registered then s
  else { s with registered := s.registered ++ [id]
                receives := fun other => if other = id then some continuation else s.receives other }

def valid (s : Space) (continuation : Continuation) (selected : List Occurrence) : Prop :=
  selected ≠ [] ∧
  matchesAll continuation.patterns selected = true ∧
  (selected.map EventPump.Event.serial).Nodup ∧
  ∀ e ∈ selected, e ∈ s.available ∧ e.serial ∉ s.spent

instance (s : Space) (c : Continuation) (selected : List Occurrence) :
    Decidable (valid s c selected) := by unfold valid; infer_instance

def commit (s : Space) (id : Nat) (selected : List Occurrence) : Space :=
  match s.receives id with
  | none => s
  | some continuation =>
    if valid s continuation selected then
      { s with available := s.available.filter (fun e => decide (e ∉ selected))
               spent := s.spent ++ selected.map EventPump.Event.serial
               receives := if continuation.persistent then s.receives else
                 fun other => if other = id then none else s.receives other
               ready := s.ready ++ [⟨id, selected⟩] }
    else s

/-- Every accepted occurrence is either available or retained in a published
reaction. The produced ledger also keeps its original payload. -/
def conserved (s : Space) : Prop :=
  ∀ e ∈ s.produced, e ∈ s.available ∨ ∃ r ∈ s.ready, e ∈ r.inputs

theorem duplicate_produce_keeps_first_payload (s : Space) (e : Occurrence) :
    produce (produce s e) e = produce s e := by
  by_cases h : e.serial ∈ s.produced.map EventPump.Event.serial
  · simp [produce, h]
  · simp [produce, h]

theorem registration_cannot_reuse_identity (s : Space) (id : Nat)
    (first second : Continuation) :
    register (register s id first) id second = register s id first := by
  by_cases h : id ∈ s.registered
  · simp [register, h]
  · simp [register, h]

theorem valid_join_has_one_occurrence_per_pattern (s : Space) (c : Continuation)
    (selected : List Occurrence) (h : valid s c selected) :
    c.patterns.length = selected.length ∧ (selected.map EventPump.Event.serial).Nodup := by
  exact ⟨matched_lists_have_equal_length c.patterns selected h.2.1, h.2.2.1⟩

theorem successful_join_is_atomic (s : Space) (id : Nat) (c : Continuation)
    (selected : List Occurrence) (registered : s.receives id = some c)
    (h : valid s c selected) :
    (commit s id selected).available = s.available.filter (fun e => decide (e ∉ selected)) ∧
    (commit s id selected).spent = s.spent ++ selected.map EventPump.Event.serial ∧
    (commit s id selected).ready = s.ready ++ [⟨id, selected⟩] := by
  simp [commit, registered, h]

theorem invalid_join_cannot_partially_consume (s : Space) (id : Nat) (c : Continuation)
    (selected : List Occurrence) (registered : s.receives id = some c)
    (h : ¬ valid s c selected) : commit s id selected = s := by
  simp [commit, registered, h]

theorem successful_join_consumes_selected (s : Space) (id : Nat) (c : Continuation)
    (selected : List Occurrence) (registered : s.receives id = some c)
    (h : valid s c selected) (e : Occurrence) (chosen : e ∈ selected) :
    e ∉ (commit s id selected).available := by
  simp [commit, registered, h, chosen]

theorem join_preserves_unselected_data (s : Space) (id : Nat) (selected : List Occurrence)
    (e : Occurrence) (notChosen : e ∉ selected) :
    e ∈ (commit s id selected).available ↔ e ∈ s.available := by
  simp only [commit]
  split
  · rfl
  · split
    · simp [notChosen]
    · rfl

theorem join_preserves_other_receives (s : Space) (id other : Nat)
    (selected : List Occurrence) (different : other ≠ id) :
    (commit s id selected).receives other = s.receives other := by
  simp only [commit]
  split
  · rfl
  · split
    · split <;> simp_all
    · rfl

theorem one_shot_receive_is_retired (s : Space) (id : Nat) (c : Continuation)
    (selected : List Occurrence) (registered : s.receives id = some c)
    (h : valid s c selected) (single : c.persistent = false) :
    (commit s id selected).receives id = none := by
  simp [commit, registered, h, single]

theorem persistent_receive_keeps_waiting (s : Space) (id : Nat) (c : Continuation)
    (selected : List Occurrence) (registered : s.receives id = some c)
    (h : valid s c selected) (persistent : c.persistent = true) :
    (commit s id selected).receives id = some c := by
  simp [commit, registered, h, persistent]

/-- Persistence of the receiver never means persistence of the consumed send. -/
theorem consumed_occurrence_cannot_react_again (s : Space) (id : Nat) (c next : Continuation)
    (selected candidate : List Occurrence) (registered : s.receives id = some c)
    (h : valid s c selected) (e : Occurrence)
    (chosen : e ∈ selected) (reused : e ∈ candidate) :
    ¬ valid (commit s id selected) next candidate := by
  intro again
  have spent := (again.2.2.2 e reused).2
  apply spent
  simp only [commit, registered, if_pos h]
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨e, chosen, rfl⟩

/-- Disjoint joins retain admission when their receivers are distinct or the
shared receiver persists. This is channel noninterference, not commutativity
of arbitrary external effects. -/
theorem independent_join_remains_enabled (s : Space) (id other : Nat)
    (first second : Continuation) (selected candidate : List Occurrence)
    (firstRegistered : s.receives id = some first)
    (secondRegistered : s.receives other = some second)
    (firstValid : valid s first selected) (secondValid : valid s second candidate)
    (receiverIndependent : other ≠ id ∨ first.persistent = true)
    (disjoint : ∀ e ∈ candidate, e.serial ∉ selected.map EventPump.Event.serial) :
    (commit s id selected).receives other = some second ∧
    valid (commit s id selected) second candidate := by
  refine ⟨?_, secondValid.1, secondValid.2.1, secondValid.2.2.1, ?_⟩
  · rcases receiverIndependent with different | persistent
    · rw [join_preserves_other_receives s id other selected different]
      exact secondRegistered
    · simpa only [commit, firstRegistered, if_pos firstValid, persistent, ↓reduceIte]
        using secondRegistered
  · intro e member
    have fresh := disjoint e member
    have notSelected : e ∉ selected := by
      intro chosen
      exact fresh (List.mem_map.mpr ⟨e, chosen, rfl⟩)
    refine ⟨(join_preserves_unselected_data s id selected e notSelected).mpr
      (secondValid.2.2.2 e member).1, ?_⟩
    rw [(successful_join_is_atomic s id first selected firstRegistered firstValid).2.1]
    simpa only [List.mem_append, not_or] using
      And.intro (secondValid.2.2.2 e member).2 fresh

/-- Disjoint committed joins have the same remaining store and receive table.
Only the order of their occurrence ledger and published reactions changes.
This permits a bag observation, not an ordered stream or arbitrary effects. -/
theorem independent_joins_commute_modulo_publication_order (s : Space) (id other : Nat)
    (first second : Continuation) (selected candidate : List Occurrence)
    (firstRegistered : s.receives id = some first)
    (secondRegistered : s.receives other = some second)
    (firstValid : valid s first selected) (secondValid : valid s second candidate)
    (receiverIndependent : other ≠ id ∨ first.persistent = true)
    (disjoint : ∀ e ∈ candidate, e.serial ∉ selected.map EventPump.Event.serial) :
    let forward := commit (commit s id selected) other candidate
    let reverse := commit (commit s other candidate) id selected
    forward.produced = reverse.produced ∧
    forward.available = reverse.available ∧
    forward.spent.Perm reverse.spent ∧
    forward.receives = reverse.receives ∧
    forward.registered = reverse.registered ∧
    forward.ready.Perm reverse.ready := by
  have reverseDisjoint : ∀ e ∈ selected, e.serial ∉ candidate.map EventPump.Event.serial := by
    intro e chosen member
    obtain ⟨otherEvent, member, same⟩ := List.mem_map.mp member
    apply disjoint otherEvent member
    exact List.mem_map.mpr ⟨e, chosen, same.symm⟩
  have reverseIndependent : id ≠ other ∨ second.persistent = true := by
    by_cases same : id = other
    · have sameReceiver : first = second := by
        apply Option.some.inj
        rw [← firstRegistered, ← secondRegistered, same]
      rcases receiverIndependent with different | persistent
      · exact False.elim (different same.symm)
      · exact Or.inr (sameReceiver ▸ persistent)
    · exact Or.inl same
  have afterFirst := independent_join_remains_enabled s id other first second
    selected candidate firstRegistered secondRegistered firstValid secondValid receiverIndependent disjoint
  have afterSecond := independent_join_remains_enabled s other id second first
    candidate selected secondRegistered firstRegistered secondValid firstValid
    reverseIndependent reverseDisjoint
  dsimp only
  simp only [commit, firstRegistered, firstValid, ↓reduceIte] at afterFirst
  simp only [commit, secondRegistered, secondValid, ↓reduceIte] at afterSecond
  simp only [commit, firstRegistered, firstValid, secondRegistered, secondValid,
    afterFirst.1, afterFirst.2, afterSecond.1, afterSecond.2, ↓reduceIte]
  refine ⟨trivial, ?_, ?_, ?_, trivial, ?_⟩
  · rw [List.filter_filter, List.filter_filter]
    congr 1
    funext event
    exact Bool.and_comm _ _
  · simpa only [List.append_assoc] using
      (List.perm_append_comm : (selected.map EventPump.Event.serial ++
        candidate.map EventPump.Event.serial).Perm
        (candidate.map EventPump.Event.serial ++ selected.map EventPump.Event.serial)).append_left s.spent
  · funext key
    split <;> split <;> by_cases left : key = id <;>
      by_cases right : key = other <;> simp_all
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      (List.Perm.swap (Reaction.mk other candidate) (Reaction.mk id selected) []).append_left s.ready

section WaveAdmission

open Mettapedia.GSLT.Causality.ResourceInteraction

/-- A send is claimed by its occurrence serial. A receiver has a distinct
identity, even when both numbers coincide. -/
inductive Resource where
  | send (serial : Nat)
  | receive (id : Nat)
  deriving DecidableEq

/-- Available unspent occurrences and live registered receivers, with one
unit of capacity per identity. This is a finite semantic snapshot, not a
claim about the cost of extracting native matcher footprints. -/
def resourceSnapshot (s : Space) : Finset Resource :=
  ((s.available.filter fun e => decide (e.serial ∉ s.spent)).map
      (fun e => Resource.send e.serial)).toFinset ∪
    ((s.registered.filter fun id => (s.receives id).isSome).map Resource.receive).toFinset

/-- Every selected send is consumed. Persistent receivers are shared reads;
one-shot receivers are consumed. Selected multiplicity is retained.
Pattern validation is a separate prerequisite for committing this demand. -/
def joinDemand (id : Nat) (c : Continuation) (selected : List Occurrence) :
    WaveDemand Resource :=
  ⟨(selected.map (fun e => Resource.send e.serial) : Multiset Resource) +
      (if c.persistent then 0 else {Resource.receive id}),
    if c.persistent then {Resource.receive id} else 0⟩

theorem mem_resourceSnapshot_send (s : Space) (serial : Nat) :
    Resource.send serial ∈ resourceSnapshot s ↔
      ∃ e ∈ s.available, e.serial = serial ∧ serial ∉ s.spent := by
  simp only [resourceSnapshot, Finset.mem_union, List.mem_toFinset, List.mem_map,
    List.mem_filter, decide_eq_true_eq, Resource.send.injEq]
  constructor
  · rintro (⟨e, ⟨available, unspent⟩, rfl⟩ | ⟨id, _, impossible⟩)
    · exact ⟨e, available, rfl, unspent⟩
    · cases impossible
  · rintro ⟨e, available, rfl, unspent⟩
    exact Or.inl ⟨e, ⟨available, unspent⟩, rfl⟩

theorem mem_resourceSnapshot_receive (s : Space) (id : Nat) :
    Resource.receive id ∈ resourceSnapshot s ↔ id ∈ s.registered ∧ (s.receives id).isSome := by
  simp [resourceSnapshot]

private theorem send_count (selected : List Occurrence) (serial : Nat) :
    (selected.map (fun e => Resource.send e.serial)).count
      (.send serial) = (selected.map EventPump.Event.serial).count serial := by
  simpa only [List.map_map, Function.comp_def] using
    List.count_map_of_injective (selected.map EventPump.Event.serial)
      Resource.send (fun _ _ equal => Resource.send.inj equal) serial

private theorem resource_count (s : Space) (resource : Resource) :
    (resourceSnapshot s).val.count resource = if resource ∈ resourceSnapshot s then 1 else 0 := by
  split_ifs with member
  · exact Multiset.count_eq_one_of_mem (resourceSnapshot s).nodup member
  · exact Multiset.count_eq_zero.mpr member

private theorem valid_send_count (s : Space) (c : Continuation) (selected : List Occurrence)
    (admitted : valid s c selected) (serial : Nat) :
    (selected.map EventPump.Event.serial).count serial =
      if serial ∈ selected.map EventPump.Event.serial then 1 else 0 := by
  split_ifs with member
  · exact List.count_eq_one_of_mem admitted.2.2.1 member
  · exact List.count_eq_zero.mpr member

private theorem valid_send_resource (s : Space) (c : Continuation) (selected : List Occurrence)
    (admitted : valid s c selected) (serial : Nat)
    (member : serial ∈ selected.map EventPump.Event.serial) :
    Resource.send serial ∈ resourceSnapshot s := by
  obtain ⟨e, selected, rfl⟩ := List.mem_map.mp member
  exact (mem_resourceSnapshot_send s e.serial).mpr
    ⟨e, (admitted.2.2.2 e selected).1, rfl, (admitted.2.2.2 e selected).2⟩

private theorem joinDemand_send_counts (id : Nat) (c : Continuation) (selected : List Occurrence)
    (serial : Nat) :
    (joinDemand id c selected).consume.count (.send serial) =
        (selected.map EventPump.Event.serial).count serial ∧
    (joinDemand id c selected).read.count (.send serial) = 0 := by
  cases persistent : c.persistent <;> simp [joinDemand, persistent, send_count]

private theorem joinDemand_receive_counts (id : Nat) (c : Continuation) (selected : List Occurrence)
    (other : Nat) :
    (joinDemand id c selected).consume.count (.receive other) =
        (if other = id ∧ c.persistent = false then 1 else 0) ∧
    (joinDemand id c selected).read.count (.receive other) =
        (if other = id ∧ c.persistent = true then 1 else 0) := by
  cases persistent : c.persistent <;> simp [joinDemand, persistent, Multiset.count_singleton]

/-- For two valid candidates, the common resource checker admits exactly
disjoint send occurrences with distinct receivers or one persistent receiver.
Patterns here are pure payload predicates; this does not justify reordering
guards that read mutable state, external effects, or ordered publication. -/
theorem pair_demand_fits_iff (s : Space) (id other : Nat)
    (first second : Continuation) (selected candidate : List Occurrence)
    (firstRegistered : s.receives id = some first)
    (secondRegistered : s.receives other = some second)
    (firstListed : id ∈ s.registered) (secondListed : other ∈ s.registered)
    (firstValid : valid s first selected) (secondValid : valid s second candidate) :
    ((joinDemand id first selected).reserve (joinDemand other second candidate).consume
      (joinDemand other second candidate).read).Fits (resourceSnapshot s).val ↔
    (other ≠ id ∨ first.persistent = true) ∧
      (∀ e ∈ candidate, e.serial ∉ selected.map EventPump.Event.serial) := by
  have sameReceiver : id = other → first = second := by
    intro same
    apply Option.some.inj
    rw [← firstRegistered, ← secondRegistered, same]
  rw [WaveDemand.reserve_fits_iff_count]
  constructor
  · intro fits
    constructor
    · by_cases different : other ≠ id
      · exact Or.inl different
      · have same : other = id := by simpa using different
        have sameContinuation := sameReceiver same.symm
        subst other
        subst second
        have bound := fits (.receive id)
        rw [(joinDemand_receive_counts id first selected id).1,
          (joinDemand_receive_counts id first selected id).2,
          (joinDemand_receive_counts id first candidate id).1,
          (joinDemand_receive_counts id first candidate id).2] at bound
        have capacity := Multiset.nodup_iff_count_le_one.mp (resourceSnapshot s).nodup (.receive id)
        cases persistent : first.persistent with
        | false => simp [persistent] at bound; omega
        | true => exact Or.inr rfl
    · intro e member repeated
      have inCandidate : e.serial ∈ candidate.map EventPump.Event.serial :=
        List.mem_map.mpr ⟨e, member, rfl⟩
      have bound := fits (.send e.serial)
      rw [(joinDemand_send_counts id first selected e.serial).1,
        (joinDemand_send_counts id first selected e.serial).2,
        (joinDemand_send_counts other second candidate e.serial).1,
        (joinDemand_send_counts other second candidate e.serial).2,
        valid_send_count s first selected firstValid,
        valid_send_count s second candidate secondValid,
        if_pos repeated, if_pos inCandidate] at bound
      have capacity := Multiset.nodup_iff_count_le_one.mp (resourceSnapshot s).nodup (.send e.serial)
      omega
  · rintro ⟨independent, disjoint⟩ resource
    cases resource with
    | send serial =>
        rw [(joinDemand_send_counts id first selected serial).1,
          (joinDemand_send_counts id first selected serial).2,
          (joinDemand_send_counts other second candidate serial).1,
          (joinDemand_send_counts other second candidate serial).2,
          valid_send_count s first selected firstValid,
          valid_send_count s second candidate secondValid, resource_count]
        by_cases left : serial ∈ selected.map EventPump.Event.serial
        · have right : serial ∉ candidate.map EventPump.Event.serial := by
            rintro member
            obtain ⟨e, chosen, same⟩ := List.mem_map.mp member
            exact disjoint e chosen (same ▸ left)
          simp [left, right, valid_send_resource s first selected firstValid serial left]
        · by_cases right : serial ∈ candidate.map EventPump.Event.serial
          · simp [left, right, valid_send_resource s second candidate secondValid serial right]
          · simp [left, right]
    | receive key =>
        rw [(joinDemand_receive_counts id first selected key).1,
          (joinDemand_receive_counts id first selected key).2,
          (joinDemand_receive_counts other second candidate key).1,
          (joinDemand_receive_counts other second candidate key).2, resource_count]
        have leftResource : Resource.receive id ∈ resourceSnapshot s := by
          rw [mem_resourceSnapshot_receive]
          exact ⟨firstListed, by simp [firstRegistered]⟩
        have rightResource : Resource.receive other ∈ resourceSnapshot s := by
          rw [mem_resourceSnapshot_receive]
          exact ⟨secondListed, by simp [secondRegistered]⟩
        by_cases left : key = id <;> by_cases right : key = other
        · have same : id = other := left.symm.trans right
          have sameContinuation := sameReceiver same
          subst second
          have persistent : first.persistent = true := by
            rcases independent with different | persistent
            · exact False.elim (different same.symm)
            · exact persistent
          subst key
          subst other
          simp [persistent, leftResource]
        · subst key
          cases first.persistent <;> simp [right, leftResource]
        · subst key
          cases second.persistent <;> simp [left, rightResource]
        · simp [left, right]

/-- The generic wave checker supplies exactly the independence obligations
needed by the channel commit theorem. Candidate validation remains separate. -/
theorem admitted_joins_commute_modulo_publication_order (s : Space) (id other : Nat)
    (first second : Continuation) (selected candidate : List Occurrence)
    (firstRegistered : s.receives id = some first)
    (secondRegistered : s.receives other = some second)
    (firstListed : id ∈ s.registered) (secondListed : other ∈ s.registered)
    (firstValid : valid s first selected) (secondValid : valid s second candidate)
    (admitted : ((joinDemand id first selected).reserve
      (joinDemand other second candidate).consume
      (joinDemand other second candidate).read).Fits (resourceSnapshot s).val) :
    let forward := commit (commit s id selected) other candidate
    let reverse := commit (commit s other candidate) id selected
    forward.produced = reverse.produced ∧
    forward.available = reverse.available ∧
    forward.spent.Perm reverse.spent ∧
    forward.receives = reverse.receives ∧
    forward.registered = reverse.registered ∧
    forward.ready.Perm reverse.ready := by
  have independent := (pair_demand_fits_iff s id other first second selected candidate
    firstRegistered secondRegistered firstListed secondListed firstValid secondValid).mp admitted
  exact independent_joins_commute_modulo_publication_order s id other first second selected candidate
    firstRegistered secondRegistered firstValid secondValid independent.1 independent.2

/-- Successful commitment removes exactly the claimed send identities and,
for a one-shot continuation, its receive identity. Persistent reads remain. -/
theorem resourceSnapshot_commit (s : Space) (id : Nat) (c : Continuation)
    (selected : List Occurrence) (registered : s.receives id = some c)
    (admitted : valid s c selected) :
    resourceSnapshot (commit s id selected) =
      resourceSnapshot s \ (joinDemand id c selected).consume.toFinset := by
  ext resource
  cases resource with
  | send serial =>
      rw [mem_resourceSnapshot_send, Finset.mem_sdiff, mem_resourceSnapshot_send]
      have consumed : Resource.send serial ∈ (joinDemand id c selected).consume.toFinset ↔
          serial ∈ selected.map EventPump.Event.serial := by
        cases persistent : c.persistent <;> simp [joinDemand, persistent]
      rw [consumed]
      simp only [commit, registered, if_pos admitted]
      constructor
      · rintro ⟨e, available, same, fresh⟩
        have old := (List.mem_filter.mp available).1
        simp only [List.mem_append, not_or] at fresh
        exact ⟨⟨e, old, same, fresh.1⟩, fresh.2⟩
      · rintro ⟨⟨e, available, same, fresh⟩, unselected⟩
        have notChosen : e ∉ selected := by
          intro member
          exact unselected (List.mem_map.mpr ⟨e, member, same⟩)
        exact ⟨e, List.mem_filter.mpr ⟨available, by simpa using notChosen⟩, same,
          by simpa only [List.mem_append, not_or] using And.intro fresh unselected⟩
  | receive key =>
      rw [mem_resourceSnapshot_receive, Finset.mem_sdiff, mem_resourceSnapshot_receive]
      have consumed : Resource.receive key ∈ (joinDemand id c selected).consume.toFinset ↔
          key = id ∧ c.persistent = false := by
        cases persistent : c.persistent <;> simp [joinDemand, persistent]
      rw [consumed]
      cases persistent : c.persistent <;> by_cases same : key = id <;>
        simp [commit, registered, admitted, persistent, same]

private theorem joinDemand_consume_nodup (s : Space) (c : Continuation)
    (selected : List Occurrence) (admitted : valid s c selected) (id : Nat) :
    (joinDemand id c selected).consume.Nodup := by
  have sends : (selected.map (fun e => Resource.send e.serial) : Multiset Resource).Nodup := by
    simpa only [Multiset.coe_nodup, List.map_map, Function.comp_def] using
      admitted.2.2.1.map (fun _ _ equal => Resource.send.inj equal)
  cases persistent : c.persistent <;>
    simp [joinDemand, persistent, Multiset.nodup_add, sends]

/-- A validated commit has exactly the projected resource effect: subtract
its consumption, retaining persistent reads. The reaction queue is accounted
for separately and is not erased by this statement about resource projection. -/
theorem commit_resource_account (s : Space) (id : Nat) (c : Continuation)
    (selected : List Occurrence) (registered : s.receives id = some c)
    (admitted : valid s c selected) :
    (resourceSnapshot (commit s id selected)).val =
      (resourceSnapshot s).val - (joinDemand id c selected).consume := by
  rw [resourceSnapshot_commit s id c selected registered admitted, Finset.sdiff_val]
  congr 1
  exact Multiset.dedup_eq_self.mpr (joinDemand_consume_nodup s c selected admitted id)

end WaveAdmission

theorem produce_preserves_conservation (s : Space) (e : Occurrence)
    (h : conserved s) : conserved (produce s e) := by
  simp only [produce]
  split
  · exact h
  · intro other member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · rcases h other old with available | ⟨reaction, ready, used⟩
      · exact Or.inl (List.mem_append_left _ available)
      · exact Or.inr ⟨reaction, ready, used⟩
    · exact Or.inl (by simp)

theorem commit_preserves_conservation (s : Space) (id : Nat) (selected : List Occurrence)
    (h : conserved s) : conserved (commit s id selected) := by
  simp only [commit]
  split
  · exact h
  · split
    · intro e member
      rcases h e member with available | ⟨r, ready, used⟩
      · by_cases chosen : e ∈ selected
        · exact Or.inr ⟨⟨id, selected⟩, by simp, chosen⟩
        · exact Or.inl (List.mem_filter.mpr ⟨available, by simp [chosen]⟩)
      · exact Or.inr ⟨r, List.mem_append_left _ ready, used⟩
    · exact h

inductive Action where
  | produce (event : Occurrence)
  | register (id : Nat) (continuation : Continuation)
  | react (id : Nat) (candidate : List Occurrence)

def step (s : Space) : Action → Space
  | .produce e => produce s e
  | .register id c => register s id c
  | .react id selected => commit s id selected

def run : List Action → Space → Space
  | [], s => s
  | action :: rest, s => run rest (step s action)

theorem spent_occurrence_stays_spent (s : Space) (a : Action) (id : Nat)
    (h : id ∈ s.spent) : id ∈ (step s a).spent := by
  cases a with
  | produce e => simp only [step, produce]; split <;> exact h
  | register serial c => simp only [step, register]; split <;> exact h
  | react serial candidate =>
    simp only [step, commit]
    split
    · exact h
    · split
      · exact List.mem_append_left _ h
      · exact h

theorem trace_cannot_recycle_spent_occurrences (s : Space) (actions : List Action)
    (id : Nat) (spent : id ∈ s.spent) (next : Continuation)
    (candidate : List Occurrence) (e : Occurrence)
    (chosen : e ∈ candidate) (same : e.serial = id) :
    ¬ valid (run actions s) next candidate := by
  have retained : id ∈ (run actions s).spent := by
    induction actions generalizing s with
    | nil => exact spent
    | cons action rest ih => exact ih (step s action) (spent_occurrence_stays_spent s action id spent)
  intro matched
  exact (matched.2.2.2 e chosen).2 (same ▸ retained)

theorem arbitrary_channel_trace_conserves_occurrences (s : Space) (actions : List Action)
    (h : conserved s) : conserved (run actions s) := by
  induction actions generalizing s with
  | nil => exact h
  | cons action rest ih =>
    apply ih
    cases action with
    | produce e => exact produce_preserves_conservation s e h
    | register id c =>
      simp only [step, register]; split <;> exact h
    | react id selected => exact commit_preserves_conservation s id selected h

open Mettapedia.GSLT.Causality.ResourceInteraction

/-- Channel claims instantiate the existing resource scheduler. Only the
available resource projection is represented here; the full reaction queue
is retained by `commit` and accounted for separately below. -/
def joinResources : System Resource where
  Site := Nat
  Instance := fun _ => Continuation × List Occurrence
  consume := fun {id} candidate => (joinDemand id candidate.1 candidate.2).consume
  read := fun {id} candidate => (joinDemand id candidate.1 candidate.2).read
  produce := fun _ => 0

/-- A discovered candidate carries its actual receiver and complete tuple.
Resource admission never substitutes for this independent match validation. -/
def candidateMatches (s : Space) (entry : joinResources.Entry) : Prop :=
  entry.1 ∈ s.registered ∧ s.receives entry.1 = some entry.2.1 ∧
    valid s entry.2.1 entry.2.2

def candidateAction (entry : joinResources.Entry) : Action := .react entry.1 entry.2.2

def candidateReaction (entry : joinResources.Entry) : Reaction := ⟨entry.1, entry.2.2⟩

/-- Every admitted match in a finite wave actually commits through the
original channel transition. Its exact input tuple is queued once per entry;
the projected resources follow the independently defined resource execution. -/
theorem admitted_wave_execution (entries : List joinResources.Entry) (s : Space)
    (matched : ∀ entry ∈ entries, candidateMatches s entry)
    (fits : joinResources.StepEnables (resourceSnapshot s).val entries) :
    joinResources.Fires entries (resourceSnapshot s).val
      (resourceSnapshot (run (entries.map candidateAction) s)).val ∧
    (run (entries.map candidateAction) s).ready = s.ready ++ entries.map candidateReaction := by
  induction entries generalizing s with
  | nil => simp [run, System.Fires]
  | cons head rest ih =>
      obtain ⟨listed, registered, validHead⟩ := matched head (by simp)
      let next := commit s head.1 head.2.2
      have nextResource : (resourceSnapshot next).val =
          joinResources.fire (resourceSnapshot s).val head.2 := by
        simpa [next, joinResources, System.fire] using
          commit_resource_account s head.1 head.2.1 head.2.2 registered validHead
      have restMatched : ∀ entry ∈ rest, candidateMatches next entry := by
        intro entry member
        obtain ⟨otherListed, otherRegistered, otherValid⟩ := matched entry (by simp [member])
        have subset : (([head, entry] : List joinResources.Entry) : Multiset joinResources.Entry) ≤
            ((head :: rest : List joinResources.Entry) : Multiset joinResources.Entry) := by
          have one : ({entry} : Multiset joinResources.Entry) ≤ (rest : Multiset _) :=
            Multiset.singleton_le.mpr (by simpa using member)
          exact Multiset.cons_le_cons head one
        have pair := joinResources.stepEnables_of_le subset fits
        have pairFit : ((joinDemand head.1 head.2.1 head.2.2).reserve
            (joinDemand entry.1 entry.2.1 entry.2.2).consume
            (joinDemand entry.1 entry.2.1 entry.2.2).read).Fits (resourceSnapshot s).val := by
          have concurrent := (joinResources.stepEnables_pair_iff
            (resourceSnapshot s).val head entry).mp pair
          exact (joinResources.concurrent_iff_union (resourceSnapshot s).val
            head.2 entry.2).mp concurrent
        obtain ⟨receivers, sends⟩ := (pair_demand_fits_iff s head.1 entry.1
          head.2.1 entry.2.1 head.2.2 entry.2.2 registered otherRegistered
          listed otherListed validHead otherValid).mp pairFit
        have preserved := independent_join_remains_enabled s head.1 entry.1
          head.2.1 entry.2.1 head.2.2 entry.2.2 registered otherRegistered
          validHead otherValid receivers sends
        refine ⟨?_, preserved⟩
        simpa [next, commit, registered, validHead] using otherListed
      have restFits : joinResources.StepEnables (resourceSnapshot next).val rest := by
        rw [nextResource]
        have enough : joinResources.consume head.2 +
            (joinResources.stepConsume rest + joinResources.stepRead rest) ≤
              (resourceSnapshot s).val := by
          have split : joinResources.consume head.2 + joinResources.stepConsume rest +
              (joinResources.read head.2 ∪ joinResources.stepRead rest) ≤
                (resourceSnapshot s).val := by
            simpa [System.StepEnables, System.stepConsume, System.stepRead] using fits
          rw [← add_assoc]
          exact le_trans (add_le_add le_rfl Multiset.le_union_right) split
        exact le_trans (le_tsub_of_add_le_left enough) (Multiset.le_add_right _ _)
      obtain ⟨tailRun, tailQueue⟩ := ih next restMatched restFits
      constructor
      · change joinResources.Enables (resourceSnapshot s).val head.2 ∧
          joinResources.Fires rest (joinResources.fire (resourceSnapshot s).val head.2)
            (resourceSnapshot (run (rest.map candidateAction) next)).val
        refine ⟨(joinResources.fires_of_stepEnables (head :: rest) _ fits).1, ?_⟩
        rwa [← nextResource]
      · change (run (rest.map candidateAction) next).ready =
          s.ready ++ candidateReaction head :: rest.map candidateReaction
        rw [tailQueue]
        have nextQueue := (successful_join_is_atomic s head.1 head.2.1 head.2.2
          registered validHead).2.2
        simp only [next, candidateReaction, nextQueue, List.append_assoc,
          List.singleton_append]

/-- The common selector may schedule its admitted matches in any order.
All selected input occurrences are published, and every order has the same
resource projection. Queue order follows the chosen execution order; it is
not erased or asserted equal to a different ordered stream. -/
theorem selected_wave_every_order (s : Space) (candidates order : List joinResources.Entry)
    (matched : ∀ entry ∈ candidates, candidateMatches s entry)
    (permutation : (joinResources.selectWave (resourceSnapshot s).val candidates).1.Perm order) :
    (resourceSnapshot (run (order.map candidateAction) s)).val =
      joinResources.waveTarget (resourceSnapshot s).val
        (joinResources.selectWave (resourceSnapshot s).val candidates).1 ∧
    (run (order.map candidateAction) s).ready = s.ready ++ order.map candidateReaction := by
  have selected := joinResources.selectWave_selected_sublist (resourceSnapshot s).val candidates
  have orderMatched : ∀ entry ∈ order, candidateMatches s entry := by
    intro entry member
    exact matched entry (selected.subset (permutation.mem_iff.mpr member))
  have enabled := joinResources.selectWave_enabled (resourceSnapshot s).val candidates
  have same : ((joinResources.selectWave (resourceSnapshot s).val candidates).1 :
      Multiset joinResources.Entry) = (order : Multiset joinResources.Entry) :=
    Multiset.coe_eq_coe.mpr permutation
  rw [same] at enabled
  obtain ⟨actual, queue⟩ := admitted_wave_execution order s orderMatched enabled
  exact ⟨joinResources.fires_target_unique order actual
    (joinResources.selectWave_every_order permutation), queue⟩

open Mettapedia.GSLT.Causality.OccurrenceHistory

/-- An admitted channel wave has a history in the existing resource
presentation. Its ordered entries retain the receiver and complete input
tuples, and an additive account reads their declared charges. This theorem
constructs a semantic witness; it does not require runtime trace recording
or identify these charges with measured native work. -/
theorem selected_wave_occurrence_account {Account : Type*} [AddCommMonoid Account]
    (charge : Nat → Continuation × List Occurrence → Account)
    (s : Space) (candidates order : List joinResources.Entry)
    (matched : ∀ entry ∈ candidates, candidateMatches s entry)
    (permutation : (joinResources.selectWave (resourceSnapshot s).val candidates).1.Perm order) :
    ∃ history : OccurrencePath joinResources.presentation (resourceSnapshot s).val
        (joinResources.waveTarget (resourceSnapshot s).val
          (joinResources.selectWave (resourceSnapshot s).val candidates).1),
      joinResources.pathEntries history = order ∧
      (resourceSnapshot (run (order.map candidateAction) s)).val =
        joinResources.waveTarget (resourceSnapshot s).val
          (joinResources.selectWave (resourceSnapshot s).val candidates).1 ∧
      (run (order.map candidateAction) s).ready =
        s.ready ++ (joinResources.pathEntries history).map candidateReaction ∧
      (joinResources.instanceValuation (fun {id} candidate => charge id candidate)).onPath history =
        (order.map fun entry => charge entry.1 entry.2).sum := by
  obtain ⟨history, entries⟩ := joinResources.exists_path_of_fires order
    (joinResources.selectWave_every_order permutation)
  obtain ⟨resources, queue⟩ := selected_wave_every_order s candidates order matched permutation
  refine ⟨history, entries, resources, ?_, ?_⟩
  · simpa only [entries] using queue
  · rw [joinResources.instanceValuation_onPath, entries]


/-! ## Revision-qualified positional publication into the channel machine -/

namespace PositionalPublication

abbrev Data := EventPump.Key × Nat
abbrev View (StoreId Revision : Type) := RevisionedStoreView StoreId Revision Data

variable {StoreId Revision : Type}

/-- A serial is local to this captured source image. It is not a permanent
runtime ID, a client label, or authority to reuse another source revision. -/
def image (origin : StoreOccurrenceId StoreId Revision × Data) : Occurrence :=
  ⟨origin.1.logicalIndex, origin.2.1, origin.2.2⟩

def source (view : View StoreId Revision) : List Occurrence := view.occurrences.map image

def inputs (view : View StoreId Revision) (positions : List Nat) : List Occurrence :=
  positions.filterMap fun index => (source view)[index]?

/-- Fresh semantic serials live above the complete captured source, including
consumed positions. Their implementation representation is erased below. -/
def outputEvents (start : Nat) (outputs : List Data) : List Occurrence :=
  (outputs.zipIdx start).map fun (entry, serial) => ⟨serial, entry.1, entry.2⟩

def produceOutputs : Space → Nat → List Data → Space
  | s, _, [] => s
  | s, serial, entry :: rest =>
      produceOutputs (produce s ⟨serial, entry.1, entry.2⟩) (serial + 1) rest

def captured (view : View StoreId Revision) (id : Nat) (continuation : Continuation) : Space :=
  register { produced := source view, available := source view } id continuation

private theorem source_lookup (view : View StoreId Revision) (index : Nat) :
    (source view)[index]? = view.entries[index]?.map (fun entry => ⟨index, entry.1, entry.2⟩) := by
  simp [source, image, RevisionedStoreView.occurrences, RevisionedStoreView.occurrenceId,
    List.getElem?_map, List.getElem?_zipIdx, Function.comp_def]

private theorem source_unique (view : View StoreId Revision) :
    ((source view).map EventPump.Event.serial).Nodup := by
  simp only [source, image, RevisionedStoreView.occurrences, RevisionedStoreView.occurrenceId,
    List.map_map, Function.comp_def, List.zipIdx_map_snd]
  exact List.nodup_range'

private theorem source_bound (view : View StoreId Revision) :
    ∀ event ∈ source view, event.serial < view.entries.length := by
  intro event member
  obtain ⟨⟨id, entry⟩, original, same⟩ := List.mem_map.mp member
  obtain ⟨⟨value, index⟩, located, origin⟩ := List.mem_map.mp original
  have bound : index < view.entries.length := by
    obtain ⟨found, limit, equal⟩ := List.exists_mem_zipIdx'.mp
      (show ∃ row ∈ view.entries.zipIdx, row = (value, index) from ⟨_, located, rfl⟩)
    have indices := (Prod.ext_iff.mp equal).2
    omega
  cases origin
  cases same
  exact bound

private theorem inputs_serials (view : View StoreId Revision) (positions : List Nat)
    (bounded : ∀ index ∈ positions, index < view.entries.length) :
    (inputs view positions).map EventPump.Event.serial = positions := by
  induction positions with
  | nil => rfl
  | cons index rest ih =>
      have bound := bounded index (by simp)
      have tail : ∀ i ∈ rest, i < view.entries.length := fun i member => bounded i (by simp [member])
      simpa [inputs, source_lookup, List.getElem?_eq_getElem bound] using congrArg (index :: ·) (ih tail)

private theorem inputs_source (view : View StoreId Revision) (positions : List Nat)
    (event : Occurrence) (member : event ∈ inputs view positions) : event ∈ source view := by
  obtain ⟨index, _, found⟩ := List.mem_filterMap.mp member
  exact List.mem_of_getElem? found

private theorem source_selected_iff (view : View StoreId Revision) (positions : List Nat)
    (bounded : ∀ index ∈ positions, index < view.entries.length)
    (event : Occurrence) (member : event ∈ source view) :
    event ∈ inputs view positions ↔ event.serial ∈ positions := by
  constructor
  · intro selected
    rw [← inputs_serials view positions bounded]
    exact List.mem_map.mpr ⟨event, selected, rfl⟩
  · intro serial
    rw [← inputs_serials view positions bounded] at serial
    obtain ⟨other, selected, same⟩ := List.mem_map.mp serial
    have equal := List.inj_on_of_nodup_map (source_unique view)
      (inputs_source view positions other selected) member same
    exact equal ▸ selected

private theorem captured_fields (view : View StoreId Revision) (id : Nat) (c : Continuation) :
    (captured view id c).produced = source view ∧ (captured view id c).available = source view ∧
      (captured view id c).spent = [] ∧ (captured view id c).receives id = some c ∧
      (captured view id c).ready = [] := by
  simp [captured, register]

/-- Positional admission supplies real distinct inputs. Channel matching is
still independently checked by the existing continuation predicates. -/
theorem inputs_valid (view : View StoreId Revision) (positions : List Nat)
    (id : Nat) (c : Continuation) (nonempty : positions ≠ []) (distinct : positions.Nodup)
    (bounded : ∀ index ∈ positions, index < view.entries.length)
    (matched : matchesAll c.patterns (inputs view positions) = true) :
    valid (captured view id c) c (inputs view positions) := by
  refine ⟨?_, matched, ?_, ?_⟩
  · intro empty
    have serials := inputs_serials view positions bounded
    exact nonempty (by simpa [empty] using serials.symm)
  · simpa only [inputs_serials view positions bounded] using distinct
  · intro event member
    exact ⟨by simpa only [(captured_fields view id c).2.1] using inputs_source view positions event member,
      by simp only [(captured_fields view id c).2.2.1, List.not_mem_nil, not_false_eq_true]⟩

/-- This is a fold of the existing produce operation, whose real freshness
checks all succeed under the source bound. Equal output payloads are retained. -/
theorem produceOutputs_exact (s : Space) (start : Nat) (outputs : List Data)
    (bounded : ∀ event ∈ s.produced, event.serial < start) :
    produceOutputs s start outputs =
      { s with produced := s.produced ++ outputEvents start outputs,
               available := s.available ++ outputEvents start outputs } := by
  induction outputs generalizing s start with
  | nil => simp [produceOutputs, outputEvents]
  | cons entry rest ih =>
      have fresh : start ∉ s.produced.map EventPump.Event.serial := by
        rintro member
        obtain ⟨event, original, same⟩ := List.mem_map.mp member
        have limit := bounded event original
        omega
      have nextBound : ∀ event ∈ (produce s ⟨start, entry.1, entry.2⟩).produced,
          event.serial < start + 1 := by
        intro event member
        simp only [produce, fresh, ↓reduceIte, List.mem_append, List.mem_singleton] at member
        rcases member with old | same
        · have limit := bounded event old
          omega
        · cases same
          exact Nat.lt_succ_self start
      rw [produceOutputs, ih _ _ nextBound]
      simp [produce, fresh, outputEvents, List.zipIdx_cons, List.append_assoc]

private theorem output_payloads (start : Nat) (outputs : List Data) :
    (outputEvents start outputs).map (fun event => (event.owner, event.payload)) = outputs := by
  simp [outputEvents, List.map_map, Function.comp_def, List.zipIdx_map_fst]

private theorem retained_events (view : View StoreId Revision) (positions : List Nat)
    (bounded : ∀ index ∈ positions, index < view.entries.length) :
    (source view).filter (fun event => decide (event ∉ inputs view positions)) =
      (RevisionedStoreView.Publication.retained view positions).map image := by
  have same : (source view).filter (fun event => decide (event ∉ inputs view positions)) =
      (source view).filter (fun event => decide (event.serial ∉ positions)) := by
    apply List.filter_congr
    intro event member
    simp only [source_selected_iff view positions bounded event member]
  rw [same]
  simp only [source, RevisionedStoreView.Publication.retained, List.filter_map]
  rfl

private theorem retained_payloads (view : View StoreId Revision) (positions : List Nat)
    (bounded : ∀ index ∈ positions, index < view.entries.length) :
    ((source view).filter (fun event => decide (event ∉ inputs view positions))).map
      (fun event => (event.owner, event.payload)) = (RevisionedStoreView.Publication.contracted view positions).rows := by
  rw [retained_events view positions bounded, List.map_map]
  exact RevisionedStoreView.Publication.retained_erasure view positions

/-- Output identities are distinct even when their payloads are equal, and
none aliases any occurrence of the complete captured source image. -/
theorem outputs_fresh (view : View StoreId Revision) (outputs : List Data) :
    ((outputEvents view.entries.length outputs).map EventPump.Event.serial).Nodup ∧
      ∀ event ∈ outputEvents view.entries.length outputs, ∀ old ∈ source view,
        event.serial ≠ old.serial := by
  have serials : (outputEvents view.entries.length outputs).map EventPump.Event.serial =
      List.range' view.entries.length outputs.length := by
    simp [outputEvents, List.map_map, Function.comp_def]
  constructor
  · rw [serials]
    exact List.nodup_range'
  · intro event member old original
    have lower : view.entries.length ≤ event.serial := by
      have located : event.serial ∈ (outputEvents view.entries.length outputs).map EventPump.Event.serial :=
        List.mem_map.mpr ⟨event, member, rfl⟩
      rw [serials] at located
      exact (List.mem_range'_1.mp located).1
    have upper := source_bound view old original
    omega

/-- One actual channel transaction under a checked positional source read.
Matching and publication use existing operations; no future-answer oracle or
origin journal is retained in this result. Native execution permission and
captured callback lifetimes remain separate obligations. -/
def transact [DecidableEq StoreId] [DecidableEq Revision]
    (view : View StoreId Revision) (read : StoreReadToken StoreId Revision)
    (positions : List Nat) (outputs : List Data) (nextRevision : Revision)
    (id : Nat) (c : Continuation) : Option (View StoreId Revision × Space) := do
  let result ← RevisionedStoreView.Publication.publish view read positions outputs nextRevision
  if valid (captured view id c) c (inputs view positions) then
    some (result, produceOutputs (commit (captured view id c) id (inputs view positions)) view.entries.length outputs)
  else none

/-- Read back the actual checked operation and its complete channel state. -/
theorem transact_admitted [DecidableEq StoreId] [DecidableEq Revision]
    (view : View StoreId Revision) (read : StoreReadToken StoreId Revision)
    (positions : List Nat) (outputs : List Data) (nextRevision : Revision)
    (id : Nat) (c : Continuation) (result : View StoreId Revision × Space)
    (accepted : transact view read positions outputs nextRevision id c = some result) :
    RevisionedStoreView.Publication.publish view read positions outputs nextRevision = some result.1 ∧
      valid (captured view id c) c (inputs view positions) ∧
      result.2 = produceOutputs (commit (captured view id c) id (inputs view positions)) view.entries.length outputs := by
  unfold transact at accepted
  cases publication : RevisionedStoreView.Publication.publish view read positions outputs nextRevision with
  | none => simp [publication] at accepted
  | some target =>
      simp only [publication] at accepted
      split at accepted
      · rename_i admitted
        cases Option.some.inj accepted
        exact ⟨rfl, admitted, rfl⟩
      · contradiction

/-- Successful channel commitment has exactly the positional publication's
ordered payloads, spends precisely those source serials, and retains its full
reaction tuple. The pre-output resource effect is the existing linear account. -/
theorem transaction_projection [DecidableEq StoreId] [DecidableEq Revision]
    (view : View StoreId Revision) (read : StoreReadToken StoreId Revision)
    (positions : List Nat) (outputs : List Data) (nextRevision : Revision)
    (id : Nat) (c : Continuation) (result : View StoreId Revision × Space)
    (accepted : transact view read positions outputs nextRevision id c = some result) :
    result.2.available = (RevisionedStoreView.Publication.retained view positions).map image ++
        outputEvents view.entries.length outputs ∧
      result.2.available.map (fun event => (event.owner, event.payload)) = result.1.entries ∧
      result.2.spent = positions ∧ result.2.ready = [⟨id, inputs view positions⟩] ∧
      (resourceSnapshot (commit (captured view id c) id (inputs view positions))).val =
        (resourceSnapshot (captured view id c)).val - (joinDemand id c (inputs view positions)).consume := by
  obtain ⟨publication, admitted, actual⟩ := transact_admitted view read positions outputs nextRevision id c result accepted
  have sourceAdmission := RevisionedStoreView.Publication.publication_admitted view read positions outputs nextRevision result.1 publication
  have bounded := sourceAdmission.2.2.1
  have fields := captured_fields view id c
  have registration := fields.2.2.2.1
  have committed := successful_join_is_atomic (captured view id c) id c (inputs view positions) registration admitted
  have original : (commit (captured view id c) id (inputs view positions)).produced = source view := by
    simp [commit, registration, admitted, fields.1]
  have limit : ∀ event ∈ (commit (captured view id c) id (inputs view positions)).produced,
      event.serial < view.entries.length := by
    rw [original]
    exact source_bound view
  rw [produceOutputs_exact _ _ _ limit] at actual
  refine ⟨?_, ?_, ?_, ?_, commit_resource_account _ id c _ registration admitted⟩
  · rw [actual]
    simp only [committed.1, fields.2.1, retained_events view positions bounded]
  · rw [actual]
    simp only [List.map_append, output_payloads, committed.1, fields.2.1, retained_payloads view positions bounded]
    rw [sourceAdmission.2.2.2.2]
    rfl
  · rw [actual]
    simpa only [committed.2.1, fields.2.2.1, List.nil_append] using inputs_serials view positions bounded
  · rw [actual]
    simp only [committed.2.2, fields.2.2.2.2, List.nil_append]

/-- Refused positional currency cannot run even a matching channel commit. -/
theorem stale_transaction_refused [DecidableEq StoreId] [DecidableEq Revision]
    (view : View StoreId Revision) (read : StoreReadToken StoreId Revision)
    (positions : List Nat) (outputs : List Data) (nextRevision : Revision)
    (id : Nat) (c : Continuation) (stale : read ≠ view.readToken) :
    transact view read positions outputs nextRevision id c = none := by
  simp [transact, RevisionedStoreView.Publication.stale_publication_refused view read positions outputs nextRevision stale]

namespace Controls

private def channel : EventPump.Key := ⟨1, 0, 0⟩
private def other : EventPump.Key := ⟨2, 0, 0⟩
private def sourceView : View Nat Nat := ⟨1, 7, [(channel, 42), (channel, 42), (other, 99)]⟩
private def receiveTwo : Continuation :=
  ⟨[⟨channel, fun _ => true⟩, ⟨channel, fun _ => true⟩], false⟩

/-- Actual commit and produce preserve equal occurrences, the unconsumed
origin and order, the complete input tuple and distinct equal fresh outputs. -/
theorem duplicate_inputs_distinct_outputs :
    (transact sourceView sourceView.readToken [0, 1] [(channel, 42), (channel, 42)] 8 7 receiveTwo).map
      (fun result => (result.1.entries, result.2.available.map EventPump.Event.serial,
        result.2.spent, result.2.ready.map (fun reaction => reaction.inputs.map EventPump.Event.serial),
        (result.2.receives 7).isNone)) =
      some ([(other, 99), (channel, 42), (channel, 42)], [2, 3, 4], [0, 1], [[0, 1]], true) := by decide

/-- Reusing one physical input twice or substituting a wrong-channel equal
candidate refuses the operation before any result can be published. -/
theorem repeated_and_wrong_channel_refused :
    (transact sourceView sourceView.readToken [0, 0] [] 8 7 receiveTwo).isNone = true ∧
      (transact sourceView sourceView.readToken [0, 2] [] 8 7 receiveTwo).isNone = true := by decide

end Controls


/-! ## One retained channel Space across finite publications -/

namespace Retained

open Mettapedia.Machines.RevisionedStoreView.Publication
open Mettapedia.GSLT.Dynamics.StableOccurrenceContraction

variable {StoreId : Type}

structure State (StoreId : Type) where
  origins : Finite.WithOrigins StoreId Data
  channel : Space

/-- The live zip of origin rows and available events is the correspondence.
It carries no extra permanent ID table or spent-history recorder. -/
def Lawful (s : State StoreId) : Prop :=
  Finite.Lawful s.origins ∧
    s.channel.available.map (fun e => (e.owner, e.payload)) = s.origins.view.entries ∧
    (s.channel.available.map EventPump.Event.serial).Nodup ∧
    (∀ e ∈ s.channel.available, e ∈ s.channel.produced ∧ e.serial ∉ s.channel.spent) ∧
    ∀ serial ∈ s.channel.spent, serial ∈ s.channel.produced.map EventPump.Event.serial

def initial (view : View StoreId Nat) (id : Nat) (c : Continuation) : State StoreId :=
  ⟨Finite.initial view, captured view id c⟩

def select (rows : List Occurrence) (positions : List Nat) : List Occurrence :=
  positions.filterMap fun index => rows[index]?

/-- A semantic fresh supply derived from existing production evidence. This
reference calculation imposes no native ID layout or bookkeeping cost. -/
def freshStart (s : Space) : Nat := (s.produced.map EventPump.Event.serial).foldr Nat.max 0 + 1

private theorem below_freshStart (s : Space) : ∀ e ∈ s.produced, e.serial < freshStart s := by
  intro e member
  have bound : e.serial ≤ (s.produced.map EventPump.Event.serial).foldr Nat.max 0 := by
    apply List.le_max_of_le (List.mem_map.mpr ⟨e, member, rfl⟩)
    exact Nat.le_refl _
  exact Nat.lt_succ_of_le bound

private theorem select_source (rows : List Occurrence) (positions : List Nat)
    (event : Occurrence) (member : event ∈ select rows positions) : event ∈ rows := by
  obtain ⟨index, _, found⟩ := List.mem_filterMap.mp member
  exact List.mem_of_getElem? found

private theorem select_mem_iff (rows : List Occurrence) (positions : List Nat)
    (unique : rows.Nodup) (index : Nat) (event : Occurrence) (found : rows[index]? = some event) :
    event ∈ select rows positions ↔ index ∈ positions := by
  constructor
  · intro member
    obtain ⟨other, selected, location⟩ := List.mem_filterMap.mp member
    obtain ⟨bound, row⟩ := List.getElem?_eq_some_iff.mp found
    obtain ⟨otherBound, otherRow⟩ := List.getElem?_eq_some_iff.mp location
    have same : other = index := unique.getElem_inj_iff.mp (otherRow.trans row.symm)
    exact same ▸ selected
  · intro chosen
    exact List.mem_filterMap.mpr ⟨index, chosen, found⟩

private theorem filter_select_contract (view : View StoreId Nat) (rows : List Occurrence)
    (positions : List Nat) (lengths : rows.length = view.entries.length) (unique : rows.Nodup) :
    rows.filter (fun event => decide (event ∉ select rows positions)) = contract (mask view positions) rows := by
  rw [Finite.mask_indexed view rows positions lengths, Finite.contract_indexed]
  have projection : (rows.zipIdx.map Prod.fst).filter (fun event => decide (event ∉ select rows positions)) =
      (rows.zipIdx.filter (fun pair => decide (pair.1 ∉ select rows positions))).map Prod.fst := by
    simp only [List.filter_map, Function.comp_def]
  rw [List.zipIdx_map_fst] at projection
  apply projection.trans
  apply congrArg (List.map Prod.fst)
  apply List.filter_congr
  intro pair member
  have found := RevisionedStoreView.getElem?_eq_some_of_mem_zipIdx member
  simp only [select_mem_iff rows positions unique pair.2 pair.1 found]

/-- The one shared consuming transition. Its complete source publication is
computed privately; output policies add Events to this same committed Space. -/
def consumeSpace [DecidableEq StoreId] (view : View StoreId Nat) (s : Space)
    (request : Finite.Request StoreId Data × Nat) : Option (View StoreId Nat × Space) := do
  let next ← Finite.apply view request.1
  let c ← s.receives request.2
  let chosen := select s.available request.1.2.1
  if valid s c chosen then some (next, commit s request.2 chosen) else none

/-- Dense output naming is the existing policy over the shared consumer. -/
def applySpace [DecidableEq StoreId] (view : View StoreId Nat) (s : Space)
    (request : Finite.Request StoreId Data × Nat) : Option (View StoreId Nat × Space) :=
  (consumeSpace view s request).map fun result =>
    (result.1, produceOutputs result.2 (freshStart s) request.1.2.2.1)

def advance [DecidableEq StoreId] (s : State StoreId) (request : Finite.Request StoreId Data × Nat) :
    Option (State StoreId) :=
  (applySpace s.origins.view s.channel request).map fun result =>
    ⟨⟨result.1, Finite.transport s.origins request.1⟩, result.2⟩

theorem initial_lawful (view : View StoreId Nat) (id : Nat) (c : Continuation) : Lawful (initial view id c) := by
  dsimp only [Lawful, initial, Finite.initial]
  have fields := captured_fields view id c
  refine ⟨Finite.initial_lawful view, ?_, ?_, ?_, ?_⟩
  · rw [fields.2.1]
    change (view.occurrences.map image).map (fun e => (e.owner, e.payload)) = view.entries
    simpa only [List.map_map, image, Function.comp_def] using view.occurrences_payloads
  · simpa only [fields.2.1] using source_unique view
  · intro event member
    exact ⟨by simpa only [fields.1, fields.2.1] using member, by simp only [fields.2.2.1, List.not_mem_nil, not_false_eq_true]⟩
  · simp only [fields.2.2.1, List.not_mem_nil, false_implies, implies_true]

private theorem consumeSpace_admitted [DecidableEq StoreId] (view : View StoreId Nat) (s : Space)
    (request : Finite.Request StoreId Data × Nat) (result : View StoreId Nat × Space)
    (accepted : consumeSpace view s request = some result) :
    Finite.apply view request.1 = some result.1 ∧
      ∃ c, s.receives request.2 = some c ∧ valid s c (select s.available request.1.2.1) ∧
        result.2 = commit s request.2 (select s.available request.1.2.1) := by
  unfold consumeSpace at accepted
  cases published : Finite.apply view request.1 with
  | none => simp [published] at accepted
  | some next =>
      simp only [published] at accepted
      cases receiver : s.receives request.2 with
      | none => simp [receiver] at accepted
      | some c =>
          simp only [receiver] at accepted
          change (if valid s c (select s.available request.1.2.1) then
            some (next, commit s request.2 (select s.available request.1.2.1)) else none) = some result at accepted
          split at accepted
          · rename_i admitted
            cases Option.some.inj accepted
            exact ⟨rfl, c, rfl, admitted, rfl⟩
          · contradiction

private theorem applySpace_admitted [DecidableEq StoreId] (view : View StoreId Nat) (s : Space)
    (request : Finite.Request StoreId Data × Nat) (result : View StoreId Nat × Space)
    (accepted : applySpace view s request = some result) :
    Finite.apply view request.1 = some result.1 ∧
      ∃ c, s.receives request.2 = some c ∧ valid s c (select s.available request.1.2.1) ∧
        result.2 = produceOutputs (commit s request.2 (select s.available request.1.2.1))
          (freshStart s) request.1.2.2.1 := by
  obtain ⟨consumed, moved, same⟩ := Option.map_eq_some_iff.mp accepted
  cases same
  obtain ⟨published, c, registered, valid, actual⟩ := consumeSpace_admitted view s request consumed moved
  exact ⟨published, c, registered, valid, congrArg (fun result => produceOutputs result (freshStart s) request.1.2.2.1) actual⟩


private theorem output_properties (start : Nat) (outputs : List Data) :
    ((outputEvents start outputs).map EventPump.Event.serial).Nodup ∧
      ∀ event ∈ outputEvents start outputs, start ≤ event.serial := by
  have serials : (outputEvents start outputs).map EventPump.Event.serial = List.range' start outputs.length := by
    simp [outputEvents, List.map_map, Function.comp_def]
  constructor
  · rw [serials]; exact List.nodup_range'
  · intro event member
    have located : event.serial ∈ (outputEvents start outputs).map EventPump.Event.serial :=
      List.mem_map.mpr ⟨event, member, rfl⟩
    rw [serials] at located
    exact (List.mem_range'_1.mp located).1

/-- Actual commit/produce preserves one live Space and its coupling to the
same contracted origin family; all old ready/spent/receiver state remains. -/
theorem advance_lawful [DecidableEq StoreId] (s next : State StoreId)
    (request : Finite.Request StoreId Data × Nat) (lawful : Lawful s)
    (accepted : advance s request = some next) : Lawful next := by
  obtain ⟨result, applied, same⟩ := Option.map_eq_some_iff.mp accepted
  cases same
  obtain ⟨sourceGrant, c, receiver, admitted, actual⟩ :=
    applySpace_admitted s.origins.view s.channel request result applied
  have moved : Finite.advance s.origins request.1 =
      some ⟨result.1, Finite.transport s.origins request.1⟩ := by
    simp only [Finite.advance, sourceGrant, Option.map_some]
  have names := Finite.advance_lawful s.origins _ request.1 lawful.1 moved
  have lengths : s.channel.available.length = s.origins.view.entries.length := by
    simpa only [List.length_map] using congrArg List.length lawful.2.1
  have uniqueRows := List.Nodup.of_map EventPump.Event.serial lawful.2.2.1
  have committed := successful_join_is_atomic s.channel request.2 c
    (select s.channel.available request.1.2.1) receiver admitted
  have produced : (commit s.channel request.2 (select s.channel.available request.1.2.1)).produced = s.channel.produced := by
    simp [commit, receiver, admitted]
  have bound : ∀ event ∈ (commit s.channel request.2 (select s.channel.available request.1.2.1)).produced,
      event.serial < freshStart s.channel := by rw [produced]; exact below_freshStart s.channel
  have finalState := actual.trans (produceOutputs_exact _ _ _ bound)
  have finalAvailable : result.2.available =
      s.channel.available.filter (fun e => decide (e ∉ select s.channel.available request.1.2.1)) ++
        outputEvents (freshStart s.channel) request.1.2.2.1 := by rw [finalState]; exact congrArg (· ++ _) committed.1
  have finalProduced : result.2.produced = s.channel.produced ++ outputEvents (freshStart s.channel) request.1.2.2.1 := by
    rw [finalState, produced]
  have finalSpent : result.2.spent = s.channel.spent ++ (select s.channel.available request.1.2.1).map EventPump.Event.serial := by
    rw [finalState]; exact committed.2.1
  have outputFacts := output_properties (freshStart s.channel) request.1.2.2.1
  refine ⟨names.1, ?_, ?_, ?_, ?_⟩
  · rw [finalAvailable, List.map_append, output_payloads,
      filter_select_contract s.origins.view s.channel.available request.1.2.1 lengths uniqueRows,
      ← contract_map, lawful.2.1]
    have erased := names.1.1
    have outputs : (fresh s.origins.view request.1.2.1 request.1.2.2.1 request.1.2.2.2).map Prod.snd = request.1.2.2.1 := by
      simp [RevisionedStoreView.Publication.fresh, List.map_map, Function.comp_def, List.zipIdx_map_fst]
    simpa only [Finite.transport, List.map_append, ← contract_map, lawful.1.1, outputs] using erased
  · rw [finalAvailable, List.map_append]
    apply List.nodup_append.mpr
    refine ⟨lawful.2.2.1.sublist (List.filter_sublist.map EventPump.Event.serial), outputFacts.1, ?_⟩
    intro old oldMember new newMember equal
    obtain ⟨oldEvent, retained, oldName⟩ := List.mem_map.mp oldMember
    obtain ⟨newEvent, created, newName⟩ := List.mem_map.mp newMember
    have oldBound := below_freshStart s.channel oldEvent (lawful.2.2.2.1 oldEvent (List.mem_filter.mp retained).1).1
    have newBound := outputFacts.2 newEvent created
    omega
  · intro event member
    rw [finalAvailable, List.mem_append] at member
    rcases member with retained | created
    · have original := (List.mem_filter.mp retained).1
      have unselected : event ∉ select s.channel.available request.1.2.1 := of_decide_eq_true (List.mem_filter.mp retained).2
      have known := lawful.2.2.2.1 event original
      refine ⟨?_, ?_⟩
      · rw [finalProduced]; exact List.mem_append_left _ known.1
      · rw [finalSpent, List.mem_append, not_or]
        refine ⟨known.2, ?_⟩
        intro spent
        obtain ⟨other, selected, equal⟩ := List.mem_map.mp spent
        have sameEvent := List.inj_on_of_nodup_map lawful.2.2.1
          (select_source _ _ other selected) original equal
        exact unselected (sameEvent ▸ selected)
    · refine ⟨?_, ?_⟩
      · rw [finalProduced]; exact List.mem_append_right _ created
      · have newBound := outputFacts.2 event created
        rw [finalSpent, List.mem_append, not_or]
        constructor
        · intro spent
          obtain ⟨old, oldProduced, equal⟩ := List.mem_map.mp (lawful.2.2.2.2 event.serial spent)
          have oldBound := below_freshStart s.channel old oldProduced
          omega
        · intro spent
          obtain ⟨old, selected, equal⟩ := List.mem_map.mp spent
          have oldBound := below_freshStart s.channel old
            (lawful.2.2.2.1 old (select_source _ _ old selected)).1
          omega
  · intro serial member
    rw [finalSpent, List.mem_append] at member
    have old : serial ∈ s.channel.produced.map EventPump.Event.serial := by
      rcases member with spent | selected
      · exact lawful.2.2.2.2 serial spent
      · obtain ⟨event, chosen, same⟩ := List.mem_map.mp selected
        exact List.mem_map.mpr ⟨event, (lawful.2.2.2.1 event (select_source _ _ event chosen)).1, same⟩
    rw [finalProduced, List.map_append]
    exact List.mem_append_left _ old


private theorem advance_origins [DecidableEq StoreId] (s next : State StoreId)
    (request : Finite.Request StoreId Data × Nat) (accepted : advance s request = some next) :
    Finite.advance s.origins request.1 = some next.origins := by
  obtain ⟨result, applied, same⟩ := Option.map_eq_some_iff.mp accepted
  cases same
  have sourceGrant := (applySpace_admitted s.origins.view s.channel request result applied).1
  simp only [Finite.advance, sourceGrant, Option.map_some]

private theorem produceOutputs_spent (s : Space) (start : Nat) (outputs : List Data) :
    (produceOutputs s start outputs).spent = s.spent := by
  induction outputs generalizing s start with
  | nil => rfl
  | cons output rest ih =>
      rw [produceOutputs, ih]
      simp only [produce]; split <;> rfl

theorem advance_spent [DecidableEq StoreId] (s next : State StoreId)
    (request : Finite.Request StoreId Data × Nat) (accepted : advance s request = some next) :
    next.channel.spent = s.channel.spent ++ (select s.channel.available request.1.2.1).map EventPump.Event.serial := by
  obtain ⟨result, applied, same⟩ := Option.map_eq_some_iff.mp accepted
  cases same
  obtain ⟨_, c, receiver, admitted, actual⟩ := applySpace_admitted s.origins.view s.channel request result applied
  rw [actual, produceOutputs_spent]
  exact (successful_join_is_atomic s.channel request.2 c _ receiver admitted).2.1

def runActual [DecidableEq StoreId] : List (Finite.Request StoreId Data × Nat) →
    View StoreId Nat × Space → Option (View StoreId Nat × Space)
  | [], state => some state
  | request :: rest, state => (applySpace state.1 state.2 request).bind (runActual rest)

def run [DecidableEq StoreId] : List (Finite.Request StoreId Data × Nat) → State StoreId → Option (State StoreId)
  | [], s => some s
  | request :: rest, s => (advance s request).bind (run rest)

theorem run_erasure [DecidableEq StoreId] (requests : List (Finite.Request StoreId Data × Nat))
    (s : State StoreId) :
    (run requests s).map (fun final => (final.origins.view, final.channel)) =
      runActual requests (s.origins.view, s.channel) := by
  induction requests generalizing s with
  | nil => rfl
  | cons request rest ih =>
      cases result : applySpace s.origins.view s.channel request with
      | none => simp [run, runActual, advance, result]
      | some next =>
          simpa [run, runActual, advance, result] using ih ⟨⟨next.1, Finite.transport s.origins request.1⟩, next.2⟩

theorem run_append [DecidableEq StoreId] (first second : List (Finite.Request StoreId Data × Nat))
    (s : State StoreId) : run (first ++ second) s = (run first s).bind (run second) := by
  induction first generalizing s with
  | nil => rfl
  | cons request rest ih =>
      cases moved : advance s request with
      | none => simp [run, moved]
      | some next => simpa [run, moved] using ih next

theorem run_lawful [DecidableEq StoreId] (requests : List (Finite.Request StoreId Data × Nat))
    (s final : State StoreId) (lawful : Lawful s) (accepted : run requests s = some final) : Lawful final := by
  induction requests generalizing s with
  | nil => cases Option.some.inj accepted; exact lawful
  | cons request rest ih =>
      obtain ⟨next, moved, continued⟩ := Option.bind_eq_some_iff.mp accepted
      exact ih next (advance_lawful s next request lawful moved) continued

/-- Every accepted channel publication advances that same source-origin
computation. Channel refusal is not erased into source success. -/
theorem run_origins [DecidableEq StoreId] (requests : List (Finite.Request StoreId Data × Nat))
    (s final : State StoreId) (accepted : run requests s = some final) :
    Finite.run (requests.map Prod.fst) s.origins = some final.origins := by
  induction requests generalizing s with
  | nil => cases Option.some.inj accepted; rfl
  | cons request rest ih =>
      obtain ⟨next, moved, continued⟩ := Option.bind_eq_some_iff.mp accepted
      simp only [List.map_cons, Finite.run, advance_origins s next request moved, Option.bind_some]
      exact ih next continued

theorem run_from_initial [DecidableEq StoreId] (requests : List (Finite.Request StoreId Data × Nat))
    (view : View StoreId Nat) (id : Nat) (c : Continuation) (final : State StoreId)
    (accepted : run requests (initial view id c) = some final) :
    runActual requests (view, captured view id c) = some (final.origins.view, final.channel) ∧
      Finite.runViews (requests.map Prod.fst) view = some final.origins.view ∧ Lawful final := by
  have erased := run_erasure requests (initial view id c)
  rw [accepted] at erased
  have origins := run_origins requests (initial view id c) final accepted
  exact ⟨erased.symm, (Finite.run_from_initial _ view final.origins origins).1,
    run_lawful requests _ final (initial_lawful view id c) accepted⟩

theorem run_spent [DecidableEq StoreId] (requests : List (Finite.Request StoreId Data × Nat))
    (s final : State StoreId) (accepted : run requests s = some final)
    (serial : Nat) (spent : serial ∈ s.channel.spent) : serial ∈ final.channel.spent := by
  induction requests generalizing s with
  | nil => cases Option.some.inj accepted; exact spent
  | cons request rest ih =>
      obtain ⟨next, moved, continued⟩ := Option.bind_eq_some_iff.mp accepted
      apply ih next continued
      rw [advance_spent s next request moved]
      exact List.mem_append_left _ spent

/-- No later valid join can recycle an occurrence already spent in the
retained Space. Fresh output publication does not renew its consume right. -/
theorem run_spent_cannot_reconsume [DecidableEq StoreId] (requests : List (Finite.Request StoreId Data × Nat))
    (s final : State StoreId) (accepted : run requests s = some final)
    (serial : Nat) (spent : serial ∈ s.channel.spent) (c : Continuation)
    (candidate : List Occurrence) (event : Occurrence) (chosen : event ∈ candidate)
    (same : event.serial = serial) : ¬ valid final.channel c candidate := by
  have retained := run_spent requests s final accepted serial spent
  intro admitted
  apply (admitted.2.2.2 event chosen).2
  simpa only [same] using retained


private theorem contract_zip {α β : Type} (mask : List Bool) (rows : List α) (events : List β) :
    contract mask (rows.zip events) = (contract mask rows).zip (contract mask events) := by
  induction mask generalizing rows events with
  | nil => simp [contract]
  | cons keep mask ih => cases rows <;> cases events <;> cases keep <;> simp [contract, ih]

private theorem kept_pair_coordinate {α β : Type} (view : View StoreId Nat)
    (rows : List α) (events : List β) (positions : List Nat)
    (rowLength : rows.length = view.entries.length) (eventLength : events.length = view.entries.length)
    (index : Nat) (origin : α) (event : β) (row : rows[index]? = some origin)
    (actual : events[index]? = some event) (unchosen : index ∉ positions) :
    ∃ target : Nat, (contract (mask view positions) rows)[target]? = some origin ∧
      (contract (mask view positions) events)[target]? = some event := by
  have lengths : (rows.zip events).length = view.entries.length := by simp [rowLength, eventLength]
  have together : (rows.zip events)[index]? = some (origin, event) := List.getElem?_zip_eq_some.mpr ⟨row, actual⟩
  have indexed : ((origin, event), index) ∈ (rows.zip events).zipIdx :=
    List.mem_of_getElem? (i := index) (by simp [together])
  have member : (origin, event) ∈ contract (mask view positions) (rows.zip events) := by
    rw [Finite.mask_indexed view (rows.zip events) positions lengths, Finite.contract_indexed]
    exact List.mem_map.mpr ⟨((origin, event), index), List.mem_filter.mpr ⟨indexed, by simpa using unchosen⟩, rfl⟩
  obtain ⟨target, located⟩ := List.getElem?_of_mem member
  rw [contract_zip] at located
  exact ⟨target, (List.getElem?_zip_eq_some.mp located).1, (List.getElem?_zip_eq_some.mp located).2⟩

/-- The same current positional contraction transports both the source name
and the complete actual Event. Equal payloads cannot exchange physical IDs. -/
theorem advance_keeps_pair [DecidableEq StoreId] (s next : State StoreId)
    (request : Finite.Request StoreId Data × Nat) (lawful : Lawful s)
    (accepted : advance s request = some next) (index : Nat)
    (origin : StoreOccurrenceId StoreId Nat × Data) (event : Occurrence)
    (named : s.origins.rows[index]? = some origin) (actualEvent : s.channel.available[index]? = some event)
    (unchosen : index ∉ request.1.2.1) :
    ∃ target : Nat, next.origins.rows[target]? = some origin ∧ next.channel.available[target]? = some event := by
  have rowLength : s.origins.rows.length = s.origins.view.entries.length := by
    simpa only [List.length_map] using congrArg List.length lawful.1.1
  have eventLength : s.channel.available.length = s.origins.view.entries.length := by
    simpa only [List.length_map] using congrArg List.length lawful.2.1
  obtain ⟨target, keptName, keptEvent⟩ := kept_pair_coordinate s.origins.view s.origins.rows s.channel.available
    request.1.2.1 rowLength eventLength index origin event named actualEvent unchosen
  obtain ⟨result, applied, same⟩ := Option.map_eq_some_iff.mp accepted
  cases same
  obtain ⟨_, c, receiver, admitted, returned⟩ := applySpace_admitted s.origins.view s.channel request result applied
  refine ⟨target, ?_, ?_⟩
  · simpa only [Finite.transport, List.getElem?_append_left (List.getElem?_eq_some_iff.mp keptName).1] using keptName
  · have produced : (commit s.channel request.2 (select s.channel.available request.1.2.1)).produced = s.channel.produced := by
      simp [commit, receiver, admitted]
    have bound : ∀ e ∈ (commit s.channel request.2 (select s.channel.available request.1.2.1)).produced,
        e.serial < freshStart s.channel := by rw [produced]; exact below_freshStart s.channel
    rw [returned, produceOutputs_exact _ _ _ bound,
      (successful_join_is_atomic s.channel request.2 c _ receiver admitted).1,
      filter_select_contract s.origins.view s.channel.available request.1.2.1 eventLength
        (List.Nodup.of_map EventPump.Event.serial lawful.2.2.1)]
    simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp keptEvent).1] using keptEvent

/-- Across arbitrary successful finite publications, every originally paired
name/event is either spent together or still paired with the identical Event
at its shifted current position. No semantic equality is supplied by a caller. -/
theorem run_origin_or_spent [DecidableEq StoreId] (requests : List (Finite.Request StoreId Data × Nat))
    (s final : State StoreId) (lawful : Lawful s) (accepted : run requests s = some final)
    (index : Nat) (origin : StoreOccurrenceId StoreId Nat × Data) (event : Occurrence)
    (named : s.origins.rows[index]? = some origin) (actualEvent : s.channel.available[index]? = some event) :
    (origin.1 ∉ final.origins.rows.map Prod.fst ∧ event.serial ∈ final.channel.spent) ∨
      ∃ target : Nat, final.origins.rows[target]? = some origin ∧ final.channel.available[target]? = some event := by
  induction requests generalizing s index with
  | nil => cases Option.some.inj accepted; exact Or.inr ⟨index, named, actualEvent⟩
  | cons request rest ih =>
      obtain ⟨next, moved, continued⟩ := Option.bind_eq_some_iff.mp accepted
      by_cases chosen : index ∈ request.1.2.1
      · have absent := Finite.consumed_name_stays_spent s.origins next.origins final.origins request.1
          (rest.map Prod.fst) lawful.1 (advance_origins s next request moved)
          (run_origins rest next final continued) index origin named chosen
        have spent : event.serial ∈ next.channel.spent := by
          rw [advance_spent s next request moved]
          apply List.mem_append_right
          exact List.mem_map.mpr ⟨event, List.mem_filterMap.mpr ⟨index, chosen, actualEvent⟩, rfl⟩
        exact Or.inl ⟨absent, run_spent rest next final continued event.serial spent⟩
      · obtain ⟨target, nameKept, eventKept⟩ := advance_keeps_pair s next request lawful moved index origin event named actualEvent chosen
        exact ih next (advance_lawful s next request lawful moved) continued target nameKept eventKept

namespace Controls

private def channel : EventPump.Key := ⟨1, 0, 0⟩
private def other : EventPump.Key := ⟨2, 0, 0⟩
private def sourceView : View Nat Nat := ⟨1, 7, [(channel, 42), (channel, 42), (other, 99)]⟩
private def receiver (persistent : Bool) : Continuation := ⟨[⟨channel, fun _ => true⟩], persistent⟩
private def requests : List (Finite.Request Nat Data × Nat) :=
  [((⟨1, 7⟩, [0], [(channel, 42)], 8), 7),
   ((⟨1, 8⟩, [0], [(channel, 42), (channel, 42)], 9), 7),
   ((⟨1, 9⟩, [1], [], 10), 7)]

private def readout (s : State Nat) :
    List Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat) × Bool :=
  (s.channel.available.map EventPump.Event.serial, s.channel.spent,
    s.channel.ready.map (fun reaction => reaction.inputs.map EventPump.Event.serial),
    s.origins.rows.map (fun origin => (origin.1.read.storeId, origin.1.read.revision, origin.1.logicalIndex)),
    (s.channel.receives 7).isSome)

set_option synthInstance.maxSize 512 in
theorem retained_duplicate_shifted_inputs :
    (run requests (initial sourceView 7 (receiver true))).map readout =
      some ([2, 4, 5], [0, 1, 3], [[0], [1], [3]], [(1, 7, 2), (1, 9, 2), (1, 9, 3)], true) := by decide

theorem one_shot_is_not_reset :
    (advance (initial sourceView 7 (receiver false)) ((⟨1, 7⟩, [0], [(channel, 42)], 8), 7)).map
      (fun s => ((s.channel.receives 7).isNone, s.channel.spent)) = some (true, [0]) ∧
      (run requests (initial sourceView 7 (receiver false))).isNone = true := by decide

end Controls

#print axioms initial_lawful
#print axioms advance_lawful
#print axioms advance_spent
#print axioms run_erasure
#print axioms run_append
#print axioms run_lawful
#print axioms run_origins
#print axioms run_from_initial
#print axioms run_spent
#print axioms run_spent_cannot_reconsume
#print axioms advance_keeps_pair
#print axioms run_origin_or_spent
#print axioms Controls.retained_duplicate_shifted_inputs
#print axioms Controls.one_shot_is_not_reset

end Retained

#print axioms inputs_valid
#print axioms produceOutputs_exact
#print axioms outputs_fresh
#print axioms transact_admitted
#print axioms transaction_projection
#print axioms stale_transaction_refused
#print axioms Controls.duplicate_inputs_distinct_outputs
#print axioms Controls.repeated_and_wrong_channel_refused

end PositionalPublication

/-! A positive consuming join finder. The independent `valid` contract above
still decides commitment. Discovery performs only retained depth-first search;
it never runs commit, produces output, or precomputes later answers. -/
namespace Discovery

open Mettapedia.GSLT.LanguageDef
open HostCalls (Pull collect)

def eligible (s : Space) (used : List Occurrence) (p : Pattern) (e : Occurrence) : Prop :=
  patternMatches p e = true ∧ e.serial ∉ s.spent ∧ e.serial ∉ used.map EventPump.Event.serial

instance (s : Space) (used : List Occurrence) (p : Pattern) (e : Occurrence) :
    Decidable (eligible s used p e) := by unfold eligible; infer_instance

/-- Independent recursive tuple meaning. Used occurrences are a reverse
prefix; this denotation is never evaluated by the search transition. -/
def choices (s : Space) : List Pattern → List Occurrence → List (List Occurrence)
  | [], _ => [[]]
  | p :: rest, used => s.available.flatMap fun e =>
      if eligible s used p e then (choices s rest (e :: used)).map (e :: ·) else []

/-- Membership is specified by pattern matching, current occurrence membership
and pairwise distinct serials, independently of any search order. -/
theorem choices_iff (s : Space) (patterns : List Pattern) (used selected : List Occurrence) :
    selected ∈ choices s patterns used ↔
      matchesAll patterns selected = true ∧ (selected.map EventPump.Event.serial).Nodup ∧
        ∀ e ∈ selected, e ∈ s.available ∧ e.serial ∉ s.spent ∧ e.serial ∉ used.map EventPump.Event.serial := by
  induction patterns generalizing used selected with
  | nil => cases selected <;> simp [choices, matchesAll]
  | cons p rest ih =>
      cases selected with
      | nil => simp [choices, matchesAll]
      | cons e tail =>
          constructor
          · intro found
            obtain ⟨candidate, available, found⟩ := List.mem_flatMap.mp found
            split at found
            next allowed =>
              obtain ⟨suffix, present, equal⟩ := List.mem_map.mp found
              cases equal
              obtain ⟨matched, unique, members⟩ := (ih _ _).mp present
              refine ⟨by simp [matchesAll, allowed.1, matched], ?_, ?_⟩
              · simp only [List.map_cons, List.nodup_cons]
                refine ⟨?_, unique⟩
                intro reused
                obtain ⟨other, member, same⟩ := List.mem_map.mp reused
                have fresh := (members other member).2.2
                simp only [List.map_cons, List.mem_cons, not_or] at fresh
                exact fresh.1 same
              · intro other member
                rcases List.mem_cons.mp member with rfl | later
                · exact ⟨available, allowed.2.1, allowed.2.2⟩
                · have fresh := members other later
                  exact ⟨fresh.1, fresh.2.1, fun old => fresh.2.2 (List.mem_cons_of_mem _ old)⟩
            next refused => simp at found
          · rintro ⟨matched, unique, members⟩
            have pair : patternMatches p e = true ∧ matchesAll rest tail = true := by
              simpa only [matchesAll, Bool.and_eq_true_iff] using matched
            have first := members e List.mem_cons_self
            have distinct : e.serial ∉ tail.map EventPump.Event.serial ∧
                (tail.map EventPump.Event.serial).Nodup := by simpa using unique
            apply List.mem_flatMap.mpr
            refine ⟨e, first.1, ?_⟩
            have allowed : eligible s used p e := ⟨pair.1, first.2.1, first.2.2⟩
            rw [if_pos allowed]
            refine List.mem_map.mpr ⟨tail, (ih _ _).mpr ⟨pair.2, distinct.2, ?_⟩, rfl⟩
            intro other member
            have old := members other (List.mem_cons_of_mem _ member)
            refine ⟨old.1, old.2.1, ?_⟩
            simp only [List.map_cons, List.mem_cons, not_or]
            refine ⟨?_, old.2.2⟩
            intro same
            exact distinct.1 (List.mem_map.mpr ⟨other, member, same⟩)

/-- A lawful physical source yields each complete tuple once. Equal values
at different occurrences still produce different tuple lists. -/
theorem choices_nodup (s : Space) (patterns : List Pattern) (used : List Occurrence)
    (unique : s.available.Nodup) : (choices s patterns used).Nodup := by
  induction patterns generalizing used with
  | nil => simp [choices]
  | cons p rest ih =>
      rw [choices, List.nodup_flatMap]
      constructor
      · intro e member
        split
        · exact (ih _).map (by intro first second same; exact List.cons.inj same |>.2)
        · exact List.nodup_nil
      · apply unique.imp
        intro first second different
        apply List.disjoint_left.mpr
        intro tuple left right
        dsimp only at left right
        split at left
        next allowed =>
          obtain ⟨one, _, equal⟩ := List.mem_map.mp left
          subst tuple
          split at right
          next allowed =>
            obtain ⟨two, _, equal⟩ := List.mem_map.mp right
            exact different (List.cons.inj equal).1.symm
          next refused => simp at right
        next refused => simp at left

inductive Work where
  | join (remaining : List Pattern) (used : List Occurrence)
  | scan (pattern : Pattern) (remaining : List Pattern) (candidates used : List Occurrence)

abbrev State := List Work

def start (c : Continuation) : State :=
  if c.patterns.isEmpty then [] else [.join c.patterns []]

/-- One search operation opens a factor, inspects one candidate, backtracks,
or yields one complete physical tuple. Equal payloads are not coalesced. -/
def pull (s : Space) : State → Pull State (List Occurrence)
  | [] => .done
  | .join [] used :: pending => .yield used.reverse pending
  | .join (p :: rest) used :: pending => .suspend (.scan p rest s.available used :: pending)
  | .scan _ _ [] _ :: pending => .suspend pending
  | .scan p rest (e :: pool) used :: pending =>
      let later := .scan p rest pool used :: pending
      if eligible s used p e then .suspend (.join rest (e :: used) :: later) else .suspend later

def workRows (s : Space) : Work → List (List Occurrence)
  | .join remaining used => (choices s remaining used).map (used.reverse ++ ·)
  | .scan p remaining pool used => pool.flatMap fun e =>
      if eligible s used p e then (choices s remaining (e :: used)).map ((e :: used).reverse ++ ·) else []

def residualRows (s : Space) (state : State) := state.flatMap (workRows s)

theorem pull_rows (s : Space) (state : State) :
    match pull s state with
    | .done => residualRows s state = []
    | .suspend next => residualRows s state = residualRows s next
    | .yield selected next => residualRows s state = selected :: residualRows s next := by
  cases state with
  | nil => rfl
  | cons work pending =>
      cases work with
      | join remaining used =>
          cases remaining with
          | nil => simp [pull, residualRows, workRows, choices]
          | cons p rest =>
              simp only [pull, residualRows, workRows, choices, List.map_flatMap,
                List.flatMap_cons]
              apply congrArg (· ++ residualRows s pending)
              apply congrArg (List.flatMap · s.available)
              funext e
              by_cases allowed : eligible s used p e <;>
                simp [allowed, List.map_map, Function.comp_def, List.reverse_cons, List.append_assoc]
      | scan p remaining pool used =>
          cases pool with
          | nil => rfl
          | cons e rest =>
              by_cases allowed : eligible s used p e <;>
                simp [pull, residualRows, workRows, allowed, List.append_assoc]

theorem start_iff (s : Space) (c : Continuation) (selected : List Occurrence) :
    selected ∈ residualRows s (start c) ↔ valid s c selected := by
  cases patterns : c.patterns with
  | nil =>
      simp only [start, patterns, List.isEmpty_nil, ↓reduceIte, residualRows, List.flatMap_nil, List.not_mem_nil, false_iff]
      intro accepted
      have length := matched_lists_have_equal_length _ _ accepted.2.1
      simp only [patterns, List.length_nil] at length
      exact accepted.1 (List.eq_nil_of_length_eq_zero length.symm)
  | cons p rest =>
      simp only [start, patterns, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        residualRows, List.flatMap_cons, List.flatMap_nil, List.append_nil, workRows,
        List.reverse_nil, List.nil_append]
      change selected ∈ (choices s (p :: rest) []).map id ↔ valid s c selected
      rw [List.map_id, choices_iff]
      simp only [List.map_nil, List.not_mem_nil, not_false_eq_true, and_true]
      constructor
      · rintro ⟨matched, unique, members⟩
        refine ⟨?_, by simpa only [patterns] using matched, unique, members⟩
        intro empty
        subst selected
        simp [matchesAll] at matched
      · intro accepted
        exact ⟨by simpa only [patterns] using accepted.2.1, accepted.2.2.1, accepted.2.2.2⟩

def joinCost (s : Space) : List Pattern → List Occurrence → Nat
  | [], _ => 1
  | p :: rest, used => 2 + (s.available.map fun e =>
      1 + if eligible s used p e then joinCost s rest (e :: used) else 0).sum

def workCost (s : Space) : Work → Nat
  | .join remaining used => joinCost s remaining used
  | .scan p remaining pool used => 1 + (pool.map fun e =>
      1 + if eligible s used p e then joinCost s remaining (e :: used) else 0).sum

def remainingCost (s : Space) (state : State) := (state.map (workCost s)).sum

theorem pull_cost (s : Space) (state : State) :
    match pull s state with
    | .done => remainingCost s state = 0
    | .suspend next => remainingCost s next < remainingCost s state
    | .yield _ next => remainingCost s next < remainingCost s state := by
  cases state with
  | nil => rfl
  | cons work pending =>
      cases work with
      | join remaining used =>
          cases remaining with
          | nil => simp [pull, remainingCost, workCost, joinCost]
          | cons p rest => simp [pull, remainingCost, workCost, joinCost]
      | scan p remaining pool used =>
          cases pool with
          | nil => simp [pull, remainingCost, workCost]
          | cons e rest =>
              by_cases allowed : eligible s used p e <;>
                simp [pull, remainingCost, workCost, allowed]
              all_goals omega

theorem collect_sound (s : Space) (fuel : Nat) (state : State) (result : List (List Occurrence))
    (finished : collect (pull s) fuel state = some result) : result = residualRows s state :=
  NativeControlCursor.collect_sound (pull s) (residualRows s)
    (fun state => by cases moved : pull s state <;> simpa only [moved] using pull_rows s state) fuel state result finished

theorem collect_complete (s : Space) (fuel : Nat) (state : State) (enough : remainingCost s state < fuel) :
    collect (pull s) fuel state = some (residualRows s state) :=
  NativeControlCursor.collect_complete (pull s) (residualRows s)
    (fun state => by cases moved : pull s state <;> simpa only [moved] using pull_rows s state)
    (remainingCost s) (fun state => by cases moved : pull s state <;> simpa only [moved] using pull_cost s state)
    fuel state enough

theorem completed_iff (s : Space) (c : Continuation) (fuel : Nat) (result : List (List Occurrence))
    (finished : collect (pull s) fuel (start c) = some result) (selected : List Occurrence) :
    selected ∈ result ↔ valid s c selected := by
  rw [collect_sound s fuel (start c) result finished]
  exact start_iff s c selected

theorem completed_nodup (s : Space) (c : Continuation) (fuel : Nat) (result : List (List Occurrence))
    (unique : s.available.Nodup) (finished : collect (pull s) fuel (start c) = some result) : result.Nodup := by
  rw [collect_sound s fuel (start c) result finished]
  cases patterns : c.patterns with
  | nil => simp [start, patterns, residualRows]
  | cons p rest =>
      simp only [start, patterns, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        residualRows, List.flatMap_cons, List.flatMap_nil, List.append_nil, workRows,
        List.reverse_nil, List.nil_append]
      change ((choices s (p :: rest) []).map id).Nodup
      rw [List.map_id]
      exact choices_nodup s _ _ unique

abbrev provider (s : Space) := NativeControlCursor.provider (pull s)

abbrev Packet (s : Space) := Cursor.Packet (provider s) (NativeControlCursor.client (List Occurrence)) ()
abbrev Outcome (s : Space) := Cursor.Outcome (provider s) (NativeControlCursor.client (List Occurrence)) ()

def buffered : Cursor.Fold.State (List (List Occurrence)) → List (List Occurrence)
  | .pulling reversed => reversed.reverse
  | .finished values => values

/-- Complete bindings already found by this bounded request, including at a
pause. Reading this buffer does not demand any later tuple. -/
def observed (s : Space) : Outcome s → List (List Occurrence)
  | .paused packet => buffered packet.2.1
  | .done result => result.2.1

def saved (s : Space) : Outcome s → State
  | .paused packet => packet.2.2
  | .done result => result.2.2

set_option backward.isDefEq.respectTransparency false in
theorem advance_rows (s : Space) (fuel : Nat) (packet : Packet s) :
    let actual := Cursor.advance (provider s) (NativeControlCursor.client (List Occurrence)) (fun _ _ => 1) fuel packet
    observed s actual.2 ++ residualRows s (saved s actual.2) =
      buffered packet.2.1 ++ residualRows s packet.2.2 := by
  induction fuel generalizing packet with
  | zero => rfl
  | succ fuel ih =>
      rcases packet with ⟨⟨⟩, control, state⟩
      cases control with
      | finished values => rfl
      | pulling reversed =>
          change State at state
          have onePoll := congrArg (fun actual : Nat × Outcome s =>
            observed s actual.2 ++ residualRows s (saved s actual.2))
            (NativeControlCursor.advance_poll (pull s) fuel state reversed)
          refine onePoll.trans ?_
          have one := pull_rows s state
          cases moved : pull s state with
          | done =>
              simp only [moved] at one
              have later := ih ⟨(), .finished reversed.reverse, state⟩
              simpa only [moved, one, buffered, List.append_nil] using later
          | suspend next =>
              simp only [moved] at one
              have later := ih (NativeControlCursor.packet (pull s) next reversed)
              simpa only [moved, buffered, NativeControlCursor.packet, ← one] using later
          | yield selected next =>
              simp only [moved] at one
              have later := ih (NativeControlCursor.packet (pull s) next (selected :: reversed))
              simpa only [moved, buffered, NativeControlCursor.packet, List.reverse_cons, List.append_assoc,
                List.singleton_append, ← one] using later

theorem bounded_sound (s : Space) (c : Continuation) (fuel : Nat) (selected : List Occurrence)
    (found : selected ∈ observed s (Cursor.advance (provider s) (NativeControlCursor.client (List Occurrence))
      (fun _ _ => 1) fuel (NativeControlCursor.packet (pull s) (start c) [])).2) : valid s c selected := by
  apply (start_iff s c selected).mp
  have conserved := advance_rows s fuel (NativeControlCursor.packet (pull s) (start c) [])
  let actual := Cursor.advance (provider s) (NativeControlCursor.client (List Occurrence))
    (fun _ _ => 1) fuel (NativeControlCursor.packet (pull s) (start c) [])
  have member : selected ∈ observed s actual.2 ++ residualRows s (saved s actual.2) := List.mem_append_left _ found
  rw [conserved] at member
  exact member

theorem split_resume (s : Space) (first second : Nat) (state : State) (reversed : List (List Occurrence)) :
    Cursor.advance (provider s) (NativeControlCursor.client (List Occurrence)) (fun _ _ => 1) (first + second)
        (NativeControlCursor.packet (pull s) state reversed) =
      Cursor.resume (provider s) (NativeControlCursor.client (List Occurrence)) (fun _ _ => 1) second
        (Cursor.advance (provider s) (NativeControlCursor.client (List Occurrence)) (fun _ _ => 1) first
          (NativeControlCursor.packet (pull s) state reversed)) :=
  NativeControlCursor.chunk_exact _ _ _ _ _

#print axioms choices_iff
#print axioms choices_nodup
#print axioms pull_rows
#print axioms start_iff
#print axioms pull_cost
#print axioms collect_sound
#print axioms collect_complete
#print axioms completed_iff
#print axioms completed_nodup
#print axioms split_resume
#print axioms advance_rows
#print axioms bounded_sound

namespace Selection

open PositionalPublication
open Mettapedia.Machines.RevisionedStoreView.Publication

variable {StoreId : Type}

/-- One retained physical binding. This is source evidence, not execution
authority. No matching or output computation is performed by capture. -/
structure Proposal (StoreId : Type) where
  read : StoreReadToken StoreId Nat
  receiver : Nat
  positions : List Nat
  inputs : List Occurrence

def positions (s : Space) (selected : List Occurrence) : List Nat :=
  selected.map (s.available.idxOf ·)

def capture (s : Retained.State StoreId) (receiver : Nat) (selected : List Occurrence) : Proposal StoreId :=
  ⟨s.origins.view.readToken, receiver, positions s.channel selected, selected⟩

/-- The existing source is held unchanged while the common cursor advances.
The returned packet contains real scan/branch work and the found tuple buffer. -/
def inspect (s : Retained.State StoreId) (fuel : Nat) (work : State) (reversed : List (List Occurrence)) :=
  (s, Cursor.advance (provider s.channel) (NativeControlCursor.client (List Occurrence))
    (fun _ _ => 1) fuel (NativeControlCursor.packet (pull s.channel) work reversed))

theorem inspection_keeps_source (s : Retained.State StoreId) (fuel : Nat) (work : State)
    (reversed : List (List Occurrence)) : (inspect s fuel work reversed).1 = s := rfl

theorem positions_resolve (s : Space) (selected : List Occurrence)
    (present : ∀ e ∈ selected, e ∈ s.available) : Retained.select s.available (positions s selected) = selected := by
  induction selected with
  | nil => rfl
  | cons e rest ih =>
      have first := List.getElem?_idxOf (present e List.mem_cons_self)
      simpa [Retained.select, positions, first] using
        congrArg (e :: ·) (ih (fun next member => present next (List.mem_cons_of_mem _ member)))

theorem positions_distinct (s : Space) (c : Continuation) (selected : List Occurrence)
    (admitted : valid s c selected) :
    (positions s selected).Nodup ∧ ∀ index ∈ positions s selected, index < s.available.length := by
  constructor
  · exact List.Nodup.map_on (fun e member _ _ same =>
      (List.idxOf_inj (admitted.2.2.2 e member).1).mp same)
      (List.Nodup.of_map EventPump.Event.serial admitted.2.2.1)
  · intro index member
    obtain ⟨e, chosen, rfl⟩ := List.mem_map.mp member
    exact List.idxOf_lt_length_iff.mpr (admitted.2.2.2 e chosen).1

/-- Revalidate this exact tuple before invoking the existing current-state
publication. Refusal never falls back to search or to another binding. -/
def perform [DecidableEq StoreId] (current : Retained.State StoreId) (proposal : Proposal StoreId)
    (outputs : List Data) (nextRevision : Nat) : Option (Retained.State StoreId) :=
  if proposal.read = current.origins.view.readToken ∧
      Retained.select current.channel.available proposal.positions = proposal.inputs then
    Retained.advance current ((proposal.read, proposal.positions, outputs, nextRevision), proposal.receiver)
  else none

theorem perform_stale [DecidableEq StoreId] (current : Retained.State StoreId) (proposal : Proposal StoreId)
    (outputs : List Data) (nextRevision : Nat) (stale : proposal.read ≠ current.origins.view.readToken) :
    perform current proposal outputs nextRevision = none := by simp [perform, stale]

theorem perform_changed_tuple [DecidableEq StoreId] (current : Retained.State StoreId) (proposal : Proposal StoreId)
    (outputs : List Data) (nextRevision : Nat)
    (changed : Retained.select current.channel.available proposal.positions ≠ proposal.inputs) :
    perform current proposal outputs nextRevision = none := by simp [perform, changed]

theorem perform_admitted [DecidableEq StoreId] (current next : Retained.State StoreId)
    (proposal : Proposal StoreId) (outputs : List Data) (nextRevision : Nat)
    (accepted : perform current proposal outputs nextRevision = some next) :
    proposal.read = current.origins.view.readToken ∧
      Retained.select current.channel.available proposal.positions = proposal.inputs ∧
      Retained.advance current ((proposal.read, proposal.positions, outputs, nextRevision), proposal.receiver) = some next ∧
      ∃ c, current.channel.receives proposal.receiver = some c ∧ valid current.channel c proposal.inputs ∧
        next.channel = produceOutputs (commit current.channel proposal.receiver proposal.inputs)
          (Retained.freshStart current.channel) outputs := by
  unfold perform at accepted
  split at accepted
  next checks =>
    refine ⟨checks.1, checks.2, accepted, ?_⟩
    obtain ⟨result, applied, equal⟩ := Option.map_eq_some_iff.mp accepted
    cases equal
    obtain ⟨_, c, registered, matched, actual⟩ := Retained.applySpace_admitted
      current.origins.view current.channel _ result applied
    exact ⟨c, registered, by simpa only [checks.2] using matched, by simpa only [checks.2] using actual⟩
  next refused => cases accepted

theorem perform_lawful [DecidableEq StoreId] (current next : Retained.State StoreId)
    (proposal : Proposal StoreId) (outputs : List Data) (nextRevision : Nat)
    (lawful : Retained.Lawful current) (accepted : perform current proposal outputs nextRevision = some next) :
    Retained.Lawful next :=
  Retained.advance_lawful current next _ lawful (perform_admitted current next proposal outputs nextRevision accepted).2.2.1

theorem perform_spends_exact_inputs [DecidableEq StoreId] (current next : Retained.State StoreId)
    (proposal : Proposal StoreId) (outputs : List Data) (nextRevision : Nat)
    (accepted : perform current proposal outputs nextRevision = some next) :
    next.channel.spent = current.channel.spent ++ proposal.inputs.map EventPump.Event.serial := by
  have proof := perform_admitted current next proposal outputs nextRevision accepted
  simpa only [proof.2.1] using Retained.advance_spent current next _ proof.2.2.1

theorem perform_effects [DecidableEq StoreId] (current next : Retained.State StoreId)
    (proposal : Proposal StoreId) (outputs : List Data) (nextRevision : Nat)
    (accepted : perform current proposal outputs nextRevision = some next) :
    next.channel.available = current.channel.available.filter (fun e => decide (e ∉ proposal.inputs)) ++
        outputEvents (Retained.freshStart current.channel) outputs ∧
      next.channel.spent = current.channel.spent ++ proposal.inputs.map EventPump.Event.serial ∧
      next.channel.ready = current.channel.ready ++ [⟨proposal.receiver, proposal.inputs⟩] := by
  obtain ⟨c, registered, admitted, actual⟩ :=
    (perform_admitted current next proposal outputs nextRevision accepted).2.2.2
  have bounded : ∀ e ∈ (commit current.channel proposal.receiver proposal.inputs).produced,
      e.serial < Retained.freshStart current.channel := by
    simpa only [commit, registered, if_pos admitted] using Retained.below_freshStart current.channel
  rw [produceOutputs_exact _ _ _ bounded] at actual
  have atomic := successful_join_is_atomic current.channel proposal.receiver c proposal.inputs registered admitted
  refine ⟨?_, ?_, ?_⟩
  · rw [actual]
    exact congrArg (· ++ outputEvents (Retained.freshStart current.channel) outputs) atomic.1
  · rw [actual]; exact atomic.2.1
  · rw [actual]; exact atomic.2.2

theorem perform_cannot_reuse [DecidableEq StoreId] (current next : Retained.State StoreId)
    (proposal : Proposal StoreId) (outputs : List Data) (nextRevision : Nat)
    (accepted : perform current proposal outputs nextRevision = some next)
    (c : Continuation) (candidate : List Occurrence) (e : Occurrence)
    (chosen : e ∈ proposal.inputs) (reused : e ∈ candidate) : ¬ valid next.channel c candidate := by
  intro again
  apply (again.2.2.2 e reused).2
  rw [perform_spends_exact_inputs current next proposal outputs nextRevision accepted]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨e, chosen, rfl⟩)

theorem perform_cannot_repeat [DecidableEq StoreId] (current next : Retained.State StoreId)
    (proposal : Proposal StoreId) (outputs laterOutputs : List Data) (nextRevision laterRevision : Nat)
    (accepted : perform current proposal outputs nextRevision = some next) :
    perform next proposal laterOutputs laterRevision = none := by
  obtain ⟨c, _, first, _⟩ := (perform_admitted current next proposal outputs nextRevision accepted).2.2.2
  cases repeated : perform next proposal laterOutputs laterRevision with
  | none => rfl
  | some final =>
      obtain ⟨later, _, matching, _⟩ := (perform_admitted next final proposal laterOutputs laterRevision repeated).2.2.2
      cases inputs : proposal.inputs with
      | nil => exact False.elim (first.1 inputs)
      | cons e rest =>
          have chosen : e ∈ proposal.inputs := by simp [inputs]
          exact False.elim (perform_cannot_reuse current next proposal outputs nextRevision accepted later proposal.inputs e chosen chosen matching)

theorem perform_reused_revision [DecidableEq StoreId] (current : Retained.State StoreId) (proposal : Proposal StoreId)
    (outputs : List Data) (nextRevision : Nat) (old : nextRevision ≤ current.origins.view.revision) :
    perform current proposal outputs nextRevision = none := by
  simp [perform, Retained.advance, Retained.applySpace, Retained.consumeSpace, Finite.apply, Nat.not_lt_of_ge old]

/-- Every independently valid discovered tuple can be selected in its current
lawful source. This does not replace the current receiver or its permission. -/
theorem discovered_binding_can_commit [DecidableEq StoreId] (s : Retained.State StoreId)
    (receiver : Nat) (c : Continuation) (selected : List Occurrence) (outputs : List Data) (nextRevision : Nat)
    (lawful : Retained.Lawful s) (registered : s.channel.receives receiver = some c)
    (discovered : selected ∈ residualRows s.channel (start c)) (fresh : s.origins.view.revision < nextRevision) :
    ∃ next, perform s (capture s receiver selected) outputs nextRevision = some next ∧ Retained.Lawful next := by
  have matched := (start_iff s.channel c selected).mp discovered
  have located := positions_resolve s.channel selected (fun e member => (matched.2.2.2 e member).1)
  obtain ⟨distinct, bounded⟩ := positions_distinct s.channel c selected matched
  have lengths : s.channel.available.length = s.origins.view.entries.length := by
    simpa only [List.length_map] using congrArg List.length lawful.2.1
  let request : Finite.Request StoreId Data × Nat :=
    ((s.origins.view.readToken, positions s.channel selected, outputs, nextRevision), receiver)
  let next : Retained.State StoreId :=
    ⟨⟨updated s.origins.view (positions s.channel selected) outputs nextRevision,
      Finite.transport s.origins request.1⟩,
      produceOutputs (commit s.channel receiver selected) (Retained.freshStart s.channel) outputs⟩
  have advanced : Retained.advance s request = some next := by
    have different : nextRevision ≠ s.origins.view.revision := Nat.ne_of_gt fresh
    have bounds : ∀ index ∈ positions s.channel selected, index < s.origins.view.entries.length :=
      fun index member => lengths ▸ bounded index member
    simp [Retained.advance, Retained.applySpace, Retained.consumeSpace, Finite.apply, publish, request, fresh,
      distinct, different, registered, located, matched, next]
    simp only [if_pos bounds, Option.bind_some]
  have accepted : perform s (capture s receiver selected) outputs nextRevision = some next := by
    simpa [perform, capture, located] using advanced
  exact ⟨next, accepted, perform_lawful s next _ outputs nextRevision lawful accepted⟩

theorem selected_cannot_retarget [DecidableEq StoreId] (current next : Retained.State StoreId)
    (proposal : Proposal StoreId) (outputs : List Data) (nextRevision : Nat)
    (accepted : perform current proposal outputs nextRevision = some next) :
    ∃ c, current.channel.receives proposal.receiver = some c ∧ valid current.channel c proposal.inputs ∧
      next.channel = produceOutputs (commit current.channel proposal.receiver proposal.inputs)
        (Retained.freshStart current.channel) outputs :=
  (perform_admitted current next proposal outputs nextRevision accepted).2.2.2

theorem bounded_binding_can_commit [DecidableEq StoreId] (s : Retained.State StoreId)
    (receiver : Nat) (c : Continuation) (fuel : Nat) (selected : List Occurrence) (outputs : List Data) (nextRevision : Nat)
    (lawful : Retained.Lawful s) (registered : s.channel.receives receiver = some c)
    (found : selected ∈ observed s.channel (inspect s fuel (start c) []).2.2)
    (fresh : s.origins.view.revision < nextRevision) :
    ∃ next, perform s (capture s receiver selected) outputs nextRevision = some next ∧ Retained.Lawful next :=
  discovered_binding_can_commit s receiver c selected outputs nextRevision lawful registered
    ((start_iff s.channel c selected).mpr (bounded_sound s.channel c fuel selected found)) fresh

#print axioms positions_resolve
#print axioms inspection_keeps_source
#print axioms positions_distinct
#print axioms perform_stale
#print axioms perform_changed_tuple
#print axioms perform_admitted
#print axioms perform_lawful
#print axioms perform_spends_exact_inputs
#print axioms perform_effects
#print axioms perform_cannot_reuse
#print axioms perform_cannot_repeat
#print axioms perform_reused_revision
#print axioms discovered_binding_can_commit
#print axioms selected_cannot_retarget
#print axioms bounded_binding_can_commit

end Selection

namespace Controls

open PositionalPublication
open Selection

def alpha : EventPump.Key := ⟨1, 0, 0⟩
def beta : EventPump.Key := ⟨2, 0, 0⟩
def view : View Nat Nat := ⟨17, 4, [(alpha, 7), (alpha, 7), (beta, 9)]⟩
def receiver : Continuation := ⟨[⟨alpha, fun _ => true⟩, ⟨alpha, fun _ => true⟩], true⟩
def source := Retained.initial view 7 receiver
def firstTuple : List Occurrence := [⟨0, alpha, 7⟩, ⟨1, alpha, 7⟩]
def secondTuple := firstTuple.reverse

def zero := inspect source 0 (start receiver) []
def page := inspect source 6 (start receiver) []
def complete := Cursor.resume (provider source.channel) (NativeControlCursor.client (List Occurrence))
  (fun _ _ => 1) 64 page.2

theorem equal_payloads_have_distinct_ordered_physical_bindings :
    collect (pull source.channel) 64 (start receiver) = some [firstTuple, secondTuple] ∧
      (observed source.channel complete.2).map (List.map EventPump.Event.serial) = [[0, 1], [1, 0]] ∧
      source.channel.spent = [] ∧ source.channel.ready = [] ∧
      ¬ valid source.channel receiver [⟨0, alpha, 7⟩, ⟨0, alpha, 7⟩] := by decide

theorem bounded_page_keeps_source_and_the_actual_unsearched_suffix :
    zero.2.1 = 0 ∧ observed source.channel zero.2.2 = [] ∧
      (match zero.2.2 with | .paused _ => true | .done _ => false) = true ∧
      observed source.channel page.2.2 = [firstTuple] ∧
      residualRows source.channel (saved source.channel page.2.2) = [secondTuple] ∧
      (NativeControlCursor.published (pull source.channel) page.2.2).isNone = true ∧
      NativeControlCursor.published (pull source.channel) complete.2 = some [firstTuple, secondTuple] ∧
      page.1.channel.spent = [] ∧ page.1.channel.ready = [] := by decide

/-- The first proposal is captured directly from a paused discovery page. -/
def selected := capture source 7 ((observed source.channel page.2.2).headD [])
def otherSelected := capture source 7 (((observed source.channel complete.2).drop 1).headD [])
def firstCommit := perform source selected [] 5
def secondCommit := perform source otherSelected [] 5

theorem selection_commits_the_chosen_binding_and_never_a_retarget :
    selected.positions = [0, 1] ∧ selected.inputs = firstTuple ∧
      firstCommit.map (fun s => (s.channel.available.map EventPump.Event.serial, s.channel.spent,
        s.channel.ready.map (fun r => r.inputs.map EventPump.Event.serial))) = some ([2], [0, 1], [[0, 1]]) ∧
      secondCommit.map (fun s => (s.channel.available.map EventPump.Event.serial, s.channel.spent,
        s.channel.ready.map (fun r => r.inputs.map EventPump.Event.serial))) = some ([2], [1, 0], [[1, 0]]) ∧
      (perform source { selected with positions := [1, 0] } [] 5).isNone = true ∧
      (perform source { selected with read := ⟨18, 4⟩ } [] 5).isNone = true ∧
      (perform source { selected with receiver := 9 } [] 5).isNone = true := by decide

def replaced := (perform source selected [(alpha, 7), (alpha, 7)] 5).getD source
def freshSelected := capture replaced 7 [⟨3, alpha, 7⟩, ⟨4, alpha, 7⟩]

theorem restored_equal_data_does_not_restore_selection_currency :
    replaced.channel.available.map (fun e => (e.serial, e.owner, e.payload)) =
      [(2, beta, 9), (3, alpha, 7), (4, alpha, 7)] ∧
      (perform replaced selected [] 6).isNone = true ∧
      (perform replaced freshSelected [] 6).map (fun s => s.channel.spent) = some [0, 1, 3, 4] ∧
      (perform source selected [] 4).isNone = true ∧
      (perform source selected [] 3).isNone = true ∧
      collect (pull { source.channel with available := [⟨0, alpha, 7⟩] }) 64 (start receiver) = some [] := by decide

#print axioms equal_payloads_have_distinct_ordered_physical_bindings
#print axioms bounded_page_keeps_source_and_the_actual_unsearched_suffix
#print axioms selection_commits_the_chosen_binding_and_never_a_retarget
#print axioms restored_equal_data_does_not_restore_selection_currency

end Controls

/-! ## Selected publication into independently owned private worlds -/

namespace PrivateWorld

open PositionalPublication
open Mettapedia.Machines.RevisionedStoreView.Publication
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.SeparationAlgebra
open _root_.CategoryTheory

variable {StoreId : Type}

def renameRead (names : StoreId ≃ StoreId) (read : StoreReadToken StoreId Nat) :
    StoreReadToken StoreId Nat := ⟨names read.storeId, read.revision⟩

def renameOccurrence (names : StoreId ≃ StoreId) (origin : StoreOccurrenceId StoreId Nat) :
    StoreOccurrenceId StoreId Nat := ⟨renameRead names origin.read, origin.logicalIndex⟩

theorem renameOccurrence_injective (names : StoreId ≃ StoreId) :
    Function.Injective (renameOccurrence names) := by
  rintro ⟨⟨left, age⟩, position⟩ ⟨⟨right, otherAge⟩, otherPosition⟩ same
  simp only [renameOccurrence, renameRead, StoreOccurrenceId.mk.injEq,
    StoreReadToken.mk.injEq] at same
  obtain ⟨⟨equal, rfl⟩, rfl⟩ := same
  cases names.injective equal
  rfl

/-- Transport store scope injectively, retaining actual channel Events and
all existing origin coordinates, payloads and ages. -/
def transport (names : StoreId ≃ StoreId) (s : Retained.State StoreId) : Retained.State StoreId :=
  ⟨⟨⟨names s.origins.view.storeId, s.origins.view.revision, s.origins.view.entries⟩,
    s.origins.rows.map fun pair => (renameOccurrence names pair.1, pair.2)⟩, s.channel⟩

theorem transport_lawful (names : StoreId ≃ StoreId) (s : Retained.State StoreId)
    (lawful : Retained.Lawful s) : Retained.Lawful (transport names s) := by
  refine ⟨⟨?_, ?_, ?_⟩, lawful.2.1, lawful.2.2.1, lawful.2.2.2.1, lawful.2.2.2.2⟩
  · simpa only [transport, List.map_map, Function.comp_def] using lawful.1.1
  · have distinct := lawful.1.2.1.map (renameOccurrence_injective names)
    simpa only [transport, List.map_map, Function.comp_def] using distinct
  · intro origin member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    have age := lawful.1.2.2 old present
    exact ⟨congrArg names age.1, age.2⟩

def fork [DecidableEq StoreId] (parent : Retained.State StoreId) (childId : StoreId) : Retained.State StoreId :=
  transport (Equiv.swap parent.origins.view.storeId childId) parent

/-- The identity transport has the existing owned child's captured data view.
Its independent revision baseline keeps the source origin ages. -/
theorem fork_capture [DecidableEq StoreId] (parent : Retained.State StoreId) (childId : StoreId) :
    (fork parent childId).origins.view =
      { (OwnedFork.capture parent.origins.view childId).view with revision := parent.origins.view.revision } ∧
      (fork parent childId).channel = parent.channel := by
  simp [fork, transport, OwnedFork.capture, OwnedFork.Child.view, OwnedFork.Child.rows]

theorem fork_lawful [DecidableEq StoreId] (parent : Retained.State StoreId) (childId : StoreId)
    (lawful : Retained.Lawful parent) : Retained.Lawful (fork parent childId) :=
  transport_lawful _ parent lawful

def privateProposal [DecidableEq StoreId] (parent : Retained.State StoreId) (childId : StoreId)
    (proposal : Selection.Proposal StoreId) : Selection.Proposal StoreId :=
  { proposal with read := renameRead (Equiv.swap parent.origins.view.storeId childId) proposal.read }

structure Branch (StoreId : Type) where
  source : StoreReadToken StoreId Nat
  state : Retained.State StoreId
  pending : List (Finite.Request StoreId Data × Nat)

variable {World : Type} [Category.{0} World]
  (authority : IndexedAuthority.{0, 0, 0} World) (point : IndexedAuthority.Point authority)
  (required : authority.Fibre point.world) [permission : Decidable (FrameUpdate point.authority required)]

/-- Check the original parent and exact tuple before publishing into a
distinct private scope. The parent is an input, never a publication target.
Discovery evidence supplies neither permission nor a detached replay right. -/
def select [DecidableEq StoreId] (parent : Retained.State StoreId) (proposal : Selection.Proposal StoreId)
    (childId : StoreId) (outputs : List Data) (nextRevision : Nat)
    (remaining : List (Finite.Request StoreId Data × Nat)) : Option (Branch StoreId) :=
  if childId ≠ parent.origins.view.storeId ∧ proposal.read = parent.origins.view.readToken ∧
      Retained.select parent.channel.available proposal.positions = proposal.inputs ∧
      FrameUpdate point.authority required then
    (Selection.perform (fork parent childId) (privateProposal parent childId proposal) outputs nextRevision).map
      fun child => ⟨proposal.read, child, remaining⟩
  else none

theorem select_admitted [DecidableEq StoreId] (parent : Retained.State StoreId)
    (proposal : Selection.Proposal StoreId) (childId : StoreId) (outputs : List Data)
    (nextRevision : Nat) (remaining : List (Finite.Request StoreId Data × Nat)) (branch : Branch StoreId)
    (accepted : select authority point required parent proposal childId outputs nextRevision remaining = some branch) :
    childId ≠ parent.origins.view.storeId ∧ proposal.read = parent.origins.view.readToken ∧
      Retained.select parent.channel.available proposal.positions = proposal.inputs ∧
      FrameUpdate point.authority required ∧ branch.source = proposal.read ∧ branch.pending = remaining ∧
      Selection.perform (fork parent childId) (privateProposal parent childId proposal) outputs nextRevision = some branch.state := by
  unfold select at accepted
  split at accepted
  next checks =>
    obtain ⟨child, performed, same⟩ := Option.map_eq_some_iff.mp accepted
    cases same
    exact ⟨checks.1, checks.2.1, checks.2.2.1, checks.2.2.2, rfl, rfl, performed⟩
  next refused => cases accepted

theorem select_effects [DecidableEq StoreId] (parent : Retained.State StoreId)
    (proposal : Selection.Proposal StoreId) (childId : StoreId) (outputs : List Data)
    (nextRevision : Nat) (remaining : List (Finite.Request StoreId Data × Nat)) (branch : Branch StoreId)
    (accepted : select authority point required parent proposal childId outputs nextRevision remaining = some branch) :
    branch.state.channel.available = parent.channel.available.filter (fun e => decide (e ∉ proposal.inputs)) ++
        outputEvents (Retained.freshStart parent.channel) outputs ∧
      branch.state.channel.spent = parent.channel.spent ++ proposal.inputs.map EventPump.Event.serial ∧
      branch.state.channel.ready = parent.channel.ready ++ [⟨proposal.receiver, proposal.inputs⟩] := by
  have admitted := select_admitted authority point required parent proposal childId outputs nextRevision remaining branch accepted
  exact Selection.perform_effects (fork parent childId) branch.state
    (privateProposal parent childId proposal) outputs nextRevision admitted.2.2.2.2.2.2

theorem select_lawful [DecidableEq StoreId] (parent : Retained.State StoreId)
    (proposal : Selection.Proposal StoreId) (childId : StoreId) (outputs : List Data)
    (nextRevision : Nat) (remaining : List (Finite.Request StoreId Data × Nat)) (branch : Branch StoreId)
    (lawful : Retained.Lawful parent)
    (accepted : select authority point required parent proposal childId outputs nextRevision remaining = some branch) :
    Retained.Lawful branch.state :=
  Selection.perform_lawful _ _ _ _ _ (fork_lawful parent childId lawful)
    (select_admitted authority point required parent proposal childId outputs nextRevision remaining branch accepted).2.2.2.2.2.2

theorem select_stale [DecidableEq StoreId] (parent : Retained.State StoreId)
    (proposal : Selection.Proposal StoreId) (childId : StoreId) (outputs : List Data)
    (nextRevision : Nat) (remaining : List (Finite.Request StoreId Data × Nat))
    (stale : proposal.read ≠ parent.origins.view.readToken) :
    select authority point required parent proposal childId outputs nextRevision remaining = none := by
  simp [select, stale]

theorem select_needs_private_identity [DecidableEq StoreId] (parent : Retained.State StoreId)
    (proposal : Selection.Proposal StoreId) (outputs : List Data) (nextRevision : Nat)
    (remaining : List (Finite.Request StoreId Data × Nat)) :
    select authority point required parent proposal parent.origins.view.storeId outputs nextRevision remaining = none := by
  simp [select]

theorem select_denied [DecidableEq StoreId] (parent : Retained.State StoreId)
    (proposal : Selection.Proposal StoreId) (childId : StoreId) (outputs : List Data)
    (nextRevision : Nat) (remaining : List (Finite.Request StoreId Data × Nat))
    (denied : ¬ FrameUpdate point.authority required) :
    select authority point required parent proposal childId outputs nextRevision remaining = none := by
  simp [select, denied]

private theorem advance_scope [DecidableEq StoreId] (s next : Retained.State StoreId)
    (request : Finite.Request StoreId Data × Nat) (accepted : Retained.advance s request = some next) :
    next.origins.view.storeId = s.origins.view.storeId ∧ next.origins.view.revision = request.1.2.2.2 := by
  obtain ⟨result, applied, same⟩ := Option.map_eq_some_iff.mp accepted
  cases same
  have published := (Retained.applySpace_admitted s.origins.view s.channel request result applied).1
  unfold Finite.apply at published
  split at published
  next fresh =>
    have exactView := (publication_admitted s.origins.view request.1.1 request.1.2.1 request.1.2.2.1
      request.1.2.2.2 result.1 published).2.2.2.2
    rw [exactView]
    exact ⟨rfl, rfl⟩
  next refused => cases published

theorem select_scope [DecidableEq StoreId] (parent : Retained.State StoreId)
    (proposal : Selection.Proposal StoreId) (childId : StoreId) (outputs : List Data)
    (nextRevision : Nat) (remaining : List (Finite.Request StoreId Data × Nat)) (branch : Branch StoreId)
    (accepted : select authority point required parent proposal childId outputs nextRevision remaining = some branch) :
    branch.source = parent.origins.view.readToken ∧
      branch.state.origins.view.storeId = childId ∧ branch.state.origins.view.revision = nextRevision := by
  have admitted := select_admitted authority point required parent proposal childId outputs nextRevision remaining branch accepted
  have moved := (Selection.perform_admitted _ _ _ _ _ admitted.2.2.2.2.2.2).2.2.1
  have scopeFacts := advance_scope _ _ _ moved
  exact ⟨admitted.2.2.2.2.1.trans admitted.2.1,
    by simpa only [fork, transport, Equiv.swap_apply_left] using scopeFacts.1, scopeFacts.2⟩

theorem observed_binding_can_select [DecidableEq StoreId] (parent : Retained.State StoreId)
    (receiver : Nat) (c : Continuation) (fuel : Nat) (chosen : List Occurrence) (childId : StoreId)
    (outputs : List Data) (nextRevision : Nat) (remaining : List (Finite.Request StoreId Data × Nat))
    (lawful : Retained.Lawful parent) (registered : parent.channel.receives receiver = some c)
    (found : chosen ∈ observed parent.channel (Selection.inspect parent fuel (start c) []).2.2)
    (different : childId ≠ parent.origins.view.storeId) (allowed : FrameUpdate point.authority required)
    (fresh : parent.origins.view.revision < nextRevision) :
    ∃ branch, select authority point required parent (Selection.capture parent receiver chosen)
      childId outputs nextRevision remaining = some branch ∧ Retained.Lawful branch.state := by
  have matched := bounded_sound parent.channel c fuel chosen found
  have located := Selection.positions_resolve parent.channel chosen (fun e member => (matched.2.2.2 e member).1)
  obtain ⟨child, performed, childLawful⟩ := Selection.discovered_binding_can_commit
    (fork parent childId) receiver c chosen outputs nextRevision (fork_lawful parent childId lawful)
    registered ((start_iff _ c chosen).mpr matched) fresh
  have captureTransport : privateProposal parent childId (Selection.capture parent receiver chosen) =
      Selection.capture (fork parent childId) receiver chosen := rfl
  refine ⟨⟨parent.origins.view.readToken, child, remaining⟩, ?_, childLawful⟩
  unfold select
  rw [if_pos ⟨different, rfl, located, allowed⟩]
  rw [captureTransport, performed]
  rfl

theorem selected_survivor_origin [DecidableEq StoreId] (parent : Retained.State StoreId)
    (proposal : Selection.Proposal StoreId) (childId : StoreId) (outputs : List Data)
    (nextRevision : Nat) (remaining : List (Finite.Request StoreId Data × Nat)) (branch : Branch StoreId)
    (lawful : Retained.Lawful parent)
    (accepted : select authority point required parent proposal childId outputs nextRevision remaining = some branch)
    (index : Nat) (origin : StoreOccurrenceId StoreId Nat × Data) (event : Occurrence)
    (named : parent.origins.rows[index]? = some origin) (actual : parent.channel.available[index]? = some event)
    (unchosen : index ∉ proposal.positions) :
    ∃ target : Nat, branch.state.origins.rows[target]? =
      some (renameOccurrence (Equiv.swap parent.origins.view.storeId childId) origin.1, origin.2) ∧
      branch.state.channel.available[target]? = some event := by
  have admitted := select_admitted authority point required parent proposal childId outputs nextRevision remaining branch accepted
  have moved := (Selection.perform_admitted _ _ _ _ _ admitted.2.2.2.2.2.2).2.2.1
  apply Retained.advance_keeps_pair (fork parent childId) branch.state _ (fork_lawful parent childId lawful) moved index _ event
  · simp only [fork, transport, List.getElem?_map, named, Option.map_some]
  · exact actual
  · exact unchosen

/-- Continue an existing positional publication word, retaining its complete
residual. The source and branch scopes are never renamed by continuation. -/
def progress [DecidableEq StoreId] (allowance : Nat) (branch : Branch StoreId) : Option (Branch StoreId) :=
  (Retained.run (branch.pending.take allowance) branch.state).map fun next =>
    { branch with state := next, pending := branch.pending.drop allowance }

theorem progress_admitted [DecidableEq StoreId] (allowance : Nat) (before after : Branch StoreId)
    (accepted : progress allowance before = some after) :
    after.source = before.source ∧ after.pending = before.pending.drop allowance ∧
      Retained.run (before.pending.take allowance) before.state = some after.state := by
  obtain ⟨next, actual, same⟩ := Option.map_eq_some_iff.mp accepted
  cases same
  exact ⟨rfl, rfl, actual⟩

theorem progress_split [DecidableEq StoreId] (first second : Nat) (branch : Branch StoreId) :
    progress (first + second) branch = (progress first branch).bind (progress second) := by
  simp only [progress, List.take_add, Retained.run_append]
  cases actual : Retained.run (List.take first branch.pending) branch.state with
  | none => rfl
  | some next => simp only [Option.bind_some, Option.map_some, progress, List.drop_drop]

theorem progress_lawful [DecidableEq StoreId] (allowance : Nat) (before after : Branch StoreId)
    (lawful : Retained.Lawful before.state) (accepted : progress allowance before = some after) :
    Retained.Lawful after.state :=
  Retained.run_lawful _ _ _ lawful (progress_admitted allowance before after accepted).2.2

/-- The original exact parent read remains a live obligation of unfinished
worlds. Retaining a private copy supplies no detached historical replay right. -/
def resume [DecidableEq StoreId] (parent : Retained.State StoreId) (allowance : Nat)
    (branch : Branch StoreId) : Option (Branch StoreId) :=
  if allowance = 0 ∨ branch.pending = [] then some branch else
  if branch.source = parent.origins.view.readToken ∧ FrameUpdate point.authority required then
    progress allowance branch
  else none

theorem resume_zero [DecidableEq StoreId] (parent : Retained.State StoreId) (branch : Branch StoreId) :
    resume authority point required parent 0 branch = some branch := by simp [resume]

theorem resume_current [DecidableEq StoreId] (parent : Retained.State StoreId) (allowance : Nat) (branch : Branch StoreId)
    (current : branch.source = parent.origins.view.readToken) (allowed : FrameUpdate point.authority required) :
    resume authority point required parent allowance branch = progress allowance branch := by
  unfold resume
  split
  next idle =>
    rcases idle with zero | finished
    · subst allowance; rfl
    · rcases branch with ⟨source, state, pending⟩
      change pending = [] at finished
      subst pending
      simp only [progress, List.take_nil, List.drop_nil, Retained.run, Option.map_some]
  next active => simp only [current, allowed, and_self, ↓reduceIte]

theorem resume_stale [DecidableEq StoreId] (parent : Retained.State StoreId) (allowance : Nat) (branch : Branch StoreId)
    (work : allowance ≠ 0 ∧ branch.pending ≠ []) (stale : branch.source ≠ parent.origins.view.readToken) :
    resume authority point required parent allowance branch = none := by simp [resume, work.1, work.2, stale]

theorem resume_denied [DecidableEq StoreId] (parent : Retained.State StoreId) (allowance : Nat) (branch : Branch StoreId)
    (work : allowance ≠ 0 ∧ branch.pending ≠ []) (denied : ¬ FrameUpdate point.authority required) :
    resume authority point required parent allowance branch = none := by simp [resume, work.1, work.2, denied]

private theorem run_scope [DecidableEq StoreId] (requests : List (Finite.Request StoreId Data × Nat))
    (before after : Retained.State StoreId) (accepted : Retained.run requests before = some after) :
    after.origins.view.storeId = before.origins.view.storeId := by
  induction requests generalizing before with
  | nil => cases Option.some.inj accepted; rfl
  | cons request rest ih =>
      obtain ⟨next, moved, continued⟩ := Option.bind_eq_some_iff.mp accepted
      exact (ih next continued).trans (advance_scope before next request moved).1

theorem progress_scope [DecidableEq StoreId] (allowance : Nat) (before after : Branch StoreId)
    (accepted : progress allowance before = some after) :
    after.source = before.source ∧ after.state.origins.view.storeId = before.state.origins.view.storeId := by
  have admitted := progress_admitted allowance before after accepted
  exact ⟨admitted.1, run_scope _ _ _ admitted.2.2⟩

theorem continued_origin_or_spent [DecidableEq StoreId] (allowance : Nat) (before after : Branch StoreId)
    (lawful : Retained.Lawful before.state) (accepted : progress allowance before = some after)
    (index : Nat) (origin : StoreOccurrenceId StoreId Nat × Data) (event : Occurrence)
    (named : before.state.origins.rows[index]? = some origin)
    (actual : before.state.channel.available[index]? = some event) :
    (origin.1 ∉ after.state.origins.rows.map Prod.fst ∧ event.serial ∈ after.state.channel.spent) ∨
      ∃ target : Nat, after.state.origins.rows[target]? = some origin ∧
        after.state.channel.available[target]? = some event :=
  Retained.run_origin_or_spent _ _ _ lawful (progress_admitted allowance before after accepted).2.2
    index origin event named actual

theorem resume_split [DecidableEq StoreId] (parent : Retained.State StoreId) (first second : Nat)
    (branch : Branch StoreId) (current : branch.source = parent.origins.view.readToken)
    (allowed : FrameUpdate point.authority required) :
    resume authority point required parent (first + second) branch =
      (resume authority point required parent first branch).bind (resume authority point required parent second) := by
  rw [resume_current authority point required parent (first + second) branch current allowed,
    resume_current authority point required parent first branch current allowed, progress_split]
  cases advanced : progress first branch with
  | none => rfl
  | some next =>
      simp only [Option.bind_some]
      exact (resume_current authority point required parent second next
        ((progress_admitted first branch next advanced).1.trans current) allowed).symm

/-- Different private publications keep different store scopes. Their Events
may share source origins; this is not a license to merge or live-consume them. -/
theorem separate_selected_scopes [DecidableEq StoreId] (parent : Retained.State StoreId)
    (leftProposal rightProposal : Selection.Proposal StoreId) (leftId rightId : StoreId)
    (leftOutputs rightOutputs : List Data) (leftRevision rightRevision : Nat)
    (leftRemaining rightRemaining : List (Finite.Request StoreId Data × Nat)) (left right : Branch StoreId)
    (different : leftId ≠ rightId)
    (leftAccepted : select authority point required parent leftProposal leftId leftOutputs leftRevision leftRemaining = some left)
    (rightAccepted : select authority point required parent rightProposal rightId rightOutputs rightRevision rightRemaining = some right) :
    left.source = right.source ∧ left.state.origins.view.storeId ≠ right.state.origins.view.storeId := by
  have leftScope := select_scope authority point required parent leftProposal leftId leftOutputs leftRevision leftRemaining left leftAccepted
  have rightScope := select_scope authority point required parent rightProposal rightId rightOutputs rightRevision rightRemaining right rightAccepted
  exact ⟨leftScope.1.trans rightScope.1.symm, by rw [leftScope.2.1, rightScope.2.1]; exact different⟩

theorem two_worlds_can_select_one_observed_binding [DecidableEq StoreId] (parent : Retained.State StoreId)
    (receiver : Nat) (c : Continuation) (fuel : Nat) (chosen : List Occurrence) (leftId rightId : StoreId)
    (outputs : List Data) (nextRevision : Nat) (leftRemaining rightRemaining : List (Finite.Request StoreId Data × Nat))
    (lawful : Retained.Lawful parent) (registered : parent.channel.receives receiver = some c)
    (found : chosen ∈ observed parent.channel (Selection.inspect parent fuel (start c) []).2.2)
    (leftFresh : leftId ≠ parent.origins.view.storeId) (rightFresh : rightId ≠ parent.origins.view.storeId)
    (separate : leftId ≠ rightId) (allowed : FrameUpdate point.authority required)
    (fresh : parent.origins.view.revision < nextRevision) :
    ∃ left right, select authority point required parent (Selection.capture parent receiver chosen)
        leftId outputs nextRevision leftRemaining = some left ∧
      select authority point required parent (Selection.capture parent receiver chosen)
        rightId outputs nextRevision rightRemaining = some right ∧
      Retained.Lawful left.state ∧ Retained.Lawful right.state ∧
      left.source = right.source ∧ left.state.origins.view.storeId ≠ right.state.origins.view.storeId := by
  obtain ⟨left, selectedLeft, lawfulLeft⟩ := observed_binding_can_select authority point required parent receiver c fuel chosen
    leftId outputs nextRevision leftRemaining lawful registered found leftFresh allowed fresh
  obtain ⟨right, selectedRight, lawfulRight⟩ := observed_binding_can_select authority point required parent receiver c fuel chosen
    rightId outputs nextRevision rightRemaining lawful registered found rightFresh allowed fresh
  exact ⟨left, right, selectedLeft, selectedRight, lawfulLeft, lawfulRight,
    separate_selected_scopes authority point required parent _ _ leftId rightId outputs outputs nextRevision nextRevision
      leftRemaining rightRemaining left right separate selectedLeft selectedRight⟩

theorem parent_publication_invalidates_pending_world [DecidableEq StoreId] (parent changed : Retained.State StoreId)
    (request : Finite.Request StoreId Data × Nat) (published : Retained.advance parent request = some changed)
    (branch : Branch StoreId) (captured : branch.source = parent.origins.view.readToken)
    (allowance : Nat) (work : allowance ≠ 0 ∧ branch.pending ≠ []) :
    resume authority point required changed allowance branch = none := by
  apply resume_stale authority point required changed allowance branch work
  intro renewed
  have equalAge := congrArg StoreReadToken.revision (captured.symm.trans renewed)
  have scopeFacts := advance_scope parent changed request published
  obtain ⟨result, applied, same⟩ := Option.map_eq_some_iff.mp published
  have granted := (Retained.applySpace_admitted parent.origins.view parent.channel request result applied).1
  unfold Finite.apply at granted
  split at granted
  next fresh =>
    have ages : parent.origins.view.revision = request.1.2.2.2 := equalAge.trans scopeFacts.2
    exact (Nat.ne_of_lt fresh) ages
  next refused => cases granted

theorem private_selection_grants_no_repeated_live_consume [DecidableEq StoreId]
    (parent liveNext : Retained.State StoreId) (proposal : Selection.Proposal StoreId)
    (outputs laterOutputs : List Data) (nextRevision laterRevision : Nat)
    (liveConsumed : Selection.perform parent proposal outputs nextRevision = some liveNext) :
    Selection.perform liveNext proposal laterOutputs laterRevision = none :=
  Selection.perform_cannot_repeat parent liveNext proposal outputs laterOutputs nextRevision laterRevision liveConsumed

variable {Holder Use : Type} [DecidableEq Holder] [DecidableEq Use]

abbrev Registry (Holder Use StoreId : Type) := ResourceOwnership.AcquiredUse.State Holder Use (Branch StoreId)

/-- The owned payload is the actual branch, including its real saved state
and remaining program. Existing registry operations control its lifetime. -/
def selectOwned [DecidableEq StoreId] (holder : Holder) (parent : Retained.State StoreId)
    (proposal : Selection.Proposal StoreId) (childId : StoreId) (outputs : List Data) (nextRevision : Nat)
    (remaining : List (Finite.Request StoreId Data × Nat)) : Option (Registry Holder Use StoreId) :=
  (select authority point required parent proposal childId outputs nextRevision remaining).map
    (ResourceOwnership.AcquiredUse.initial holder)

/-- Mutation requires an actual exclusive issued use as well as current
parent/permission checks. A lifetime copy cannot run this operation. -/
def advanceUse [DecidableEq StoreId] (parent : Retained.State StoreId) (use : Use) (allowance : Nat)
    (registry : Registry Holder Use StoreId) : Option (Registry Holder Use StoreId) :=
  if ResourceOwnership.AcquiredUse.mayMutate use registry then
    (ResourceOwnership.AcquiredUse.readUse use registry).bind fun branch =>
      (resume authority point required parent allowance branch).map fun next => { registry with resource := some next }
  else none

omit [DecidableEq Holder] in
theorem advanceUse_admitted [DecidableEq StoreId] (parent : Retained.State StoreId) (use : Use) (allowance : Nat)
    (before after : Registry Holder Use StoreId)
    (accepted : advanceUse authority point required parent use allowance before = some after) :
    ResourceOwnership.AcquiredUse.mayMutate use before ∧
      ∃ branch next, ResourceOwnership.AcquiredUse.readUse use before = some branch ∧
        resume authority point required parent allowance branch = some next ∧
        after = { before with resource := some next } := by
  unfold advanceUse at accepted
  split at accepted
  next owned =>
    obtain ⟨branch, held, advanced⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨next, resumed, same⟩ := Option.map_eq_some_iff.mp advanced
    exact ⟨owned, branch, next, held, resumed, same.symm⟩
  next refused => cases accepted

omit [DecidableEq Holder] in
theorem advanceUse_wellFormed [DecidableEq StoreId] (parent : Retained.State StoreId) (use : Use) (allowance : Nat)
    (before after : Registry Holder Use StoreId) (valid : ResourceOwnership.AcquiredUse.WellFormed before)
    (accepted : advanceUse authority point required parent use allowance before = some after) :
    ResourceOwnership.AcquiredUse.WellFormed after := by
  obtain ⟨owned, branch, next, _, _, rfl⟩ := advanceUse_admitted authority point required parent use allowance before after accepted
  refine ⟨?_, valid.exclusive_issued⟩
  exact ⟨fun _ => Or.inr ⟨use, owned.1⟩, fun _ => rfl⟩

omit [DecidableEq Holder] in
theorem unknown_or_lifetime_use_refused [DecidableEq StoreId] (parent : Retained.State StoreId)
    (use : Use) (allowance : Nat) (registry : Registry Holder Use StoreId)
    (noRight : ¬ ResourceOwnership.AcquiredUse.mayMutate use registry) :
    advanceUse authority point required parent use allowance registry = none := by simp [advanceUse, noRight]

omit [DecidableEq Holder] in
theorem moved_world_is_the_same_saved_computation (source destination : Use)
    (before : Registry Holder Use StoreId)
    (result : ResourceOwnership.AcquiredUse.Result Holder Use (Branch StoreId))
    (moved : ResourceOwnership.AcquiredUse.moveUse source destination before = some result) :
    result.next.resource = before.resource ∧ result.next.current = before.current := by
  have kept := ResourceOwnership.AcquiredUse.moveUse_keeps_currency source destination moved
  exact ⟨kept.2, kept.1⟩

/-- Resuming one independent private owner frames the complete sibling
registry. It does not combine their resource snapshots. -/
def advanceLeft [DecidableEq StoreId] (parent : Retained.State StoreId) (use : Use) (allowance : Nat)
    (pair : Registry Holder Use StoreId × Registry Holder Use StoreId) :=
  (advanceUse authority point required parent use allowance pair.1).map fun next => (next, pair.2)

def advanceRight [DecidableEq StoreId] (parent : Retained.State StoreId) (use : Use) (allowance : Nat)
    (pair : Registry Holder Use StoreId × Registry Holder Use StoreId) :=
  (advanceUse authority point required parent use allowance pair.2).map fun next => (pair.1, next)

omit [DecidableEq Holder] in
theorem independent_worlds_commute [DecidableEq StoreId] (parent : Retained.State StoreId)
    (leftUse rightUse : Use) (leftAllowance rightAllowance : Nat)
    (pair : Registry Holder Use StoreId × Registry Holder Use StoreId) :
    (advanceLeft authority point required parent leftUse leftAllowance pair).bind
        (advanceRight authority point required parent rightUse rightAllowance) =
      (advanceRight authority point required parent rightUse rightAllowance pair).bind
        (advanceLeft authority point required parent leftUse leftAllowance) := by
  unfold advanceLeft advanceRight
  cases left : advanceUse authority point required parent leftUse leftAllowance pair.1 <;>
    cases right : advanceUse authority point required parent rightUse rightAllowance pair.2 <;>
    simp [left, right]

#print axioms progress_scope
#print axioms continued_origin_or_spent
#print axioms resume_split
#print axioms separate_selected_scopes
#print axioms two_worlds_can_select_one_observed_binding
#print axioms parent_publication_invalidates_pending_world
#print axioms private_selection_grants_no_repeated_live_consume
#print axioms advanceUse_admitted
#print axioms advanceUse_wellFormed
#print axioms unknown_or_lifetime_use_refused
#print axioms moved_world_is_the_same_saved_computation
#print axioms independent_worlds_commute

namespace Controls

local instance : Fintype Access :=
  ⟨{.none, .read, .consume}, by intro access; cases access <;> simp⟩

def held : IndexedAuthority.Point revocationWorlds := ⟨false, .consume⟩
def revoked : IndexedAuthority.Point revocationWorlds :=
  IndexedAuthority.push held (homOfLE (by decide) : false ⟶ true)

local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (Access.consume : revocationWorlds.Fibre point.world)) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate point.authority frame = true → Access.separate Access.consume frame = true))

def alpha : EventPump.Key := ⟨1, 0, 0⟩
def beta : EventPump.Key := ⟨2, 0, 0⟩
def view : View Nat Nat := ⟨17, 4, [(alpha, 7), (alpha, 7), (beta, 9)]⟩
def receiver : Continuation := ⟨[⟨alpha, fun _ => true⟩], true⟩
def parent := Retained.initial view 7 receiver
def chosen := (observed parent.channel (Selection.inspect parent 3 (start receiver) []).2.2).headD []
def proposal := Selection.capture parent 7 chosen
def remaining (child : Nat) : List (Finite.Request Nat Data × Nat) :=
  [((⟨child, 5⟩, [0], [(alpha, 7)], 6), 7), ((⟨child, 6⟩, [1], [], 7), 7)]
def fallback : Branch Nat := ⟨view.readToken, parent, []⟩
def left := (select revocationWorlds held Access.consume parent proposal 101 [(alpha, 42)] 5 (remaining 101)).getD fallback
def right := (select revocationWorlds held Access.consume parent proposal 102 [(alpha, 42)] 5 (remaining 102)).getD fallback

def readout (branch : Branch Nat) : Nat × Nat × Nat × Nat × List Nat × List Nat × List (List Nat) × Nat :=
  (branch.source.storeId, branch.source.revision, branch.state.origins.view.storeId, branch.state.origins.view.revision,
    branch.state.channel.available.map EventPump.Event.serial, branch.state.channel.spent,
    branch.state.channel.ready.map (fun row => row.inputs.map EventPump.Event.serial), branch.pending.length)

local instance : DecidableEq (List Nat × List Nat × List (List Nat) × Nat) := inferInstance

theorem one_source_two_private_publications_with_exact_input_identity :
    chosen.map EventPump.Event.serial = [0] ∧
      readout left = (17, 4, 101, 5, [1, 2, 3], [0], [[0]], 2) ∧
      readout right = (17, 4, 102, 5, [1, 2, 3], [0], [[0]], 2) ∧
      parent.channel.available.map EventPump.Event.serial = [0, 1, 2] ∧ parent.channel.spent = [] ∧
      ((Selection.perform parent proposal [] 5).bind (fun next => Selection.perform next proposal [] 6)).isNone = true := by
  decide

theorem continuation_keeps_own_origin_scope_and_complete_residual :
    (resume revocationWorlds held Access.consume parent 1 left).map readout =
      some (17, 4, 101, 6, [2, 3, 4], [0, 1], [[0], [1]], 1) ∧
      (resume revocationWorlds held Access.consume parent 2 left).map readout =
      some (17, 4, 101, 7, [2, 4], [0, 1, 3], [[0], [1], [3]], 0) ∧
      readout right = (17, 4, 102, 5, [1, 2, 3], [0], [[0]], 2) := by decide

def changed := (Selection.perform parent proposal [(alpha, 7)] 5).getD parent

theorem forged_scope_stale_parent_and_revoked_invocation_refuse :
    (select revocationWorlds held Access.consume parent proposal 17 [] 5 []).isNone = true ∧
      (select revocationWorlds held Access.consume parent { proposal with read := ⟨101, 4⟩ } 101 [] 5 []).isNone = true ∧
      (select revocationWorlds held Access.consume changed proposal 103 [] 6 []).isNone = true ∧
      (resume revocationWorlds held Access.consume changed 1 left).isNone = true ∧
      (resume revocationWorlds revoked Access.consume parent 1 left).isNone = true ∧
      readout left = (17, 4, 101, 5, [1, 2, 3], [0], [[0]], 2) := by decide

def registry : Registry Nat Nat Nat :=
  (selectOwned revocationWorlds held Access.consume 9 parent proposal 101 [(alpha, 42)] 5 (remaining 101)).getD
    (ResourceOwnership.AcquiredUse.initial 9 fallback)
def acquired := (ResourceOwnership.AcquiredUse.acquire 1 .exclusive 9 11 registry).map ResourceOwnership.AcquiredUse.Result.next
def owned := acquired.getD registry
def closed := (ResourceOwnership.AcquiredUse.releaseHolder 9 owned).map ResourceOwnership.AcquiredUse.Result.next
def moved := closed.bind fun state => ResourceOwnership.AcquiredUse.moveUse 11 12 state
def transferred := moved.map ResourceOwnership.AcquiredUse.Result.next
def completed := transferred.bind (advanceUse revocationWorlds held Access.consume parent 12 2)
def disposed := completed.bind (ResourceOwnership.AcquiredUse.releaseUse 12)

theorem transferred_owner_runs_same_saved_world_after_holder_disposal :
    acquired.isSome = true ∧ moved.isSome = true ∧
      (transferred.bind (advanceUse revocationWorlds held Access.consume parent 11 1)).isNone = true ∧
      (transferred.bind fun state => state.resource.map readout) = some (17, 4, 101, 5, [1, 2, 3], [0], [[0]], 2) ∧
      (completed.bind fun state => state.resource.map readout) = some (17, 4, 101, 7, [2, 4], [0, 1, 3], [[0], [1], [3]], 0) ∧
      (disposed.bind fun result => result.retired.map readout) = some (17, 4, 101, 7, [2, 4], [0, 1, 3], [[0], [1], [3]], 0) ∧
      (disposed.bind fun result => result.next.resource).isNone = true := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

def lifetime := (ResourceOwnership.AcquiredUse.forkLifetime 2 11 13 owned).map ResourceOwnership.AcquiredUse.Result.next

theorem capacity_lifetime_copy_and_repeated_disposal_do_not_create_rights :
    (ResourceOwnership.AcquiredUse.acquire 1 .lifetime 9 14 owned).isNone = true ∧
      (ResourceOwnership.AcquiredUse.moveUse 11 11 owned).isNone = true ∧
      lifetime.isSome = true ∧
      (lifetime.bind (advanceUse revocationWorlds held Access.consume parent 13 2)).isNone = true ∧
      (transferred.bind (advanceUse revocationWorlds held Access.consume changed 12 1)).isNone = true ∧
      (disposed.bind fun result => ResourceOwnership.AcquiredUse.releaseUse 12 result.next).isNone = true := by decide

theorem zero_private_allowance_is_inert_under_stale_parent :
    resume revocationWorlds revoked Access.consume changed 0 left = some left :=
  resume_zero revocationWorlds revoked Access.consume changed left

#print axioms one_source_two_private_publications_with_exact_input_identity
#print axioms continuation_keeps_own_origin_scope_and_complete_residual
#print axioms forged_scope_stale_parent_and_revoked_invocation_refuse
#print axioms transferred_owner_runs_same_saved_world_after_holder_disposal
#print axioms capacity_lifetime_copy_and_repeated_disposal_do_not_create_rights
#print axioms zero_private_allowance_is_inert_under_stale_parent

end Controls

#print axioms select_scope
#print axioms observed_binding_can_select
#print axioms selected_survivor_origin
#print axioms progress_admitted
#print axioms progress_split
#print axioms progress_lawful
#print axioms resume_zero
#print axioms resume_current
#print axioms resume_stale
#print axioms resume_denied

#print axioms renameOccurrence_injective
#print axioms transport_lawful
#print axioms fork_capture
#print axioms fork_lawful
#print axioms select_admitted
#print axioms select_effects
#print axioms select_lawful
#print axioms select_stale
#print axioms select_needs_private_identity
#print axioms select_denied

end PrivateWorld

end Discovery

/-! ## Captured pure planning and one atomic committed turn

This normalized profile keeps a decision's actual input separate from the
revision-qualified positions used by its publication plan. Pure planning reads
the immutable captured view. Only acceptance touches the live store. The local
Inbox is constructed from that input's record and claim; it is neither a new
global mailbox registry nor an optional debugging history.
-/

namespace CommittedTurn

open PositionalPublication
open Mettapedia.Machines.Cursor
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.SeparationAlgebra
open _root_.CategoryTheory

namespace Query
export Mettapedia.Machines.Cursor.ReadOnlyQuery (provider client readCharge completed? recorded)
end Query

variable {StoreId Scope : Type}

/-- Existing normalized publication data: consumed positions and fresh rows.
The fixed receiver and authority are held by the decision, not this value. -/
abbrev Plan := List Nat × List Data

def observe (scope : Scope → Data → Bool) (captured : Retained.State StoreId) (key : Scope) : List Data :=
  captured.origins.view.entries.filter (scope key)

structure Decision (StoreId : Type) (scope : Scope → Data → Bool) where
  captured : Retained.State StoreId
  input : Occurrence
  inbox : EventPump.Inbox
  receiver : Nat
  program : Mettapedia.Machines.ReadOnlyQuery.Program Scope (List Data) (List Plan)
  planner : Nat × Outcome (Query.provider (observe scope captured))
    (Query.client (Answer := List Plan)) PUnit.unit
  spent : Bool := false
  cancelled : Bool := false

variable (scope : Scope → Data → Bool)

/-- Select the actual current occurrence, then use the old record/claim
operations to construct the decision's local delivery phase. -/
def begin (current : Retained.State StoreId) (inputPosition receiver : Nat)
    (program : Occurrence → Mettapedia.Machines.ReadOnlyQuery.Program Scope (List Data) (List Plan)) :
    Option (Decision StoreId scope) :=
  current.channel.available[inputPosition]?.map fun input =>
    { captured := current, input := input,
      inbox := EventPump.claim (EventPump.record (EventPump.FiniteBurst.initial input.owner) input) input.serial,
      receiver := receiver, program := program input,
      planner := (0, .paused ⟨PUnit.unit, program input, []⟩) }

/-- Reachability is proof evidence, not a stored execution journal or a
future-answer oracle. It retains the exact paid cursor and all read replies. -/
def Reachable (decision : Decision StoreId scope) : Prop :=
  ∃ allowance, decision.planner =
    Cursor.advance (Query.provider (observe scope decision.captured)) Query.client
      (Query.readCharge (observe scope decision.captured)) allowance
      ⟨PUnit.unit, decision.program, []⟩

theorem begin_actual (current : Retained.State StoreId) (position receiver : Nat)
    (program : Occurrence → Mettapedia.Machines.ReadOnlyQuery.Program Scope (List Data) (List Plan))
    (decision : Decision StoreId scope) (created : begin scope current position receiver program = some decision) :
    current.channel.available[position]? = some decision.input ∧ decision.captured = current ∧
      decision.inbox.journal = [decision.input] ∧ decision.inbox.owner = decision.input.owner ∧
      decision.inbox.phase decision.input.serial = some .claimed ∧
      EventPump.FiniteBurst.WellFormed decision.inbox ∧ Reachable scope decision := by
  obtain ⟨input, actual, same⟩ := Option.map_eq_some_iff.mp created
  cases same
  refine ⟨actual, rfl, ?_, ?_, ?_, ?_, ⟨0, rfl⟩⟩
  · simp [EventPump.record, EventPump.claim, EventPump.FiniteBurst.initial]
  · simp [EventPump.record, EventPump.claim, EventPump.FiniteBurst.initial]
  · simp [EventPump.record, EventPump.claim, EventPump.FiniteBurst.initial]
  · exact EventPump.FiniteBurst.step_wellFormed _ (.claim input.serial)
      (EventPump.FiniteBurst.step_wellFormed _ (.arrival input)
        (EventPump.FiniteBurst.initial_wellFormed input.owner))

/-- No live store or database is consulted here. Both current and stale
decisions may finish pure lookahead in their own immutable captured world. -/
def resume (allowance : Nat) (decision : Decision StoreId scope) : Decision StoreId scope :=
  if decision.spent || decision.cancelled then decision else
    let later := Cursor.resume (Query.provider (observe scope decision.captured)) Query.client
      (Query.readCharge (observe scope decision.captured)) allowance decision.planner
    { decision with planner := later }

theorem resume_retains_capture (allowance : Nat) (decision : Decision StoreId scope) :
    (resume scope allowance decision).captured = decision.captured ∧
      (resume scope allowance decision).input = decision.input ∧
      (resume scope allowance decision).inbox = decision.inbox ∧
      (resume scope allowance decision).program = decision.program := by
  unfold resume
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem resume_reachable (allowance : Nat) (decision : Decision StoreId scope)
    (reachable : Reachable scope decision) : Reachable scope (resume scope allowance decision) := by
  unfold resume
  split
  · exact reachable
  · obtain ⟨earlier, same⟩ := reachable
    refine ⟨earlier + allowance, ?_⟩
    change Cursor.resume _ _ _ allowance decision.planner = _
    rw [same, ← Cursor.advance_add]

theorem resume_zero (decision : Decision StoreId scope) : resume scope 0 decision = decision := by
  simp [resume, Cursor.resume_zero]

/-- Fixed captured planning splits exactly, including all saved state and
paid reads. This does not compose live acceptance attempts or authority changes. -/
theorem resume_add (first second : Nat) (decision : Decision StoreId scope) :
    resume scope second (resume scope first decision) = resume scope (first + second) decision := by
  rcases decision with ⟨captured, input, inbox, receiver, program, planner, spent, cancelled⟩
  cases spent <;> cases cancelled <;> simp [resume, Cursor.resume_add]

def plans (decision : Decision StoreId scope) : Option (List Plan) :=
  (Query.completed? (observe scope decision.captured) decision.planner.2).map
    Mettapedia.Machines.ReadOnlyQuery.Observation.answer

/-- Only an actual completed planner exposes a plan list. Its order and
duplicate positions agree with the independent captured source interpreter. -/
theorem completed_source (decision : Decision StoreId scope) (reachable : Reachable scope decision)
    (answers : List Plan) (complete : plans scope decision = some answers) :
    answers = (Mettapedia.Machines.ReadOnlyQuery.run (observe scope decision.captured) decision.program).answer := by
  obtain ⟨allowance, executed⟩ := reachable
  obtain ⟨observation, completed, answer⟩ := Option.map_eq_some_iff.mp complete
  rw [executed] at completed
  have meaning := Mettapedia.Machines.Cursor.ReadOnlyQuery.completed_correct
    (observe scope decision.captured) allowance decision.program observation completed
  exact answer.symm.trans (congrArg Mettapedia.Machines.ReadOnlyQuery.Observation.answer meaning)

/-- Local cancellation does not requeue a durable Ready or consume its input.
The captured plan stays readable, but this decision cannot later attempt it. -/
def cancel (decision : Decision StoreId scope) : Decision StoreId scope := { decision with cancelled := true }

theorem cancel_retains_planner (decision : Decision StoreId scope) :
    (cancel scope decision).planner = decision.planner ∧
      (cancel scope decision).inbox = decision.inbox ∧ plans scope (cancel scope decision) = plans scope decision :=
  ⟨rfl, rfl, rfl⟩

def selected (decision : Decision StoreId scope) (plan : Plan) : List Occurrence :=
  Retained.select decision.captured.channel.available plan.1

/-- Compilation retains the original read, exact positions and actual
selected Events. It does not execute a query against the live store. -/
def compile (decision : Decision StoreId scope) (plan : Plan) : Discovery.Selection.Proposal StoreId :=
  ⟨decision.captured.origins.view.readToken, decision.receiver, plan.1, selected scope decision plan⟩

def admissible (decision : Decision StoreId scope) (plan : Plan) : Prop :=
  decision.inbox.phase decision.input.serial = some .claimed ∧
    decision.input ∈ selected scope decision plan ∧ plan.1.Nodup ∧
    (∀ position ∈ plan.1, position < decision.captured.channel.available.length) ∧
    match decision.captured.channel.receives decision.receiver with
    | none => False
    | some receiver => valid decision.captured.channel receiver (selected scope decision plan)

instance admissibleDecision (decision : Decision StoreId scope) (plan : Plan) :
    Decidable (admissible scope decision plan) := by
  unfold admissible
  cases decision.captured.channel.receives decision.receiver <;> infer_instance

instance resourceDecision (current : Space) (id : Nat) (receiver : Continuation)
    (inputs : List Occurrence) :
    Decidable (joinResources.Enables (resourceSnapshot current).val (site := id) (receiver, inputs)) :=
  inferInstanceAs (Decidable ((joinDemand id receiver inputs).consume +
    (joinDemand id receiver inputs).read ≤ (resourceSnapshot current).val))

/-- The actual live footprint must be enabled. Exact source/tuple validation
and publication still use the existing selected operation. -/
def publish [DecidableEq StoreId] (current : Retained.State StoreId)
    (decision : Decision StoreId scope) (plan : Plan) (nextRevision : Nat) : Option (Retained.State StoreId) :=
  match current.channel.receives decision.receiver with
  | none => none
  | some receiver =>
      if joinResources.Enables (resourceSnapshot current.channel).val
          (site := decision.receiver) (receiver, selected scope decision plan) then
        Discovery.Selection.perform current (compile scope decision plan) plan.2 nextRevision
      else none

theorem publish_admitted [DecidableEq StoreId] (current next : Retained.State StoreId)
    (decision : Decision StoreId scope) (plan : Plan) (nextRevision : Nat)
    (published : publish scope current decision plan nextRevision = some next) :
    ∃ receiver, current.channel.receives decision.receiver = some receiver ∧
      joinResources.Enables (resourceSnapshot current.channel).val
        (site := decision.receiver) (receiver, selected scope decision plan) ∧
      Discovery.Selection.perform current (compile scope decision plan) plan.2 nextRevision = some next := by
  unfold publish at published
  cases registered : current.channel.receives decision.receiver with
  | none => simp [registered] at published
  | some receiver =>
      simp only [registered] at published
      split at published
      · exact ⟨receiver, rfl, by assumption, published⟩
      · cases published

/-- The existing retained callback provider drives this very query cursor.
A closed planner publishes its complete ordered list only as a terminal return;
it cannot offer a partial plan as an accepted item. The rearm branch is unused. -/
def plannerProvider (quantum : Nat) (captured : Retained.State StoreId) :=
  Fold.OwnedSequence.CallbackBoundary.Retained.provider
    (Query.provider (observe scope captured)) (Query.client (Answer := List Plan)) PUnit.unit
    (Query.readCharge (observe scope captured)) quantum (fun _ => false)
    (fun result => ⟨PUnit.unit, .pure result.2.1, result.2.2⟩)
    (fun (_ : Unit) _ => (false, ()))

/-- One visit of the common callback sequencer. The outer charge counts a
provider operation; the retained inner charge still counts query reads. -/
def plannerVisit (quantum : Nat) (decision : Decision StoreId scope) :=
  Fold.OwnedSequence.CallbackBoundary.fromCallbacks
    (plannerProvider scope quantum decision.captured) (fun _ _ => 1) 1 none 0
    ⟨decision.planner, ()⟩

theorem plannerVisit_exact (quantum : Nat) (decision : Decision StoreId scope) :
    let later := Cursor.resume (Query.provider (observe scope decision.captured)) Query.client
      (Query.readCharge (observe scope decision.captured)) quantum decision.planner
    plannerVisit scope quantum decision =
      (1, ⟨⟨match later.2 with | .paused _ => none | .done result => some result, none, 0⟩,
        ⟨later, ()⟩⟩) := by
  dsimp only
  cases later : (Cursor.resume (Query.provider (observe scope decision.captured)) Query.client
    (Query.readCharge (observe scope decision.captured)) quantum decision.planner).2 <;>
    simp [plannerVisit, plannerProvider, Fold.OwnedSequence.CallbackBoundary.fromCallbacks,
      Fold.OwnedSequence.CallbackBoundary.Retained.provider, later]

/-- The common callback stores the identical paid source packet used by
`resume`, including the complete unfinished suffix and captured read replies. -/
theorem resume_from_callback (quantum : Nat) (decision : Decision StoreId scope)
    (active : (decision.spent || decision.cancelled) = false) :
    HEq (resume scope quantum decision).planner
      (plannerVisit scope quantum decision).2.2.computation := by
  rcases decision with ⟨captured, input, inbox, receiver, program, planner, spent, cancelled⟩
  cases spent <;> cases cancelled <;> simp_all [resume, plannerVisit_exact]

inductive Status where
  | refused | conflict | committed | unknown
  deriving DecidableEq, Repr

structure Result (StoreId : Type) (scope : Scope → Data → Bool) where
  status : Status
  world : Retained.State StoreId
  decision : Decision StoreId scope

variable {World : Type} [Category.{0} World]
  (authority : IndexedAuthority.{0, 0, 0} World) (point : IndexedAuthority.Point authority)
  (required : Plan → authority.Fibre point.world)
  [permission : ∀ plan, Decidable (FrameUpdate point.authority (required plan))]

/-- Incomplete/invalid/unauthorized plans refuse before attempting publication.
Once publication is attempted the decision is spent, including conflict.
Input consumption and local settlement are returned together on success. -/
def attempt [DecidableEq StoreId] (current : Retained.State StoreId)
    (decision : Decision StoreId scope) (alternative nextRevision : Nat) : Result StoreId scope :=
  let refused : Result StoreId scope := ⟨.refused, current, decision⟩
  if decision.spent || decision.cancelled then refused else
    match plans scope decision with
    | none => refused
    | some answers => match answers[alternative]? with
      | none => refused
      | some plan =>
          if admissible scope decision plan ∧ FrameUpdate point.authority (required plan) then
            let spent := { decision with spent := true }
            match publish scope current decision plan nextRevision with
            | none => ⟨.conflict, current, spent⟩
            | some next =>
                ⟨.committed, next,
                  { spent with inbox := EventPump.settle decision.inbox decision.input.serial }⟩
          else refused

theorem preattempt_incomplete [DecidableEq StoreId] (current : Retained.State StoreId)
    (decision : Decision StoreId scope) (alternative nextRevision : Nat)
    (incomplete : plans scope decision = none) :
    attempt scope authority point required current decision alternative nextRevision = ⟨.refused, current, decision⟩ := by
  simp [attempt, incomplete]

theorem preattempt_denied [DecidableEq StoreId] (current : Retained.State StoreId)
    (decision : Decision StoreId scope) (answers : List Plan) (plan : Plan)
    (alternative nextRevision : Nat) (complete : plans scope decision = some answers)
    (indexed : answers[alternative]? = some plan)
    (denied : ¬ FrameUpdate point.authority (required plan)) :
    attempt scope authority point required current decision alternative nextRevision =
      ⟨.refused, current, decision⟩ := by
  simp [attempt, complete, indexed, denied]

theorem spent_cannot_attempt_again [DecidableEq StoreId] (current : Retained.State StoreId)
    (decision : Decision StoreId scope) (alternative nextRevision : Nat) (spent : decision.spent = true) :
    attempt scope authority point required current decision alternative nextRevision = ⟨.refused, current, decision⟩ := by
  simp [attempt, spent]

theorem cancelled_input_is_not_consumed [DecidableEq StoreId] (current : Retained.State StoreId)
    (decision : Decision StoreId scope) (alternative nextRevision : Nat) :
    attempt scope authority point required current (cancel scope decision) alternative nextRevision =
      ⟨.refused, current, cancel scope decision⟩ := by simp [attempt, cancel]

theorem attempt_preserves_planner [DecidableEq StoreId] (current : Retained.State StoreId)
    (decision : Decision StoreId scope) (alternative nextRevision : Nat) :
    let result := attempt scope authority point required current decision alternative nextRevision
    HEq result.decision.planner decision.planner ∧ result.decision.captured = decision.captured ∧
      result.decision.input = decision.input ∧ plans scope result.decision = plans scope decision := by
  unfold attempt
  split
  · exact ⟨HEq.rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨HEq.rfl, rfl, rfl, rfl⟩
    · split
      · exact ⟨HEq.rfl, rfl, rfl, rfl⟩
      · split
        · split <;> exact ⟨HEq.rfl, rfl, rfl, rfl⟩
        · exact ⟨HEq.rfl, rfl, rfl, rfl⟩

theorem success_admitted [DecidableEq StoreId] (current : Retained.State StoreId)
    (decision : Decision StoreId scope) (alternative nextRevision : Nat)
    (success : (attempt scope authority point required current decision alternative nextRevision).status = .committed) :
    ∃ answers plan next, plans scope decision = some answers ∧ answers[alternative]? = some plan ∧
      admissible scope decision plan ∧ FrameUpdate point.authority (required plan) ∧
      publish scope current decision plan nextRevision = some next ∧
      attempt scope authority point required current decision alternative nextRevision =
        ⟨.committed, next, { decision with spent := true, inbox := EventPump.settle decision.inbox decision.input.serial }⟩ := by
  unfold attempt at success ⊢
  split at success
  · cases success
  · rename_i openDecision
    cases completed : plans scope decision with
    | none => simp [completed] at success
    | some answers =>
        simp only [completed] at success ⊢
        cases selectedPlan : answers[alternative]? with
        | none => simp [selectedPlan] at success
        | some plan =>
            simp only [selectedPlan] at success ⊢
            split at success
            · rename_i permitted
              cases published : publish scope current decision plan nextRevision with
              | none => simp [published] at success
              | some next =>
                  exact ⟨answers, plan, next, rfl, selectedPlan, permitted.1, permitted.2,
                    published, by rw [if_neg openDecision, if_pos permitted]⟩
            · cases success

/-- Forgetting an acknowledgment preserves the actual post-state, spent
decision, input phase and earned plan. UNKNOWN is not evidence of rollback. -/
def forgetAcknowledgment (result : Result StoreId scope) : Result StoreId scope :=
  match result.status with
  | .committed | .conflict => { result with status := .unknown }
  | _ => result

theorem unknown_retains_actual_state (result : Result StoreId scope) :
    (forgetAcknowledgment scope result).world = result.world ∧
      (forgetAcknowledgment scope result).decision = result.decision := by
  cases status : result.status <;> simp [forgetAcknowledgment, status]

private theorem run_outputs (s : Space) (start : Nat) (outputs : List Data) :
    ChannelJoin.run ((outputEvents start outputs).map Action.produce) s = produceOutputs s start outputs := by
  induction outputs generalizing s start with
  | nil => rfl
  | cons entry rest ih =>
      simpa only [outputEvents, List.zipIdx_cons, List.map_cons, ChannelJoin.run, ChannelJoin.step,
        produceOutputs] using ih (produce s ⟨start, entry.1, entry.2⟩) (start + 1)

/-- The compiled turn follows the old channel react/produce operations.
Its consume/read footprint is an enabled firing of the independent resource
system; fresh output publication retains the complete channel state. -/
theorem publication_source [DecidableEq StoreId] (current next : Retained.State StoreId)
    (decision : Decision StoreId scope) (plan : Plan) (nextRevision : Nat)
    (published : publish scope current decision plan nextRevision = some next) :
    ∃ receiver, current.channel.receives decision.receiver = some receiver ∧
      joinResources.Fires [⟨decision.receiver, receiver, selected scope decision plan⟩]
        (resourceSnapshot current.channel).val
        (resourceSnapshot (commit current.channel decision.receiver (selected scope decision plan))).val ∧
      next.channel = ChannelJoin.run
        (.react decision.receiver (selected scope decision plan) ::
          (outputEvents (Retained.freshStart current.channel) plan.2).map Action.produce) current.channel := by
  obtain ⟨receiver, registered, enabled, performed⟩ := publish_admitted scope current next decision plan nextRevision published
  obtain ⟨other, otherRegistered, matched, actual⟩ :=
    (Discovery.Selection.perform_admitted current next (compile scope decision plan) plan.2 nextRevision performed).2.2.2
  have same : other = receiver := Option.some.inj (otherRegistered.symm.trans registered)
  subst other
  refine ⟨receiver, registered, ⟨enabled, ?_⟩, ?_⟩
  · simpa only [System.Fires, System.fire, joinResources, add_zero] using
      commit_resource_account current.channel decision.receiver receiver (selected scope decision plan) registered matched
  · exact actual.trans (run_outputs _ _ _).symm

/-- Source-derived completed plan selection, actual publication, input
consumption and local acknowledgment form one transition. No completed-source
or footprint equality is supplied by a caller. -/
theorem successful_turn [DecidableEq StoreId] (current : Retained.State StoreId)
    (decision : Decision StoreId scope) (alternative nextRevision : Nat)
    (reachable : Reachable scope decision)
    (success : (attempt scope authority point required current decision alternative nextRevision).status = .committed) :
    ∃ plan next,
      (Mettapedia.Machines.ReadOnlyQuery.run (observe scope decision.captured) decision.program).answer[alternative]? = some plan ∧
      attempt scope authority point required current decision alternative nextRevision =
        ⟨.committed, next, { decision with spent := true, inbox := EventPump.settle decision.inbox decision.input.serial }⟩ ∧
      (EventPump.settle decision.inbox decision.input.serial).phase decision.input.serial = some .settled ∧
      (EventPump.settle decision.inbox decision.input.serial).receipts = decision.inbox.receipts ++ [decision.input.serial] ∧
      decision.input.serial ∈ next.channel.spent ∧
      ∃ receiver, joinResources.Fires [⟨decision.receiver, receiver, selected scope decision plan⟩]
        (resourceSnapshot current.channel).val
        (resourceSnapshot (commit current.channel decision.receiver (selected scope decision plan))).val ∧
        next.channel = ChannelJoin.run
          (.react decision.receiver (selected scope decision plan) ::
            (outputEvents (Retained.freshStart current.channel) plan.2).map Action.produce) current.channel := by
  obtain ⟨answers, plan, next, complete, indexed, admitted, permitted, published, exactResult⟩ :=
    success_admitted scope authority point required current decision alternative nextRevision success
  have source := completed_source scope decision reachable answers complete
  obtain ⟨receiver, _, firing, ordinary⟩ := publication_source scope current next decision plan nextRevision published
  obtain ⟨_, _, _, performed⟩ := publish_admitted scope current next decision plan nextRevision published
  have spent := Discovery.Selection.perform_spends_exact_inputs current next (compile scope decision plan)
    plan.2 nextRevision performed
  refine ⟨plan, next, source ▸ indexed, exactResult, ?_, ?_, ?_, receiver, firing, ordinary⟩
  · simp [EventPump.settle, admitted.1]
  · simp [EventPump.settle, admitted.1]
  · rw [spent]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨decision.input, admitted.2.1, rfl⟩)

theorem attempted_decision_is_spent [DecidableEq StoreId] (current : Retained.State StoreId)
    (decision : Decision StoreId scope) (alternative nextRevision : Nat) :
    let result := attempt scope authority point required current decision alternative nextRevision
    result.status ≠ .refused → result.decision.spent = true := by
  unfold attempt
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split
        · split <;> simp
        · simp

/-- Only immutable pure source inspections fuse here. Callback service visits,
accepted-return grants and physical native work retain their separate units. -/
theorem pure_schedule (grants : List Nat) (decision : Decision StoreId scope) :
    grants.foldl (fun saved grant => resume scope grant saved) decision = resume scope grants.sum decision := by
  induction grants generalizing decision with
  | nil => exact (resume_zero scope decision).symm
  | cons grant rest ih => simp only [List.foldl_cons, List.sum_cons, ih, resume_add]

namespace Controls

local instance : Fintype Access :=
  ⟨{.none, .read, .consume}, by intro access; cases access <;> simp⟩

def held : IndexedAuthority.Point revocationWorlds := ⟨false, .consume⟩
def revoked : IndexedAuthority.Point revocationWorlds :=
  IndexedAuthority.push held (homOfLE (by decide) : false ⟶ true)

local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (Access.consume : revocationWorlds.Fibre point.world)) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate point.authority frame = true → Access.separate Access.consume frame = true))

def request : EventPump.Key := ⟨0, 0, 0⟩
def slot : EventPump.Key := ⟨1, 0, 0⟩
def actor : EventPump.Key := ⟨2, 0, 0⟩
def intent : EventPump.Key := ⟨3, 0, 0⟩
def view : View Nat Nat := ⟨17, 4, [(request, 7), (request, 7), (slot, 3), (actor, 100)]⟩
def receiver : Continuation := ⟨[⟨request, fun _ => true⟩, ⟨slot, fun _ => true⟩,
  ⟨actor, fun _ => true⟩], true⟩
def source := Retained.initial view 7 receiver
def matchesScope (key : Nat) (entry : Data) : Bool := decide (entry.1.owner = key)

/-- The plan uses actual captured request/state replies, including an absence
read. Equal alternatives occupy separate positions in the completed list. -/
def program (input : Occurrence) :
    Mettapedia.Machines.ReadOnlyQuery.Program Nat (List Data) (List Plan) :=
  .read 0 fun requests => .read 2 fun actors => .read 9 fun absent =>
    let payload := (requests.headD (request, 0)).2
    let next := (actors.headD (actor, 0)).2 + 1
    let plan : Plan := ([input.serial, 2, 3], [(actor, next), (intent, payload)])
    .pure (if absent.isEmpty then [plan, plan] else [])

def first : Decision Nat matchesScope := (begin matchesScope source 0 7 program).get (by decide)
def sibling : Decision Nat matchesScope := (begin matchesScope source 1 7 program).get (by decide)
def foreign : Decision Nat matchesScope :=
  resume matchesScope 1 ((begin matchesScope source 0 7
    (fun _ => .pure [([1,2,3],[(intent,7)])])).get (by decide))
def planned := resume matchesScope 1 (resume matchesScope 2 (resume matchesScope 1 first))
def accepted := attempt matchesScope revocationWorlds held (fun _ => Access.consume) source planned 1 5

theorem retained_planning_has_no_early_plan :
    plans matchesScope (resume matchesScope 3 first) = none ∧
      (resume matchesScope 3 first).planner.1 = 3 ∧
      (resume matchesScope 0 first).planner.1 = 0 ∧
      plans matchesScope planned = some [([0,2,3], [(actor,101),(intent,7)]),
        ([0,2,3], [(actor,101),(intent,7)])] ∧
      (Query.recorded (observe matchesScope planned.captured) planned.planner.2).map Prod.fst = [0,2,9] := by
  decide

theorem atomic_duplicate_input_and_effects :
    accepted.status = .committed ∧ accepted.decision.spent = true ∧
      accepted.decision.inbox.phase 0 = some .settled ∧ accepted.decision.inbox.receipts = [0] ∧
      accepted.world.channel.available.map EventPump.Event.serial = [1,4,5] ∧
      accepted.world.origins.view.entries = [(request,7),(actor,101),(intent,7)] ∧
      accepted.world.channel.spent = [0,2,3] ∧
      plans matchesScope accepted.decision = plans matchesScope planned := by decide

/-- Stale pure planning is allowed; acceptance cannot retarget the other
identical request or refresh the original source read. Attempted conflict spends
this decision, while leaving the durable input and any effects unchanged. -/
theorem stale_planning_conflicts_without_retarget :
    let oldPlan := resume matchesScope 4 sibling
    let conflict := attempt matchesScope revocationWorlds held (fun _ => Access.consume)
      accepted.world oldPlan 0 6
    plans matchesScope oldPlan = some [([1,2,3],[(actor,101),(intent,7)]),
      ([1,2,3],[(actor,101),(intent,7)])] ∧
      conflict.status = .conflict ∧ conflict.decision.spent = true ∧
      conflict.world.channel.available.map EventPump.Event.serial = [1,4,5] ∧
      conflict.decision.inbox.phase 1 = some .claimed ∧
      conflict.decision.inbox.receipts = [] ∧
      (attempt matchesScope revocationWorlds held (fun _ => Access.consume)
        conflict.world conflict.decision 0 7).status = .refused := by decide

theorem denied_incomplete_and_foreign_input_refuse_before_attempt :
    let denied := attempt matchesScope revocationWorlds revoked (fun _ => Access.consume) source planned 0 5
    let incomplete := attempt matchesScope revocationWorlds held (fun _ => Access.consume) source first 0 5
    let invalid := attempt matchesScope revocationWorlds held (fun _ => Access.consume) source foreign 0 5
    denied.status = .refused ∧ denied.decision.spent = false ∧ denied.decision.planner.1 = 3 ∧
      incomplete.status = .refused ∧ incomplete.decision.spent = false ∧
      invalid.status = .refused ∧ invalid.decision.spent = false ∧
      denied.world.origins.view.entries = view.entries ∧
      invalid.world.channel.spent = [] ∧
      (attempt matchesScope revocationWorlds held (fun _ => Access.consume)
        denied.world denied.decision 0 5).status = .committed := by decide

theorem cancellation_preserves_input_for_a_new_decision :
    let cancelled := attempt matchesScope revocationWorlds held (fun _ => Access.consume)
      source (cancel matchesScope planned) 0 5
    cancelled.status = .refused ∧ cancelled.world.channel.spent = [] ∧
      cancelled.decision.inbox.phase 0 = some .claimed ∧
      cancelled.decision.inbox.receipts = [] ∧
      plans matchesScope cancelled.decision = plans matchesScope planned ∧
      (begin matchesScope cancelled.world 0 7 program).isSome = true := by decide

theorem unknown_acknowledgment_does_not_undo_effects :
    let unknown := forgetAcknowledgment matchesScope accepted
    unknown.status = .unknown ∧ unknown.decision.spent = true ∧
      unknown.decision.inbox.phase 0 = some .settled ∧
      unknown.world.origins.view.entries = [(request,7),(actor,101),(intent,7)] ∧
      plans matchesScope unknown.decision = plans matchesScope planned ∧
      (attempt matchesScope revocationWorlds held (fun _ => Access.consume)
        unknown.world unknown.decision 1 6).status = .refused := by decide

end Controls

#print axioms plannerVisit_exact
#print axioms resume_from_callback
#print axioms Controls.retained_planning_has_no_early_plan
#print axioms Controls.atomic_duplicate_input_and_effects
#print axioms Controls.stale_planning_conflicts_without_retarget
#print axioms Controls.denied_incomplete_and_foreign_input_refuse_before_attempt
#print axioms Controls.cancellation_preserves_input_for_a_new_decision
#print axioms Controls.unknown_acknowledgment_does_not_undo_effects

#print axioms publication_source
#print axioms successful_turn
#print axioms attempted_decision_is_spent
#print axioms pure_schedule

#print axioms publish_admitted
#print axioms preattempt_incomplete
#print axioms preattempt_denied
#print axioms spent_cannot_attempt_again
#print axioms attempt_preserves_planner
#print axioms success_admitted
#print axioms unknown_retains_actual_state

#print axioms begin_actual
#print axioms resume_reachable
#print axioms resume_zero
#print axioms resume_retains_capture
#print axioms resume_add
#print axioms completed_source
#print axioms cancel_retains_planner
#print axioms cancelled_input_is_not_consumed

end CommittedTurn

/-! ## Scoped stable-key selection into retained positional joins

Scope observations are read evidence. Current stable keys are unique, while
scope arrays may overlap. Exact issued stamps are recompiled to current
positions only after explicit scoped validation. This consuming profile adds
no output events or permanent runtime identity registry.
-/

namespace ScopedPublication

open Mettapedia.Machines
open RevisionedStoreView.Publication
open PositionalPublication

set_option synthInstance.maxSize 256

variable {Epoch Site Letter Version : Type}
variable [DecidableEq Epoch] [DecidableEq Site] [DecidableEq Letter] [DecidableEq Version]

local notation "Rows" => ScopedRecords.Source Epoch Nat Site Letter Version
local notation "Stamp" => ScopedRecords.Stamp Site Letter Version
local notation "Required" => ScopedRecords.Captured Epoch Site Letter Version Nat

/-- Repeated scope views may mention an issued row repeatedly; this list is
read evidence and never a supply of duplicate consume permissions. -/
def witnessed (required : Required) :
    List (Stamp) :=
  required.reads.flatMap fun read => read.2.2.map Prod.fst

def compile (current : Rows)
    (required : Required) (chosen : List Stamp) : Option (List Nat) :=
  if ScopedRecords.validate current required = true ∧
      (current.entries.map Prod.fst).Nodup ∧ (chosen.map Prod.fst).Nodup ∧
      (∀ stamp ∈ chosen, stamp ∈ witnessed required) ∧ (∀ stamp ∈ chosen, stamp ∈ current.entries) then
    some (Keyed.positions id current chosen)
  else none

theorem compile_admitted (current : Rows) (required : Required) (chosen : List Stamp) (positions : List Nat)
    (accepted : compile current required chosen = some positions) :
    ScopedRecords.validate current required = true ∧
      (current.entries.map Prod.fst).Nodup ∧ (chosen.map Prod.fst).Nodup ∧
      (∀ stamp ∈ chosen, stamp ∈ witnessed required) ∧ (∀ stamp ∈ chosen, stamp ∈ current.entries) ∧
      positions = Keyed.positions id current chosen := by
  unfold compile at accepted
  split at accepted
  · rename_i allowed
    exact ⟨allowed.1, allowed.2.1, allowed.2.2.1, allowed.2.2.2.1, allowed.2.2.2.2,
      (Option.some.inj accepted).symm⟩
  · cases accepted

/-- The actual selected coordinate resolves the exact issued stamp, under a
new current positional read rather than the earlier captured read token. -/
theorem selected_resolves (current : Rows) (required : Required) (chosen : List Stamp) (positions : List Nat)
    (accepted : compile current required chosen = some positions) (stamp : Stamp) (selected : stamp ∈ chosen) :
    current.resolve (current.occurrenceId (Keyed.index id current stamp)) = some stamp ∧
      Keyed.index id current stamp ∈ positions := by
  have valid := compile_admitted current required chosen positions accepted
  refine ⟨?_, ?_⟩
  · rw [RevisionedStoreView.resolve_current]
    exact Keyed.lookup_key current stamp (valid.2.2.2.2.1 stamp selected)
  · rw [valid.2.2.2.2.2]
    exact List.mem_map.mpr ⟨stamp, selected, rfl⟩

/-- Selected rows really came from an observed scope of the captured source.
This authenticates read origin, not effect authority. -/
theorem selected_origin (contents : Epoch → Stamp → Nat) (captured current : Rows)
    (scopes : List (ScopedRecords.Scope Site Letter)) (chosen : List Stamp) (positions : List Nat)
    (accepted : compile current (ScopedRecords.capture contents captured scopes) chosen = some positions)
    (stamp : Stamp) (selected : stamp ∈ chosen) :
    stamp ∈ captured.entries ∧ ∃ scope ∈ scopes, ScopedRecords.accepts scope stamp = true := by
  have observed := (compile_admitted current _ chosen positions accepted).2.2.2.1 stamp selected
  obtain ⟨read, readMember, rowMember⟩ := List.mem_flatMap.mp observed
  obtain ⟨scope, scopeMember, same⟩ := List.mem_map.mp readMember
  cases same
  obtain ⟨row, member, sameStamp⟩ := List.mem_map.mp rowMember
  obtain ⟨found, filtered, sameRow⟩ := List.mem_map.mp member
  cases sameRow
  simp only at sameStamp
  subst stamp
  have original := List.mem_filter.mp filtered
  exact ⟨original.1, scope, scopeMember, original.2⟩

variable [Encodable Epoch] [Encodable Site] [Encodable Letter] [Encodable Version]

/-- Reference names encode the complete source identity, never its payload or
current positional index. This construction specifies no runtime ID layout. -/
def event (contents : Epoch → Stamp → Nat) (epoch : Epoch) (stamp : Stamp) : Occurrence :=
  ⟨Encodable.encode (epoch, stamp), ⟨Encodable.encode stamp.1.1, 0, 0⟩, contents epoch stamp⟩

def events (contents : Epoch → Stamp → Nat) (current : Rows) : List Occurrence :=
  current.entries.map (event contents current.storeId)

def project (contents : Epoch → Stamp → Nat) (current : Rows) : View Epoch Nat :=
  ⟨current.storeId, current.revision, (events contents current).map fun e => (e.owner, e.payload)⟩

omit [DecidableEq Epoch] [DecidableEq Site] [DecidableEq Letter] [DecidableEq Version] in
theorem serial_eq_iff (contents : Epoch → Stamp → Nat) (firstEpoch secondEpoch : Epoch)
    (first second : Stamp) :
    (event contents firstEpoch first).serial = (event contents secondEpoch second).serial ↔
      firstEpoch = secondEpoch ∧ first = second := by
  change Encodable.encode (firstEpoch, first) = Encodable.encode (secondEpoch, second) ↔ _
  rw [Encodable.encode_inj, Prod.mk.injEq]

omit [DecidableEq Epoch] [DecidableEq Site] [DecidableEq Letter] [DecidableEq Version] in
theorem event_injective (contents : Epoch → Stamp → Nat) (epoch : Epoch) :
    Function.Injective (event contents epoch) := by
  intro first second equal
  exact congrArg Prod.snd (Encodable.encode_injective (congrArg EventPump.Event.serial equal))

omit [DecidableEq Epoch] [DecidableEq Site] [DecidableEq Letter] [DecidableEq Version] in
theorem event_mem_iff (contents : Epoch → Stamp → Nat) (epoch : Epoch) (rows : List Stamp) (stamp : Stamp) :
    event contents epoch stamp ∈ rows.map (event contents epoch) ↔ stamp ∈ rows := by
  constructor
  · intro member
    obtain ⟨other, present, equal⟩ := List.mem_map.mp member
    exact event_injective contents epoch equal ▸ present
  · intro member
    exact List.mem_map.mpr ⟨stamp, member, rfl⟩

def initial (contents : Epoch → Stamp → Nat) (current : Rows) (receiver : Nat) (c : Continuation) :
    Retained.State Epoch :=
  ⟨Finite.initial (project contents current),
    register { produced := events contents current, available := events contents current } receiver c⟩

def Coupled (contents : Epoch → Stamp → Nat) (current : Rows) (s : Retained.State Epoch) : Prop :=
  Retained.Lawful s ∧ s.origins.view.readToken = current.readToken ∧ s.channel.available = events contents current

omit [DecidableEq Epoch] [DecidableEq Site] [DecidableEq Letter] [DecidableEq Version] in
theorem initial_coupled (contents : Epoch → Stamp → Nat) (current : Rows)
    (unique : (current.entries.map Prod.fst).Nodup) (receiver : Nat) (c : Continuation) :
    Coupled contents current (initial contents current receiver c) := by
  have stamps : current.entries.Nodup := List.Nodup.of_map Prod.fst unique
  have serials : ((events contents current).map EventPump.Event.serial).Nodup := by
    simp only [events, event, List.map_map, Function.comp_def]
    exact stamps.map (fun first second same => congrArg Prod.snd (Encodable.encode_injective same))
  refine ⟨⟨Finite.initial_lawful _, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · simp [initial, register, project, Finite.initial]
  · simpa [initial, register] using serials
  · intro e member
    simp only [initial, register, List.not_mem_nil, ↓reduceIte] at member ⊢
    exact ⟨member, by simp⟩
  · simp [initial, register]
  · simp [initial, register]

/-- This is a finite cold adapter, not a new evaluator. The source and actual
Space must agree at entrance. Both existing publications are private pure
values; refusal exposes neither a partially consumed source nor a partial join. -/
def perform (contents : Epoch → Stamp → Nat) (current : Rows) (required : Required)
    (chosen : List Stamp) (s : Retained.State Epoch) (receiver nextGeneration : Nat) :
    Option (Rows × Retained.State Epoch) := do
  let positions ← compile current required chosen
  if s.origins.view.readToken = current.readToken ∧ s.channel.available = events contents current then
    let next ← Keyed.publish id current current.readToken chosen [] nextGeneration
    let reached ← Retained.advance s ((current.readToken, positions, [], nextGeneration), receiver)
    some (next, reached)
  else none

theorem perform_admitted (contents : Epoch → Stamp → Nat) (current : Rows) (required : Required)
    (chosen : List Stamp) (s next : Retained.State Epoch) (receiver nextGeneration : Nat) (published : Rows)
    (accepted : perform contents current required chosen s receiver nextGeneration = some (published, next)) :
    ∃ positions, compile current required chosen = some positions ∧
      s.origins.view.readToken = current.readToken ∧ s.channel.available = events contents current ∧
      Keyed.publish id current current.readToken chosen [] nextGeneration = some published ∧
      Retained.advance s ((current.readToken, positions, [], nextGeneration), receiver) = some next := by
  unfold perform at accepted
  obtain ⟨positions, compiled, continued⟩ := Option.bind_eq_some_iff.mp accepted
  split at continued
  · rename_i entrance
    obtain ⟨rows, published, rest⟩ := Option.bind_eq_some_iff.mp continued
    obtain ⟨reached, advanced, pair⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj pair
    exact ⟨positions, compiled, entrance.1, entrance.2, published, advanced⟩
  · cases continued

omit [DecidableEq Epoch] in
theorem selected_events (contents : Epoch → Stamp → Nat) (current : Rows)
    (chosen : List Stamp) (present : ∀ stamp ∈ chosen, stamp ∈ current.entries) :
    Retained.select (events contents current) (Keyed.positions id current chosen) =
      chosen.map (event contents current.storeId) := by
  have exactRows := Keyed.select_exact current chosen present
  have mapped := congrArg (List.map (event contents current.storeId)) exactRows
  simpa only [Retained.select, events, List.getElem?_map, List.map_filterMap, Function.comp_def] using mapped

/-- The keyed reference removes precisely the rows consumed by the actual
retained channel operation, preserving original surviving Event identities. -/
theorem perform_source (contents : Epoch → Stamp → Nat) (current : Rows) (required : Required)
    (chosen : List Stamp) (s next : Retained.State Epoch) (receiver nextGeneration : Nat) (published : Rows)
    (lawful : Retained.Lawful s)
    (accepted : perform contents current required chosen s receiver nextGeneration = some (published, next)) :
    published = Keyed.reference id current chosen [] nextGeneration ∧ Retained.Lawful next ∧
      next.channel.available = events contents published ∧
      next.channel.spent = s.channel.spent ++ (chosen.map (event contents current.storeId)).map EventPump.Event.serial := by
  obtain ⟨positions, compiled, currentRead, currentEvents, sourceGrant, advanced⟩ :=
    perform_admitted contents current required chosen s next receiver nextGeneration published accepted
  have compilation := compile_admitted current required chosen positions compiled
  have sourceResult := (Keyed.admitted id current current.readToken chosen [] nextGeneration published sourceGrant).2.2.2.2.2
  have tuple := selected_events contents current chosen compilation.2.2.2.2.1
  rw [← compilation.2.2.2.2.2, ← currentEvents] at tuple
  obtain ⟨result, applied, same⟩ := Option.map_eq_some_iff.mp advanced
  cases same
  obtain ⟨_, c, receiverGrant, permitted, actual⟩ := Retained.applySpace_admitted s.origins.view s.channel _ result applied
  have available := (successful_join_is_atomic s.channel receiver c _ receiverGrant permitted).1
  have exactAvailable : result.2.available =
      s.channel.available.filter (fun e => decide (e ∉ chosen.map (event contents current.storeId))) := by
    rw [actual]
    simpa only [produceOutputs, tuple] using available
  refine ⟨sourceResult, Retained.advance_lawful s _ _ lawful advanced, ?_, ?_⟩
  · rw [exactAvailable, currentEvents, sourceResult]
    simp [events, Keyed.reference, Keyed.remaining, RevisionedStoreView.replaceRevision,
      List.filter_map, Function.comp_def, event_mem_iff]
  · simpa only [tuple] using Retained.advance_spent s _ _ advanced

/-- The old positional name is retained as proof origin at its shifted
coordinate, together with exactly the same actual Event and payload. -/
theorem perform_keeps_origin (contents : Epoch → Stamp → Nat) (current : Rows) (required : Required)
    (chosen : List Stamp) (s next : Retained.State Epoch) (receiver nextGeneration : Nat) (published : Rows)
    (lawful : Retained.Lawful s)
    (accepted : perform contents current required chosen s receiver nextGeneration = some (published, next))
    (index : Nat) (stamp : Stamp) (found : current.entries[index]? = some stamp) (unchosen : stamp ∉ chosen)
    (origin : StoreOccurrenceId Epoch Nat × Data) (e : Occurrence)
    (named : s.origins.rows[index]? = some origin) (actual : s.channel.available[index]? = some e) :
    ∃ target : Nat, next.origins.rows[target]? = some origin ∧ next.channel.available[target]? = some e := by
  obtain ⟨positions, compiled, _, _, _, advanced⟩ :=
    perform_admitted contents current required chosen s next receiver nextGeneration published accepted
  have compilation := compile_admitted current required chosen positions compiled
  have unique : current.entries.Nodup := List.Nodup.of_map Prod.fst compilation.2.1
  have kept : index ∉ positions := by
    rw [compilation.2.2.2.2.2]
    simpa using (Keyed.selected_iff id current (by simpa using unique) chosen index stamp found).not.mpr unchosen
  exact Retained.advance_keeps_pair s next _ lawful advanced index origin e named actual kept

/-- The complete consuming comparison can start from actual scoped capture;
selected-source provenance is derived rather than supplied by the caller. -/
theorem captured_perform_source (contents : Epoch → Stamp → Nat) (captured current : Rows)
    (scopes : List (ScopedRecords.Scope Site Letter)) (chosen : List Stamp)
    (s next : Retained.State Epoch) (receiver nextGeneration : Nat) (published : Rows)
    (lawful : Retained.Lawful s)
    (accepted : perform contents current (ScopedRecords.capture contents captured scopes) chosen s receiver nextGeneration =
      some (published, next)) :
    published = Keyed.reference id current chosen [] nextGeneration ∧
      ∀ stamp ∈ chosen, stamp ∈ captured.entries ∧
        ∃ scope ∈ scopes, ScopedRecords.accepts scope stamp = true := by
  refine ⟨(perform_source contents current _ chosen s next receiver nextGeneration published lawful accepted).1, ?_⟩
  obtain ⟨positions, compiled, _⟩ := perform_admitted contents current _ chosen s next receiver nextGeneration published accepted
  exact fun stamp selected => selected_origin contents captured current scopes chosen positions compiled stamp selected

/-- Entrance correspondence is reconstructed after the actual retained
publication. No surviving event is renamed to its new positional index. -/
theorem perform_coupled (contents : Epoch → Stamp → Nat) (current : Rows) (required : Required)
    (chosen : List Stamp) (s next : Retained.State Epoch) (receiver nextGeneration : Nat) (published : Rows)
    (lawful : Retained.Lawful s)
    (accepted : perform contents current required chosen s receiver nextGeneration = some (published, next)) :
    Coupled contents published next ∧ (published.entries.map Prod.fst).Nodup := by
  obtain ⟨positions, compiled, currentRead, _, sourceGrant, advanced⟩ :=
    perform_admitted contents current required chosen s next receiver nextGeneration published accepted
  have sourceMeaning := perform_source contents current required chosen s next receiver nextGeneration published lawful accepted
  have liveUnique := (compile_admitted current required chosen positions compiled).2.1
  refine ⟨⟨sourceMeaning.2.1, ?_, sourceMeaning.2.2.1⟩, ?_⟩
  · obtain ⟨result, applied, same⟩ := Option.map_eq_some_iff.mp advanced
    cases same
    have granted := (Retained.applySpace_admitted s.origins.view s.channel _ result applied).1
    unfold Finite.apply at granted
    split at granted
    · have actual := (publication_admitted s.origins.view current.readToken positions [] nextGeneration result.1 granted).2.2.2.2
      change result.1.readToken = published.readToken
      rw [actual, sourceMeaning.1]
      exact congrArg (fun token : StoreReadToken Epoch Nat => (⟨token.storeId, nextGeneration⟩ : StoreReadToken Epoch Nat)) currentRead
    · cases granted
  · rw [sourceMeaning.1]
    simpa only [Keyed.reference, RevisionedStoreView.replaceRevision, Keyed.remaining, List.append_nil]
      using liveUnique.sublist (List.filter_sublist.map Prod.fst)

namespace Controls

abbrev StampN := ScopedRecords.Stamp Nat Nat Nat
abbrev RowsN := ScopedRecords.Source Nat Nat Nat Nat Nat

def contentsN (_epoch : Nat) (_stamp : StampN) : Nat := 42

def first : StampN := ((1, [10, 0]), 1)
def second : StampN := ((1, [10, 1]), 1)
def outside : StampN := ((2, [9]), 1)
def original : RowsN := ⟨17, 4, [outside, first, second]⟩
def current : RowsN := ⟨17, 5, [first, second]⟩
def scopes : List (ScopedRecords.Scope Nat Nat) := [.prefix 1 [10], .key 1 [10, 0]]
def read := ScopedRecords.capture contentsN original scopes

def waiting : Continuation := ⟨[⟨⟨1, 0, 0⟩, fun _ => true⟩], true⟩
def start := initial contentsN current 7 waiting

def one := (perform contentsN current read [first] start 7 6).get (by decide)
def remainingRead := ScopedRecords.capture contentsN one.1 [.key 1 [10, 1]]
def two := (perform contentsN one.1 remainingRead [second] one.2 7 7).get (by decide)

theorem equal_payloads_keep_distinct_stable_and_event_identities :
    first ≠ second ∧ contentsN 17 first = contentsN 17 second ∧
      (event contentsN 17 first).serial ≠ (event contentsN 17 second).serial ∧
      (events contentsN current).map EventPump.Event.payload = [42, 42] := by decide

theorem unrelated_shift_is_recompiled_but_old_positional_read_refuses :
    ScopedRecords.validate current read = true ∧
      compile original read [second] = some [2] ∧ compile current read [second] = some [1] ∧
      Keyed.publish id current original.readToken [second] [] 6 = none ∧
      (event contentsN original.storeId second).serial = (event contentsN current.storeId second).serial := by decide

theorem overlapping_read_views_do_not_multiply_consume_rights :
    (witnessed read).length = 3 ∧ compile current read [first] = some [0] ∧
      compile current read [first, first] = none ∧
      (perform contentsN current read [first, first] start 7 6).isNone = true ∧
      (perform contentsN current read [first] start 8 6).isNone = true := by decide

theorem real_repeated_publication_keeps_surviving_event_and_receiver :
    one.1.entries = [second] ∧ one.1.revision = 6 ∧
      one.2.channel.available = [event contentsN 17 second] ∧
      one.2.channel.spent = [(event contentsN 17 first).serial] ∧
      one.2.channel.ready = [⟨7, [event contentsN 17 first]⟩] ∧
      compile one.1 remainingRead [second] = some [0] ∧
      two.1.entries = [] ∧ two.2.channel.available = [] ∧
      two.2.channel.produced = start.channel.produced ∧
      two.2.channel.spent = [(event contentsN 17 first).serial, (event contentsN 17 second).serial] ∧
      two.2.channel.ready = [⟨7, [event contentsN 17 first]⟩, ⟨7, [event contentsN 17 second]⟩] ∧
      (two.2.channel.receives 7).isSome = true := by decide

theorem replaced_versions_duplicate_keys_and_unobserved_rows_refuse :
    let replacement : RowsN := ⟨17, 6, [((1, [10, 0]), 2), second]⟩
    let duplicates : RowsN := ⟨17, 6, [first, ((1, [10, 0]), 2), second]⟩
    contentsN 17 first = contentsN 17 ((1, [10, 0]), 2) ∧
      compile replacement read [first] = none ∧
      compile duplicates (ScopedRecords.capture contentsN duplicates scopes) [second] = none ∧
      compile original read [outside] = none ∧
      compile ⟨18, 5, current.entries⟩ read [second] = none := by decide

theorem spent_or_changed_source_cannot_be_reused_from_the_old_cut :
    (perform contentsN one.1 read [first] one.2 7 7).isNone = true ∧
      (perform contentsN current read [first] one.2 7 7).isNone = true ∧
      (perform contentsN one.1 remainingRead [second] one.2 7 6).isNone = true := by decide

end Controls

#print axioms perform_coupled
#print axioms Controls.equal_payloads_keep_distinct_stable_and_event_identities
#print axioms Controls.unrelated_shift_is_recompiled_but_old_positional_read_refuses
#print axioms Controls.overlapping_read_views_do_not_multiply_consume_rights
#print axioms Controls.real_repeated_publication_keeps_surviving_event_and_receiver
#print axioms Controls.replaced_versions_duplicate_keys_and_unobserved_rows_refuse
#print axioms Controls.spent_or_changed_source_cannot_be_reused_from_the_old_cut

#print axioms compile_admitted
#print axioms selected_resolves
#print axioms selected_origin
#print axioms serial_eq_iff
#print axioms event_injective
#print axioms event_mem_iff
#print axioms initial_coupled
#print axioms perform_admitted
#print axioms selected_events
#print axioms perform_source
#print axioms captured_perform_source
#print axioms perform_keeps_origin

end ScopedPublication

/-! ## Checked supplied output Events over the common retained consumer -/

namespace PositionalPublication.Retained

open PositionalPublication
open RevisionedStoreView.Publication
open Mettapedia.GSLT.Dynamics.StableOccurrenceContraction

variable {StoreId : Type}

/-- The existing produce operation, folded over actual supplied Events. -/
def appendEvents (s : Space) (outputs : List Occurrence) : Space := outputs.foldl produce s

def FreshOutputs (s : Space) (outputs : List Occurrence) : Prop :=
  (outputs.map EventPump.Event.serial).Nodup ∧
    ∀ event ∈ outputs, event.serial ∉ s.produced.map EventPump.Event.serial

instance freshOutputsDecision (s : Space) (outputs : List Occurrence) : Decidable (FreshOutputs s outputs) := by
  unfold FreshOutputs
  infer_instance

theorem appendEvents_exact (s : Space) (outputs : List Occurrence) (fresh : FreshOutputs s outputs) :
    appendEvents s outputs = { s with produced := s.produced ++ outputs, available := s.available ++ outputs } := by
  induction outputs generalizing s with
  | nil => simp [appendEvents]
  | cons event rest ih =>
      have new := fresh.2 event List.mem_cons_self
      have later : FreshOutputs (produce s event) rest := by
        refine ⟨(List.nodup_cons.mp fresh.1).2, ?_⟩
        intro other member
        simp only [produce, new, ↓reduceIte, List.map_append, List.map_singleton, List.mem_append, List.mem_singleton, not_or]
        exact ⟨fresh.2 other (List.mem_cons_of_mem event member), fun same =>
          (List.nodup_cons.mp fresh.1).1 (same ▸ List.mem_map.mpr ⟨other, member, rfl⟩)⟩
      change appendEvents (produce s event) rest = _
      rw [ih _ later]
      simp [produce, new, List.append_assoc]

theorem appendEvents_dense (s : Space) (start : Nat) (rows : List Data) :
    appendEvents s (outputEvents start rows) = produceOutputs s start rows := by
  induction rows generalizing s start with
  | nil => rfl
  | cons row rest ih =>
      simpa only [appendEvents, outputEvents, List.zipIdx_cons, List.map_cons,
        List.foldl_cons, produceOutputs] using ih (produce s ⟨start, row.1, row.2⟩) (start + 1)

/-- Every supplied output is qualified before the shared consuming transition.
No output can recycle an earlier produced occurrence, even after it is spent. -/
def applyWithEvents [DecidableEq StoreId] (view : View StoreId Nat) (s : Space)
    (request : Finite.Request StoreId Data × Nat) (outputs : List Occurrence) : Option (View StoreId Nat × Space) :=
  if outputs.map (fun e => (e.owner, e.payload)) = request.1.2.2.1 ∧ FreshOutputs s outputs then
    (consumeSpace view s request).map fun result => (result.1, appendEvents result.2 outputs)
  else none

def advanceWithEvents [DecidableEq StoreId] (s : State StoreId)
    (request : Finite.Request StoreId Data × Nat) (outputs : List Occurrence) : Option (State StoreId) :=
  (applyWithEvents s.origins.view s.channel request outputs).map fun result =>
    ⟨⟨result.1, Finite.transport s.origins request.1⟩, result.2⟩

theorem supplied_admitted [DecidableEq StoreId] (s next : State StoreId)
    (request : Finite.Request StoreId Data × Nat) (outputs : List Occurrence)
    (accepted : advanceWithEvents s request outputs = some next) :
    outputs.map (fun e => (e.owner, e.payload)) = request.1.2.2.1 ∧ FreshOutputs s.channel outputs ∧
      Finite.advance s.origins request.1 = some next.origins ∧
      ∃ c, s.channel.receives request.2 = some c ∧ valid s.channel c (select s.channel.available request.1.2.1) ∧
        next.channel = appendEvents (commit s.channel request.2 (select s.channel.available request.1.2.1)) outputs := by
  obtain ⟨result, applied, same⟩ := Option.map_eq_some_iff.mp accepted
  cases same
  unfold applyWithEvents at applied
  split at applied
  · rename_i allowed
    obtain ⟨consumed, moved, same⟩ := Option.map_eq_some_iff.mp applied
    cases same
    obtain ⟨published, c, registered, matched, actual⟩ := consumeSpace_admitted s.origins.view s.channel request consumed moved
    refine ⟨allowed.1, allowed.2, ?_, c, registered, matched, congrArg (fun space => appendEvents space outputs) actual⟩
    simp only [Finite.advance, published, Option.map_some]
  · cases applied

theorem supplied_fields [DecidableEq StoreId] (s next : State StoreId)
    (request : Finite.Request StoreId Data × Nat) (outputs : List Occurrence)
    (accepted : advanceWithEvents s request outputs = some next) :
    next.channel.produced = s.channel.produced ++ outputs ∧
      next.channel.available = s.channel.available.filter (fun e => decide (e ∉ select s.channel.available request.1.2.1)) ++ outputs ∧
      next.channel.spent = s.channel.spent ++ (select s.channel.available request.1.2.1).map EventPump.Event.serial ∧
      next.channel.ready = s.channel.ready ++ [⟨request.2, select s.channel.available request.1.2.1⟩] := by
  obtain ⟨_, fresh, _, c, registered, matched, actual⟩ := supplied_admitted s next request outputs accepted
  have produced : (commit s.channel request.2 (select s.channel.available request.1.2.1)).produced = s.channel.produced := by
    simp [commit, registered, matched]
  have new : FreshOutputs (commit s.channel request.2 (select s.channel.available request.1.2.1)) outputs :=
    ⟨fresh.1, by simpa only [produced] using fresh.2⟩
  have finished := appendEvents_exact _ outputs new
  rw [actual, finished]
  have committed := successful_join_is_atomic s.channel request.2 c _ registered matched
  exact ⟨by simp only [produced], congrArg (· ++ outputs) committed.1, committed.2.1, committed.2.2⟩

theorem supplied_lawful [DecidableEq StoreId] (s next : State StoreId)
    (request : Finite.Request StoreId Data × Nat) (outputs : List Occurrence)
    (lawful : Lawful s) (accepted : advanceWithEvents s request outputs = some next) : Lawful next := by
  obtain ⟨payloads, fresh, moved, c, registered, matched, _⟩ := supplied_admitted s next request outputs accepted
  have names := (Finite.advance_lawful s.origins next.origins request.1 lawful.1 moved).1
  obtain ⟨produced, available, spent, _⟩ := supplied_fields s next request outputs accepted
  have lengths : s.channel.available.length = s.origins.view.entries.length := by
    simpa only [List.length_map] using congrArg List.length lawful.2.1
  have uniqueRows := List.Nodup.of_map EventPump.Event.serial lawful.2.2.1
  refine ⟨names, ?_, ?_, ?_, ?_⟩
  · rw [available, List.map_append, payloads,
      filter_select_contract s.origins.view s.channel.available request.1.2.1 lengths uniqueRows,
      ← contract_map, lawful.2.1]
    obtain ⟨view, _, same⟩ := Option.map_eq_some_iff.mp moved
    have erased := names.1
    rw [← congrArg Finite.WithOrigins.rows same] at erased
    have newRows : (RevisionedStoreView.Publication.fresh s.origins.view request.1.2.1 request.1.2.2.1 request.1.2.2.2).map Prod.snd = request.1.2.2.1 := by
      simp [RevisionedStoreView.Publication.fresh, List.map_map, Function.comp_def, List.zipIdx_map_fst]
    simpa only [Finite.transport, List.map_append, ← contract_map, lawful.1.1, newRows] using erased
  · rw [available, List.map_append]
    apply List.nodup_append.mpr
    refine ⟨lawful.2.2.1.sublist (List.filter_sublist.map EventPump.Event.serial), fresh.1, ?_⟩
    intro old oldMember new newMember same
    obtain ⟨oldEvent, kept, oldName⟩ := List.mem_map.mp oldMember
    obtain ⟨newEvent, created, newName⟩ := List.mem_map.mp newMember
    apply fresh.2 newEvent created
    exact List.mem_map.mpr ⟨oldEvent, (lawful.2.2.2.1 oldEvent (List.mem_filter.mp kept).1).1, oldName.trans (same.trans newName.symm)⟩
  · intro event member
    rw [available, List.mem_append] at member
    rcases member with kept | created
    · have original := (List.mem_filter.mp kept).1
      have unselected := of_decide_eq_true (List.mem_filter.mp kept).2
      have known := lawful.2.2.2.1 event original
      refine ⟨?_, ?_⟩
      · rw [produced]; exact List.mem_append_left _ known.1
      · rw [spent, List.mem_append, not_or]
        refine ⟨known.2, ?_⟩
        intro chosen
        obtain ⟨other, selected, same⟩ := List.mem_map.mp chosen
        have equal := List.inj_on_of_nodup_map lawful.2.2.1 (select_source _ _ other selected) original same
        exact unselected (equal ▸ selected)
    · refine ⟨?_, ?_⟩
      · rw [produced]; exact List.mem_append_right _ created
      · rw [spent, List.mem_append, not_or]
        constructor
        · exact fun old => fresh.2 event created (lawful.2.2.2.2 event.serial old)
        · intro chosen
          obtain ⟨other, selected, same⟩ := List.mem_map.mp chosen
          exact fresh.2 event created (List.mem_map.mpr ⟨other, (lawful.2.2.2.1 other (select_source _ _ other selected)).1, same⟩)
  · intro serial member
    rw [spent, List.mem_append] at member
    have old : serial ∈ s.channel.produced.map EventPump.Event.serial := by
      rcases member with old | chosen
      · exact lawful.2.2.2.2 serial old
      · obtain ⟨event, selected, same⟩ := List.mem_map.mp chosen
        exact List.mem_map.mpr ⟨event, (lawful.2.2.2.1 event (select_source _ _ event selected)).1, same⟩
    rw [produced, List.map_append]
    exact List.mem_append_left _ old

theorem supplied_keeps_pair [DecidableEq StoreId] (s next : State StoreId)
    (request : Finite.Request StoreId Data × Nat) (outputs : List Occurrence)
    (lawful : Lawful s) (accepted : advanceWithEvents s request outputs = some next)
    (index : Nat) (origin : StoreOccurrenceId StoreId Nat × Data) (event : Occurrence)
    (named : s.origins.rows[index]? = some origin) (actual : s.channel.available[index]? = some event)
    (unchosen : index ∉ request.1.2.1) :
    ∃ target : Nat, next.origins.rows[target]? = some origin ∧ next.channel.available[target]? = some event := by
  have moved := (supplied_admitted s next request outputs accepted).2.2.1
  have rowLength : s.origins.rows.length = s.origins.view.entries.length := by simpa using congrArg List.length lawful.1.1
  have eventLength : s.channel.available.length = s.origins.view.entries.length := by simpa using congrArg List.length lawful.2.1
  obtain ⟨target, keptName, keptEvent⟩ := kept_pair_coordinate s.origins.view s.origins.rows s.channel.available
    request.1.2.1 rowLength eventLength index origin event named actual unchosen
  obtain ⟨view, _, same⟩ := Option.map_eq_some_iff.mp moved
  have rows : next.origins.rows = Finite.transport s.origins request.1 := (congrArg Finite.WithOrigins.rows same).symm
  refine ⟨target, ?_, ?_⟩
  · rw [rows]
    simpa only [Finite.transport, List.getElem?_append_left (List.getElem?_eq_some_iff.mp keptName).1] using keptName
  · rw [(supplied_fields s next request outputs accepted).2.1,
      filter_select_contract s.origins.view s.channel.available request.1.2.1 eventLength
        (List.Nodup.of_map EventPump.Event.serial lawful.2.2.1)]
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp keptEvent).1).trans keptEvent

/-- Each new actual Event and its newly issued positional origin occupy the
same appended coordinate, even when all returned payloads are equal. -/
theorem supplied_output_pair [DecidableEq StoreId] (s next : State StoreId)
    (request : Finite.Request StoreId Data × Nat) (outputs : List Occurrence)
    (lawful : Lawful s) (accepted : advanceWithEvents s request outputs = some next)
    (index : Nat) (event : Occurrence) (found : outputs[index]? = some event) :
    let target := (contracted s.origins.view request.1.2.1).rows.length + index
    next.origins.rows[target]? = some
      ((updated s.origins.view request.1.2.1 request.1.2.2.1 request.1.2.2.2).occurrenceId target, (event.owner, event.payload)) ∧
      next.channel.available[target]? = some event := by
  dsimp only
  obtain ⟨payloads, _, moved, _⟩ := supplied_admitted s next request outputs accepted
  obtain ⟨view, _, same⟩ := Option.map_eq_some_iff.mp moved
  have rows : next.origins.rows = Finite.transport s.origins request.1 := (congrArg Finite.WithOrigins.rows same).symm
  have rowMap : (contract (mask s.origins.view request.1.2.1) s.origins.rows).map Prod.snd =
      (contracted s.origins.view request.1.2.1).rows := by
    rw [← contract_map, lawful.1.1]
    simp only [contracted, compile_rows_exact]
  have rowLength := congrArg List.length rowMap
  simp only [List.length_map] at rowLength
  have dataAt : request.1.2.2.1[index]? = some (event.owner, event.payload) := by
    rw [← payloads, List.getElem?_map, found]
    rfl
  have freshAt : (RevisionedStoreView.Publication.fresh s.origins.view request.1.2.1 request.1.2.2.1 request.1.2.2.2)[index]? =
      some ((updated s.origins.view request.1.2.1 request.1.2.2.1 request.1.2.2.2).occurrenceId
        ((contracted s.origins.view request.1.2.1).rows.length + index), (event.owner, event.payload)) := by
    simp [RevisionedStoreView.Publication.fresh, List.getElem?_map, List.getElem?_zipIdx, dataAt]
  constructor
  · rw [rows]
    change (contract (mask s.origins.view request.1.2.1) s.origins.rows ++ _)[_]? = _
    rw [List.getElem?_append_right (by omega)]
    simpa only [rowLength, Nat.add_sub_cancel_left] using freshAt
  · have eventLength : s.channel.available.length = s.origins.view.entries.length := by simpa using congrArg List.length lawful.2.1
    have filtered := filter_select_contract s.origins.view s.channel.available request.1.2.1 eventLength
      (List.Nodup.of_map EventPump.Event.serial lawful.2.2.1)
    have eventMap : (contract (mask s.origins.view request.1.2.1) s.channel.available).map (fun e => (e.owner, e.payload)) =
        (contracted s.origins.view request.1.2.1).rows := by
      rw [← contract_map, lawful.2.1]
      simp only [contracted, compile_rows_exact]
    have eventCount := congrArg List.length eventMap
    simp only [List.length_map] at eventCount
    rw [(supplied_fields s next request outputs accepted).2.1, filtered,
      List.getElem?_append_right (by omega)]
    simpa only [eventCount, Nat.add_sub_cancel_left] using found

#print axioms supplied_keeps_pair
#print axioms supplied_output_pair

theorem dense_outputs_fresh (s : Space) (rows : List Data) : FreshOutputs s (outputEvents (freshStart s) rows) := by
  refine ⟨(output_properties _ rows).1, ?_⟩
  intro event member old
  obtain ⟨original, produced, same⟩ := List.mem_map.mp old
  have before := below_freshStart s original produced
  have after := (output_properties (freshStart s) rows).2 event member
  omega

theorem supplied_dense [DecidableEq StoreId] (s : State StoreId) (request : Finite.Request StoreId Data × Nat) :
    advanceWithEvents s request (outputEvents (freshStart s.channel) request.1.2.2.1) = advance s request := by
  have qualified : (outputEvents (freshStart s.channel) request.1.2.2.1).map (fun e => (e.owner, e.payload)) = request.1.2.2.1 ∧
      FreshOutputs s.channel (outputEvents (freshStart s.channel) request.1.2.2.1) :=
    ⟨output_payloads _ _, dense_outputs_fresh _ _⟩
  simp only [advanceWithEvents, applyWithEvents, if_pos qualified, advance, applySpace]
  simp only [appendEvents_dense]

#print axioms appendEvents_exact
#print axioms appendEvents_dense
#print axioms supplied_admitted
#print axioms supplied_fields
#print axioms supplied_lawful
#print axioms dense_outputs_fresh
#print axioms supplied_dense

end PositionalPublication.Retained

/-! ## Consuming and producing scoped-key turns -/

namespace ScopedPublication

open Mettapedia.Machines
open PositionalPublication
open RevisionedStoreView.Publication

set_option synthInstance.maxSize 256

variable {Epoch Site Letter Version : Type}
variable [DecidableEq Epoch] [DecidableEq Site] [DecidableEq Letter] [DecidableEq Version]
variable [Encodable Epoch] [Encodable Site] [Encodable Letter] [Encodable Version]

local notation "Rows" => ScopedRecords.Source Epoch Nat Site Letter Version
local notation "Stamp" => ScopedRecords.Stamp Site Letter Version
local notation "Required" => ScopedRecords.Captured Epoch Site Letter Version Nat
local notation "Pair" => Rows × Retained.State Epoch
local notation "Turn" => Required × List Stamp × List Stamp × Nat × Nat

def issuedEvents (contents : Epoch → Stamp → Nat) (current : Rows) (outputs : List Stamp) : List Occurrence :=
  outputs.map (event contents current.storeId)

/-- A consumed key may be replaced at a genuinely fresh version. Outputs
may not collide with surviving keys or with one another. -/
def outputKeys (current : Rows) (chosen outputs : List Stamp) : Prop :=
  ((Keyed.remaining id current.entries chosen ++ outputs).map Prod.fst).Nodup

instance outputKeysDecision (current : Rows) (chosen outputs : List Stamp) : Decidable (outputKeys current chosen outputs) := by
  unfold outputKeys
  infer_instance

/-- Output identity/payloads are built from the actual issued rows. The shared
retained consumer checks their freshness before its one committing transition. -/
def performOutputs (contents : Epoch → Stamp → Nat) (current : Rows) (required : Required)
    (chosen outputs : List Stamp) (s : Retained.State Epoch) (receiver nextGeneration : Nat) : Option Pair := do
  let positions ← compile current required chosen
  if s.origins.view.readToken = current.readToken ∧ s.channel.available = events contents current ∧
      outputKeys current chosen outputs then
    let published ← Keyed.publish id current current.readToken chosen outputs nextGeneration
    let supplied := issuedEvents contents current outputs
    let reached ← Retained.advanceWithEvents s
      ((current.readToken, positions, supplied.map (fun e => (e.owner, e.payload)), nextGeneration), receiver) supplied
    some (published, reached)
  else none

theorem outputs_admitted (contents : Epoch → Stamp → Nat) (current : Rows) (required : Required)
    (chosen outputs : List Stamp) (s next : Retained.State Epoch) (receiver nextGeneration : Nat) (published : Rows)
    (accepted : performOutputs contents current required chosen outputs s receiver nextGeneration = some (published, next)) :
    ∃ positions, compile current required chosen = some positions ∧
      s.origins.view.readToken = current.readToken ∧ s.channel.available = events contents current ∧
      outputKeys current chosen outputs ∧ Keyed.publish id current current.readToken chosen outputs nextGeneration = some published ∧
      Retained.advanceWithEvents s
        ((current.readToken, positions, (issuedEvents contents current outputs).map (fun e => (e.owner, e.payload)), nextGeneration), receiver)
        (issuedEvents contents current outputs) = some next := by
  unfold performOutputs at accepted
  obtain ⟨positions, compiled, continued⟩ := Option.bind_eq_some_iff.mp accepted
  split at continued
  · rename_i entrance
    obtain ⟨rows, sourceGrant, rest⟩ := Option.bind_eq_some_iff.mp continued
    obtain ⟨reached, advanced, same⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj same
    exact ⟨positions, compiled, entrance.1, entrance.2.1, entrance.2.2, sourceGrant, advanced⟩
  · cases continued

theorem outputs_source (contents : Epoch → Stamp → Nat) (current : Rows) (required : Required)
    (chosen outputs : List Stamp) (s next : Retained.State Epoch) (receiver nextGeneration : Nat) (published : Rows)
    (lawful : Retained.Lawful s)
    (accepted : performOutputs contents current required chosen outputs s receiver nextGeneration = some (published, next)) :
    published = Keyed.reference id current chosen outputs nextGeneration ∧ Retained.Lawful next ∧
      next.channel.available = events contents published ∧
      next.channel.produced = s.channel.produced ++ issuedEvents contents current outputs ∧
      next.channel.spent = s.channel.spent ++ (chosen.map (event contents current.storeId)).map EventPump.Event.serial ∧
      next.channel.ready = s.channel.ready ++ [⟨receiver, chosen.map (event contents current.storeId)⟩] := by
  obtain ⟨positions, compiled, _, currentEvents, _, sourceGrant, advanced⟩ :=
    outputs_admitted contents current required chosen outputs s next receiver nextGeneration published accepted
  have compilation := compile_admitted current required chosen positions compiled
  have sourceResult := (Keyed.admitted id current current.readToken chosen outputs nextGeneration published sourceGrant).2.2.2.2.2
  have tuple := selected_events contents current chosen compilation.2.2.2.2.1
  rw [← compilation.2.2.2.2.2, ← currentEvents] at tuple
  obtain ⟨produced, available, spent, ready⟩ := Retained.supplied_fields s next _ _ advanced
  refine ⟨sourceResult, Retained.supplied_lawful s next _ _ lawful advanced, ?_, produced, ?_, ?_⟩
  · rw [available, tuple, currentEvents, sourceResult]
    simp [events, issuedEvents, Keyed.reference, Keyed.remaining, RevisionedStoreView.replaceRevision,
      List.filter_map, Function.comp_def, event_mem_iff]
  · simpa only [tuple] using spent
  · simpa only [tuple] using ready

theorem outputs_coupled (contents : Epoch → Stamp → Nat) (current : Rows) (required : Required)
    (chosen outputs : List Stamp) (s next : Retained.State Epoch) (receiver nextGeneration : Nat) (published : Rows)
    (lawful : Retained.Lawful s)
    (accepted : performOutputs contents current required chosen outputs s receiver nextGeneration = some (published, next)) :
    Coupled contents published next ∧ (published.entries.map Prod.fst).Nodup := by
  obtain ⟨positions, _, currentRead, _, keys, _, advanced⟩ :=
    outputs_admitted contents current required chosen outputs s next receiver nextGeneration published accepted
  have meaning := outputs_source contents current required chosen outputs s next receiver nextGeneration published lawful accepted
  refine ⟨⟨meaning.2.1, ?_, meaning.2.2.1⟩, ?_⟩
  · have moved := (Retained.supplied_admitted s next _ _ advanced).2.2.1
    obtain ⟨view, grant, same⟩ := Option.map_eq_some_iff.mp moved
    have nextView : next.origins.view = view := (congrArg Finite.WithOrigins.view same).symm
    unfold Finite.apply at grant
    split at grant
    · have actual := (publication_admitted s.origins.view current.readToken positions _ nextGeneration view grant).2.2.2.2
      change next.origins.view.readToken = published.readToken
      rw [nextView, actual, meaning.1]
      exact congrArg (fun token : StoreReadToken Epoch Nat => (⟨token.storeId, nextGeneration⟩ : StoreReadToken Epoch Nat)) currentRead
    · cases grant
  · rw [meaning.1]
    exact keys

/-- Surviving original names and actual Events are transported together by
this same consuming/producing operation. -/
theorem outputs_keep_origin (contents : Epoch → Stamp → Nat) (current : Rows) (required : Required)
    (chosen outputs : List Stamp) (s next : Retained.State Epoch) (receiver nextGeneration : Nat) (published : Rows)
    (lawful : Retained.Lawful s)
    (accepted : performOutputs contents current required chosen outputs s receiver nextGeneration = some (published, next))
    (index : Nat) (stamp : Stamp) (found : current.entries[index]? = some stamp) (unchosen : stamp ∉ chosen)
    (origin : StoreOccurrenceId Epoch Nat × Data) (e : Occurrence)
    (named : s.origins.rows[index]? = some origin) (actual : s.channel.available[index]? = some e) :
    ∃ target : Nat, next.origins.rows[target]? = some origin ∧ next.channel.available[target]? = some e := by
  obtain ⟨positions, compiled, _, _, _, _, advanced⟩ :=
    outputs_admitted contents current required chosen outputs s next receiver nextGeneration published accepted
  have compilation := compile_admitted current required chosen positions compiled
  have unique : current.entries.Nodup := List.Nodup.of_map Prod.fst compilation.2.1
  have kept : index ∉ positions := by
    rw [compilation.2.2.2.2.2]
    simpa using (Keyed.selected_iff id current (by simpa using unique) chosen index stamp found).not.mpr unchosen
  exact Retained.supplied_keeps_pair s next _ _ lawful advanced index origin e named actual kept

/-- The actual issued stamp materializes one payload/Event and one fresh
positional origin at the same retained coordinate. -/
theorem outputs_issued_origin (contents : Epoch → Stamp → Nat) (current : Rows) (required : Required)
    (chosen outputs : List Stamp) (s next : Retained.State Epoch) (receiver nextGeneration : Nat) (published : Rows)
    (lawful : Retained.Lawful s)
    (accepted : performOutputs contents current required chosen outputs s receiver nextGeneration = some (published, next))
    (index : Nat) (stamp : Stamp) (found : outputs[index]? = some stamp) :
    let emitted := event contents current.storeId stamp
    stamp ∈ published.entries ∧ ∃ target : Nat, ∃ origin : StoreOccurrenceId Epoch Nat,
      next.origins.rows[target]? = some (origin, (emitted.owner, emitted.payload)) ∧
        next.channel.available[target]? = some emitted ∧ origin.read.storeId = current.storeId ∧
        origin.read.revision = nextGeneration := by
  dsimp only
  obtain ⟨positions, _, currentRead, _, _, _, advanced⟩ :=
    outputs_admitted contents current required chosen outputs s next receiver nextGeneration published accepted
  have emitted : (issuedEvents contents current outputs)[index]? = some (event contents current.storeId stamp) := by
    rw [issuedEvents, List.getElem?_map, found]
    rfl
  have pair := Retained.supplied_output_pair s next _ _ lawful advanced index _ emitted
  have meaning := (outputs_source contents current required chosen outputs s next receiver nextGeneration published lawful accepted).1
  refine ⟨?_, _, _, pair.1, pair.2, ?_, rfl⟩
  · rw [meaning]
    exact List.mem_append_right _ (List.mem_of_getElem? found)
  · change s.origins.view.storeId = current.storeId
    exact congrArg StoreReadToken.storeId currentRead

theorem invalid_outputs_refused (contents : Epoch → Stamp → Nat) (current : Rows) (required : Required)
    (chosen outputs : List Stamp) (s : Retained.State Epoch) (receiver nextGeneration : Nat)
    (bad : ¬ outputKeys current chosen outputs ∨ ¬ Retained.FreshOutputs s.channel (issuedEvents contents current outputs)) :
    performOutputs contents current required chosen outputs s receiver nextGeneration = none := by
  cases result : performOutputs contents current required chosen outputs s receiver nextGeneration with
  | none => rfl
  | some pair =>
      obtain ⟨_, _, _, _, keys, _, advanced⟩ := outputs_admitted contents current required chosen outputs s pair.2 receiver nextGeneration pair.1 result
      rcases bad with bad | bad
      · exact False.elim (bad keys)
      · exact False.elim (bad (Retained.supplied_admitted s pair.2 _ _ advanced).2.1)

/-- An adapter word has no scheduler or future-answer oracle; each entry
calls the same actual checked operation on the whole returned saved state. -/
def runOutputs (contents : Epoch → Stamp → Nat) : List Turn → Pair → Option Pair
  | [], saved => some saved
  | turn :: rest, saved =>
      (performOutputs contents saved.1 turn.1 turn.2.1 turn.2.2.1 saved.2 turn.2.2.2.1 turn.2.2.2.2).bind (runOutputs contents rest)

/-- Independent ordered keyed removal/append semantics, with no Event queue,
position compiler, scoped validator or origin transport. -/
def referenceOutputs : List Turn → Rows → Rows
  | [], current => current
  | turn :: rest, current => referenceOutputs rest (Keyed.reference id current turn.2.1 turn.2.2.1 turn.2.2.2.2)

theorem runOutputs_append (contents : Epoch → Stamp → Nat) (first second : List Turn) (saved : Pair) :
    runOutputs contents (first ++ second) saved = (runOutputs contents first saved).bind (runOutputs contents second) := by
  induction first generalizing saved with
  | nil => rfl
  | cons turn rest ih =>
      simp only [List.cons_append, runOutputs]
      rw [Option.bind_assoc]
      congr 1
      funext next
      exact ih next

theorem runOutputs_source (contents : Epoch → Stamp → Nat) (turns : List Turn) (saved final : Pair)
    (coupled : Coupled contents saved.1 saved.2) (unique : (saved.1.entries.map Prod.fst).Nodup)
    (accepted : runOutputs contents turns saved = some final) :
    final.1 = referenceOutputs turns saved.1 ∧ Coupled contents final.1 final.2 ∧ (final.1.entries.map Prod.fst).Nodup := by
  induction turns generalizing saved with
  | nil => cases Option.some.inj accepted; exact ⟨rfl, coupled, unique⟩
  | cons turn rest ih =>
      obtain ⟨next, moved, continued⟩ := Option.bind_eq_some_iff.mp accepted
      have actual := outputs_source contents saved.1 turn.1 turn.2.1 turn.2.2.1 saved.2 next.2 turn.2.2.2.1 turn.2.2.2.2 next.1 coupled.1 moved
      have preserved := outputs_coupled contents saved.1 turn.1 turn.2.1 turn.2.2.1 saved.2 next.2 turn.2.2.2.1 turn.2.2.2.2 next.1 coupled.1 moved
      have result := ih next preserved.1 preserved.2 continued
      exact ⟨result.1.trans (by rw [referenceOutputs, ← actual.1]), result.2⟩

/-- The entry invariant is constructed from the actual initial source, so
arbitrary successful turn words need no supplied final-coupling assertion. -/
theorem outputs_from_initial (contents : Epoch → Stamp → Nat) (current : Rows) (receiver : Nat) (c : Continuation)
    (unique : (current.entries.map Prod.fst).Nodup) (turns : List Turn) (final : Pair)
    (accepted : runOutputs contents turns (current, initial contents current receiver c) = some final) :
    final.1 = referenceOutputs turns current ∧ Coupled contents final.1 final.2 ∧ (final.1.entries.map Prod.fst).Nodup :=
  runOutputs_source contents turns _ final (initial_coupled contents current unique receiver c) unique accepted

namespace OutputsControls

open Controls

def replacement : StampN := ((1, [10, 0]), 2)
def created (version : Nat) : StampN := ((1, [20]), version)
def firstOutputs : List StampN := [replacement, created 1]

def one := (performOutputs contentsN current read [first] firstOutputs start 7 6).get (by decide)
def secondRead := ScopedRecords.capture contentsN one.1 [.key 1 [20]]
def two := (performOutputs contentsN one.1 secondRead [created 1] [created 2] one.2 7 7).get (by decide)
def thirdRead := ScopedRecords.capture contentsN two.1 [.key 1 [20]]
def retry := (performOutputs contentsN two.1 thirdRead [created 2] [created 3] two.2 7 8).get (by decide)

theorem actual_turn_replaces_consumed_key_and_appends_distinct_equal_payloads :
    outputKeys current [first] firstOutputs ∧ one.1.entries = [second, replacement, created 1] ∧
      one.1.revision = 6 ∧
      one.2.channel.available = [event contentsN 17 second, event contentsN 17 replacement, event contentsN 17 (created 1)] ∧
      one.2.channel.produced = start.channel.produced ++ issuedEvents contentsN current firstOutputs ∧
      one.2.channel.spent = [(event contentsN 17 first).serial] ∧
      (one.2.channel.available.map EventPump.Event.payload) = [42, 42, 42] ∧
      (event contentsN 17 first).serial ≠ (event contentsN 17 replacement).serial := by decide

theorem repeated_turns_preserve_old_origins_and_construct_new_output_pairs :
    two.1.entries = [second, replacement, created 2] ∧
      two.2.channel.available = [event contentsN 17 second, event contentsN 17 replacement, event contentsN 17 (created 2)] ∧
      (two.2.origins.rows.map fun row => (row.1.read.revision, row.1.logicalIndex)) = [(5, 1), (6, 1), (7, 2)] ∧
      two.2.channel.produced = start.channel.produced ++ issuedEvents contentsN current firstOutputs ++
        [event contentsN 17 (created 2)] ∧
      two.2.channel.ready = [⟨7, [event contentsN 17 first]⟩, ⟨7, [event contentsN 17 (created 1)]⟩] ∧
      (two.2.channel.receives 7).isSome = true := by decide

theorem collision_and_reused_live_keys_refuse_before_consumption :
    let liveReplacement : StampN := ((1, [10, 1]), 2)
    (performOutputs contentsN current read [first] [liveReplacement] start 7 6).isNone = true ∧
      (performOutputs contentsN current read [first] [created 1, created 1] start 7 6).isNone = true ∧
      outputKeys current [first] [first] ∧
      (performOutputs contentsN current read [first] [first] start 7 6).isNone = true ∧
      (Retained.advanceWithEvents start
        ((current.readToken, [0], [((event contentsN 17 second).owner, 42)], 6), 7)
        [event contentsN 17 second]).isNone = true := by decide

theorem old_output_cannot_return_after_retirement_but_fresh_retry_uses_same_state :
    event contentsN 17 (created 1) ∈ two.2.channel.produced ∧
      event contentsN 17 (created 1) ∉ two.2.channel.available ∧
      outputKeys two.1 [created 2] [created 1] ∧
      (performOutputs contentsN two.1 thirdRead [created 2] [created 1] two.2 7 8).isNone = true ∧
      retry.1.entries = [second, replacement, created 3] ∧ retry.2.channel.ready.length = 3 ∧
      retry.2.channel.produced.length = 6 ∧
      retry.2.channel.spent = [(event contentsN 17 first).serial, (event contentsN 17 (created 1)).serial,
        (event contentsN 17 (created 2)).serial] := by decide

def singleStart := initial contentsN current 7 { waiting with persistent := false }
def single := (performOutputs contentsN current read [first] [replacement] singleStart 7 6).get (by decide)

theorem output_readability_does_not_reissue_one_shot_receiver :
    single.1.entries = [second, replacement] ∧ (single.2.channel.receives 7).isNone = true ∧
      (performOutputs contentsN single.1 (ScopedRecords.capture contentsN single.1 [.key 1 [10, 0]])
        [replacement] [created 1] single.2 7 7).isNone = true ∧
      single.2.channel.ready.length = 1 := by decide

end OutputsControls

#print axioms OutputsControls.actual_turn_replaces_consumed_key_and_appends_distinct_equal_payloads
#print axioms OutputsControls.repeated_turns_preserve_old_origins_and_construct_new_output_pairs
#print axioms OutputsControls.collision_and_reused_live_keys_refuse_before_consumption
#print axioms OutputsControls.old_output_cannot_return_after_retirement_but_fresh_retry_uses_same_state
#print axioms OutputsControls.output_readability_does_not_reissue_one_shot_receiver

#print axioms outputs_admitted
#print axioms outputs_source
#print axioms outputs_coupled
#print axioms outputs_keep_origin
#print axioms outputs_issued_origin
#print axioms invalid_outputs_refused
#print axioms runOutputs_append
#print axioms runOutputs_source
#print axioms outputs_from_initial

end ScopedPublication

end Mettapedia.Machines.ChannelJoin
