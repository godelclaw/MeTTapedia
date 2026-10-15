import Mettapedia.Machines.EventPump
import Mettapedia.GSLT.Causality.ResourceWaves
import Mettapedia.GSLT.Causality.ResourceRuns

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

end Mettapedia.Machines.ChannelJoin
