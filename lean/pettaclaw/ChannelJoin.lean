import EventPump

/-!
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

namespace ChannelJoin

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

/-- Independent joins stay enabled after either order of commitment. This is
channel noninterference, not commutativity of arbitrary external effects. -/
theorem independent_join_remains_enabled (s : Space) (id other : Nat)
    (first second : Continuation) (selected candidate : List Occurrence)
    (firstRegistered : s.receives id = some first)
    (secondRegistered : s.receives other = some second)
    (firstValid : valid s first selected) (secondValid : valid s second candidate)
    (different : other ≠ id)
    (disjoint : ∀ e ∈ candidate, e.serial ∉ selected.map EventPump.Event.serial) :
    (commit s id selected).receives other = some second ∧
    valid (commit s id selected) second candidate := by
  refine ⟨?_, secondValid.1, secondValid.2.1, secondValid.2.2.1, ?_⟩
  · rw [join_preserves_other_receives s id other selected different]
    exact secondRegistered
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

end ChannelJoin
