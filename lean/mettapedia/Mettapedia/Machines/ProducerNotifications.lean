import Mettapedia.Machines.ProducerReadReuse
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Actual-read producer notifications

The specification computes affected readers from their captured read traces.
The native reverse index implements this relation through intrusive edges.
Publication changes one producer's append revision and schedules its readers;
recapture replaces one reader's trace and discharges its pending obligation.

The invariant establishes agreement for every unqueued reader, including empty
answer reads. An empty queue therefore establishes complete read agreement,
which permits exact replay of pure adaptive programs. Purity, append-only
answers, coherent capture and a fixed read region remain admission obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProducerNotifications

open ReadOnlyQuery

universe u v
variable {Producer : Type u} {Reader : Type v}
variable [DecidableEq Producer] [DecidableEq Reader] [Fintype Reader]

def traceKeys (trace : Reads Producer Nat) : Finset Producer :=
  (trace.map Prod.fst).toFinset

@[simp] theorem mem_traceKeys (source : Producer) (trace : Reads Producer Nat) :
    source ∈ traceKeys trace ↔ ∃ revision, (source, revision) ∈ trace := by
  simp only [traceKeys, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨key, revision⟩, member, rfl⟩
    exact ⟨revision, member⟩
  · rintro ⟨revision, member⟩
    exact ⟨(source, revision), member, rfl⟩

def affectedReaders (captures : Reader → Reads Producer Nat) (source : Producer) :
    Finset Reader := Finset.univ.filter fun reader => source ∈ traceKeys (captures reader)

omit [DecidableEq Reader] in
@[simp] theorem mem_affectedReaders (captures : Reader → Reads Producer Nat)
    (source : Producer) (reader : Reader) :
    reader ∈ affectedReaders captures source ↔ source ∈ traceKeys (captures reader) := by
  simp [affectedReaders]

theorem unobserved_update_agrees (current : Producer → Nat) (trace : Reads Producer Nat)
    (source : Producer) (revision : Nat) (unread : source ∉ traceKeys trace)
    (valid : Agrees current trace) :
    Agrees (Function.update current source revision) trace := by
  intro ⟨key, observed⟩ member
  have different : key ≠ source := by
    intro equality
    subst key
    apply unread
    exact (mem_traceKeys source trace).mpr ⟨observed, member⟩
  simpa [Function.update_of_ne different] using valid (key, observed) member

structure State (Producer : Type u) (Reader : Type v) where
  current : Producer → Nat
  captures : Reader → Reads Producer Nat
  pending : Finset Reader

def Valid (state : State Producer Reader) : Prop :=
  ∀ reader, reader ∉ state.pending → Agrees state.current (state.captures reader)

def initial (current : Producer → Nat) (captures : Reader → Reads Producer Nat) :
    State Producer Reader :=
  ⟨current, captures, Finset.univ.filter fun reader => checkReads current (captures reader) = false⟩

omit [DecidableEq Producer] [DecidableEq Reader] in
theorem initial_valid (current : Producer → Nat) (captures : Reader → Reads Producer Nat) :
    Valid (initial current captures) := by
  intro reader clean
  have accepted : checkReads current (captures reader) = true := by
    simpa [initial] using clean
  exact (checkReads_iff _ _).mp accepted

def publish (state : State Producer Reader) (source : Producer) : State Producer Reader :=
  {state with
    current := Function.update state.current source (state.current source + 1)
    pending := state.pending ∪ affectedReaders state.captures source}

theorem publish_valid (state : State Producer Reader) (source : Producer)
    (valid : Valid state) : Valid (publish state source) := by
  intro reader clean
  have absent : reader ∉ state.pending ∧ source ∉ traceKeys (state.captures reader) := by
    simpa [publish] using clean
  exact unobserved_update_agrees state.current (state.captures reader) source _
    absent.2 (valid reader absent.1)

theorem publication_wakes_every_reader (state : State Producer Reader) (source : Producer)
    (reader : Reader) (reads : source ∈ traceKeys (state.captures reader)) :
    reader ∈ (publish state source).pending := by simp [publish, reads]

theorem publication_preserves_other_obligations (state : State Producer Reader)
    (source : Producer) (reader : Reader) (pending : reader ∈ state.pending) :
    reader ∈ (publish state source).pending := by simp [publish, pending]

def recapture (state : State Producer Reader) (reader : Reader) (trace : Reads Producer Nat) :
    State Producer Reader :=
  {state with
    captures := Function.update state.captures reader trace
    pending := state.pending.erase reader}

omit [DecidableEq Producer] [Fintype Reader] in
theorem recapture_valid (state : State Producer Reader) (reader : Reader)
    (trace : Reads Producer Nat) (coherent : Agrees state.current trace)
    (valid : Valid state) : Valid (recapture state reader trace) := by
  intro other clean
  by_cases same : other = reader
  · subst other
    simpa [recapture] using coherent
  · have absent : other ∉ state.pending := by simpa [recapture, same] using clean
    simpa [recapture, same] using valid other absent

theorem recapture_changes_reverse_relation (state : State Producer Reader) (reader : Reader)
    (trace : Reads Producer Nat) (source : Producer) :
    reader ∈ affectedReaders (recapture state reader trace).captures source ↔
      source ∈ traceKeys trace := by simp [recapture]

omit [DecidableEq Producer] [DecidableEq Reader] [Fintype Reader] in
theorem empty_queue_establishes_read_agreement (state : State Producer Reader)
    (valid : Valid state) (finished : state.pending = ∅) :
    ∀ reader, Agrees state.current (state.captures reader) := by
  intro reader
  exact valid reader (by simp [finished])

omit [DecidableEq Producer] [DecidableEq Reader] [Fintype Reader] in
theorem completed_reader_replays_exact {Answer : Type*}
    (state : State Producer Reader) (valid : Valid state) (finished : state.pending = ∅)
    (reader : Reader) (stores : Nat → Producer → Nat) (start : Nat)
    (program : Program Producer Nat Answer)
    (captured : state.captures reader = (ProducerReadReuse.runChanging stores start program).reads) :
    run state.current program = ProducerReadReuse.runChanging stores start program := by
  apply ProducerReadReuse.replay_changing_exact
  rw [← captured]
  exact empty_queue_establishes_read_agreement state valid finished reader

/-- Absence is still a read: an empty answer list has append revision zero. -/
theorem empty_answer_read_is_not_optional :
    () ∈ (publish (initial (fun _ : Unit => 0) (fun _ : Unit => [((), 0)])) ()).pending := by
  decide

theorem omitted_empty_read_can_falsely_complete :
    ¬ Agrees (fun _ : Unit => 1) [((), 0)] ∧
      Agrees (fun _ : Unit => 1) ([] : Reads Unit Nat) := by simp [Agrees]

end Mettapedia.Machines.ProducerNotifications
