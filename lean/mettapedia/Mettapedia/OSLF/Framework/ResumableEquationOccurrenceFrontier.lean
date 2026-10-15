import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Resumable search through equation representatives and primitive occurrences

One queue entry contains an actual equation-conversion history. Exploring it
appends every primitive firing occurrence, including repeated endpoints, and
enqueues newly encountered equation representatives. Visited representatives
are not re-expanded merely because a second conversion reaches them. All
discovered conversion histories remain available independently of firings.

Partial enumerators retain explicit obligations. Queue exhaustion alone is not
a completeness certificate. The finite-coverage checker supplies that further
contract. The search allowance counts work on representatives; it is not a
charge account, a physical reaction count, or a proof of fairness.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier

universe u v w z

/-- An enumerator may supply proved answers while retaining unhandled work. -/
structure Batch (Answer : Type u) (Obligation : Type v) where
  answers : List Answer
  unresolved : List Obligation
  deriving Repr

/-- The fixed providers of one search. Their meanings are specified separately. -/
structure Model (Node : Type u) (EquationOrigin : Type v)
    (Occurrence : Type w) (Obligation : Type z) where
  equations : Node → Batch (EquationOrigin × Node) Obligation
  firings : Node → Batch (Occurrence × Node) Obligation

/-- Each conversion records its authored origin and the resulting representative. -/
structure Entry (Node : Type u) (EquationOrigin : Type v) where
  state : Node
  conversions : List (EquationOrigin × Node)
  deriving DecidableEq, Repr

/-- A primitive occurrence keeps its representative, conversion history,
enumeration position, authored receipt and target separately. -/
structure Receipt (Node : Type u) (EquationOrigin : Type v) (Occurrence : Type w) where
  representative : Entry Node EquationOrigin
  occurrenceIndex : Nat
  origin : Occurrence
  target : Node
  deriving DecidableEq, Repr

inductive Phase where
  | equation
  | firing
  deriving DecidableEq, Repr

structure Parked (Node : Type u) (EquationOrigin : Type v) (Obligation : Type z) where
  representative : Entry Node EquationOrigin
  phase : Phase
  reason : Obligation
  deriving DecidableEq, Repr

structure Snapshot (Node : Type u) (EquationOrigin : Type v)
    (Occurrence : Type w) (Obligation : Type z) where
  pending : List (Entry Node EquationOrigin)
  visited : List (Entry Node EquationOrigin)
  conversions : List (Entry Node EquationOrigin)
  receipts : List (Receipt Node EquationOrigin Occurrence)
  parked : List (Parked Node EquationOrigin Obligation)
  work : Nat
  deriving DecidableEq, Repr

variable {Node : Type u} {EquationOrigin : Type v}
  {Occurrence : Type w} {Obligation : Type z}

def initial (source : Node) : Snapshot Node EquationOrigin Occurrence Obligation where
  pending := [⟨source, []⟩]
  visited := []
  conversions := []
  receipts := []
  parked := []
  work := 0

def Entry.extend (entry : Entry Node EquationOrigin) (edge : EquationOrigin × Node) :
    Entry Node EquationOrigin :=
  ⟨edge.2, entry.conversions ++ [edge]⟩

def discoveries (entry : Entry Node EquationOrigin)
    (answers : List (EquationOrigin × Node)) : List (Entry Node EquationOrigin) :=
  answers.map entry.extend

def readouts (entry : Entry Node EquationOrigin)
    (answers : List (Occurrence × Node)) : List (Receipt Node EquationOrigin Occurrence) :=
  answers.zipIdx.map fun (answer, index) => ⟨entry, index, answer.1, answer.2⟩

def obligations (entry : Entry Node EquationOrigin) (phase : Phase)
    (reasons : List Obligation) : List (Parked Node EquationOrigin Obligation) :=
  reasons.map fun reason => ⟨entry, phase, reason⟩

/-- Explore one pending representative without discarding unsupported obligations. -/
def tick [DecidableEq Node] (model : Model Node EquationOrigin Occurrence Obligation)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) :
    Snapshot Node EquationOrigin Occurrence Obligation :=
  match snapshot.pending with
  | [] => snapshot
  | entry :: rest =>
    if entry.state ∈ snapshot.visited.map Entry.state then
      { snapshot with pending := rest, work := snapshot.work + 1 }
    else
      let equationBatch := model.equations entry.state
      let firingBatch := model.firings entry.state
      let next := discoveries entry equationBatch.answers
      let known := entry.state :: (snapshot.visited.map Entry.state ++ rest.map Entry.state)
      { pending := rest ++ next.filter (fun candidate => decide (candidate.state ∉ known))
        visited := snapshot.visited ++ [entry]
        conversions := snapshot.conversions ++ next
        receipts := snapshot.receipts ++ readouts entry firingBatch.answers
        parked := snapshot.parked ++
          (obligations entry .equation equationBatch.unresolved ++
            obligations entry .firing firingBatch.unresolved)
        work := snapshot.work + 1 }

def run [DecidableEq Node] (model : Model Node EquationOrigin Occurrence Obligation) :
    Nat → Snapshot Node EquationOrigin Occurrence Obligation →
      Snapshot Node EquationOrigin Occurrence Obligation
  | 0, snapshot => snapshot
  | fuel + 1, snapshot => run model fuel (tick model snapshot)

/-- The exact resumable state includes all retained origins and pending work. -/
theorem run_add [DecidableEq Node] (model : Model Node EquationOrigin Occurrence Obligation)
    (first second : Nat) (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) :
    run model (first + second) snapshot = run model second (run model first snapshot) := by
  induction first generalizing snapshot with
  | zero => simp [run]
  | succ first ih =>
    simpa only [Nat.succ_add, run] using ih (tick model snapshot)

theorem tick_receipts_extend [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) :
    ∃ added, (tick model snapshot).receipts = snapshot.receipts ++ added := by
  cases pending : snapshot.pending with
  | nil => exact ⟨[], by simp [tick, pending]⟩
  | cons entry rest =>
    by_cases seen : entry.state ∈ snapshot.visited.map Entry.state
    · exact ⟨[], by simp [tick, pending, seen]⟩
    · exact ⟨readouts entry (model.firings entry.state).answers,
        by simp [tick, pending, seen]⟩

theorem run_receipts_extend [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation)
    (fuel : Nat) (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) :
    ∃ added, (run model fuel snapshot).receipts = snapshot.receipts ++ added := by
  induction fuel generalizing snapshot with
  | zero => exact ⟨[], by simp [run]⟩
  | succ fuel ih =>
    obtain ⟨first, firstEq⟩ := tick_receipts_extend model snapshot
    obtain ⟨rest, restEq⟩ := ih (tick model snapshot)
    exact ⟨first ++ rest, by rw [run, restEq, firstEq, List.append_assoc]⟩

theorem run_preserves_receipt [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation)
    (fuel : Nat) (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (receipt : Receipt Node EquationOrigin Occurrence) (present : receipt ∈ snapshot.receipts) :
    receipt ∈ (run model fuel snapshot).receipts := by
  obtain ⟨added, represented⟩ := run_receipts_extend model fuel snapshot
  rw [represented]
  exact List.mem_append_left added present

/-- This readout rejects both runnable and parked unfinished work. It becomes
semantic completeness only after the independent coverage check is proved. -/
def quiescent (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) : Bool :=
  snapshot.pending.isEmpty && snapshot.parked.isEmpty

theorem quiescent_iff (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) :
    quiescent snapshot = true ↔ snapshot.pending = [] ∧ snapshot.parked = [] := by
  simp [quiescent]

theorem parked_not_quiescent (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (unfinished : snapshot.parked ≠ []) : quiescent snapshot = false := by
  cases pending : snapshot.pending <;> cases parked : snapshot.parked <;>
    simp_all [quiescent]

/-- Validity reads every authored equation origin in the retained trace. -/
def TraceValid (equation : EquationOrigin → Node → Node → Prop) :
    Node → List (EquationOrigin × Node) → Node → Prop
  | source, [], target => source = target
  | source, edge :: rest, target =>
      equation edge.1 source edge.2 ∧ TraceValid equation edge.2 rest target

def Entry.Valid (equation : EquationOrigin → Node → Node → Prop)
    (source : Node) (entry : Entry Node EquationOrigin) : Prop :=
  TraceValid equation source entry.conversions entry.state

theorem trace_append (equation : EquationOrigin → Node → Node → Prop)
    (source middle target : Node) (first second : List (EquationOrigin × Node))
    (before : TraceValid equation source first middle)
    (after : TraceValid equation middle second target) :
    TraceValid equation source (first ++ second) target := by
  induction first generalizing source with
  | nil => simpa only [TraceValid, List.nil_append] using before ▸ after
  | cons edge rest ih => exact ⟨before.1, ih edge.2 before.2⟩

theorem Entry.valid_extend (equation : EquationOrigin → Node → Node → Prop)
    (source : Node) (entry : Entry Node EquationOrigin) (edge : EquationOrigin × Node)
    (before : entry.Valid equation source) (next : equation edge.1 entry.state edge.2) :
    (entry.extend edge).Valid equation source := by
  exact trace_append equation source entry.state edge.2 entry.conversions [edge]
    before ⟨next, rfl⟩

theorem TraceValid.equivalent (equation : EquationOrigin → Node → Node → Prop)
    (source target : Node) (trace : List (EquationOrigin × Node))
    (valid : TraceValid equation source trace target) :
    Relation.EqvGen (fun left right => ∃ origin, equation origin left right) source target := by
  induction trace generalizing source with
  | nil => exact valid ▸ .refl source
  | cons edge rest ih =>
    exact .trans source edge.2 target (.rel source edge.2 ⟨edge.1, valid.1⟩)
      (ih edge.2 valid.2)

def Receipt.Valid (equation : EquationOrigin → Node → Node → Prop)
    (firing : Node → Occurrence → Node → Prop) (source : Node)
    (receipt : Receipt Node EquationOrigin Occurrence) : Prop :=
  receipt.representative.Valid equation source ∧
    firing receipt.representative.state receipt.origin receipt.target

/-- The invariant covers pending work and saved equation histories as well as
emitted primitive receipts. -/
structure Snapshot.Valid (equation : EquationOrigin → Node → Node → Prop)
    (firing : Node → Occurrence → Node → Prop) (source : Node)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) : Prop where
  pending : ∀ entry ∈ snapshot.pending, entry.Valid equation source
  visited : ∀ entry ∈ snapshot.visited, entry.Valid equation source
  conversions : ∀ entry ∈ snapshot.conversions, entry.Valid equation source
  receipts : ∀ receipt ∈ snapshot.receipts, receipt.Valid equation firing source
  parked : ∀ entry ∈ snapshot.parked, entry.representative.Valid equation source

theorem initial_valid (equation : EquationOrigin → Node → Node → Prop)
    (firing : Node → Occurrence → Node → Prop) (source : Node) :
    (initial source : Snapshot Node EquationOrigin Occurrence Obligation).Valid
      equation firing source := by
  constructor
  · intro entry member
    simp only [initial, List.mem_singleton] at member
    subst entry
    rfl
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]

theorem discoveries_valid (equation : EquationOrigin → Node → Node → Prop)
    (source : Node) (entry : Entry Node EquationOrigin)
    (answers : List (EquationOrigin × Node)) (before : entry.Valid equation source)
    (sound : ∀ answer ∈ answers, equation answer.1 entry.state answer.2) :
    ∀ next ∈ discoveries entry answers, next.Valid equation source := by
  intro next member
  obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp member
  exact entry.valid_extend equation source edge before (sound edge edgeMember)

theorem readouts_valid (equation : EquationOrigin → Node → Node → Prop)
    (firing : Node → Occurrence → Node → Prop) (source : Node)
    (entry : Entry Node EquationOrigin) (answers : List (Occurrence × Node))
    (before : entry.Valid equation source)
    (sound : ∀ answer ∈ answers, firing entry.state answer.1 answer.2) :
    ∀ receipt ∈ readouts entry answers, receipt.Valid equation firing source := by
  intro receipt member
  obtain ⟨⟨⟨origin, target⟩, index⟩, selected, rfl⟩ := List.mem_map.mp member
  exact ⟨before, sound (origin, target) (List.fst_mem_of_mem_zipIdx selected)⟩

theorem obligations_valid (equation : EquationOrigin → Node → Node → Prop)
    (source : Node) (entry : Entry Node EquationOrigin) (phase : Phase)
    (reasons : List Obligation) (before : entry.Valid equation source) :
    ∀ parked ∈ obligations entry phase reasons,
      parked.representative.Valid equation source := by
  intro parked member
  obtain ⟨reason, _, rfl⟩ := List.mem_map.mp member
  exact before

/-- Partial answers are sound without assuming that their enumerators are
exhaustive. The same invariant retains the blocked obligations. -/
theorem tick_valid [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation)
    (equation : EquationOrigin → Node → Node → Prop)
    (firing : Node → Occurrence → Node → Prop)
    (equations_sound : ∀ node edge, edge ∈ (model.equations node).answers →
      equation edge.1 node edge.2)
    (firings_sound : ∀ node answer, answer ∈ (model.firings node).answers →
      firing node answer.1 answer.2)
    (source : Node) (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (before : snapshot.Valid equation firing source) :
    (tick model snapshot).Valid equation firing source := by
  cases pending : snapshot.pending with
  | nil => simpa [tick, pending] using before
  | cons entry rest =>
    have entryValid := before.pending entry (by simp [pending])
    have restValid : ∀ next ∈ rest, next.Valid equation source := by
      intro next member
      exact before.pending next (by simp [pending, member])
    by_cases seen : entry.state ∈ snapshot.visited.map Entry.state
    · simp only [tick, pending, seen, if_true]
      exact ⟨restValid, before.visited, before.conversions, before.receipts, before.parked⟩
    · simp only [tick, pending, seen, if_false]
      have nextValid := discoveries_valid equation source entry
        (model.equations entry.state).answers entryValid (equations_sound entry.state)
      constructor
      · intro next member
        rcases List.mem_append.mp member with old | fresh
        · exact restValid next old
        · exact nextValid next (List.mem_filter.mp fresh).1
      · intro next member
        rcases List.mem_append.mp member with old | fresh
        · exact before.visited next old
        · have equal := List.mem_singleton.mp fresh
          subst next
          exact entryValid
      · intro next member
        rcases List.mem_append.mp member with old | fresh
        · exact before.conversions next old
        · exact nextValid next fresh
      · intro receipt member
        rcases List.mem_append.mp member with old | fresh
        · exact before.receipts receipt old
        · exact readouts_valid equation firing source entry
            (model.firings entry.state).answers entryValid (firings_sound entry.state)
            receipt fresh
      · intro parked member
        rcases List.mem_append.mp member with old | fresh
        · exact before.parked parked old
        · rcases List.mem_append.mp fresh with eqPending | firePending
          · exact obligations_valid equation source entry .equation
              (model.equations entry.state).unresolved entryValid parked eqPending
          · exact obligations_valid equation source entry .firing
              (model.firings entry.state).unresolved entryValid parked firePending

theorem run_valid [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation)
    (equation : EquationOrigin → Node → Node → Prop)
    (firing : Node → Occurrence → Node → Prop)
    (equations_sound : ∀ node edge, edge ∈ (model.equations node).answers →
      equation edge.1 node edge.2)
    (firings_sound : ∀ node answer, answer ∈ (model.firings node).answers →
      firing node answer.1 answer.2)
    (source : Node) (fuel : Nat)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (before : snapshot.Valid equation firing source) :
    (run model fuel snapshot).Valid equation firing source := by
  induction fuel generalizing snapshot with
  | zero => exact before
  | succ fuel ih =>
    exact ih (tick model snapshot)
      (tick_valid model equation firing equations_sound firings_sound source snapshot before)

/-- Every returned receipt supplies a conversion to its actual representative
and the independent primitive firing there. -/
theorem emitted_sound [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation)
    (equation : EquationOrigin → Node → Node → Prop)
    (firing : Node → Occurrence → Node → Prop)
    (equations_sound : ∀ node edge, edge ∈ (model.equations node).answers →
      equation edge.1 node edge.2)
    (firings_sound : ∀ node answer, answer ∈ (model.firings node).answers →
      firing node answer.1 answer.2)
    (source : Node) (fuel : Nat) (receipt : Receipt Node EquationOrigin Occurrence)
    (present : receipt ∈ (run model fuel (initial source)).receipts) :
    Relation.EqvGen (fun left right => ∃ origin, equation origin left right)
      source receipt.representative.state ∧
      firing receipt.representative.state receipt.origin receipt.target := by
  have sound := (run_valid model equation firing equations_sound firings_sound source
    fuel (initial source) (initial_valid equation firing source)).receipts receipt present
  exact ⟨TraceValid.equivalent equation source receipt.representative.state
    receipt.representative.conversions sound.1, sound.2⟩

end Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier
