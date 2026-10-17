import Mettapedia.GSLT.Core.InferenceRecordingPrefix
import Mettapedia.Machines.TraceObservationBoundary
import Mettapedia.Machines.VariableInventory
import Mettapedia.Machines.RevisionedOccurrenceStore
import Mettapedia.GSLT.Core.OpenTotalityObservation
import Mettapedia.Algorithms.WellFoundedServices.DependencyAnalysis
import Mettapedia.Machines.OccurrenceMachine
import Mettapedia.Machines.ResumableRegion
import Mettapedia.GSLT.Causality.OccurrenceMachineHistory

/-!
# Owned execution history readouts

Native call/return ports project to the existing bounded recording prefix and
causal receipt. Recording positions distinguish equal answer occurrences;
producer links distinguish one producer's several uses from separate producers.
The readout does not supply replay authority or observe a foreign callback's
interior. Payload transport and recording completeness are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ExecutionHistoryReadout

open Mettapedia.GSLT.Core.InferenceControl.Recording

inductive Kind where
  | call | returned | alternative | redo | fault | suspend | resume | cancel
  | answer | external | complete | use
  deriving DecidableEq, Repr

structure Event (Payload : Type*) where
  ordinal : Nat
  kind : Kind
  producer : Option Nat
  payload : Option Payload
  deriving DecidableEq, Repr

variable {Payload NextPayload : Type*}

/-- Only published answer ports enter this ordered projection. A missing
answer payload refuses the projection rather than silently deleting it. -/
def answers : List (Event Payload) → Option (List Payload)
  | [] => some []
  | event :: rest => do
      let first ← if event.kind = .answer then event.payload.map List.singleton else some []
      let remaining ← answers rest
      pure (first ++ remaining)

theorem answers_append (first second : List (Event Payload)) :
    answers (first ++ second) = (do
      let left ← answers first
      let right ← answers second
      pure (left ++ right)) := by
  induction first with
  | nil => simp [answers]
  | cons event rest ih =>
      by_cases isAnswer : event.kind = .answer
      · cases available : event.payload <;>
          simp [answers, isAnswer, available, ih, Option.bind_assoc, List.append_assoc]
      · simp [answers, isAnswer, ih]

def answerEvents (first producer : Nat) : List Payload → List (Event Payload)
  | [] => []
  | value :: rest =>
      ⟨first, .answer, some producer, some value⟩ :: answerEvents (first + 1) producer rest

@[simp] theorem answerEvents_length (first producer : Nat) (values : List Payload) :
    (answerEvents first producer values).length = values.length := by
  induction values generalizing first <;> simp_all [answerEvents]

@[simp] theorem answers_answerEvents (first producer : Nat) (values : List Payload) :
    answers (answerEvents first producer values) = some values := by
  induction values generalizing first <;> simp_all [answerEvents, answers, List.singleton]

theorem answerEvents_append (first producer : Nat) (before after : List Payload) :
    answerEvents first producer (before ++ after) =
      answerEvents first producer before ++
        answerEvents (first + before.length) producer after := by
  induction before generalizing first with
  | nil => simp [answerEvents]
  | cons value rest ih =>
      simp [answerEvents, ih, Nat.add_comm, Nat.add_left_comm]

theorem answerEvents_ordinal_bounds (first producer : Nat) (values : List Payload)
    (event : Event Payload) (member : event ∈ answerEvents first producer values) :
    first ≤ event.ordinal ∧ event.ordinal < first + values.length := by
  induction values generalizing first with
  | nil => simp [answerEvents] at member
  | cons value rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst event
        simp [List.length_cons]
      · have bounds := ih (first + 1) later
        simp only [List.length_cons]
        omega

/-- Earlier and later delivery batches have disjoint, strictly ordered
occurrence ordinals, even when all their payload values are equal. -/
theorem answerEvents_append_ordinals (first producer : Nat) (before after : List Payload)
    (old fresh : Event Payload) (oldMember : old ∈ answerEvents first producer before)
    (freshMember : fresh ∈ answerEvents (first + before.length) producer after) :
    old.ordinal < fresh.ordinal :=
  (answerEvents_ordinal_bounds first producer before old oldMember).2.trans_le
    (answerEvents_ordinal_bounds (first + before.length) producer after fresh freshMember).1

theorem answers_no_answer_ports (events : List (Event Payload))
    (ports : ∀ event ∈ events, event.kind ≠ .answer) : answers events = some [] := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      have head := ports event (by simp)
      have tail : ∀ item ∈ rest, item.kind ≠ .answer := by
        intro item member
        exact ports item (by simp [member])
      simp [answers, head, ih tail]

def completeAnswers (record : Prefix (Event Payload)) : Option (List Payload) :=
  record.complete?.bind answers

/-- The actual publication loop's ordered bag is recovered when the entire
declared prefix fits. Calls, returns and completion ports surrounding it may
remain in the history; they do not become extra answers. -/
theorem publication_readout (capacity first producer : Nat)
    (before after : List (Event Payload)) (values : List Payload)
    (beforePorts : ∀ event ∈ before, event.kind ≠ .answer)
    (afterPorts : ∀ event ∈ after, event.kind ≠ .answer)
    (fits : (before ++ answerEvents first producer values ++ after).length ≤ capacity) :
    completeAnswers ((Prefix.initial capacity).append
      (before ++ answerEvents first producer values ++ after)) = some values := by
  have full := (Prefix.complete_iff capacity
    (before ++ answerEvents first producer values ++ after)).2 fits
  unfold completeAnswers
  rw [full]
  simp [answers_append, answers_no_answer_ports before beforePorts,
    answers_no_answer_ports after afterPorts]

theorem truncated_readout_refused (capacity : Nat) (events : List (Event Payload))
    (tooMany : capacity < events.length) :
    completeAnswers ((Prefix.initial capacity).append events) = none := by
  have omitted : events.length - capacity ≠ 0 := by omega
  simp [completeAnswers, Prefix.complete?, Prefix.initial_omitted, omitted]

/-- Resumption appends to the retained prefix, retaining its capacity and
omissions. It cannot create a fresh complete recording of an earlier run. -/
theorem resumption_readout (record : Prefix (Event Payload))
    (before after : List (Event Payload)) :
    completeAnswers ((record.append before).append after) =
      completeAnswers (record.append (before ++ after)) := by
  rw [Prefix.append_append]

def mapPayload (mapping : Payload → NextPayload) (event : Event Payload) : Event NextPayload :=
  ⟨event.ordinal, event.kind, event.producer, event.payload.map mapping⟩

theorem answers_transport (mapping : Payload → NextPayload) (events : List (Event Payload)) :
    answers (events.map (mapPayload mapping)) = (answers events).map (List.map mapping) := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      by_cases isAnswer : event.kind = .answer
      · cases available : event.payload <;> cases tail : answers rest <;>
          simp [answers, mapPayload, isAnswer, available, ih, tail, List.singleton]
      · simp [answers, mapPayload, isAnswer, ih]

theorem complete_answers_transport (mapping : Payload → NextPayload)
    (record : Prefix (Event Payload)) :
    completeAnswers (record.map (mapPayload mapping)) =
      (completeAnswers record).map (List.map mapping) := by
  unfold completeAnswers
  rw [Prefix.complete?_map]
  cases available : record.complete? <;> simp [answers_transport]

/-- Equal values have unequal recording positions. Erasing one of them is a
loss of observation, despite equality of the remaining semantic value. -/
theorem equal_answers_keep_positions (first producer : Nat) (value : Payload) :
    (answerEvents first producer [value, value]).map Event.ordinal = [first, first + 1] ∧
      answers (answerEvents first producer [value, value]) = some [value, value] := by
  simp [answerEvents, answers, List.singleton]

theorem deleting_equal_answer_changes_readout (first producer : Nat) (value : Payload) :
    answers (answerEvents first producer [value, value]) ≠
      answers (answerEvents first producer [value]) := by
  simp only [answers_answerEvents, ne_eq, Option.some.injEq]
  intro equal
  have lengths := congrArg List.length equal
  simp at lengths

/-! ## Retained publication delivery

The existing captured-store cursor can retain an append-only publication's
previously delivered snapshot. Its read token names one publication lineage:
the revision here is a fixed generation, not a counter incremented on append.
Every advance checks both that token and the entire prior content prefix.

These laws concern ordered delivery occurrences. A caller must exclusively
thread the returned cursor and commit delivery together with its updated cursor.
Copying an old cursor permits delivery again; the pure token grants no linear
authority, cancellation protocol, durable transaction or external exactly-once
guarantee. Those are ownership and service obligations, not list properties.
-/

namespace Publication

open Mettapedia.Machines

variable {StreamId Entry : Type}

abbrev Cursor (StreamId Entry : Type) := OwnedFork.Cursor StreamId Entry

def initial (lineage : StoreReadToken StreamId Nat) : Cursor StreamId Entry :=
  ⟨⟨lineage.storeId, lineage.revision, []⟩, 0⟩

/-- Only a cursor parked at the end of its complete delivered snapshot may
advance to another snapshot in this same append-only publication lineage. -/
def Compatible (cursor : Cursor StreamId Entry)
    (publication : RevisionedStoreView StreamId Nat Entry) : Prop :=
  cursor.next = cursor.captured.entries.length ∧
    cursor.captured.readToken = publication.readToken ∧
    cursor.captured.entries.IsPrefix publication.entries

instance [DecidableEq StreamId] [DecidableEq Entry]
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry) :
    Decidable (Compatible cursor publication) := by
  unfold Compatible
  infer_instance

/-- Reuse the retained cursor and answer-port encoding. Refusal retains the
complete original cursor; success installs the current snapshot and delivers
only its previously uncommitted suffix, with absolute occurrence ordinals. -/
def advance [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry) :
    Cursor StreamId Entry × Option (List (Event Entry)) :=
  if Compatible cursor publication then
    (⟨publication, publication.entries.length⟩,
      some (answerEvents cursor.next producer (publication.entries.drop cursor.next)))
  else (cursor, none)

/-- A publication list from the same retained run keeps its fixed lineage.
Cross-run adapters must instead use `advance` with the actual current token. -/
def advanceValues [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (values : List Entry) :
    Cursor StreamId Entry × Option (List (Event Entry)) :=
  advance producer cursor { cursor.captured with entries := values }

theorem advance_accepted [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (compatible : Compatible cursor publication) :
    advance producer cursor publication =
      (⟨publication, publication.entries.length⟩,
        some (answerEvents cursor.next producer (publication.entries.drop cursor.next))) := by
  simp [advance, compatible]

theorem advance_refused [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (incompatible : ¬ Compatible cursor publication) :
    advance producer cursor publication = (cursor, none) := by
  simp [advance, incompatible]

/-- Acceptance recovers the old publication plus exactly the newly delivered
payload suffix. Equal values at distinct positions remain separate entries. -/
theorem advance_readout [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (compatible : Compatible cursor publication) :
    (advance producer cursor publication).2.bind answers =
      some (publication.entries.drop cursor.next) ∧
    cursor.captured.entries ++ publication.entries.drop cursor.next = publication.entries := by
  rw [advance_accepted producer cursor publication compatible]
  refine ⟨by simp, ?_⟩
  rw [compatible.1]
  exact (List.prefix_append_drop compatible.2.2).symm

theorem advance_replay [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (publication : RevisionedStoreView StreamId Nat Entry) :
    advance producer ⟨publication, publication.entries.length⟩ publication =
      (⟨publication, publication.entries.length⟩, some []) := by
  simp [advance, Compatible, answerEvents]

theorem advance_initial [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (publication : RevisionedStoreView StreamId Nat Entry) :
    advance producer (initial publication.readToken) publication =
      (⟨publication, publication.entries.length⟩,
        some (answerEvents 0 producer publication.entries)) := by
  simp [advance, Compatible, initial, RevisionedStoreView.readToken]

theorem advanceValues_accepted [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (values : List Entry)
    (consumed : cursor.next = cursor.captured.entries.length)
    (grows : cursor.captured.entries.IsPrefix values) :
    advanceValues producer cursor values =
      (⟨{ cursor.captured with entries := values }, values.length⟩,
        some (answerEvents cursor.next producer (values.drop cursor.next))) := by
  apply advance_accepted
  exact ⟨consumed, rfl, grows⟩

/-- Reusing the actual returned cursor against the same publication emits
no occurrences. This premise does not cover a copied earlier cursor. -/
theorem advance_retained_replay [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (compatible : Compatible cursor publication) :
    advance producer (advance producer cursor publication).1 publication =
      ((advance producer cursor publication).1, some []) := by
  rw [advance_accepted producer cursor publication compatible]
  exact advance_replay producer publication

/-- Newly returned event ordinals begin at the old cursor and stop before
the end of the current publication. -/
theorem advance_ordinal_bounds [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (compatible : Compatible cursor publication) (events : List (Event Entry))
    (delivered : (advance producer cursor publication).2 = some events)
    (event : Event Entry) (member : event ∈ events) :
    cursor.next ≤ event.ordinal ∧ event.ordinal < publication.entries.length := by
  rw [advance_accepted producer cursor publication compatible] at delivered
  have same := Option.some.inj delivered
  subst events
  have bounds := answerEvents_ordinal_bounds cursor.next producer
    (publication.entries.drop cursor.next) event member
  have priorLength : cursor.next ≤ publication.entries.length := by
    rw [compatible.1]
    exact compatible.2.2.length_le
  simpa [List.length_drop, Nat.add_sub_of_le priorLength] using bounds

theorem advance_extension [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (more : List Entry)
    (consumed : cursor.next = cursor.captured.entries.length) :
    advanceValues producer cursor (cursor.captured.entries ++ more) =
      (⟨{ cursor.captured with entries := cursor.captured.entries ++ more },
        cursor.captured.entries.length + more.length⟩,
        some (answerEvents cursor.next producer more)) := by
  simp [advanceValues, advance, Compatible, consumed, RevisionedStoreView.readToken]

/-- Splitting append-only publication across a pause changes neither the
final retained cursor nor the complete delivered occurrence list. -/
theorem advanceValues_partition [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (first second : List Entry)
    (consumed : cursor.next = cursor.captured.entries.length) :
    let earlier := advanceValues producer cursor (cursor.captured.entries ++ first)
    let later := advanceValues producer earlier.1
      (cursor.captured.entries ++ first ++ second)
    let together := advanceValues producer cursor
      (cursor.captured.entries ++ (first ++ second))
    later.1 = together.1 ∧
      earlier.2.bind (fun before => later.2.map (before ++ ·)) = together.2 := by
  dsimp only
  rw [advance_extension producer cursor first consumed,
    advance_extension producer cursor (first ++ second) consumed]
  dsimp only
  rw [advance_extension producer _ second (by simp)]
  dsimp only
  constructor
  · simp [List.append_assoc, Nat.add_assoc]
  · simp only [Option.bind_some, Option.map_some, Option.some.injEq]
    simpa [consumed] using (answerEvents_append cursor.next producer first second).symm

/-- Deliver at most `limit` newly visible occurrences. Validate the actual
publication before taking its suffix, then reuse the existing cursor advance
on exactly the delivered prefix. Unselected entries remain in the publication;
the cursor never pretends they were consumed. -/
def advanceBounded [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (limit : Nat) : Cursor StreamId Entry × Option (List (Event Entry)) :=
  if Compatible cursor publication then
    advanceValues producer cursor
      (cursor.captured.entries ++ (publication.entries.drop cursor.next).take limit)
  else (cursor, none)

theorem advanceBounded_accepted [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (limit : Nat) (compatible : Compatible cursor publication) :
    advanceBounded producer cursor publication limit =
      (⟨{ cursor.captured with entries :=
          cursor.captured.entries ++ (publication.entries.drop cursor.next).take limit },
        cursor.next + ((publication.entries.drop cursor.next).take limit).length⟩,
       some (answerEvents cursor.next producer ((publication.entries.drop cursor.next).take limit))) := by
  rw [advanceBounded, if_pos compatible,
    advance_extension producer cursor _ compatible.1, ← compatible.1]

theorem advanceBounded_refused [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (limit : Nat) (incompatible : ¬ Compatible cursor publication) :
    advanceBounded producer cursor publication limit = (cursor, none) := by
  simp only [advanceBounded, if_neg incompatible]

/-- A zero delivery allowance preserves the whole cursor, even when new
answers are available. This concerns delivery, not a producer work budget. -/
theorem advanceBounded_zero [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (compatible : Compatible cursor publication) :
    advanceBounded producer cursor publication 0 = (cursor, some []) := by
  rw [advanceBounded_accepted producer cursor publication 0 compatible]
  cases cursor
  simp only [List.take_zero, List.append_nil, List.length_nil, Nat.add_zero,
    answerEvents]

theorem advanceBounded_readout [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (limit : Nat) (compatible : Compatible cursor publication) :
    (advanceBounded producer cursor publication limit).2.bind answers =
      some ((publication.entries.drop cursor.next).take limit) := by
  rw [advanceBounded_accepted producer cursor publication limit compatible]
  simp only [Option.bind_some, answers_answerEvents]

theorem advanceBounded_count [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (limit : Nat) (compatible : Compatible cursor publication) :
    ((advanceBounded producer cursor publication limit).1).next =
      cursor.next + min limit (publication.entries.length - cursor.next) := by
  rw [advanceBounded_accepted producer cursor publication limit compatible]
  simp only [List.length_take, List.length_drop]

/-- The retained delivered prefix is an actual prefix of the validated
publication. No fabricated or skipped entry is installed in the cursor. -/
theorem advanceBounded_prefix [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (limit : Nat) (compatible : Compatible cursor publication) :
    ((advanceBounded producer cursor publication limit).1).captured.entries <+:
      publication.entries := by
  rw [advanceBounded_accepted producer cursor publication limit compatible]
  obtain ⟨remaining, retained⟩ := compatible.2.2
  dsimp only
  rw [← retained, compatible.1, List.drop_left]
  exact List.prefix_append_right_inj _ |>.mpr (List.take_prefix limit remaining)

/-- The updated cursor stays parked at the end of exactly its delivered
snapshot and can consume the remaining suffix of the same publication. -/
theorem advanceBounded_compatible [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (limit : Nat) (compatible : Compatible cursor publication) :
    Compatible (advanceBounded producer cursor publication limit).1 publication := by
  have kept := advanceBounded_prefix producer cursor publication limit compatible
  rw [advanceBounded_accepted producer cursor publication limit compatible] at kept ⊢
  exact ⟨by simp only [List.length_append, compatible.1], compatible.2.1, kept⟩

/-- The undelivered suffix follows the requested cut, including when the
allowance exceeds the number of currently published entries. -/
theorem advanceBounded_remaining [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (limit : Nat) (compatible : Compatible cursor publication) :
    publication.entries.drop (advanceBounded producer cursor publication limit).1.next =
      (publication.entries.drop cursor.next).drop limit := by
  rw [advanceBounded_count producer cursor publication limit compatible,
    ← List.drop_drop]
  simpa only [List.length_drop] using
    (List.drop_eq_drop_min (l := publication.entries.drop cursor.next) (i := limit)).symm

/-- Against one fixed publication, splitting a delivery allowance preserves
both the final cursor and the ordered events. Producer work may publish more
entries between calls; that case requires its separate readiness contract. -/
theorem advanceBounded_partition [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (first second : Nat) (compatible : Compatible cursor publication) :
    let earlier := advanceBounded producer cursor publication first
    let later := advanceBounded producer earlier.1 publication second
    let together := advanceBounded producer cursor publication (first + second)
    later.1 = together.1 ∧
      earlier.2.bind (fun before => later.2.map (before ++ ·)) = together.2 := by
  dsimp only
  have after := advanceBounded_compatible producer cursor publication first compatible
  have remaining := advanceBounded_remaining producer cursor publication first compatible
  rw [advanceBounded_accepted producer _ publication second after, remaining,
    advanceBounded_accepted producer cursor publication first compatible,
    advanceBounded_accepted producer cursor publication (first + second) compatible]
  dsimp only
  constructor
  · simp only [List.take_add, List.length_append, List.append_assoc, Nat.add_assoc]
  · simp only [Option.bind_some, Option.map_some, Option.some.injEq, List.take_add]
    exact (answerEvents_append cursor.next producer
      ((publication.entries.drop cursor.next).take first)
      (((publication.entries.drop cursor.next).drop first).take second)).symm

/-- A different publication lineage is refused before selection, including
when no answer has been requested. A delivery bound grants no transport. -/
theorem advanceBounded_foreign_refused [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (limit : Nat) (foreign : cursor.captured.readToken ≠ publication.readToken) :
    advanceBounded producer cursor publication limit = (cursor, none) :=
  advanceBounded_refused producer cursor publication limit (fun compatible => foreign compatible.2.1)

/-- An accepted prefix growth supplies the same suffix used by the existing
captured-store cursor's ordered enumeration. -/
theorem advance_cursor_read [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (compatible : Compatible cursor publication) :
    (advance producer cursor publication).2.bind answers =
      some ((OwnedFork.Cursor.mk publication cursor.next).read publication.entries.length) := by
  rw [OwnedFork.cursor_prefix, (advance_readout producer cursor publication compatible).1]
  simp

theorem advance_changed_prefix [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (changed : ¬ cursor.captured.entries.IsPrefix publication.entries) :
    advance producer cursor publication = (cursor, none) :=
  advance_refused producer cursor publication (fun valid => changed valid.2.2)

theorem advance_stale_lineage [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (stale : cursor.captured.readToken ≠ publication.readToken) :
    advance producer cursor publication = (cursor, none) :=
  advance_refused producer cursor publication (fun valid => stale valid.2.1)

theorem advance_shrunken [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (shrunken : publication.entries.length < cursor.captured.entries.length) :
    advance producer cursor publication = (cursor, none) :=
  advance_refused producer cursor publication (fun valid =>
    (Nat.not_le_of_gt shrunken) valid.2.2.length_le)

theorem advance_incomplete_cursor [DecidableEq StreamId] [DecidableEq Entry] (producer : Nat)
    (cursor : Cursor StreamId Entry) (publication : RevisionedStoreView StreamId Nat Entry)
    (incomplete : cursor.next ≠ cursor.captured.entries.length) :
    advance producer cursor publication = (cursor, none) :=
  advance_refused producer cursor publication (fun valid => incomplete valid.1)

namespace Controls

private def duplicatePublication : RevisionedStoreView Nat Nat Nat := ⟨7, 3, [42, 42]⟩

theorem duplicate_values_have_separate_delivery_positions :
    (advance 9 (initial duplicatePublication.readToken) duplicatePublication).2 =
      some [⟨0, .answer, some 9, some 42⟩, ⟨1, .answer, some 9, some 42⟩] := by
  decide

theorem replay_has_no_new_occurrences :
    (advance 9 (advance 9 (initial duplicatePublication.readToken) duplicatePublication).1
      duplicatePublication).2 = some [] := by
  decide

theorem bounded_duplicate_deliveries_keep_positions :
    let start : Cursor Nat Nat := initial duplicatePublication.readToken
    let first := advanceBounded 9 start duplicatePublication 1
    let second := advanceBounded 9 first.1 duplicatePublication 1
    first.2 = some [⟨0, .answer, some 9, some 42⟩] ∧
      second.2 = some [⟨1, .answer, some 9, some 42⟩] ∧
      (advanceBounded 9 second.1 duplicatePublication 1).2 = some [] := by
  decide

theorem bounded_zero_retains_available_occurrences :
    let start : Cursor Nat Nat := initial duplicatePublication.readToken
    advanceBounded 9 start duplicatePublication 0 = (start, some []) ∧
      (advanceBounded 9 start duplicatePublication 2).2 =
        some [⟨0, .answer, some 9, some 42⟩, ⟨1, .answer, some 9, some 42⟩] := by
  dsimp only
  constructor
  · apply advanceBounded_zero
    simp [Compatible, initial, RevisionedStoreView.readToken]
  · decide

theorem split_duplicate_publication :
    let start : Cursor Nat Nat := initial ⟨7, 3⟩
    let first := advanceValues 9 start [42]
    let second := advanceValues 9 first.1 [42, 42]
    first.2.bind (fun before => second.2.map (before ++ ·)) =
      (advanceValues 9 start [42, 42]).2 := by
  decide

theorem whole_prefix_reemission_changes_delivery :
    (answerEvents 0 9 [42] ++ answerEvents 0 9 [42, 42]) ≠
      answerEvents 0 9 [42, 42] := by
  decide

theorem changed_prefix_of_same_length_is_refused :
    advance 9 (⟨⟨7, 3, [42]⟩, 1⟩ : Cursor Nat Nat) ⟨7, 3, [43]⟩ =
      (⟨⟨7, 3, [42]⟩, 1⟩, none) := by
  exact advance_changed_prefix 9 _ _ (by decide)

theorem stale_generation_is_refused :
    advance 9 (⟨⟨7, 3, [42]⟩, 1⟩ : Cursor Nat Nat) ⟨7, 4, [42, 42]⟩ =
      (⟨⟨7, 3, [42]⟩, 1⟩, none) := by
  exact advance_stale_lineage 9 _ _ (by decide)

theorem copying_old_cursor_permits_repeated_delivery :
    (advance 9 (initial duplicatePublication.readToken) duplicatePublication).2 =
      some (answerEvents 0 9 [42, 42]) ∧
    (advance 9 (initial duplicatePublication.readToken) duplicatePublication).2 ≠ some [] := by
  decide

end Controls

end Publication

/-! Producer causality uses the existing receipt identities, not payload
identity. The following is the owned producer/delivery component: one Call
occurrence can support arbitrarily many separate Use occurrences. -/

def useEvents (first producer : Nat) : Nat → List (CausalEvent Nat)
  | 0 => []
  | count + 1 => ⟨first, [producer]⟩ :: useEvents (first + 1) producer count

private theorem uses_ordered (available : List Nat) (first producer count : Nat)
    (earlier : ∀ value ∈ available, value < first) (live : producer ∈ available) :
    CausalReceipt.Ordered available (useEvents first producer count) := by
  induction count generalizing first available with
  | zero => trivial
  | succ count ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro present
        exact Nat.lt_irrefl first (earlier first present)
      · intro cause depends
        simpa only [List.mem_singleton.mp depends] using live
      · apply ih (available ++ [first]) (first + 1)
        · intro value member
          rcases List.mem_append.mp member with old | added
          · exact (earlier value old).trans (by omega)
          · have same := List.mem_singleton.mp added
            omega
        · exact List.mem_append_left _ live

def producerReceipt (count : Nat) : CausalReceipt Nat where
  roots := (useEvents 2 1 count).map CausalEvent.event
  events := ⟨1, []⟩ :: useEvents 2 1 count

theorem producer_receipt_wellFormed (count : Nat) :
    CausalReceipt.WellFormed [] (producerReceipt count) := by
  refine ⟨by simp, ?_, ?_⟩
  · refine ⟨by simp, by simp, ?_⟩
    exact uses_ordered [1] 2 1 count (by simp) (by simp)
  · intro root present
    simpa [producerReceipt, CausalReceipt.known, CausalReceipt.flattenedSupport] using
      List.mem_cons_of_mem 1 present

theorem producer_receipt_check (count : Nat) :
    CausalReceipt.check [] (producerReceipt count) = true :=
  (CausalReceipt.check_iff [] _).2 (producer_receipt_wellFormed count)

theorem producer_receipt_acyclic (count event : Nat) :
    ¬ Relation.TransGen (producerReceipt count).Direct event event :=
  CausalReceipt.no_causal_cycle [] _ (producer_receipt_wellFormed count) event

theorem two_uses_remain_distinct :
    (producerReceipt 2).flattenedSupport = [1, 2, 3] := by decide

theorem lost_use_changes_receipt :
    (producerReceipt 2).flattenedSupport ≠ (producerReceipt 1).flattenedSupport := by decide

theorem forward_producer_is_refused :
    CausalReceipt.check [] (⟨[2], [⟨1, []⟩, ⟨2, [3]⟩]⟩ : CausalReceipt Nat) = false := by decide

/-! A complete ancestry readout uses the same bounded prefix. Captured
boundary references remain explicit, and omitted events refuse a claim about
the complete represented ancestry. This does not authenticate native edges. -/

variable {Occurrence : Type*}

def completeAncestors [DecidableEq Occurrence] (record : Prefix (CausalEvent Occurrence))
    (boundary roots : List Occurrence) (identity : Occurrence) : Option (List Occurrence) :=
  (record.graph? boundary roots).bind fun receipt => receipt.ancestors? boundary identity

/-- Recording that fits yields the same ancestry as the checked receipt,
including its original captured boundary and selected occurrence. -/
theorem recorded_ancestry [DecidableEq Occurrence] (receipt : CausalReceipt Occurrence)
    (capacity : Nat) (boundary : List Occurrence) (identity : Occurrence)
    (fits : receipt.events.length ≤ capacity) :
    completeAncestors ((Prefix.initial capacity).append receipt.events)
      boundary receipt.roots identity = receipt.ancestors? boundary identity := by
  have full := (Prefix.complete_iff capacity receipt.events).2 fits
  unfold completeAncestors Prefix.graph?
  rw [full]
  change (if receipt.check boundary then some receipt else none).bind
    (fun checked => checked.ancestors? boundary identity) = receipt.ancestors? boundary identity
  cases checked : receipt.check boundary <;> simp [checked, CausalReceipt.ancestors?]

/-- A bounded recording cannot turn a missing suffix into a complete
ancestry certificate, even if the selected node lies in the retained prefix. -/
theorem truncated_ancestry_refused [DecidableEq Occurrence]
    (capacity : Nat) (events : List (CausalEvent Occurrence))
    (boundary roots : List Occurrence) (identity : Occurrence)
    (tooMany : capacity < events.length) :
    completeAncestors ((Prefix.initial capacity).append events) boundary roots identity = none := by
  have omitted : ((Prefix.initial capacity).append events).omitted ≠ 0 := by
    rw [Prefix.initial_omitted]
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt tooMany)
  unfold completeAncestors
  rw [Prefix.graph?_truncated boundary roots _ omitted]
  rfl

theorem ancestry_resumption [DecidableEq Occurrence] (record : Prefix (CausalEvent Occurrence))
    (before after : List (CausalEvent Occurrence))
    (boundary roots : List Occurrence) (identity : Occurrence) :
    completeAncestors ((record.append before).append after) boundary roots identity =
      completeAncestors (record.append (before ++ after)) boundary roots identity := by
  rw [Prefix.append_append]

/-- An accepted ancestry readout carries the existing complete graph
certificate and the exact retained causal relation. Native event authenticity
remains an independent obligation. -/
theorem complete_ancestry_sound [DecidableEq Occurrence]
    (record : Prefix (CausalEvent Occurrence)) (boundary roots : List Occurrence)
    (identity : Occurrence) (result : List Occurrence)
    (reported : completeAncestors record boundary roots identity = some result) :
    ∃ receipt : CausalReceipt Occurrence,
      record.complete? = some receipt.events ∧ receipt.roots = roots ∧
      receipt.WellFormed boundary ∧ identity ∈ receipt.known boundary ∧
      ∀ cause, cause ∈ result ↔
        cause = identity ∨ Relation.TransGen receipt.Direct cause identity := by
  obtain ⟨receipt, graphRead, ancestryRead⟩ := Option.bind_eq_some_iff.mp reported
  obtain ⟨complete, _, sameRoots⟩ := Prefix.graph?_sound boundary roots record receipt graphRead
  obtain ⟨valid, known, exactCauses⟩ :=
    CausalReceipt.ancestors?_exact boundary receipt identity result ancestryRead
  exact ⟨receipt, complete, sameRoots, valid, known, exactCauses⟩

/-- A complete retained graph supports both distinct uses of one producer. -/
theorem complete_producer_ancestry :
    completeAncestors ((Prefix.initial 3).append (producerReceipt 2).events) [] [2, 3] 2 =
      some [2, 1] ∧
    completeAncestors ((Prefix.initial 3).append (producerReceipt 2).events) [] [2, 3] 3 =
      some [3, 1] := by decide

/-- Recording only the producer and its first use does not justify a complete
explanation of either use in the three-occurrence history. -/
theorem truncated_producer_ancestry :
    completeAncestors ((Prefix.initial 2).append (producerReceipt 2).events) [] [2, 3] 2 = none ∧
    completeAncestors ((Prefix.initial 2).append (producerReceipt 2).events) [] [2, 3] 3 = none := by
  decide

namespace Candidate

variable {Key Revision Reason : Type*}

/-- Admission is not completion. A pending decision cannot license rejection
or closure; a rejected decision retains its particular explanation. -/
inductive Decision (Reason : Type*) where
  | admitted
  | pending
  | rejected (reason : Reason)
  deriving DecidableEq, Repr

/-- Candidate keys identify occurrences, not equal printed payloads. The
linear inventory oracle is read newest-first for this observation. -/
def latest [DecidableEq Key] (events : List (Key × Decision Reason)) (key : Key) :
    Option (Decision Reason) :=
  (VariableInventory.scan events.reverse key).map Prod.snd

@[simp] theorem latest_none_iff [DecidableEq Key]
    (events : List (Key × Decision Reason)) (key : Key) :
    latest events key = none ↔ key ∉ events.map Prod.fst := by
  simp [latest, VariableInventory.scan_none_iff, List.map_reverse]

/-- A later decision supersedes the earlier decision for that same occurrence.
It does not change any other occurrence's latest decision. -/
theorem latest_append [DecidableEq Key]
    (before after : List (Key × Decision Reason)) (key : Key) :
    latest (before ++ after) key = (latest after key).or (latest before key) := by
  simp only [latest, List.reverse_append, VariableInventory.scan_append]
  cases VariableInventory.scan after.reverse key <;>
    cases VariableInventory.scan before.reverse key <;> rfl

@[simp] theorem latest_new [DecidableEq Key]
    (events : List (Key × Decision Reason)) (key : Key) (decision : Decision Reason) :
    latest (events ++ [(key, decision)]) key = some decision := by
  rw [latest_append]
  simp [latest, VariableInventory.scan_cons]

theorem latest_other [DecidableEq Key]
    (events : List (Key × Decision Reason)) (key other : Key)
    (decision : Decision Reason) (different : other ≠ key) :
    latest (events ++ [(other, decision)]) key = latest events key := by
  rw [latest_append]
  simp [latest, different, VariableInventory.scan]

/-- Renaming occurrence identities preserves the latest verdict exactly.
The mapping cannot collapse separate candidates into one occurrence. -/
theorem latest_transport {NextKey : Type*} [DecidableEq Key] [DecidableEq NextKey]
    (mapping : Key → NextKey) (faithful : Function.Injective mapping)
    (events : List (Key × Decision Reason)) (key : Key) :
    latest (events.map (fun entry => (mapping entry.1, entry.2))) (mapping key) =
      latest events key := by
  unfold latest
  rw [← List.map_reverse]
  have lookup := VariableInventory.scan_transport mapping faithful
    (fun decision : Decision Reason => decision) events.reverse key
  rw [lookup]
  cases VariableInventory.scan events.reverse key <;> rfl

/-- Latest recorded decision on the interval retained by `Prefix.complete?`.
`none` means a suffix was omitted, so the retained items are historical and
this is not a latest decision. `some none` means this complete interval
records no decision for the key. That is not `Decision.rejected`, and it says
nothing about an earlier unrecorded prefix. `some (some decision)` is the
latest decision recorded in the interval. `explain` reads this result after
its stale-context and inventory guards. `Decision.admitted`,
`Decision.pending`, and `Decision.rejected` are the source readings of
Accepted, Pending, and Rejected in `history:explain`
(`lib/native_history.metta`). The authored consumer is
`tests/prime/need_admission_history.metta`. These theorems do not show that
the native evaluator implements this function, and they do not constrain how
that evaluator treats a code-shaped payload. A certified admission is not
current execution authority. `CausalReceipt.causes?` keeps the same shape for
a causal query: `none` is a missing occurrence and `some []` is a recorded
occurrence with no predecessors. `ancestors?` does not speak for history
before its captured boundary. -/
def coveredLatest [DecidableEq Key] (record : Prefix (Key × Decision Reason)) (key : Key) :
    Option (Option (Decision Reason)) :=
  record.complete?.map (fun events => latest events key)

theorem coveredLatest_omitted [DecidableEq Key] (record : Prefix (Key × Decision Reason))
    (key : Key) (lost : record.omitted ≠ 0) : coveredLatest record key = none := by
  simp [coveredLatest, Prefix.complete?, lost]

theorem coveredLatest_of_complete [DecidableEq Key] (events : List (Key × Decision Reason))
    (capacity : Nat) (key : Key) (fits : events.length ≤ capacity) :
    coveredLatest ((Prefix.initial capacity).append events) key =
      some (latest events key) := by
  rw [coveredLatest, (Prefix.complete_iff capacity events).mpr fits]
  rfl

/-- A complete interval retains its ordered events as `items`, with no
omission, and `coveredLatest` reads `latest` on those events. -/
theorem complete_interval_payload [DecidableEq Key] (events : List (Key × Decision Reason))
    (capacity : Nat) (key : Key) (fits : events.length ≤ capacity) :
    coveredLatest ((Prefix.initial capacity).append events) key =
        some (latest events key) ∧
      ((Prefix.initial capacity).append events).items = events ∧
      ((Prefix.initial capacity).append events).omitted = 0 := by
  refine ⟨coveredLatest_of_complete events capacity key fits, ?_, ?_⟩
  · rw [Prefix.initial_items, List.take_of_length_le fits]
  · rw [Prefix.initial_omitted, Nat.sub_eq_zero_of_le fits]

theorem covered_rejection_keeps_reason [DecidableEq Key] (events : List (Key × Decision Reason))
    (capacity : Nat) (key : Key) (reason : Reason) (fits : events.length ≤ capacity)
    (found : latest events key = some (.rejected reason)) :
    coveredLatest ((Prefix.initial capacity).append events) key =
      some (some (.rejected reason)) := by
  rw [coveredLatest_of_complete events capacity key fits, found]

/-- An empty complete interval certifies that no decision was recorded.
That certificate is not a rejection. -/
theorem empty_admissions_are_not_rejection [DecidableEq Key] (capacity : Nat) (key : Key)
    (reason : Reason) :
    coveredLatest ((Prefix.initial capacity).append ([] : List (Key × Decision Reason))) key =
      some none ∧
      some (none : Option (Decision Reason)) ≠ some (some (.rejected reason)) := by
  refine ⟨?_, ?_⟩
  · rw [coveredLatest_of_complete [] capacity key (Nat.zero_le capacity),
      (latest_none_iff ([] : List (Key × Decision Reason)) key).2 (by simp)]
  · intro same
    injection same with flat
    cases flat

/-- Certified absence inside this interval does not remove a decision that
was recorded only in an earlier, unrecorded prefix. -/
theorem covered_absence_ignores_earlier [DecidableEq Key]
    (earlier interval : List (Key × Decision Reason)) (capacity : Nat) (key : Key)
    (fits : interval.length ≤ capacity) (absent : key ∉ interval.map Prod.fst)
    (seen : key ∈ earlier.map Prod.fst) :
    coveredLatest ((Prefix.initial capacity).append interval) key = some none ∧
      latest (earlier ++ interval) key ≠ none := by
  have missingInterval : latest interval key = none :=
    (latest_none_iff interval key).2 absent
  have earlierSome : latest earlier key ≠ none := by
    intro gone
    exact ((latest_none_iff earlier key).1 gone) seen
  refine ⟨?_, ?_⟩
  · rw [coveredLatest_of_complete interval capacity key fits, missingInterval]
  · rw [latest_append, missingInterval]
    cases found : latest earlier key with
    | none => exact absurd found earlierSome
    | some decision =>
        rw [show none.or (some decision) = some decision from rfl]
        exact Option.some_ne_none decision

theorem coveredLatest_transport {NextKey : Type*} [DecidableEq Key] [DecidableEq NextKey]
    (mapping : Key → NextKey) (faithful : Function.Injective mapping)
    (record : Prefix (Key × Decision Reason)) (key : Key) :
    coveredLatest (record.map (fun entry => (mapping entry.1, entry.2))) (mapping key) =
      coveredLatest record key := by
  cases complete : record.complete? with
  | none => simp [coveredLatest, Prefix.complete?_map, complete]
  | some events =>
      simp [coveredLatest, Prefix.complete?_map, complete, latest_transport mapping faithful]

inductive Explanation (Reason : Type*) where
  | staleContext
  | outsideInquiry
  | incompleteRecording
  | noRecordedDecision
  | recorded (decision : Decision Reason)
  deriving DecidableEq, Repr

/-- The revision includes every context component observed by this inquiry.
The interval branch is `coveredLatest`: omission stays incomplete, and a
complete interval with no recorded decision is not a rejection. -/
def explain [DecidableEq Key] [DecidableEq Revision]
    (captured current : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason)) (key : Key) : Explanation Reason :=
  if captured ≠ current then .staleContext
  else if key ∉ inventory then .outsideInquiry
  else match coveredLatest record key with
    | none => .incompleteRecording
    | some none => .noRecordedDecision
    | some (some decision) => .recorded decision

theorem explain_covered [DecidableEq Key] [DecidableEq Revision]
    (revision : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason)) (key : Key)
    (present : key ∈ inventory) :
    explain revision revision inventory record key =
      match coveredLatest record key with
      | none => .incompleteRecording
      | some none => .noRecordedDecision
      | some (some decision) => .recorded decision := by
  simp [explain, present]

theorem explain_recorded [DecidableEq Key] [DecidableEq Revision]
    (revision : Revision) (inventory : List Key)
    (events : List (Key × Decision Reason)) (capacity : Nat) (key : Key)
    (present : key ∈ inventory) (fits : events.length ≤ capacity) :
    explain revision revision inventory ((Prefix.initial capacity).append events) key =
      match latest events key with
      | none => .noRecordedDecision
      | some decision => .recorded decision := by
  rw [explain_covered revision inventory ((Prefix.initial capacity).append events) key present,
    coveredLatest_of_complete events capacity key fits]
  cases latest events key <;> rfl

theorem explain_missing [DecidableEq Key] [DecidableEq Revision]
    (revision : Revision) (inventory : List Key)
    (events : List (Key × Decision Reason)) (capacity : Nat) (key : Key)
    (present : key ∈ inventory) (fits : events.length ≤ capacity)
    (missing : key ∉ events.map Prod.fst) :
    explain revision revision inventory ((Prefix.initial capacity).append events) key =
      .noRecordedDecision := by
  rw [explain_recorded revision inventory events capacity key present fits,
    (latest_none_iff events key).2 missing]

theorem explain_truncated [DecidableEq Key] [DecidableEq Revision]
    (revision : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason)) (key : Key)
    (present : key ∈ inventory) (omitted : record.omitted ≠ 0) :
    explain revision revision inventory record key = .incompleteRecording := by
  rw [explain_covered revision inventory record key present,
    coveredLatest_omitted record key omitted]

/-- The explanation transports through the same occurrence map as the
bounded recording. Capacity, omissions, revision and decision meanings stay
fixed; only candidate identities change. -/
theorem explain_transport {NextKey : Type*}
    [DecidableEq Key] [DecidableEq NextKey] [DecidableEq Revision]
    (mapping : Key → NextKey) (faithful : Function.Injective mapping)
    (captured current : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason)) (key : Key) :
    explain captured current (inventory.map mapping)
      (record.map (fun entry => (mapping entry.1, entry.2))) (mapping key) =
        explain captured current inventory record key := by
  have member : mapping key ∈ inventory.map mapping ↔ key ∈ inventory := by
    constructor
    · intro mapped
      obtain ⟨candidate, present, same⟩ := List.mem_map.mp mapped
      exact faithful same ▸ present
    · intro present
      exact List.mem_map_of_mem present
  by_cases same : captured = current
  · by_cases present : key ∈ inventory
    · rw [same,
        explain_covered current (inventory.map mapping)
          (record.map (fun entry => (mapping entry.1, entry.2))) (mapping key)
          (member.mpr present),
        explain_covered current inventory record key present,
        coveredLatest_transport mapping faithful record key]
    · simp [explain, same, member, present]
  · simp [explain, same]

def rejections [DecidableEq Key] (events : List (Key × Decision Reason)) :
    List Key → Option (List (Key × Reason))
  | [] => some []
  | key :: rest => match latest events key with
      | some (.rejected reason) =>
          (rejections events rest).map ((key, reason) :: ·)
      | _ => none

/-- Exact per-occurrence coverage: every inventory position has a recorded
latest rejection. Equal payloads never merge two different keys. -/
theorem rejections_iff [DecidableEq Key] (events : List (Key × Decision Reason))
    (inventory : List Key) (result : List (Key × Reason)) :
    rejections events inventory = some result ↔
      List.Forall₂ (fun key entry => entry.1 = key ∧
        latest events key = some (.rejected entry.2)) inventory result := by
  induction inventory generalizing result with
  | nil => cases result <;> simp [rejections]
  | cons key rest ih =>
      cases decision : latest events key with
      | none => cases result <;> simp [rejections, decision, List.forall₂_cons]
      | some decisionValue =>
          cases decisionValue with
          | admitted => cases result <;> simp [rejections, decision, List.forall₂_cons]
          | pending => cases result <;> simp [rejections, decision, List.forall₂_cons]
          | rejected reason =>
              cases result with
              | nil => simp [rejections, decision]
              | cons entry tail =>
                  cases entry with
                  | mk entryKey entryReason =>
                      simp [rejections, decision, List.forall₂_cons, ih, and_assoc, and_comm,
                        eq_comm]

theorem rejections_transport {NextKey : Type*} [DecidableEq Key] [DecidableEq NextKey]
    (mapping : Key → NextKey) (faithful : Function.Injective mapping)
    (events : List (Key × Decision Reason)) (inventory : List Key) :
    rejections (events.map (fun entry => (mapping entry.1, entry.2))) (inventory.map mapping) =
      (rejections events inventory).map (List.map (fun entry => (mapping entry.1, entry.2))) := by
  induction inventory with
  | nil => rfl
  | cons key rest ih =>
      simp only [List.map_cons, rejections, latest_transport mapping faithful]
      cases decision : latest events key with
      | none => rfl
      | some decisionValue =>
          cases decisionValue with
          | admitted => rfl
          | pending => rfl
          | rejected reason =>
              rw [ih]
              cases rejections events rest <;> rfl

/-- Complete rejection coverage for this captured finite inventory. It does
not by itself close a search frontier or authenticate the inventory. -/
def completeRejections? [DecidableEq Key] [DecidableEq Revision]
    (captured current : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason)) : Option (List (Key × Reason)) :=
  if captured = current then record.complete?.bind (fun events => rejections events inventory)
  else none

theorem complete_rejections_sound [DecidableEq Key] [DecidableEq Revision]
    (captured current : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason)) (result : List (Key × Reason))
    (accepted : completeRejections? captured current inventory record = some result) :
    captured = current ∧ ∃ events,
      record.complete? = some events ∧
      List.Forall₂ (fun key entry => entry.1 = key ∧
        latest events key = some (.rejected entry.2)) inventory result := by
  unfold completeRejections? at accepted
  split at accepted
  · rename_i currentContext
    obtain ⟨events, complete, rejected⟩ := Option.bind_eq_some_iff.mp accepted
    exact ⟨currentContext, events, complete, (rejections_iff events inventory result).1 rejected⟩
  · simp at accepted

theorem rejections_missing [DecidableEq Key]
    (events : List (Key × Decision Reason)) (inventory : List Key) (key : Key)
    (present : key ∈ inventory) (missing : latest events key = none) :
    rejections events inventory = none := by
  cases result : rejections events inventory with
  | none => rfl
  | some entries =>
      have covered := (rejections_iff events inventory entries).1 result
      have examined : latest events key ≠ none := by
        clear result
        induction covered with
        | nil => simp at present
        | @cons candidate entry rest entries head tail ih =>
            rcases List.mem_cons.mp present with same | later
            · rw [same, head.2]
              simp
            · exact ih later
      exact (examined missing).elim

theorem complete_rejections_resumption [DecidableEq Key] [DecidableEq Revision]
    (captured current : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason)) (before after : List (Key × Decision Reason)) :
    completeRejections? captured current inventory ((record.append before).append after) =
      completeRejections? captured current inventory (record.append (before ++ after)) := by
  rw [Prefix.append_append]

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.OpenTotalityObservation

/-- Closed absence additionally inspects the actual controlled run. The
returned coverage is the existing empty-frontier witness, not a new flag.
Native adapters must still justify this system, census, revision and history. -/
def closedAbsence? {Node Answer Memory : Type*} [DecidableEq Node] [DecidableEq Answer]
    [DecidableEq Key] [DecidableEq Revision]
    (system : BranchingSystem Node Answer) (controller : Controller Node Answer Memory)
    (roots : List Node) (fuel : Nat) (captured current : Revision)
    (inventory : List Key) (record : Prefix (Key × Decision Reason)) :
    Option (ControlledCoverage system controller roots fuel × List (Key × Reason)) :=
  match completeRejections? captured current inventory record with
  | none => none
  | some rejected =>
      let outcome := InferenceControl.Snapshot.run system controller fuel
        (InferenceControl.Snapshot.initial controller roots)
      if closed : outcome.search.frontier = [] then
        if outcome.search.events = [] then some (⟨closed⟩, rejected) else none
      else none

theorem closed_absence_sound {Node Answer Memory : Type*}
    [DecidableEq Node] [DecidableEq Answer] [DecidableEq Key] [DecidableEq Revision]
    (system : BranchingSystem Node Answer) (controller : Controller Node Answer Memory)
    (roots : List Node) (fuel : Nat) (captured current : Revision)
    (inventory : List Key) (record : Prefix (Key × Decision Reason))
    (result : ControlledCoverage system controller roots fuel × List (Key × Reason))
    (accepted : closedAbsence? system controller roots fuel captured current
      inventory record = some result) :
    completeRejections? captured current inventory record = some result.2 ∧
      (InferenceControl.Snapshot.run system controller fuel
        (InferenceControl.Snapshot.initial controller roots)).search.events = [] := by
  unfold closedAbsence? at accepted
  split at accepted
  · simp at accepted
  · rename_i rejected complete
    dsimp only at accepted
    split at accepted
    · split at accepted
      · have same := Option.some.inj accepted
        subst result
        exact ⟨complete, by assumption⟩
      · simp at accepted
    · simp at accepted

/-- A closed absence readout has zero answer denotation under the existing
additive account law. It is a theorem about that qualified branching system,
not a conclusion from zero allowance, missing trace entries or source hashes. -/
theorem closed_absence_denotation {Node Answer Memory : Type*}
    [DecidableEq Node] [DecidableEq Answer] [DecidableEq Key] [DecidableEq Revision]
    (system : BranchingSystem Node Answer) (controller : Controller Node Answer Memory)
    (denotation : AdditiveDenotation system) (roots : List Node) (fuel : Nat)
    (captured current : Revision) (inventory : List Key)
    (record : Prefix (Key × Decision Reason))
    (result : ControlledCoverage system controller roots fuel × List (Key × Reason))
    (accepted : closedAbsence? system controller roots fuel captured current
      inventory record = some result) : foldValues denotation.value roots = 0 := by
  have noAnswers := (closed_absence_sound system controller roots fuel captured current
    inventory record result accepted).2
  have preserved := InferenceControl.Snapshot.completed_run_denotation system controller
    denotation roots fuel result.1.frontierEmpty
  rw [noAnswers] at preserved
  simpa [eventBag] using preserved.symm

namespace Controls

private def decisions : List (Nat × Decision Nat) :=
  [(1, .rejected 7), (2, .pending), (3, .admitted)]

theorem distinct_candidate_statuses :
    explain 4 4 [1, 2, 3, 5] ((Prefix.initial 3).append decisions) 1 =
      .recorded (.rejected 7) ∧
    explain 4 4 [1, 2, 3, 5] ((Prefix.initial 3).append decisions) 2 =
      .recorded .pending ∧
    explain 4 4 [1, 2, 3, 5] ((Prefix.initial 3).append decisions) 3 =
      .recorded .admitted ∧
    explain 4 4 [1, 2, 3, 5] ((Prefix.initial 3).append decisions) 5 =
      .noRecordedDecision := by decide

theorem changed_and_truncated_refused :
    explain 4 5 [1, 2, 3] ((Prefix.initial 3).append decisions) 1 = .staleContext ∧
    explain 4 4 [1, 2, 3] ((Prefix.initial 1).append decisions) 1 =
      .incompleteRecording := by decide

theorem newest_decision_wins :
    latest (decisions ++ [(1, .pending)]) 1 = some .pending ∧
    latest (decisions ++ [(1, .pending)]) 2 = some .pending := by decide

theorem incomplete_inventory_refused :
    completeRejections? 4 4 [1, 2] ((Prefix.initial 3).append decisions) = none ∧
    completeRejections? 4 4 [1, 5] ((Prefix.initial 3).append decisions) = none := by decide

private def finiteInquiry : BranchingSystem Nat Nat where
  emit _ := none
  successors node := if node = 0 then [1, 2] else []

private def fullRejections : Prefix (Nat × Decision Nat) :=
  (Prefix.initial 2).append [(1, .rejected 7), (2, .rejected 8)]

theorem actual_closed_search_accepted :
    (closedAbsence? finiteInquiry (Controller.fixed Scheduler.breadthFirst)
      [0] 3 4 4 [1, 2] fullRejections).isSome = true := by decide

/-- The same complete rejection trace cannot close a still-live run, including
a run with no execution allowance. -/
theorem live_and_zero_allowance_refused :
    (closedAbsence? finiteInquiry (Controller.fixed Scheduler.breadthFirst)
      [0] 2 4 4 [1, 2] fullRejections).isNone = true ∧
    (closedAbsence? finiteInquiry (Controller.fixed Scheduler.breadthFirst)
      [0] 0 4 4 [1, 2] fullRejections).isNone = true := by decide

theorem same_reason_keeps_candidate_occurrences :
    completeRejections? 4 4 [1, 2]
      ((Prefix.initial 2).append [(1, Decision.rejected 7), (2, .rejected 7)]) =
        some [(1, 7), (2, 7)] := by decide

theorem late_capture_is_not_coverage :
    completeRejections? 4 4 [1, 2]
      ((Prefix.initial 1).append [(2, Decision.rejected 8)]) = none := by decide

theorem collapsed_identity_changes_latest :
    latest ([(1, Decision.rejected 7), (2, .pending)] : List (Nat × Decision Nat)) 1 =
      some (.rejected 7) ∧
    latest ([(1, Decision.rejected 7), (2, .pending)].map
      (fun entry : Nat × Decision Nat => (0, entry.2))) 0 = some .pending := by decide

private def answeringInquiry : BranchingSystem Nat Nat where
  emit node := if node = 2 then some 99 else none
  successors node := if node = 0 then [1, 2] else []

/-- Rejection metadata cannot override an actual answer in the controlled
run. This also separates complete execution from closed answer absence. -/
theorem actual_answer_blocks_absence :
    (closedAbsence? answeringInquiry (Controller.fixed Scheduler.breadthFirst)
      [0] 3 4 4 [1, 2] fullRejections).isNone = true := by decide

private def acceptedThenPending : List (Nat × Decision Nat) :=
  [(0, .admitted), (0, .pending)]

private def acceptedThenRejected : List (Nat × Decision Nat) :=
  [(1, .admitted), (1, .rejected 9)]

private def orderedVerdicts : List (Nat × Decision Nat) :=
  [(0, .admitted), (1, .rejected 4), (0, .pending)]

/-- A complete interval retains every verdict in order. The later pending
decision is latest for key 0, the rejection keeps its reason, and a missing
key is certified absence on this interval rather than rejection. -/
theorem complete_interval_reads_ordered_verdicts :
    ((Prefix.initial 3).append orderedVerdicts).items = orderedVerdicts ∧
      ((Prefix.initial 3).append orderedVerdicts).omitted = 0 ∧
      coveredLatest ((Prefix.initial 3).append orderedVerdicts) 0 =
        some (some .pending) ∧
      coveredLatest ((Prefix.initial 3).append orderedVerdicts) 1 =
        some (some (.rejected 4)) ∧
      coveredLatest ((Prefix.initial 3).append orderedVerdicts) 2 = some none ∧
      explain 4 4 [0, 1, 2] ((Prefix.initial 3).append orderedVerdicts) 0 =
        .recorded .pending ∧
      explain 4 4 [0, 1, 2] ((Prefix.initial 3).append orderedVerdicts) 2 =
        .noRecordedDecision := by
  have fits : orderedVerdicts.length ≤ 3 := by decide
  have payload := complete_interval_payload orderedVerdicts 3 0 fits
  refine ⟨payload.2.1, payload.2.2, ?_,
      covered_rejection_keeps_reason orderedVerdicts 3 1 4 fits ?_, ?_, ?_, ?_⟩
  · rw [coveredLatest_of_complete orderedVerdicts 3 0 fits]
    decide
  · decide
  · rw [coveredLatest_of_complete orderedVerdicts 3 2 fits]
    decide
  · rw [explain_recorded 4 [0, 1, 2] orderedVerdicts 3 0 (by decide) fits]
    decide
  · rw [explain_missing 4 [0, 1, 2] orderedVerdicts 3 2 (by decide) fits (by decide)]

/-- Capacity keeps the earlier admission and omits the later decision for
the same key. The retained admission is a historical item. `coveredLatest`
does not certify it as the latest decision, and `explain` reports the
omission rather than that admission. The same omission shape is a missing
causal query, not a recorded empty cause list. -/
theorem omitted_later_decision_is_not_latest :
    coveredLatest ((Prefix.initial 1).append acceptedThenPending) 0 = none ∧
      ((Prefix.initial 1).append acceptedThenPending).items = [(0, .admitted)] ∧
      latest acceptedThenPending 0 = some .pending ∧
      explain 4 4 [0] ((Prefix.initial 1).append acceptedThenPending) 0 =
        .incompleteRecording ∧
      coveredLatest ((Prefix.initial 1).append acceptedThenRejected) 1 = none ∧
      ((Prefix.initial 1).append acceptedThenRejected).items = [(1, .admitted)] ∧
      latest acceptedThenRejected 1 = some (.rejected 9) ∧
      explain 4 4 [1] ((Prefix.initial 1).append acceptedThenRejected) 1 =
        .incompleteRecording ∧
      (_root_.Mettapedia.Machines.CausalReceipt.Controls.shared).causes? 0 = none ∧
      (_root_.Mettapedia.Machines.CausalReceipt.Controls.shared).causes? 1 = some [] := by
  have pendingLost : ((Prefix.initial 1).append acceptedThenPending).omitted ≠ 0 := by
    decide
  have rejectedLost : ((Prefix.initial 1).append acceptedThenRejected).omitted ≠ 0 := by
    decide
  refine ⟨coveredLatest_omitted _ 0 pendingLost, ?_, ?_,
      explain_truncated 4 [0] ((Prefix.initial 1).append acceptedThenPending) 0
        (by decide) pendingLost,
      coveredLatest_omitted _ 1 rejectedLost, ?_, ?_,
      explain_truncated 4 [1] ((Prefix.initial 1).append acceptedThenRejected) 1
        (by decide) rejectedLost,
      _root_.Mettapedia.Machines.CausalReceipt.Controls.missing_occurrence_differs_from_empty_causes.1,
      _root_.Mettapedia.Machines.CausalReceipt.Controls.missing_occurrence_differs_from_empty_causes.2⟩
  · decide
  · decide
  · decide
  · decide

end Controls
end Candidate

/-- `follow` runs its own pure replay algorithm. It is not constant-time
forgetting. It certifies a bounded index interval from its recorded start
only when `Prefix.complete?` retains that interval. The consumer chooses
this checker. Validation grants no authority to advance the live runtime. -/
theorem complete_bounded_history
    {Term State Answer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (start : State) (capacity : Nat) (trace : List Nat) (target : State) :
    ((Prefix.initial capacity).append trace).complete?.bind (machine.follow start) =
        some target ↔
      trace.length ≤ capacity ∧ machine.follow start trace = some target :=
  Prefix.complete_bind_iff (machine.follow start) capacity trace target

/-! ## Source frontier as one occurrence machine

`frontierAnswer` steps by the actual expansion, and has no step once the
pending list is empty. `machine` is that answer machine viewed through
`OccurrenceMachineCore.ofDeterministic`. `bounded` reads the endpoint of the
existing `MachineCore.runSlice`; it is `SourceFrontier.resume`. Further fuel
at a closed state performs no transition.
-/

namespace SourceFrontierMachine

open Mettapedia.Algorithms.WellFoundedServices.OccurrenceGraph

def stepOf (graph : Graph) (frontier : SourceFrontier) : Option SourceFrontier :=
  match frontier.pending with
  | [] => none
  | _ => some (frontier.expand graph)

def answerOf (frontier : SourceFrontier) : Option Nat :=
  match frontier.pending with
  | [] => some frontier.paid
  | _ => none

theorem answerOf_final (graph : Graph) (frontier : SourceFrontier) (value : Nat)
    (observed : answerOf frontier = some value) : stepOf graph frontier = none := by
  cases pending : frontier.pending with
  | nil =>
    unfold stepOf
    rw [pending]
  | cons _ _ =>
    unfold answerOf at observed
    rw [pending] at observed
    cases observed

def frontierAnswer (graph : Graph) : AnswerMachineCore Nat Nat where
  State := SourceFrontier
  load := SourceFrontier.start
  step := stepOf graph
  answer := answerOf
  answer_final := answerOf_final graph

def core (graph : Graph) : MachineCore Nat :=
  (frontierAnswer graph).toMachineCore

def machine (graph : Graph) : OccurrenceMachineCore Nat SourceFrontier Nat :=
  OccurrenceMachineCore.ofDeterministic (frontierAnswer graph)

/-- Endpoint of `MachineCore.runSlice`. Not a second stepper. -/
def bounded (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) : SourceFrontier :=
  (MachineCore.runSlice (core graph) fuel frontier).1

theorem step_closed (graph : Graph) (frontier : SourceFrontier)
    (done : frontier.pending = []) : (core graph).step frontier = none := by
  simp [core, frontierAnswer, stepOf, done]

theorem step_live (graph : Graph) (frontier : SourceFrontier)
    {node : Nat} {rest : List Nat} (pending : frontier.pending = node :: rest) :
    (core graph).step frontier = some (frontier.expand graph) := by
  simp [core, frontierAnswer, stepOf, pending]

theorem bounded_resume (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    bounded graph fuel frontier = frontier.resume graph fuel := by
  induction fuel generalizing frontier with
  | zero => rfl
  | succ fuel ih =>
    cases pending : frontier.pending with
    | nil =>
      have stopped := step_closed graph frontier pending
      simp [bounded, MachineCore.runSlice, stopped, SourceFrontier.resume, pending,
        List.isEmpty_nil]
    | cons _ _ =>
      have moved := step_live graph frontier pending
      simp [bounded, MachineCore.runSlice, moved, SourceFrontier.resume, pending,
        List.isEmpty_cons]
      exact ih (frontier.expand graph)

theorem closed_extra_fuel (graph : Graph) (frontier : SourceFrontier) (fuel : Nat)
    (done : frontier.pending = []) :
    MachineCore.runSlice (core graph) fuel frontier = (frontier, 0) :=
  MachineCore.runSlice_of_final (core graph) frontier (step_closed graph frontier done) fuel

/-! The index word is optional. Its length is `runSlice`'s accepted-step count:
how many expansions ran. That count is not the admission cost, not a second
counter, and not the `List.iterate` snapshot. -/

open Mettapedia.GSLT.Causality.OccurrenceMachineHistory

def realTrace (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) : List Nat :=
  List.replicate (MachineCore.runSlice (core graph) fuel frontier).2 0

theorem follow_bounded (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    (machine graph).follow frontier (realTrace graph fuel frontier) =
      some (bounded graph fuel frontier) := by
  induction fuel generalizing frontier with
  | zero => rfl
  | succ fuel ih =>
    cases pending : frontier.pending with
    | nil =>
      have stopped := step_closed graph frontier pending
      simp [realTrace, bounded, MachineCore.runSlice, stopped, machine,
        OccurrenceMachineCore.ofDeterministic, OccurrenceMachineCore.follow]
    | cons _ _ =>
      have moved := step_live graph frontier pending
      have count : (MachineCore.runSlice (core graph) (fuel + 1) frontier).2 =
          (MachineCore.runSlice (core graph) fuel (frontier.expand graph)).2 + 1 := by
        simp [MachineCore.runSlice, moved]
      rw [realTrace, count, List.replicate_succ, OccurrenceMachineCore.follow]
      have next : (machine graph).next frontier = [frontier.expand graph] := by
        simp [machine, OccurrenceMachineCore.ofDeterministic, frontierAnswer, stepOf, pending]
      rw [next]
      rw [show ([frontier.expand graph] : List SourceFrontier)[0]? =
        some (frontier.expand graph) from rfl]
      simp [bounded, MachineCore.runSlice, moved]
      exact ih (frontier.expand graph)

theorem follow_resume (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    (machine graph).follow frontier (realTrace graph fuel frontier) =
      some (frontier.resume graph fuel) := by
  rw [follow_bounded, bounded_resume]

/-- A complete record of one real index interval replays from its recorded
start. `follow` runs that pure replay. The recording does not advance the
frontier, and validation grants no authority to advance the live runtime. -/
theorem frontier_interval_replays (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    ((Prefix.initial (realTrace graph fuel frontier).length).append
        (realTrace graph fuel frontier)).complete?.bind
      ((machine graph).follow frontier) =
        some (frontier.resume graph fuel) :=
  (complete_bounded_history (machine graph) frontier
      (realTrace graph fuel frontier).length (realTrace graph fuel frontier)
      (frontier.resume graph fuel)).mpr
    ⟨Nat.le_refl _, follow_resume graph fuel frontier⟩

/-- Take the frontier's only successor and write its position then.
Extra fuel at a closed frontier adds no index. This is that deterministic
step, not a schedule over several live branches. -/
def recordedRun (graph : Graph) :
    Nat → RecordedState SourceFrontier → RecordedState SourceFrontier
  | 0, state => state
  | fuel + 1, state =>
    match (recordedMachine (machine graph)).next state with
    | [] => state
    | successor :: _ => recordedRun graph fuel successor

theorem recordedRun_frontier (graph : Graph) (fuel : Nat) (frontier : SourceFrontier)
    (record : Prefix Nat) :
    recordedRun graph fuel ⟨frontier, record⟩ =
      ⟨frontier.resume graph fuel, record.append (realTrace graph fuel frontier)⟩ := by
  induction fuel generalizing frontier record with
  | zero =>
      simp [recordedRun, SourceFrontier.resume, realTrace, MachineCore.runSlice, Prefix.append]
  | succ fuel ih =>
      cases pending : frontier.pending with
      | nil =>
          have stopped := step_closed graph frontier pending
          have nextNil : (machine graph).next frontier = [] := by
            simp [machine, OccurrenceMachineCore.ofDeterministic, frontierAnswer, stepOf, pending]
          simp [recordedRun, recordedMachine, nextNil, List.zipIdx_nil, SourceFrontier.resume,
            pending, List.isEmpty_nil, realTrace, MachineCore.runSlice, stopped, Prefix.append]
      | cons _ _ =>
          have moved := step_live graph frontier pending
          have only : (machine graph).next frontier = [frontier.expand graph] := by
            simp [machine, OccurrenceMachineCore.ofDeterministic, frontierAnswer, stepOf, pending]
          have stepped := recordedMachine_head (machine graph) ⟨frontier, record⟩
            (frontier.expand graph) only
          simp only [recordedRun, stepped]
          rw [ih (frontier.expand graph) (record.push (fun () => 0))]
          have count : (MachineCore.runSlice (core graph) (fuel + 1) frontier).2 =
              (MachineCore.runSlice (core graph) fuel (frontier.expand graph)).2 + 1 := by
            simp [MachineCore.runSlice, moved]
          simp [SourceFrontier.resume, pending, List.isEmpty_cons, realTrace, count,
            List.replicate_succ, Prefix.append]

/-- The prefix written by `recordedRun` is the real index word. Replaying it
uses `follow` from the original frontier. -/
theorem frontier_recorded_replay (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    let ran := recordedRun graph fuel
      ⟨frontier, Prefix.initial (realTrace graph fuel frontier).length⟩
    ran.base = frontier.resume graph fuel ∧
      ran.record.items = realTrace graph fuel frontier ∧
      ran.record.complete?.bind ((machine graph).follow frontier) =
        some (frontier.resume graph fuel) := by
  rw [recordedRun_frontier]
  refine ⟨rfl, ?_, frontier_interval_replays graph fuel frontier⟩
  simp [Prefix.initial_items, List.take_length]

/-- Following the real index word appends those positions to the prefix already
attached and reaches the resumed frontier. -/
theorem recordedFrontier_follow (graph : Graph) (fuel : Nat) (frontier : SourceFrontier)
    (record : Prefix Nat) :
    (recordedMachine (machine graph)).follow ⟨frontier, record⟩
        (realTrace graph fuel frontier) =
      some ⟨frontier.resume graph fuel,
        record.append (realTrace graph fuel frontier)⟩ := by
  rw [recordedMachine_follow, follow_resume]
  rfl

theorem realTrace_add (graph : Graph) (first second : Nat) (frontier : SourceFrontier) :
    realTrace graph (first + second) frontier =
      realTrace graph first frontier ++
        realTrace graph second (frontier.resume graph first) := by
  have split := MachineCore.runSlice_add (core graph) first second frontier
  simp only [realTrace]
  rw [split]
  simp only [List.replicate_add]
  rw [← bounded, bounded_resume]

def realHistory (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    History (machine graph) frontier (frontier.resume graph fuel) :=
  ofTrace (machine graph) (realTrace graph fuel frontier) (follow_resume graph fuel frontier)

/-- The history of a split run is the composite of the two histories.
`resume_add` lines up the endpoints and does not choose which occurrences were taken. -/
theorem realHistory_add (graph : Graph) (first second : Nat) (frontier : SourceFrontier) :
    HEq (realHistory graph (first + second) frontier)
      ((realHistory graph first frontier).comp
        (realHistory graph second (frontier.resume graph first))) := by
  rw [realHistory, realHistory, realHistory]
  exact ofTrace_append_eq (machine graph)
    (realTrace graph first frontier)
    (realTrace graph second (frontier.resume graph first))
    (follow_resume graph first frontier)
    (follow_resume graph second (frontier.resume graph first))
    (realTrace graph (first + second) frontier)
    (follow_resume graph (first + second) frontier)
    (realTrace_add graph first second frontier)
    (SourceFrontier.resume_add graph first second frontier).symm

theorem indices_realHistory (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    indices (machine graph) (realHistory graph fuel frontier) = realTrace graph fuel frontier := by
  rw [realHistory]
  exact indices_ofTrace (machine graph) (realTrace graph fuel frontier)
    (follow_resume graph fuel frontier)

/-- `follow` replays the retained index path to the resumed frontier. -/
theorem history_replay_endpoint (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    (machine graph).follow frontier (indices (machine graph) (realHistory graph fuel frontier)) =
      some (frontier.resume graph fuel) :=
  follow_indices (machine graph) (realHistory graph fuel frontier)

theorem history_splits (graph : Graph) (first second : Nat) (frontier : SourceFrontier) :
    indices (machine graph)
        ((realHistory graph first frontier).comp
          (realHistory graph second (frontier.resume graph first))) =
      realTrace graph first frontier ++
        realTrace graph second (frontier.resume graph first) := by
  rw [indices_comp, indices_realHistory, indices_realHistory]

theorem diary_splits (graph : Graph) (first second : Nat) (frontier : SourceFrontier) :
    (eventAccount (machine graph) (fun _ _ index => FreeMonoid.of index)).of
        ((realHistory graph first frontier).comp
          (realHistory graph second (frontier.resume graph first))) =
      (eventAccount (machine graph) (fun _ _ index => FreeMonoid.of index)).of
          (realHistory graph first frontier) *
        (eventAccount (machine graph) (fun _ _ index => FreeMonoid.of index)).of
          (realHistory graph second (frontier.resume graph first)) :=
  (eventAccount (machine graph) (fun _ _ index => FreeMonoid.of index)).of_comp
    (realHistory graph first frontier)
    (realHistory graph second (frontier.resume graph first))

theorem resumed_history_endpoint (graph : Graph) (first second : Nat) (frontier : SourceFrontier) :
    (machine graph).follow frontier
        (indices (machine graph)
          ((realHistory graph first frontier).comp
            (realHistory graph second (frontier.resume graph first)))) =
      some (frontier.resume graph (first + second)) := by
  rw [history_splits, ← realTrace_add, follow_resume]

theorem closed_stutter_is_not_an_event (graph : Graph) (frontier : SourceFrontier)
    (done : frontier.pending = []) : (machine graph).follow frontier [0] = none := by
  have stopped : (frontierAnswer graph).step frontier = none := by
    simp [frontierAnswer, stepOf, done]
  simp [OccurrenceMachineCore.follow, machine, OccurrenceMachineCore.ofDeterministic, stopped]
  rfl

/-- One actual expansion's admission cost: the matched row count of its node. -/
def paidEdge (before after : SourceFrontier) (_index : Nat) : Multiplicative Nat :=
  Multiplicative.ofAdd (after.paid - before.paid)

def paidAccount (graph : Graph) :
    Mettapedia.Effects.RunAccount
      (Mettapedia.OSLF.Binding.RewriteEventHistory.HistoryCategory (system (machine graph)))
      (Multiplicative Nat) :=
  eventAccount (machine graph) paidEdge

theorem edge_paid_charge (graph : Graph) {before after : SourceFrontier}
    (member : after ∈ (machine graph).next before) :
    ∃ node rest, before.pending = node :: rest ∧ after = before.expand graph ∧
      after.paid = before.paid + (graph.rows node).length := by
  cases before with
  | mk paid pending =>
    cases pending with
    | nil =>
      simp [machine, OccurrenceMachineCore.ofDeterministic, frontierAnswer, stepOf] at member
    | cons node rest =>
      simp [machine, OccurrenceMachineCore.ofDeterministic, frontierAnswer, stepOf] at member
      subst after
      exact ⟨node, rest, rfl, rfl, rfl⟩

theorem edge_paid_mono (graph : Graph) {before after : SourceFrontier}
    (member : after ∈ (machine graph).next before) : before.paid ≤ after.paid := by
  obtain ⟨_, _, _, _, charge⟩ := edge_paid_charge graph member
  omega

/-- Whichever prefix is already attached, the recorded history's paid account
is the base paid difference of the resumed frontier. -/
theorem frontier_recorded_account (graph : Graph) (fuel : Nat) (frontier : SourceFrontier)
    (record : Prefix Nat) :
    (eventAccount (recordedMachine (machine graph)) (recordedEdge (·.paid))).of
      (ofTrace (recordedMachine (machine graph)) (realTrace graph fuel frontier)
        (recordedFrontier_follow graph fuel frontier record)) =
      Multiplicative.ofAdd ((frontier.resume graph fuel).paid - frontier.paid) :=
  recordedMachine_account (machine graph) (·.paid)
    (fun _before _after index found =>
      edge_paid_mono graph ((List.mem_iff_getElem?).mpr ⟨index, found⟩)) _

theorem history_paid_le (graph : Graph)
    {source target : Mettapedia.OSLF.Binding.RewriteEventHistory.State (system (machine graph))}
    (history : Quiver.Path source target) : source.term.paid ≤ target.term.paid :=
  potential_path_le (machine graph) (·.paid)
    (fun _before _after index found =>
      edge_paid_mono graph ((List.mem_iff_getElem?).mpr ⟨index, found⟩))
    history

/-- The run account of any real edge path is the paid difference of its endpoints. -/
theorem history_paid (graph : Graph)
    {source target : Mettapedia.OSLF.Binding.RewriteEventHistory.State (system (machine graph))}
    (history : Quiver.Path source target) :
    (paidAccount graph).of history =
      Multiplicative.ofAdd (target.term.paid - source.term.paid) :=
  potential_path_account (machine graph) (·.paid) paidEdge
    (fun _before _after _index => rfl)
    (fun _before _after index found =>
      edge_paid_mono graph ((List.mem_iff_getElem?).mpr ⟨index, found⟩))
    history

theorem paid_resume (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    (paidAccount graph).of (realHistory graph fuel frontier) =
      Multiplicative.ofAdd ((frontier.resume graph fuel).paid - frontier.paid) :=
  history_paid graph (realHistory graph fuel frontier)

theorem paid_splits (graph : Graph) (first second : Nat) (frontier : SourceFrontier) :
    (paidAccount graph).of
        ((realHistory graph first frontier).comp
          (realHistory graph second (frontier.resume graph first))) =
      (paidAccount graph).of (realHistory graph first frontier) *
        (paidAccount graph).of (realHistory graph second (frontier.resume graph first)) :=
  (paidAccount graph).of_comp _ _

theorem paid_resume_splits (graph : Graph) (first second : Nat) (frontier : SourceFrontier) :
    (paidAccount graph).of
        ((realHistory graph first frontier).comp
          (realHistory graph second (frontier.resume graph first))) =
      Multiplicative.ofAdd ((frontier.resume graph (first + second)).paid - frontier.paid) := by
  simpa only [SourceFrontier.resume_add] using history_paid graph
    ((realHistory graph first frontier).comp
      (realHistory graph second (frontier.resume graph first)))

/-- The real run, retained as an arrow of the free history category. -/
abbrev retainedRun (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :=
  retained (machine graph) (realHistory graph fuel frontier)

theorem retained_endpoint (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    (retainedRun graph fuel frontier).right.term = frontier.resume graph fuel := by
  rw [retained_right (machine graph) (realHistory graph fuel frontier)]
  rfl

theorem retained_paid (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    (retainedRun graph fuel frontier).right.term.paid =
      (frontier.resume graph fuel).paid := by
  rw [retained_endpoint]

theorem retained_pending (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    (retainedRun graph fuel frontier).right.term.pending =
      (frontier.resume graph fuel).pending := by
  rw [retained_endpoint]

theorem retained_account (graph : Graph) (fuel : Nat) (frontier : SourceFrontier) :
    (paidAccount graph).of (retainedRun graph fuel frontier).hom =
      Multiplicative.ofAdd
        ((retainedRun graph fuel frontier).right.term.paid - frontier.paid) := by
  exact paid_resume graph fuel frontier

theorem retained_split (graph : Graph) (first second : Nat) (frontier : SourceFrontier) :
    (retainedRun graph (first + second) frontier).right.term =
      (retainedRun graph second
        (retainedRun graph first frontier).right.term).right.term := by
  rw [retained_endpoint, retained_endpoint, retained_endpoint, SourceFrontier.resume_add]

theorem retained_paid_split (graph : Graph) (first second : Nat) (frontier : SourceFrontier) :
    (paidAccount graph).of
        ((retainedRun graph first frontier).hom.comp
          (retainedRun graph second (frontier.resume graph first)).hom) =
      Multiplicative.ofAdd
        ((retainedRun graph (first + second) frontier).right.term.paid - frontier.paid) := by
  exact paid_resume_splits graph first second frontier

/-- The retained arrows themselves compose across split and resume. -/
theorem retained_split_arrow (graph : Graph) (first second : Nat) (frontier : SourceFrontier) :
    HEq (retainedRun graph (first + second) frontier).hom
      ((retainedRun graph first frontier).hom.comp
        (retainedRun graph second (frontier.resume graph first)).hom) :=
  realHistory_add graph first second frontier

/-- The resumed frontier is the base state. It carries no prefix. -/
theorem late_starts_at_retained_endpoint
    (graph : Graph) (elapsed : Nat) (frontier : SourceFrontier) :
    (CategoryTheory.Under.forget (historyVertex (machine graph) frontier)).obj
        (retainedRun graph elapsed frontier) =
      historyVertex (machine graph) (frontier.resume graph elapsed) := by
  rw [retained_forgets (machine graph) (realHistory graph elapsed frontier),
    retained_right (machine graph) (realHistory graph elapsed frontier)]

/-- Resume the ordinary base for `elapsed` steps, open a caller-chosen
capacity at that state, and run the recorded machine once for `later` steps.
Stop keeps the prefix that run produced and returns the base continuation.
The capacity is an input, not the length of a future trace. The result is
not a history path. -/
def lateDiary (graph : Graph) (elapsed capacity later : Nat) (frontier : SourceFrontier) :
    (SourceFrontier × RecordedState SourceFrontier) × SourceFrontier :=
  stopRecording (frontier.resume graph elapsed)
    (recordedRun graph later
      ⟨frontier.resume graph elapsed, Prefix.initial capacity⟩)

/-- The stopped pair starts at the resumed frontier and stores the prefix
`recordedRun` produced. The pair is replay data. The continuation is the
later base frontier. Endpoint equality does not authenticate that start. -/
theorem late_record (graph : Graph) (elapsed capacity later : Nat) (frontier : SourceFrontier) :
    (lateDiary graph elapsed capacity later frontier).1.1 =
        frontier.resume graph elapsed ∧
      (lateDiary graph elapsed capacity later frontier).1.2.record =
        (Prefix.initial capacity).append
          (realTrace graph later (frontier.resume graph elapsed)) ∧
      (lateDiary graph elapsed capacity later frontier).2 =
        (frontier.resume graph elapsed).resume graph later := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lateDiary, stopRecording]
  · rw [lateDiary, stopRecording, recordedRun_frontier]
  · rw [lateDiary, stopRecording, forgetRecording, recordedRun_frontier]

theorem late_endpoint (graph : Graph) (elapsed capacity later : Nat) (frontier : SourceFrontier) :
    (lateDiary graph elapsed capacity later frontier).2 =
      (frontier.resume graph elapsed).resume graph later :=
  (late_record graph elapsed capacity later frontier).2.2

theorem late_paid (graph : Graph) (elapsed capacity later : Nat) (frontier : SourceFrontier) :
    (lateDiary graph elapsed capacity later frontier).2.paid =
      (frontier.resume graph (elapsed + later)).paid := by
  rw [late_endpoint, ← SourceFrontier.resume_add]

theorem late_pending (graph : Graph) (elapsed capacity later : Nat) (frontier : SourceFrontier) :
    (lateDiary graph elapsed capacity later frontier).2.pending =
      (frontier.resume graph (elapsed + later)).pending := by
  rw [late_endpoint, ← SourceFrontier.resume_add]

/-- A capacity chosen large enough lets the endpoint checker replay the later
index word from the resumed frontier onto the stored endpoint. The history
witness is not the diary, and the verdict is not a continuation. -/
theorem late_checked (graph : Graph) (elapsed capacity later : Nat) (frontier : SourceFrontier)
    (fits : (realTrace graph later (frontier.resume graph elapsed)).length ≤ capacity) :
    checkStopped (machine graph) (lateDiary graph elapsed capacity later frontier).1
        (realTrace graph later (frontier.resume graph elapsed)) =
      some (lateDiary graph elapsed capacity later frontier).2 :=
  (checkStopped_agrees (machine graph) (lateDiary graph elapsed capacity later frontier).1
      (realTrace graph later (frontier.resume graph elapsed))
      (lateDiary graph elapsed capacity later frontier).2).mpr
    ⟨by
      rw [(late_record graph elapsed capacity later frontier).2.1]
      exact (Prefix.complete_iff capacity _).mpr fits,
    by
      rw [(late_record graph elapsed capacity later frontier).1, late_endpoint]
      exact follow_resume graph later (frontier.resume graph elapsed),
    by
      rw [lateDiary, stopRecording, forgetRecording]⟩

/-- A short capacity keeps the omission. The known later index word does not
decode from that prefix. -/
theorem late_truncated (graph : Graph) (elapsed capacity later : Nat) (frontier : SourceFrontier)
    (short : capacity < (realTrace graph later (frontier.resume graph elapsed)).length) :
    (lateDiary graph elapsed capacity later frontier).1.2.record.omitted ≠ 0 ∧
      checkStopped (machine graph) (lateDiary graph elapsed capacity later frontier).1
        (realTrace graph later (frontier.resume graph elapsed)) = none := by
  have omitted : (lateDiary graph elapsed capacity later frontier).1.2.record.omitted ≠ 0 := by
    rw [(late_record graph elapsed capacity later frontier).2.1, Prefix.initial_omitted]
    omega
  exact ⟨omitted,
    checkStopped_omitted (machine graph) (lateDiary graph elapsed capacity later frontier).1
      (realTrace graph later (frontier.resume graph elapsed)) omitted⟩

/-- The paid account of the later base interval. `realHistory` is the proof
witness. The stopped diary stores the bounded prefix, not this path. -/
theorem late_account (graph : Graph) (elapsed capacity later : Nat) (frontier : SourceFrontier) :
    (paidAccount graph).of
        (realHistory graph later (frontier.resume graph elapsed)) =
      Multiplicative.ofAdd
        ((lateDiary graph elapsed capacity later frontier).2.paid -
          (frontier.resume graph elapsed).paid) := by
  rw [paid_resume, late_endpoint]

/-- The paid history of the expansions a source-metric budget actually admits
is the quoted unfolding work removed from the pending multiset. Repeated
successors stay in that multiset. The quotation is `sourceValuation` on one
finite acyclic occurrence catalogue. It is not coverage of an arbitrary
higher-order Prime analyzer, and `weigh-by-self` is not this metric. -/
theorem budgeted_history_eq_quoted_drop (graph : Graph) (acyclic : graph.catalogue.Acyclic)
    (source budget fuel : Nat) (frontier : SourceFrontier)
    (balanced : frontier.accounts graph acyclic source) :
    (paidAccount graph).of
        (realHistory graph (SourceFrontier.continueWithin graph budget fuel frontier).steps
          frontier) =
      Multiplicative.ofAdd
        (pendingWork graph acyclic frontier.pending -
          pendingWork graph acyclic
            (SourceFrontier.continueWithin graph budget fuel frontier).frontier.pending) := by
  have account := paid_resume graph
    (SourceFrontier.continueWithin graph budget fuel frontier).steps frontier
  have same := SourceFrontier.continueWithin_resume graph budget fuel frontier
  have resumed := SourceFrontier.resume_accounts graph acyclic source
    (SourceFrontier.continueWithin graph budget fuel frontier).steps frontier balanced
  rw [show (frontier.resume graph
      (SourceFrontier.continueWithin graph budget fuel frontier).steps).paid =
    (SourceFrontier.continueWithin graph budget fuel frontier).frontier.paid from
      congrArg SourceFrontier.paid same.symm] at account
  rw [same.symm] at resumed
  rw [SourceFrontier.accounts] at balanced resumed
  have drop :
      (SourceFrontier.continueWithin graph budget fuel frontier).frontier.paid - frontier.paid =
        pendingWork graph acyclic frontier.pending -
          pendingWork graph acyclic
            (SourceFrontier.continueWithin graph budget fuel frontier).frontier.pending := by
    omega
  rw [drop] at account
  exact account

/-- A fuel pause keeps pending work and is the ordinary resume split. The
paid history of that split is the paid difference across both pieces. -/
theorem paused_budget_is_resume_split (graph : Graph) (budget fuel more : Nat)
    (frontier : SourceFrontier)
    (paused : (SourceFrontier.continueWithin graph budget fuel frontier).stop =
      SourceFrontier.BudgetStop.paused) :
    let first := SourceFrontier.continueWithin graph budget fuel frontier
    let second := SourceFrontier.continueWithin graph first.remaining more first.frontier
    first.frontier.pending ≠ [] ∧
      first.frontier = frontier.resume graph first.steps ∧
      second.frontier = first.frontier.resume graph second.steps ∧
      (paidAccount graph).of
          ((realHistory graph first.steps frontier).comp
            (realHistory graph second.steps (frontier.resume graph first.steps))) =
        Multiplicative.ofAdd
          ((frontier.resume graph (first.steps + second.steps)).paid - frontier.paid) := by
  have live := SourceFrontier.continueWithin_paused_pending graph budget fuel frontier paused
  refine ⟨live, SourceFrontier.continueWithin_resume graph budget fuel frontier,
    SourceFrontier.continueWithin_resume graph
      (SourceFrontier.continueWithin graph budget fuel frontier).remaining more
      (SourceFrontier.continueWithin graph budget fuel frontier).frontier,
    paid_resume_splits graph
      (SourceFrontier.continueWithin graph budget fuel frontier).steps
      (SourceFrontier.continueWithin graph
          (SourceFrontier.continueWithin graph budget fuel frontier).remaining more
          (SourceFrontier.continueWithin graph budget fuel frontier).frontier).steps
      frontier⟩

/-- When the budget admits every later step, `late_account` is that admitted
spend. The diary's capacity does not enter the charge. -/
theorem late_account_eq_admitted_spend (graph : Graph) (elapsed later budget : Nat)
    (frontier : SourceFrontier)
    (covered : (SourceFrontier.continueWithin graph budget later
        (frontier.resume graph elapsed)).steps = later) :
    (paidAccount graph).of
        (realHistory graph later (frontier.resume graph elapsed)) =
      Multiplicative.ofAdd
        ((SourceFrontier.continueWithin graph budget later
            (frontier.resume graph elapsed)).frontier.paid -
          (frontier.resume graph elapsed).paid) := by
  rw [late_account graph elapsed 0 later frontier,
    late_paid graph elapsed 0 later frontier, SourceFrontier.resume_add]
  have same := SourceFrontier.continueWithin_resume graph budget later
    (frontier.resume graph elapsed)
  rw [covered] at same
  rw [show ((frontier.resume graph elapsed).resume graph later).paid =
      (SourceFrontier.continueWithin graph budget later
        (frontier.resume graph elapsed)).frontier.paid from
    congrArg SourceFrontier.paid same.symm]

/-- The stopped prefix retains only what fit in the caller capacity. A fresh
prefix at the continuation is empty. The base history composition is a
witness already in hand; it is not read out of the stopped prefix. -/
theorem late_known_prefix (graph : Graph) (elapsed capacity later : Nat)
    (frontier : SourceFrontier) :
    (lateDiary graph elapsed capacity later frontier).1.2.record.items =
      (realTrace graph later (frontier.resume graph elapsed)).take capacity ∧
    (restartRecording (lateDiary graph elapsed capacity later frontier).2
        capacity).record.items = [] ∧
    (restartRecording (lateDiary graph elapsed capacity later frontier).2
        capacity).record.omitted = 0 ∧
    HEq (realHistory graph (elapsed + later) frontier)
      ((CategoryTheory.Under.map (realHistory graph elapsed frontier)).obj
        (retained (machine graph)
          (realHistory graph later (frontier.resume graph elapsed)))).hom := by
  refine ⟨?_, ?_, ?_, realHistory_add graph elapsed later frontier⟩
  · rw [(late_record graph elapsed capacity later frontier).2.1, Prefix.initial_items]
  · exact (restartRecording_excludes
      (lateDiary graph elapsed capacity later frontier).2 capacity []).1
  · exact (restartRecording_excludes
      (lateDiary graph elapsed capacity later frontier).2 capacity []).2.1

namespace Controls

/-- Depth fan, budget 10: the paid history account is the quoted unfolding
work. The transition length is not that work. Budget 9 refuses the last
repeated successor and leaves it pending, so the frontier has no final
answer. Dependency depth and answer counts are separated in
`depth_fan_source_budget_completes`. -/
theorem depth_fan_budget_joins_paid_history :
    (paidAccount depthFanGraph).of
        (realHistory depthFanGraph
          (SourceFrontier.continueWithin depthFanGraph 10 6 (SourceFrontier.start 0)).steps
          (SourceFrontier.start 0)) =
      Multiplicative.ofAdd (depthFanGraph.sourceValuation depthFanCertificate 0).work ∧
    (paidAccount depthFanGraph).of
        (realHistory depthFanGraph 6 (SourceFrontier.start 0)) =
      Multiplicative.ofAdd
        ((SourceFrontier.continueWithin depthFanGraph 10 6 (SourceFrontier.start 0)).frontier.paid -
          (SourceFrontier.start 0).paid) ∧
    (realTrace depthFanGraph
        (SourceFrontier.continueWithin depthFanGraph 10 6 (SourceFrontier.start 0)).steps
        (SourceFrontier.start 0)).length ≠
      (depthFanGraph.sourceValuation depthFanCertificate 0).work ∧
    answerOf
        (SourceFrontier.continueWithin depthFanGraph 9 6 (SourceFrontier.start 0)).frontier = none ∧
    (SourceFrontier.continueWithin depthFanGraph 9 6 (SourceFrontier.start 0)).stop =
      SourceFrontier.BudgetStop.insufficient ∧
    (SourceFrontier.continueWithin depthFanGraph 9 6 (SourceFrontier.start 0)).frontier.pending =
      [1] ∧
    (SourceFrontier.continueWithin depthFanGraph 9 6 (SourceFrontier.start 0)).frontier.paid = 9 := by
  have shape := depth_fan_source_budget_completes
  have refusal := depth_fan_insufficient_budget_keeps_pending
  have account := budgeted_history_eq_quoted_drop depthFanGraph depthFanCertificate
    (depthFanGraph.catalogue.unfoldingWork depthFanCertificate
      (fun node => (depthFanGraph.rows node).length) 0)
    10 6 (SourceFrontier.start 0)
    (SourceFrontier.start_accounts depthFanGraph depthFanCertificate 0)
  have quoted :
      pendingWork depthFanGraph depthFanCertificate (SourceFrontier.start 0).pending -
        pendingWork depthFanGraph depthFanCertificate
          (SourceFrontier.continueWithin depthFanGraph 10 6 (SourceFrontier.start 0)).frontier.pending =
        (depthFanGraph.sourceValuation depthFanCertificate 0).work := by
    rw [shape.1]
    dsimp
    simp only [pendingWork, SourceFrontier.start, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero, Nat.sub_zero]
    rw [← depthFanGraph.sourceValuation_work]
  rw [quoted] at account
  have zeroStep : (SourceFrontier.start 0).resume depthFanGraph 0 = SourceFrontier.start 0 := by
    unfold SourceFrontier.resume
    rfl
  have covered : (SourceFrontier.continueWithin depthFanGraph 10 6
      ((SourceFrontier.start 0).resume depthFanGraph 0)).steps = 6 := by
    rw [zeroStep, shape.1]
  have late := late_account_eq_admitted_spend depthFanGraph 0 6 10
    (SourceFrontier.start 0) covered
  rw [zeroStep] at late
  have length : (realTrace depthFanGraph
      (SourceFrontier.continueWithin depthFanGraph 10 6 (SourceFrontier.start 0)).steps
      (SourceFrontier.start 0)).length = 6 := by
    rw [shape.1]
    decide
  have work : (depthFanGraph.sourceValuation depthFanCertificate 0).work = 10 := by
    rw [← shape.2.1, shape.1]
  refine ⟨account, late, ?_, ?_, ?_, ?_, ?_⟩
  · rw [length, work]
    decide
  · rw [refusal.1]
    rfl
  · rw [refusal.1]
  · rw [refusal.1]
  · rw [refusal.1]

theorem repeated_branch_run_slice :
    bounded repeatedBranchGraph 3 (SourceFrontier.start 0) = repeatedBranchDone ∧
      repeatedBranchExpanded.pending = [1, 1] ∧
      repeatedBranchExpanded.paid = 3 ∧
      repeatedBranchDone.pending = [] ∧
      repeatedBranchDone.paid = 5 ∧
      MachineCore.runSlice (core repeatedBranchGraph) 2 repeatedBranchDone =
        (repeatedBranchDone, 0) ∧
      bounded repeatedBranchGraph 1 repeatedBranchDropped ≠
        bounded repeatedBranchGraph 2 (SourceFrontier.start 0) := by
  obtain ⟨both, three, empty, five, _⟩ := repeated_successor_frontier_pays
  refine ⟨?_, both, three, empty, five,
    closed_extra_fuel repeatedBranchGraph repeatedBranchDone 2 empty, ?_⟩
  · rw [bounded_resume, repeatedBranchDone]
  · obtain ⟨_, _, _, differ⟩ := dropped_occurrence_breaks_iteration
    intro same
    apply differ
    rw [bounded_resume, bounded_resume] at same
    exact same

/-- The index path has one entry per accepted step. The iterate snapshot
also repeats the closed state, and that repetition is not an event. -/
theorem repeated_branch_erased_diary :
    realTrace repeatedBranchGraph 5 (SourceFrontier.start 0) = [0, 0, 0] ∧
      (MachineCore.runSlice (core repeatedBranchGraph) 5 (SourceFrontier.start 0)).2 = 3 ∧
      (machine repeatedBranchGraph).follow (SourceFrontier.start 0) [0, 0, 0, 0] = none ∧
      ((SourceFrontier.start 0).recorded repeatedBranchGraph 5).length = 5 ∧
      repeatedBranchDone.recorded repeatedBranchGraph 2 =
        [repeatedBranchDone, repeatedBranchDone] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · rw [SourceFrontier.recorded, List.length_iterate]
  · obtain ⟨_, _, empty, _, _⟩ := repeated_successor_frontier_pays
    rw [SourceFrontier.recorded]
    have step1 : List.iterate (SourceFrontier.expand repeatedBranchGraph) repeatedBranchDone 2 =
        repeatedBranchDone ::
          List.iterate (SourceFrontier.expand repeatedBranchGraph)
            (repeatedBranchDone.expand repeatedBranchGraph) 1 := rfl
    rw [step1, SourceFrontier.expand_fixed repeatedBranchGraph repeatedBranchDone empty]
    rfl

/-- Three expansions admit five rows. The index word counts the expansions. -/
theorem repeated_branch_transitions_are_not_admissions :
    (realTrace repeatedBranchGraph 5 (SourceFrontier.start 0)).length = 3 ∧
      (paidAccount repeatedBranchGraph).of
          (realHistory repeatedBranchGraph 5 (SourceFrontier.start 0)) =
        Multiplicative.ofAdd 5 ∧
      (realTrace repeatedBranchGraph 1 (SourceFrontier.start 0)).length = 1 ∧
      (paidAccount repeatedBranchGraph).of
          (realHistory repeatedBranchGraph 1 (SourceFrontier.start 0)) =
        Multiplicative.ofAdd 3 ∧
      (realTrace repeatedBranchGraph 2 repeatedBranchExpanded).length = 2 ∧
      (paidAccount repeatedBranchGraph).of
          (realHistory repeatedBranchGraph 2 repeatedBranchExpanded) =
        Multiplicative.ofAdd 2 ∧
      (paidAccount repeatedBranchGraph).of
          ((realHistory repeatedBranchGraph 1 (SourceFrontier.start 0)).comp
            (realHistory repeatedBranchGraph 2 repeatedBranchExpanded)) =
        Multiplicative.ofAdd 5 := by
  simp only [paid_resume]
  decide

/-- One index past the three accepted steps is not a history.
Closing the frontier does not add an occurrence. -/
theorem repeated_branch_extra_index_is_not_a_history :
    ¬ ∃ (target : SourceFrontier)
        (history : History (machine repeatedBranchGraph) (SourceFrontier.start 0) target),
      indices (machine repeatedBranchGraph) history = [0, 0, 0, 0] := by
  intro ⟨target, history, same⟩
  have accepted := follow_indices (machine repeatedBranchGraph) history
  rw [same] at accepted
  have none := repeated_branch_erased_diary.2.2.1
  rw [none] at accepted
  cases accepted

/-- The repeated successor stays two index `0` events in the composite arrow. -/
theorem repeated_branch_history_arrow_splits :
    realTrace repeatedBranchGraph 1 (SourceFrontier.start 0) = [0] ∧
      realTrace repeatedBranchGraph 2
        ((SourceFrontier.start 0).resume repeatedBranchGraph 1) = [0, 0] ∧
      indices (machine repeatedBranchGraph)
        (realHistory repeatedBranchGraph (1 + 2) (SourceFrontier.start 0)) = [0, 0, 0] ∧
      HEq (realHistory repeatedBranchGraph (1 + 2) (SourceFrontier.start 0))
        ((realHistory repeatedBranchGraph 1 (SourceFrontier.start 0)).comp
          (realHistory repeatedBranchGraph 2
            ((SourceFrontier.start 0).resume repeatedBranchGraph 1))) := by
  have first : realTrace repeatedBranchGraph 1 (SourceFrontier.start 0) = [0] := by
    decide
  have second : realTrace repeatedBranchGraph 2
      ((SourceFrontier.start 0).resume repeatedBranchGraph 1) = [0, 0] := by
    decide
  refine ⟨first, second, ?_, realHistory_add repeatedBranchGraph 1 2 (SourceFrontier.start 0)⟩
  rw [indices_realHistory,
    realTrace_add repeatedBranchGraph 1 2 (SourceFrontier.start 0), first, second]
  rfl

/-- Capacity two omits one index of the three-step run, so `complete?` does
not consult `follow`. The resumed frontier and its paid account stay the
five-row completion. -/
theorem repeated_branch_truncated_interval_refuses_replay :
    realTrace repeatedBranchGraph 3 (SourceFrontier.start 0) = [0, 0, 0] ∧
      ((Prefix.initial 2).append [0, 0, 0]).omitted = 1 ∧
      ((Prefix.initial 2).append [0, 0, 0]).complete?.bind
        ((machine repeatedBranchGraph).follow (SourceFrontier.start 0)) = none ∧
      (SourceFrontier.start 0).resume repeatedBranchGraph 3 = repeatedBranchDone ∧
      repeatedBranchDone.paid = 5 ∧
      (paidAccount repeatedBranchGraph).of
          (realHistory repeatedBranchGraph 3 (SourceFrontier.start 0)) =
        Multiplicative.ofAdd 5 := by
  rw [paid_resume]
  decide

/-- A complete record of an index the run never took is not a replay.
`follow` rejects that literal trace. The paid endpoint stays five. -/
theorem repeated_branch_missing_index_refuses_replay :
    ((Prefix.initial 4).append [0, 0, 0, 0]).complete? = some [0, 0, 0, 0] ∧
      ((Prefix.initial 4).append [0, 0, 0, 0]).complete?.bind
        ((machine repeatedBranchGraph).follow (SourceFrontier.start 0)) = none ∧
      (SourceFrontier.start 0).resume repeatedBranchGraph 3 = repeatedBranchDone ∧
      repeatedBranchDone.paid = 5 := by
  decide

/-- Capacity two is chosen before the suffix run. The produced prefix checks
as `[0, 0]` from the resumed frontier and is not the original word. Capacity
zero at that same state keeps the omissions and does not decode. The paid
account is the base witness. A fresh prefix at the continuation is empty. -/
theorem repeated_branch_late_suffix_is_not_the_original_run :
    realTrace repeatedBranchGraph 2
        ((SourceFrontier.start 0).resume repeatedBranchGraph 1) = [0, 0] ∧
      realTrace repeatedBranchGraph 3 (SourceFrontier.start 0) = [0, 0, 0] ∧
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record.items =
        [0, 0] ∧
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record.omitted = 0 ∧
      checkStopped (machine repeatedBranchGraph)
          (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1 [0, 0] =
        some repeatedBranchDone ∧
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record.complete? ≠
        some [0, 0, 0] ∧
      checkStopped (machine repeatedBranchGraph)
          (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1 [0, 0, 0] = none ∧
      (machine repeatedBranchGraph).follow (SourceFrontier.start 0) [0, 0] ≠
        some repeatedBranchDone ∧
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).2.paid = 5 ∧
      (paidAccount repeatedBranchGraph).of
          (realHistory repeatedBranchGraph 2
            ((SourceFrontier.start 0).resume repeatedBranchGraph 1)) =
        Multiplicative.ofAdd 2 ∧
      (lateDiary repeatedBranchGraph 1 0 2 (SourceFrontier.start 0)).1.2.record.items = [] ∧
      (lateDiary repeatedBranchGraph 1 0 2 (SourceFrontier.start 0)).1.2.record.omitted = 2 ∧
      (lateDiary repeatedBranchGraph 1 0 2 (SourceFrontier.start 0)).1.2.record.complete? =
        none ∧
      checkStopped (machine repeatedBranchGraph)
          (lateDiary repeatedBranchGraph 1 0 2 (SourceFrontier.start 0)).1 [0, 0] = none ∧
      (lateDiary repeatedBranchGraph 1 0 2 (SourceFrontier.start 0)).2.paid = 5 ∧
      (restartRecording
          (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).2 2).record.items = [] ∧
      (restartRecording
          (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).2 2).record ≠
        (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record := by
  have suffixTrace : realTrace repeatedBranchGraph 2
      ((SourceFrontier.start 0).resume repeatedBranchGraph 1) = [0, 0] := by
    decide
  have wholeTrace : realTrace repeatedBranchGraph 3 (SourceFrontier.start 0) = [0, 0, 0] := by
    decide
  obtain ⟨_, expandedPaid, _, donePaid, _⟩ := repeated_successor_frontier_pays
  have fullRecord := late_record repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)
  have blankRecord := late_record repeatedBranchGraph 1 0 2 (SourceFrontier.start 0)
  have fullItems :
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record.items = [0, 0] := by
    rw [fullRecord.2.1, suffixTrace, Prefix.initial_items]
    rfl
  have fullOmitted :
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record.omitted = 0 := by
    rw [fullRecord.2.1, suffixTrace, Prefix.initial_omitted]
    rfl
  have fullComplete :
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record.complete? =
        some [0, 0] := by
    rw [fullRecord.2.1, suffixTrace]
    exact (Prefix.complete_iff 2 [0, 0]).mpr (Nat.le_refl _)
  have fits : (realTrace repeatedBranchGraph 2
      ((SourceFrontier.start 0).resume repeatedBranchGraph 1)).length ≤ 2 := by
    rw [suffixTrace]
    exact Nat.le_refl _
  have checkedFull := late_checked repeatedBranchGraph 1 2 2 (SourceFrontier.start 0) fits
  rw [suffixTrace, late_endpoint, ← SourceFrontier.resume_add, show (1 + 2) = 3 from rfl,
    show (SourceFrontier.start 0).resume repeatedBranchGraph 3 = repeatedBranchDone from rfl]
      at checkedFull
  have notOriginal :
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record.complete? ≠
        some [0, 0, 0] := by
    rw [fullComplete]
    decide
  have wrongWord : checkStopped (machine repeatedBranchGraph)
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1 [0, 0, 0] = none := by
    cases outcome : checkStopped (machine repeatedBranchGraph)
        (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1 [0, 0, 0] with
    | none => rfl
    | some target =>
        have records :=
          ((checkStopped_agrees (machine repeatedBranchGraph)
              (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1
              [0, 0, 0] target).mp outcome).1
        rw [fullComplete] at records
        exact absurd records (by decide)
  have notRoot : (machine repeatedBranchGraph).follow (SourceFrontier.start 0) [0, 0] ≠
      some repeatedBranchDone := by
    decide
  have fullPaid : (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).2.paid = 5 := by
    rw [late_paid, show (1 + 2) = 3 from rfl,
      show (SourceFrontier.start 0).resume repeatedBranchGraph 3 = repeatedBranchDone from rfl]
    exact donePaid
  have account : (paidAccount repeatedBranchGraph).of
      (realHistory repeatedBranchGraph 2
        ((SourceFrontier.start 0).resume repeatedBranchGraph 1)) =
      Multiplicative.ofAdd 2 := by
    rw [late_account repeatedBranchGraph 1 2 2 (SourceFrontier.start 0),
      late_paid repeatedBranchGraph 1 2 2 (SourceFrontier.start 0),
      show (1 + 2) = 3 from rfl,
      show (SourceFrontier.start 0).resume repeatedBranchGraph 3 = repeatedBranchDone from rfl,
      donePaid]
    have step : (SourceFrontier.start 0).resume repeatedBranchGraph 1 = repeatedBranchExpanded := by
      decide
    rw [step, expandedPaid]
  have blankItems :
      (lateDiary repeatedBranchGraph 1 0 2 (SourceFrontier.start 0)).1.2.record.items = [] := by
    rw [blankRecord.2.1, suffixTrace, Prefix.initial_items]
    rfl
  have blankOmitted :
      (lateDiary repeatedBranchGraph 1 0 2 (SourceFrontier.start 0)).1.2.record.omitted = 2 := by
    rw [blankRecord.2.1, suffixTrace, Prefix.initial_omitted]
    rfl
  have short : 0 < (realTrace repeatedBranchGraph 2
      ((SourceFrontier.start 0).resume repeatedBranchGraph 1)).length := by
    rw [suffixTrace]
    decide
  have truncated := late_truncated repeatedBranchGraph 1 0 2 (SourceFrontier.start 0) short
  have blankComplete :
      (lateDiary repeatedBranchGraph 1 0 2 (SourceFrontier.start 0)).1.2.record.complete? = none := by
    rw [Prefix.complete?, if_neg truncated.1]
  have blankPaid : (lateDiary repeatedBranchGraph 1 0 2 (SourceFrontier.start 0)).2.paid = 5 := by
    rw [late_paid, show (1 + 2) = 3 from rfl,
      show (SourceFrontier.start 0).resume repeatedBranchGraph 3 = repeatedBranchDone from rfl]
    exact donePaid
  have fresh := (restartRecording_excludes
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).2 2 []).1
  have restarted :
      (restartRecording (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).2 2).record ≠
        (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record := by
    intro same
    have eq := congrArg Prefix.items same
    rw [fresh, fullItems] at eq
    cases eq
  rw [suffixTrace] at truncated
  exact ⟨suffixTrace, wholeTrace, fullItems, fullOmitted, checkedFull, notOriginal, wrongWord,
    notRoot, fullPaid, account, blankItems, blankOmitted, blankComplete, truncated.2, blankPaid,
    fresh, restarted⟩

/-- The suffix checks at its recorded endpoint. A changed endpoint still has
a trace readout and fails the endpoint check. The original root, an omitted
prefix, and one dropped copy of index `0` fail the endpoint check. Equality
validates the claimed endpoint and does not authenticate the supplied root.
The verdict is not a continuation or a one-shot token. -/
theorem repeated_branch_stopped_endpoint_check :
    checkStopped (machine repeatedBranchGraph)
        (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1 [0, 0] =
        some repeatedBranchDone ∧
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.base =
        repeatedBranchDone ∧
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record.items =
        [0, 0] ∧
      checkStoppedTrace (machine repeatedBranchGraph)
          ((SourceFrontier.start 0).resume repeatedBranchGraph 1,
            ⟨SourceFrontier.start 0,
              (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record⟩)
          [0, 0] = some repeatedBranchDone ∧
      checkStopped (machine repeatedBranchGraph)
          ((SourceFrontier.start 0).resume repeatedBranchGraph 1,
            ⟨SourceFrontier.start 0,
              (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record⟩)
          [0, 0] = none ∧
      checkStopped (machine repeatedBranchGraph)
          (SourceFrontier.start 0,
            (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2) [0, 0] =
        none ∧
      checkStopped (machine repeatedBranchGraph)
          (lateDiary repeatedBranchGraph 1 0 2 (SourceFrontier.start 0)).1 [0, 0] = none ∧
      checkStopped (machine repeatedBranchGraph)
          (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1 [0] = none ∧
      (machine repeatedBranchGraph).follow
          ((SourceFrontier.start 0).resume repeatedBranchGraph 1) [0] ≠
        some repeatedBranchDone := by
  have suffixTrace : realTrace repeatedBranchGraph 2
      ((SourceFrontier.start 0).resume repeatedBranchGraph 1) = [0, 0] := by
    decide
  have fits : (realTrace repeatedBranchGraph 2
      ((SourceFrontier.start 0).resume repeatedBranchGraph 1)).length ≤ 2 := by
    rw [suffixTrace]
    exact Nat.le_refl _
  have checked := late_checked repeatedBranchGraph 1 2 2 (SourceFrontier.start 0) fits
  rw [suffixTrace, late_endpoint, ← SourceFrontier.resume_add, show (1 + 2) = 3 from rfl,
    show (SourceFrontier.start 0).resume repeatedBranchGraph 3 = repeatedBranchDone from rfl]
      at checked
  have agreed := (checkStopped_agrees (machine repeatedBranchGraph)
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1 [0, 0]
      repeatedBranchDone).mp checked
  have endpoint :
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.base =
        repeatedBranchDone := agreed.2.2.symm
  have items :
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record.items =
        [0, 0] := by
    rw [(late_record repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).2.1, suffixTrace,
      Prefix.initial_items]
    rfl
  have stored :
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record.complete? =
        some [0, 0] := by
    rw [(late_record repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).2.1, suffixTrace]
    exact (Prefix.complete_iff 2 [0, 0]).mpr (Nat.le_refl _)
  have followed := agreed.2.1
  rw [(late_record repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1] at followed
  have tracedForged : checkStoppedTrace (machine repeatedBranchGraph)
      ((SourceFrontier.start 0).resume repeatedBranchGraph 1,
        ⟨SourceFrontier.start 0,
          (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record⟩)
      [0, 0] = some repeatedBranchDone :=
    (checkStoppedTrace_agrees (machine repeatedBranchGraph) _ [0, 0] repeatedBranchDone).mpr
      ⟨stored, followed⟩
  have changed : repeatedBranchDone ≠ SourceFrontier.start 0 := by
    decide
  have forgedRefused := checkStopped_rejects_endpoint (machine repeatedBranchGraph)
      ((SourceFrontier.start 0).resume repeatedBranchGraph 1,
        ⟨SourceFrontier.start 0,
          (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2.record⟩)
      [0, 0] repeatedBranchDone tracedForged changed
  have notRoot : (machine repeatedBranchGraph).follow (SourceFrontier.start 0) [0, 0] ≠
      some repeatedBranchDone := by
    decide
  have wrongRoot : checkStopped (machine repeatedBranchGraph)
      (SourceFrontier.start 0,
        (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2) [0, 0] = none := by
    cases outcome : checkStopped (machine repeatedBranchGraph)
        (SourceFrontier.start 0,
          (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1.2) [0, 0] with
    | none => rfl
    | some target =>
        have rootAgreed := (checkStopped_agrees (machine repeatedBranchGraph) _
            [0, 0] target).mp outcome
        have targetDone : target = repeatedBranchDone := by
          rw [← endpoint]
          exact rootAgreed.2.2
        rw [targetDone] at rootAgreed
        exact False.elim (notRoot rootAgreed.2.1)
  have short : 0 < (realTrace repeatedBranchGraph 2
      ((SourceFrontier.start 0).resume repeatedBranchGraph 1)).length := by
    rw [suffixTrace]
    decide
  have omitted := late_truncated repeatedBranchGraph 1 0 2 (SourceFrontier.start 0) short
  rw [suffixTrace] at omitted
  have dropped : checkStopped (machine repeatedBranchGraph)
      (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1 [0] = none := by
    cases outcome : checkStopped (machine repeatedBranchGraph)
        (lateDiary repeatedBranchGraph 1 2 2 (SourceFrontier.start 0)).1 [0] with
    | none => rfl
    | some target =>
        have one := (checkStopped_agrees (machine repeatedBranchGraph) _
            [0] target).mp outcome
        rw [stored] at one
        exact False.elim (absurd one.1 (by decide))
  have oneStep : (machine repeatedBranchGraph).follow
      ((SourceFrontier.start 0).resume repeatedBranchGraph 1) [0] ≠
      some repeatedBranchDone := by
    decide
  exact ⟨checked, endpoint, items, tracedForged, forgedRefused, wrongRoot, omitted.2, dropped,
    oneStep⟩

/-- One pass records the three index-`0` expansions in order. Capacity zero
still carries a prefix: it omits those positions and reaches the same paid
endpoint. Both recorded accounts are the five-row base difference. -/
theorem repeated_branch_recorded_run :
    recordedRun repeatedBranchGraph 3
        ⟨SourceFrontier.start 0, Prefix.initial 3⟩ =
      ⟨repeatedBranchDone, (Prefix.initial 3).append [0, 0, 0]⟩ ∧
    ((Prefix.initial 3).append [0, 0, 0]).items = [0, 0, 0] ∧
    ((Prefix.initial 3).append [0, 0, 0]).omitted = 0 ∧
    ((Prefix.initial 3).append [0, 0, 0]).complete?.bind
        ((machine repeatedBranchGraph).follow (SourceFrontier.start 0)) =
      some repeatedBranchDone ∧
    recordedRun repeatedBranchGraph 3
        ⟨SourceFrontier.start 0, Prefix.initial 0⟩ =
      ⟨repeatedBranchDone, (Prefix.initial 0).append [0, 0, 0]⟩ ∧
    ((Prefix.initial 0).append [0, 0, 0]).items = [] ∧
    ((Prefix.initial 0).append [0, 0, 0]).omitted = 3 ∧
    ((Prefix.initial 0).append [0, 0, 0]).complete? = none ∧
    (eventAccount (recordedMachine (machine repeatedBranchGraph)) (recordedEdge (·.paid))).of
        (ofTrace (recordedMachine (machine repeatedBranchGraph))
          (realTrace repeatedBranchGraph 3 (SourceFrontier.start 0))
          (recordedFrontier_follow repeatedBranchGraph 3 (SourceFrontier.start 0)
            (Prefix.initial 3))) =
      Multiplicative.ofAdd 5 ∧
    (eventAccount (recordedMachine (machine repeatedBranchGraph)) (recordedEdge (·.paid))).of
        (ofTrace (recordedMachine (machine repeatedBranchGraph))
          (realTrace repeatedBranchGraph 3 (SourceFrontier.start 0))
          (recordedFrontier_follow repeatedBranchGraph 3 (SourceFrontier.start 0)
            (Prefix.initial 0))) =
      Multiplicative.ofAdd 5 := by
  obtain ⟨trace, _, _, resumed, five, _⟩ :=
    repeated_branch_truncated_interval_refuses_replay
  have fullRun := recordedRun_frontier repeatedBranchGraph 3 (SourceFrontier.start 0)
    (Prefix.initial 3)
  have blankRun := recordedRun_frontier repeatedBranchGraph 3 (SourceFrontier.start 0)
    (Prefix.initial 0)
  rw [trace, resumed] at fullRun blankRun
  have replay := frontier_interval_replays repeatedBranchGraph 3 (SourceFrontier.start 0)
  rw [trace, resumed] at replay
  have fullAccount := frontier_recorded_account repeatedBranchGraph 3
    (SourceFrontier.start 0) (Prefix.initial 3)
  have blankAccount := frontier_recorded_account repeatedBranchGraph 3
    (SourceFrontier.start 0) (Prefix.initial 0)
  refine ⟨fullRun, ?_, ?_, replay, blankRun, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Prefix.initial_items]
    rfl
  · rw [Prefix.initial_omitted]
    rfl
  · rw [Prefix.initial_items]
    rfl
  · rw [Prefix.initial_omitted]
    rfl
  · have lost : ((Prefix.initial 0).append [0, 0, 0]).omitted ≠ 0 := by
      rw [Prefix.initial_omitted]
      decide
    rw [Prefix.complete?, if_neg lost]
  · rw [fullAccount, resumed, five, SourceFrontier.start, Nat.sub_zero]
  · rw [blankAccount, resumed, five, SourceFrontier.start, Nat.sub_zero]

end Controls

end SourceFrontierMachine

/-! The unequal-length lowering is an existing consumer. A complete record
exposes `follow` only for the declared interval from its recorded start.
`follow` is that pure replay, not an authority to advance the live runtime.
`forward_realization_allows_extra_answer` remains the unauthorized-edge
negative. -/

namespace LoweringReplay

open Mettapedia.GSLT.Causality.OccurrenceMachineHistory
open Mettapedia.GSLT.Causality.OccurrenceMachineHistory.LoweringControls

/-- The implementing indices `[0, 0]` are a complete replay from the target
root. The source occurrence stays the separate certificate `[0]`. -/
theorem implementing_interval_replays :
    indices (target false) ((lowering false).histories.map duplicateFirst) = [0, 0] ∧
      ((Prefix.initial 2).append [0, 0]).complete?.bind
        ((target false).follow .root) = some .done :=
  ⟨(distinct_implementing_paths false).1,
    (complete_bounded_history (target false) .root 2 [0, 0] .done).mpr
      ⟨Nat.le_refl _, implementing_paths_replay.1⟩⟩

/-- Capacity one omits the commit index. The retained item is the preparation
step, and the complete replay is refused. -/
theorem truncated_interval_stops_at_preparation :
    indices (target false) ((lowering false).histories.map duplicateFirst) = [0, 0] ∧
      ((Prefix.initial 1).append [0, 0]).omitted = 1 ∧
      ((Prefix.initial 1).append [0, 0]).complete?.bind
        ((target false).follow .root) = none ∧
      ((Prefix.initial 1).append [0, 0]).items = [0] ∧
      (target false).follow .root [0] = some .prepared := by
  refine ⟨(distinct_implementing_paths false).1, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide

/-- A complete record of the missing index `2` does not replay.
`missing_occurrence_rejected` is that refusal for a history to `done`. -/
theorem missing_index_refuses_replay :
    ((Prefix.initial 1).append [2]).complete?.bind
        (OccurrenceMachineCore.duplicateExample.follow .root) = none ∧
      ¬ ∃ history : History OccurrenceMachineCore.duplicateExample .root .done,
        indices OccurrenceMachineCore.duplicateExample history = [2] := by
  refine ⟨?_, missing_occurrence_rejected⟩
  · decide

/-- The source certificate `[0]` completes to `done` on the source machine
and reaches preparation on the target. -/
theorem source_interval_is_not_target_replay :
    ((Prefix.initial 1).append [0]).complete?.bind
        (OccurrenceMachineCore.duplicateExample.follow .root) = some .done ∧
      ((Prefix.initial 1).append [0]).complete?.bind
        ((target false).follow .root) = some .prepared := by
  decide

/-- A complete suffix from preparation reaches `done`. That record is not
the implementing interval `[0, 0]`. -/
theorem late_suffix_is_not_the_implementing_interval :
    ((Prefix.initial 1).append [0]).complete?.bind
        ((target false).follow .prepared) = some .done ∧
      ((Prefix.initial 1).append [0]).complete? ≠ some [0, 0] ∧
      indices (target false) ((lowering false).histories.map duplicateFirst) = [0, 0] := by
  refine ⟨?_, ?_, (distinct_implementing_paths false).1⟩
  · decide
  · decide

end LoweringReplay

end Mettapedia.Machines.ExecutionHistoryReadout
