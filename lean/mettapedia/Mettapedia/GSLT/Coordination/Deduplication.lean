import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Commits
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Finset.Basic

/-!
# Exactly-once effects from at-least-once delivery

## Deduplication by identifier

**Fault model.** A sender keeps a durable outbox of messages with distinct identifiers and
retransmits; the network delivers outbox messages late, reordered and any number of times, and
delivers nothing else (`deliveries ⊆ outbox`). The receiver keeps the identifiers it has applied,
in the same atomic step as the effect.

* **At most once** (`applied_nodup`): no identifier is applied twice.
* **Exactly what was delivered** (`mem_applied`): an identifier is applied exactly when it was
  delivered at least once.
* **Exactly once** (`exactly_once`): when every outbox message is delivered at least once, the
  applied log is a permutation of the outbox: an atomic exactly-once delivery in some order.
* Without the check a repeated delivery is applied twice (`Controls.blind_applies_twice`).

## Content identity is not occurrence identity

Keying by content is right for facts, whose effects are idempotent, and wrong for linear
occurrences: two payments with equal content are two occurrences, each taken once, while a store
that identified them by content holds one and loses a take (`Controls.hashcons_loses_take`).

## Idempotent effects

When effects commute and are idempotent, at-least-once execution reaches the exactly-once state
with no record of identifiers at all (`idempotent_dedup`, `idempotent_same_set`). Inserting an
occurrence keyed by its identifier into a store is such an effect (`Controls.keyed_insert`); this
is how keyed mail is exactly once. A counter increment is not (`Controls.increment_not_idempotent`).

## Durable continuations: unknown is never rerun

An activity is begun (recorded durably), its external effect is called, and it is finished. A
crash loses the volatile record of what was called. On recovery an activity that was begun and not
finished can be

* marked **unknown** and never called again: each activity's external effect happens at most once,
  for every sequence of begins, calls, finishes, crashes and recoveries
  (`unknownRule_at_most_once`);
* **rerun blindly**: its effect can happen twice (`Controls.blind_rerun_twice`);
* rerun with the activity identifier as the **idempotence key** at the external resource: the
  resource applies each activity once however often it is called (`keyed_rerun_at_most_once`), and
  the rerun can finish the activity (`Controls.keyed_rerun_finishes`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.Deduplication

universe u v

/-! ## Deduplication by identifier -/

section Dedup

variable {I : Type u} [DecidableEq I]

/-- The receiver: identifiers seen, and the applied log. -/
structure Receiver (I : Type u) where
  seen : Finset I
  applied : List I

/-- Receive one delivery: apply it unless its identifier was seen, recording it in the same step. -/
def receive (r : Receiver I) (id : I) : Receiver I :=
  if id ∈ r.seen then r else ⟨insert id r.seen, r.applied ++ [id]⟩

/-- Receive a sequence of deliveries. -/
def receiveAll (r : Receiver I) (deliveries : List I) : Receiver I := deliveries.foldl receive r

/-- The receiver's invariant: the seen identifiers are exactly the applied ones, each once. -/
structure Inv (r : Receiver I) : Prop where
  nodup : r.applied.Nodup
  seen_iff : ∀ id, id ∈ r.seen ↔ id ∈ r.applied

theorem inv_receive {r : Receiver I} (inv : Inv r) (id : I) : Inv (receive r id) := by
  unfold receive
  split_ifs with seen
  · exact inv
  · refine ⟨List.nodup_append.mpr ⟨inv.nodup, List.nodup_singleton id, fun a inA b inB same => ?_⟩,
      fun x => ?_⟩
    · rw [List.mem_singleton] at inB
      subst inB; subst same
      exact seen ((inv.seen_iff a).mpr inA)
    · simp only [Finset.mem_insert, List.mem_append, List.mem_singleton, inv.seen_iff]
      tauto

theorem inv_receiveAll {r : Receiver I} (inv : Inv r) (deliveries : List I) :
    Inv (receiveAll r deliveries) := by
  induction deliveries generalizing r with
  | nil => exact inv
  | cons d rest ih => exact ih (inv_receive inv d)

/-- The empty receiver. -/
def Receiver.empty : Receiver I := ⟨∅, []⟩

omit [DecidableEq I] in
theorem inv_empty : Inv (Receiver.empty : Receiver I) := ⟨List.nodup_nil, fun _ => by simp [Receiver.empty]⟩

/-- **At most once.** -/
theorem applied_nodup (deliveries : List I) : (receiveAll Receiver.empty deliveries).applied.Nodup :=
  (inv_receiveAll inv_empty deliveries).nodup

theorem mem_receiveAll_seen (r : Receiver I) (deliveries : List I) (id : I) :
    id ∈ (receiveAll r deliveries).seen ↔ id ∈ r.seen ∨ id ∈ deliveries := by
  induction deliveries generalizing r with
  | nil => simp [receiveAll]
  | cons d rest ih =>
      simp only [receiveAll, List.foldl_cons] at ih ⊢
      rw [ih]
      unfold receive
      split_ifs with seen
      · simp only [List.mem_cons]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | rfl | h)
          · exact Or.inl h
          · exact Or.inl seen
          · exact Or.inr h
      · simp only [Finset.mem_insert, List.mem_cons]
        tauto

/-- **Exactly what was delivered is applied.** -/
theorem mem_applied (deliveries : List I) (id : I) :
    id ∈ (receiveAll Receiver.empty deliveries).applied ↔ id ∈ deliveries := by
  rw [← ((inv_receiveAll inv_empty deliveries).seen_iff id), mem_receiveAll_seen]
  simp [Receiver.empty]

/-- **Exactly once**: when every outbox message is delivered at least once and nothing else is
delivered, the applied log is a permutation of the outbox. -/
theorem exactly_once {outbox deliveries : List I} (distinct : outbox.Nodup)
    (atLeastOnce : ∀ id ∈ outbox, id ∈ deliveries) (onlyOutbox : ∀ id ∈ deliveries, id ∈ outbox) :
    (receiveAll Receiver.empty deliveries).applied.Perm outbox :=
  (List.perm_ext_iff_of_nodup (applied_nodup deliveries) distinct).mpr fun id => by
    rw [mem_applied]
    exact ⟨onlyOutbox id, atLeastOnce id⟩

end Dedup

/-! ## Idempotent effects -/

section Idempotent

variable {S : Type u} {I : Type v} [DecidableEq I]

/-- Apply the effects of a delivery sequence. -/
def applyAll (effect : I → S → S) (state : S) (deliveries : List I) : S :=
  deliveries.foldl (fun s id => effect id s) state

/-- Effects commute pairwise and each is idempotent. -/
structure CommutingIdempotent (effect : I → S → S) : Prop where
  comm : ∀ a b s, effect a (effect b s) = effect b (effect a s)
  idem : ∀ a s, effect a (effect a s) = effect a s

omit [DecidableEq I] in
theorem applyAll_perm {effect : I → S → S} (laws : CommutingIdempotent effect) {first second : List I}
    (perm : first.Perm second) (state : S) :
    applyAll effect state first = applyAll effect state second :=
  perm.foldl_eq' (fun x _ y _ z => laws.comm y x z) state

/-- **With commuting idempotent effects, repeated deliveries change nothing**: applying a delivery
sequence equals applying it with duplicates removed. -/
theorem idempotent_dedup {effect : I → S → S} (laws : CommutingIdempotent effect)
    (deliveries : List I) (state : S) :
    applyAll effect state deliveries = applyAll effect state deliveries.dedup := by
  induction deliveries generalizing state with
  | nil => rfl
  | cons d rest ih =>
      by_cases repeated : d ∈ rest
      · rw [List.dedup_cons_of_mem repeated]
        show applyAll effect (effect d state) rest = _
        rw [← ih]
        -- move the repeated `d` next to the first one
        have perm := List.perm_cons_erase repeated
        rw [applyAll_perm laws perm, applyAll_perm laws perm]
        show applyAll effect (effect d (effect d state)) _ = applyAll effect (effect d state) _
        rw [laws.idem]
      · rw [List.dedup_cons_of_notMem repeated]
        exact ih (effect d state)

/-- **Same identifiers, same state**: two delivery sequences with the same identifiers reach the
same state, so at-least-once delivery of an outbox reaches the exactly-once state. -/
theorem idempotent_same_set {effect : I → S → S} (laws : CommutingIdempotent effect)
    {first second : List I} (same : ∀ id, id ∈ first ↔ id ∈ second) (state : S) :
    applyAll effect state first = applyAll effect state second := by
  rw [idempotent_dedup laws first, idempotent_dedup laws second]
  exact applyAll_perm laws ((List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)).mpr
    fun id => by simp [List.mem_dedup, same id]) state

end Idempotent

/-! ## Durable continuations -/

section Continuations

variable {A : Type u} [DecidableEq A]

/-- The durable status of an activity. -/
inductive Status where
  | absent
  | begun
  | finished
  | unknown
  deriving DecidableEq, Repr

/-- The activity runner: durable statuses, the volatile record of calls made since the last
restart, and the effects the outside world has seen. -/
structure Runner (A : Type u) where
  status : A → Status
  called : Finset A
  external : List A

/-- What a recovery does with an activity begun and not finished. -/
inductive Recovery where
  | markUnknown
  | rerun
  deriving DecidableEq

/-- Runner events. -/
inductive RunnerEvent (A : Type u) where
  | begin (a : A)
  | call (a : A)
  | finish (a : A)
  | crash

/-- One runner event. A crash loses the volatile record and recovers by the policy. -/
def runnerStep (policy : Recovery) (r : Runner A) : RunnerEvent A → Runner A
  | .begin a => if r.status a = .absent then { r with status := Function.update r.status a .begun } else r
  | .call a =>
      if r.status a = .begun ∧ a ∉ r.called then
        { r with called := insert a r.called, external := r.external ++ [a] }
      else r
  | .finish a =>
      if r.status a = .begun ∧ a ∈ r.called then
        { r with status := Function.update r.status a .finished }
      else r
  | .crash =>
      match policy with
      | .markUnknown =>
          { status := fun a => if r.status a = .begun then .unknown else r.status a,
            called := ∅, external := r.external }
      | .rerun => { r with called := ∅ }

/-- A run of the runner. -/
def runRunner (policy : Recovery) (r : Runner A) : List (RunnerEvent A) → Runner A
  | [] => r
  | e :: es => runRunner policy (runnerStep policy r e) es

/-- A fresh runner. -/
def Runner.fresh : Runner A := ⟨fun _ => .absent, ∅, []⟩

/-- Under the unknown rule: effects are distinct; an absent activity has no effect; an activity
called in this life is not absent; a begun activity's effect was seen outside exactly when it was
called in this life. -/
structure UnknownInv (r : Runner A) : Prop where
  nodup : r.external.Nodup
  absentNone : ∀ a, r.status a = .absent → a ∉ r.external
  calledPresent : ∀ a ∈ r.called, r.status a ≠ .absent
  begunCalled : ∀ a, r.status a = .begun → (a ∈ r.external ↔ a ∈ r.called)

theorem unknownInv_step {r : Runner A} (inv : UnknownInv r) (e : RunnerEvent A) :
    UnknownInv (runnerStep .markUnknown r e) := by
  cases e with
  | begin a =>
      simp only [runnerStep]
      split_ifs with isAbsent
      · refine ⟨inv.nodup, fun x h => ?_, fun x member => ?_, fun x h => ?_⟩
        · by_cases same : x = a
          · subst same; simp at h
          · simp only [Function.update_of_ne same] at h; exact inv.absentNone x h
        · by_cases same : x = a
          · subst same; simp
          · simp only [Function.update_of_ne same]; exact inv.calledPresent x member
        · by_cases same : x = a
          · subst same
            have notExternal := inv.absentNone x isAbsent
            have notCalled : x ∉ r.called := fun member => inv.calledPresent x member isAbsent
            exact ⟨fun ext => absurd ext notExternal, fun called => absurd called notCalled⟩
          · simp only [Function.update_of_ne same] at h ⊢; exact inv.begunCalled x h
      · exact inv
  | call a =>
      simp only [runnerStep]
      split_ifs with ok
      · obtain ⟨isBegun, notCalled⟩ := ok
        have notExternal : a ∉ r.external := fun ext => notCalled ((inv.begunCalled a isBegun).mp ext)
        refine ⟨List.nodup_append.mpr ⟨inv.nodup, List.nodup_singleton a,
            fun x inX y inY same => ?_⟩, fun x h => ?_, fun x member => ?_, fun x h => ?_⟩
        · rw [List.mem_singleton] at inY; subst inY; subst same; exact notExternal inX
        · have := inv.absentNone x h
          simp only [List.mem_append, List.mem_singleton, not_or]
          refine ⟨this, fun same => ?_⟩
          subst same; rw [isBegun] at h; cases h
        · rcases Finset.mem_insert.mp member with rfl | old
          · rw [isBegun]; exact fun h => by cases h
          · exact inv.calledPresent x old
        · simp only [List.mem_append, List.mem_singleton, Finset.mem_insert]
          have := inv.begunCalled x h
          tauto
      · exact inv
  | finish a =>
      simp only [runnerStep]
      split_ifs with ok
      · refine ⟨inv.nodup, fun x h => ?_, fun x member => ?_, fun x h => ?_⟩
        · by_cases same : x = a
          · subst same; simp at h
          · simp only [Function.update_of_ne same] at h; exact inv.absentNone x h
        · by_cases same : x = a
          · subst same; simp
          · simp only [Function.update_of_ne same]; exact inv.calledPresent x member
        · by_cases same : x = a
          · subst same; simp at h
          · simp only [Function.update_of_ne same] at h; exact inv.begunCalled x h
      · exact inv
  | crash =>
      simp only [runnerStep]
      refine ⟨inv.nodup, fun x h => ?_, fun x member => by simp at member, fun x h => ?_⟩
      · dsimp only at h ⊢
        by_cases wasBegun : r.status x = .begun
        · simp [wasBegun] at h
        · simp only [wasBegun, if_false] at h
          exact inv.absentNone x h
      · dsimp only at h ⊢
        by_cases wasBegun : r.status x = .begun
        · simp [wasBegun] at h
        · simp only [wasBegun, if_false] at h

omit [DecidableEq A] in
theorem unknownInv_fresh : UnknownInv (Runner.fresh : Runner A) :=
  ⟨List.nodup_nil, fun _ _ => by simp [Runner.fresh], fun _ member => by simp [Runner.fresh] at member,
    fun _ h => by simp [Runner.fresh] at h⟩

/-- **Unknown is never rerun**: under the unknown rule, every activity's external effect happens
at most once, for every sequence of begins, calls, finishes, crashes and recoveries. -/
theorem unknownRule_at_most_once (events : List (RunnerEvent A)) :
    (runRunner .markUnknown Runner.fresh events).external.Nodup := by
  suffices ∀ r : Runner A, UnknownInv r → UnknownInv (runRunner .markUnknown r events) from
    (this _ unknownInv_fresh).nodup
  induction events with
  | nil => exact fun _ inv => inv
  | cons e rest ih => exact fun r inv => ih _ (unknownInv_step inv e)

/-- **Rerun keyed by the activity**: the external resource receives the runner's calls, repeated
after reruns, and applies each activity once: deduplication by identifier. -/
theorem keyed_rerun_at_most_once (events : List (RunnerEvent A)) :
    (receiveAll Receiver.empty (runRunner .rerun Runner.fresh events).external).applied.Nodup :=
  applied_nodup _

end Continuations

/-! ## Controls -/

namespace Controls

/-- A receiver that applies every delivery. -/
def blind (applied : List ℕ) (id : ℕ) : List ℕ := applied ++ [id]

/-- **Without the check a repeated delivery is applied twice.** -/
theorem blind_applies_twice :
    [1, 1].foldl blind [] = [1, 1] ∧ (receiveAll Receiver.empty [1, 1]).applied = [1] := by
  decide

/-- Inserting a keyed occurrence. -/
theorem keyed_insert : CommutingIdempotent (fun (id : ℕ) (store : Finset ℕ) => insert id store) :=
  ⟨fun a b s => Finset.insert_comm a b s, fun a s => by simp⟩

/-- **Keyed mail is exactly once by idempotence**: event `7` delivered three times and event `8`
once reach the store of one delivery each. -/
theorem keyed_mail_exactly_once :
    applyAll (fun (id : ℕ) (store : Finset ℕ) => insert id store) ∅ [7, 8, 7, 7] =
      applyAll (fun (id : ℕ) (store : Finset ℕ) => insert id store) ∅ [8, 7] :=
  idempotent_same_set keyed_insert (fun id => by simp; tauto) ∅

/-- **A counter increment is not idempotent**: a repeated delivery counts twice. -/
theorem increment_not_idempotent :
    ¬ CommutingIdempotent (fun (_ : ℕ) (count : ℕ) => count + 1) ∧
      applyAll (fun (_ : ℕ) (count : ℕ) => count + 1) 0 [7, 7] = 2 := by
  refine ⟨fun laws => ?_, rfl⟩
  have := laws.idem 7 0
  simp at this

/-- **A blind rerun calls twice**: activity `0` is begun and called, the runner crashes, and the
rerun calls it again. -/
theorem blind_rerun_twice :
    (runRunner .rerun Runner.fresh [.begin 0, .call 0, .crash, .call 0]).external = [0, 0] := by
  decide

/-- **Under the unknown rule the same events call once**, and the activity stays unknown: it is
never finished without a further decision. -/
theorem unknown_blocks :
    (runRunner .markUnknown Runner.fresh [.begin 0, .call 0, .crash, .call 0, .finish 0]).external = [0] ∧
      (runRunner .markUnknown Runner.fresh [.begin 0, .call 0, .crash, .call 0, .finish 0]).status 0 =
        .unknown := by
  decide

/-- **Keyed rerun finishes**: the rerun calls again, finishes, and the resource applied the
activity once. -/
theorem keyed_rerun_finishes :
    (runRunner .rerun Runner.fresh [.begin 0, .call 0, .crash, .call 0, .finish 0]).status 0 =
        .finished ∧
      (receiveAll Receiver.empty
        (runRunner .rerun Runner.fresh [.begin 0, .call 0, .crash, .call 0, .finish 0]).external).applied =
        [0] := by
  decide

section Identity

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

/-- Every occurrence of this control carries the same content: one payment. -/
def payment : ℕ → Unit := fun _ => ()

/-- Take occurrence `n`. -/
def takePayment (n : ℕ) : Commit ℕ Unit := ⟨{n}, ∅, ∅, []⟩

/-- **Hash-consing loses a take**: occurrences `1` and `2` carry equal content, and as occurrences
both can be taken, one after the other; identified by content they are one payment, and after one
take nothing is left. -/
theorem hashcons_loses_take :
    labels payment ({1, 2} : Finset ℕ) = {(), ()} ∧
      Enabled payment ({1, 2} : Finset ℕ) (takePayment 1) ∧
      Enabled payment (fire ({1, 2} : Finset ℕ) (takePayment 1)) (takePayment 2) ∧
      (({1, 2} : Finset ℕ).image payment).erase () = ∅ := by
  refine ⟨by decide, ⟨by decide, by decide, by decide, by decide, by simp [takePayment]⟩,
    ⟨by decide, by decide, by decide, by decide, by simp [takePayment]⟩, by decide⟩

end Identity

end Controls

end Mettapedia.GSLT.Coordination.Deduplication
