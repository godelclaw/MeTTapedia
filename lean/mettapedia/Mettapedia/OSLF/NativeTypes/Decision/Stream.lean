import Mathlib.Data.List.Enum

/-!
# Delayed finite work with exact continuation cursors

A pause performs one suspended inspection; a yield retains one ordered
answer. Neither running nor checking closure computes the complete stream.
Flattening and the total work bound are separate exhaustive operations used
to prove coverage. Mapping preserves answer ordinals independently of pauses.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Scheduling

universe u v

inductive Stream (Item : Type u) where
  | done
  | pause (next : Unit → Stream Item)
  | yield (item : Item) (next : Unit → Stream Item)

namespace Stream

def flatten {Item : Type u} : Stream Item → List Item
  | .done => []
  | .pause next => flatten (next ())
  | .yield item next => item :: flatten (next ())

def workBound {Item : Type u} : Stream Item → Nat
  | .done => 0
  | .pause next => 1 + workBound (next ())
  | .yield _item next => 1 + workBound (next ())

def append {Item : Type u} (first : Stream Item) (second : Unit → Stream Item) : Stream Item :=
  match first with
  | .done => .pause second
  | .pause next => .pause (fun _ => append (next ()) second)
  | .yield item next => .yield item (fun _ => append (next ()) second)

theorem flatten_append {Item : Type u} (first : Stream Item) (second : Unit → Stream Item) :
    (first.append second).flatten = first.flatten ++ (second ()).flatten := by
  induction first with
  | done => rfl
  | pause next ih => exact ih ()
  | yield item next ih => exact congrArg (List.cons item) (ih ())

def ofList {Item : Type u} : List Item → Stream Item
  | [] => .done
  | item :: rest => .yield item (fun _ => ofList rest)

theorem flatten_ofList {Item : Type u} (items : List Item) : (ofList items).flatten = items := by
  induction items with
  | nil => rfl
  | cons item rest ih => exact congrArg (List.cons item) ih

def mapIdx {Item : Type u} {Result : Type v} (transform : Item → Nat → Result)
    (stream : Stream Item) (ordinal : Nat := 0) : Stream Result :=
  match stream with
  | .done => .done
  | .pause next => .pause (fun _ => mapIdx transform (next ()) ordinal)
  | .yield item next => .yield (transform item ordinal)
      (fun _ => mapIdx transform (next ()) (ordinal + 1))

def mapFrom {Item : Type u} {Result : Type v} (transform : Item → Nat → Result) :
    List Item → Nat → List Result
  | [], _ordinal => []
  | item :: rest, ordinal => transform item ordinal :: mapFrom transform rest (ordinal + 1)

theorem flatten_mapIdx {Item : Type u} {Result : Type v} (transform : Item → Nat → Result)
    (stream : Stream Item) (ordinal : Nat) :
    (mapIdx transform stream ordinal).flatten = mapFrom transform stream.flatten ordinal := by
  induction stream generalizing ordinal with
  | done => rfl
  | pause next ih => exact ih () ordinal
  | yield item next ih => exact congrArg (List.cons (transform item ordinal)) (ih () (ordinal + 1))

theorem mapFrom_zipIdx {Item : Type u} {Result : Type v} (transform : Item → Nat → Result)
    (items : List Item) (ordinal : Nat) :
    mapFrom transform items ordinal = (items.zipIdx ordinal).map (fun (item, index) => transform item index) := by
  induction items generalizing ordinal with
  | nil => rfl
  | cons item rest ih => simp only [mapFrom, List.zipIdx_cons, List.map_cons, ih]

theorem flatten_mapIdx_zero {Item : Type u} {Result : Type v} (transform : Item → Nat → Result)
    (stream : Stream Item) :
    (mapIdx transform stream).flatten = stream.flatten.zipIdx.map (fun (item, ordinal) => transform item ordinal) := by
  rw [flatten_mapIdx, mapFrom_zipIdx]

end Stream

structure Cursor (Item : Type u) where
  pending : Stream Item
  reversed : List Item

def Cursor.outputs {Item : Type u} (cursor : Cursor Item) : List Item := cursor.reversed.reverse

def Cursor.closed {Item : Type u} (cursor : Cursor Item) : Bool :=
  match cursor.pending with
  | .done => true
  | .pause _ | .yield _ _ => false

def start {Item : Type u} (stream : Stream Item) : Cursor Item := ⟨stream, []⟩

def advance {Item : Type u} (cursor : Cursor Item) : Cursor Item :=
  match cursor.pending with
  | .done => cursor
  | .pause next => ⟨next (), cursor.reversed⟩
  | .yield item next => ⟨next (), item :: cursor.reversed⟩

def resume {Item : Type u} : Nat → Cursor Item → Cursor Item
  | 0, cursor => cursor
  | more + 1, cursor => resume more (advance cursor)

def run {Item : Type u} (stream : Stream Item) (budget : Nat) : Cursor Item := resume budget (start stream)

theorem resume_add {Item : Type u} (first more : Nat) (cursor : Cursor Item) :
    resume (first + more) cursor = resume more (resume first cursor) := by
  induction first generalizing cursor with
  | zero => simp only [Nat.zero_add, resume]
  | succ first ih => simp only [Nat.succ_add, resume, ih]

theorem run_resume {Item : Type u} (stream : Stream Item) (first more : Nat) :
    run stream (first + more) = resume more (run stream first) := resume_add first more (start stream)

theorem advance_partition {Item : Type u} (cursor : Cursor Item) :
    (advance cursor).outputs ++ (advance cursor).pending.flatten = cursor.outputs ++ cursor.pending.flatten := by
  rcases cursor with ⟨pending, reversed⟩
  cases pending with
  | done => rfl
  | pause next => rfl
  | yield item next => simp only [advance, Cursor.outputs, Stream.flatten, List.reverse_cons, List.append_assoc,
      List.singleton_append]

theorem resume_partition {Item : Type u} (budget : Nat) (cursor : Cursor Item) :
    (resume budget cursor).outputs ++ (resume budget cursor).pending.flatten =
      cursor.outputs ++ cursor.pending.flatten := by
  induction budget generalizing cursor with
  | zero => rfl
  | succ budget ih => exact (ih (advance cursor)).trans (advance_partition cursor)

theorem run_partition {Item : Type u} (stream : Stream Item) (budget : Nat) :
    (run stream budget).outputs ++ (run stream budget).pending.flatten = stream.flatten :=
  resume_partition budget (start stream)

theorem resume_done {Item : Type u} (budget : Nat) (reversed : List Item) :
    resume budget ⟨.done, reversed⟩ = ⟨.done, reversed⟩ := by
  induction budget with
  | zero => rfl
  | succ budget ih => exact ih

theorem resume_complete {Item : Type u} (stream : Stream Item) (reversed : List Item)
    (budget : Nat) (enough : stream.workBound ≤ budget) :
    (resume budget ⟨stream, reversed⟩).pending = .done := by
  induction stream generalizing reversed budget with
  | done => rw [resume_done]
  | pause next ih =>
      cases budget with
      | zero => simp only [Stream.workBound] at enough; omega
      | succ budget =>
          apply ih () reversed budget
          simp only [Stream.workBound] at enough
          omega
  | yield item next ih =>
      cases budget with
      | zero => simp only [Stream.workBound] at enough; omega
      | succ budget =>
          apply ih () (item :: reversed) budget
          simp only [Stream.workBound] at enough
          omega

theorem run_closed_at {Item : Type u} (stream : Stream Item) (budget : Nat)
    (enough : stream.workBound ≤ budget) : (run stream budget).closed = true := by
  unfold Cursor.closed
  rw [show (run stream budget).pending = .done from resume_complete stream [] budget enough]

theorem closed_readout {Item : Type u} (stream : Stream Item) (budget : Nat)
    (closed : (run stream budget).closed = true) : (run stream budget).outputs = stream.flatten := by
  have partition := run_partition stream budget
  cases pending : (run stream budget).pending with
  | done => simpa only [pending, Stream.flatten, List.append_nil] using partition
  | pause next => simp only [Cursor.closed, pending, Bool.false_eq_true] at closed
  | yield item next => simp only [Cursor.closed, pending, Bool.false_eq_true] at closed

theorem listed_sound {Item : Type u} (stream : Stream Item) (budget : Nat) (item : Item)
    (listed : item ∈ (run stream budget).outputs) : item ∈ stream.flatten := by
  rw [← run_partition stream budget]
  exact List.mem_append_left _ listed

theorem resume_stable {Item : Type u} (stream : Stream Item) (reversed : List Item)
    (budget : Nat) (enough : stream.workBound ≤ budget) :
    resume budget ⟨stream, reversed⟩ = resume stream.workBound ⟨stream, reversed⟩ := by
  have complete := resume_complete stream reversed stream.workBound (Nat.le_refl _)
  rw [← Nat.add_sub_of_le enough, resume_add]
  generalize settled : resume stream.workBound ⟨stream, reversed⟩ = cursor at complete ⊢
  rcases cursor with ⟨pending, reversed⟩
  cases complete
  exact resume_done _ reversed

theorem run_stable {Item : Type u} (stream : Stream Item) (budget : Nat)
    (enough : stream.workBound ≤ budget) : run stream budget = run stream stream.workBound :=
  resume_stable stream [] budget enough

end Mettapedia.OSLF.NativeTypes.Decision.Scheduling
