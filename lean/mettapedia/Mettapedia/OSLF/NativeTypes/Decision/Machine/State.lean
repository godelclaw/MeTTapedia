import Mettapedia.OSLF.NativeTypes.Decision.Machine.ModalStreams

open Mettapedia.OSLF.Framework

/-!
# Retained global state and a total transition budget

One active transition consumes one pause, observation or child answer.
All sibling and nested work shares this state and its spent counter.
Resuming continues the retained stream; settled states use no further work.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Machine

open Mettapedia.GSLT
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Scheduling

universe u v

structure Observation {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : CursorBackend.{u,v} system admitted) where
  source : system.Term
  receipt : backend.Receipt source
  listed : receipt ∈ (backend.tasks source).flatten
  location : List Nat

theorem Observation.step {system : GSLT.{u}} {admitted : system.Term → Prop}
    {backend : CursorBackend.{u,v} system admitted} (observation : Observation backend) :
    system.Step observation.source (backend.target observation.source observation.receipt) :=
  backend.sound _ _ observation.listed

/-- A structural decomposition is evidence about a source, not an execution step. -/
structure SpatialObservation {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : CursorBackend.{u,v} system admitted) where
  index : Nat
  source : system.Term
  parts : system.Term × system.Term
  listed : parts ∈ (backend.splitTasks index source).flatten
  location : List Nat

theorem SpatialObservation.split {system : GSLT.{u}} {admitted : system.Term → Prop}
    {backend : CursorBackend.{u,v} system admitted} (observation : SpatialObservation backend) :
    backend.spatial.theory.Split observation.index observation.source
      observation.parts.1 observation.parts.2 :=
  backend.spatial.sound _ _ _ (by
    rw [← backend.splitTasks_exact]
    exact observation.listed)

/-- Retained evidence preserves the distinction between transitions and decompositions. -/
inductive Evidence {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : CursorBackend.{u,v} system admitted) where
  | operational : Observation backend → Evidence backend
  | separation : SpatialObservation backend → Evidence backend

def Evidence.operational? {system : GSLT.{u}} {admitted : system.Term → Prop}
    {backend : CursorBackend.{u,v} system admitted} : Evidence backend → Option (Observation backend)
  | .operational observation => some observation
  | .separation _ => none

def Evidence.separation? {system : GSLT.{u}} {admitted : system.Term → Prop}
    {backend : CursorBackend.{u,v} system admitted} : Evidence backend → Option (SpatialObservation backend)
  | .operational _ => none
  | .separation observation => some observation

@[simp] theorem Evidence.mem_operational {system : GSLT.{u}} {admitted : system.Term → Prop}
    {backend : CursorBackend.{u,v} system admitted} (observation : Observation backend)
    (evidence : List (Evidence backend)) :
    observation ∈ evidence.filterMap Evidence.operational? ↔
      Evidence.operational observation ∈ evidence := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨entry, listed, selected⟩
    cases entry with
    | operational value => cases selected; exact listed
    | separation value => cases selected
  · intro listed
    exact ⟨.operational observation, listed, rfl⟩

structure State (Obs : Type v) (statement : Prop) where
  pending : Stream (Event Obs statement)
  reversed : List Obs
  outcome : Outcome statement
  spent : Nat

def State.observations {Obs : Type v} {statement : Prop} (state : State Obs statement) : List Obs :=
  state.reversed.reverse

def State.closed {Obs : Type v} {statement : Prop} (state : State Obs statement) : Bool :=
  match state.pending with
  | .done => true
  | _ => false

def startStream {Obs : Type v} {statement : Prop} (stream : Stream (Event Obs statement)) : State Obs statement :=
  ⟨stream, [], .unknown, 0⟩

def advance {Obs : Type v} {statement : Prop} (state : State Obs statement) : State Obs statement :=
  match state.outcome with
  | .proved _ | .refuted _ => state
  | .unknown => match state.pending with
    | .done => state
    | .pause next => ⟨next (), state.reversed, .unknown, state.spent + 1⟩
    | .yield (.observed value) next => ⟨next (), value :: state.reversed, .unknown, state.spent + 1⟩
    | .yield (.answered result) next => match result with
      | .proved _ | .refuted _ => ⟨.done, state.reversed, result, state.spent + 1⟩
      | .unknown => ⟨next (), state.reversed, .unknown, state.spent + 1⟩

def resume {Obs : Type v} {statement : Prop} : Nat → State Obs statement → State Obs statement
  | 0, state => state
  | more + 1, state => match state.outcome with
    | .proved _ | .refuted _ => state
    | .unknown => match state.pending with
      | .done => state
      | _ => resume more (advance state)

theorem resume_conclusive {Obs : Type v} {statement : Prop} (state : State Obs statement)
    (decided : state.outcome.Decided) (budget : Nat) : resume budget state = state := by
  cases budget with
  | zero => rfl
  | succ budget =>
    cases result : state.outcome with
    | proved proof => simp only [resume, result]
    | refuted refutation => simp only [resume, result]
    | unknown => obtain ⟨_, read⟩ := decided; rw [result] at read; cases read

theorem resume_done {Obs : Type v} {statement : Prop} (state : State Obs statement)
    (closed : state.pending = .done) (budget : Nat) : resume budget state = state := by
  cases budget with
  | zero => rfl
  | succ budget => cases result : state.outcome <;> simp only [resume, result, closed]

theorem resume_add {Obs : Type v} {statement : Prop} (first more : Nat) (state : State Obs statement) :
    resume (first + more) state = resume more (resume first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, resume]
  | succ first ih =>
    cases result : state.outcome with
    | proved proof =>
      have settled : state.outcome.Decided := ⟨true, by simp only [result, Outcome.answer]⟩
      simp only [resume_conclusive state settled]
    | refuted refutation =>
      have settled : state.outcome.Decided := ⟨false, by simp only [result, Outcome.answer]⟩
      simp only [resume_conclusive state settled]
    | unknown =>
      cases pending : state.pending with
      | done => simp only [resume_done state pending]
      | pause next | yield item next => simp only [Nat.succ_add, resume, result, pending, ih]

theorem advance_spent_le {Obs : Type v} {statement : Prop} (state : State Obs statement) :
    (advance state).spent ≤ state.spent + 1 := by
  cases result : state.outcome with
  | proved proof | refuted proof => simp only [advance, result]; omega
  | unknown =>
    cases pending : state.pending with
    | done => simp only [advance, result, pending]; omega
    | pause next => simp only [advance, result, pending]; omega
    | yield item next => cases item with
      | observed value => simp only [advance, result, pending]; omega
      | answered reply => cases reply <;> simp only [advance, result, pending] <;> omega

theorem advance_spent_exact {Obs : Type v} {statement : Prop} (state : State Obs statement)
    (unknown : state.outcome = .unknown) (active : state.pending ≠ .done) :
    (advance state).spent = state.spent + 1 := by
  cases pending : state.pending with
  | done => exact (active pending).elim
  | pause next => simp only [advance, unknown, pending]
  | yield item next =>
    cases item with
    | observed value => simp only [advance, unknown, pending]
    | answered reply => cases reply <;> simp only [advance, unknown, pending]

theorem advance_observations_prefix {Obs : Type v} {statement : Prop} (state : State Obs statement) :
    ∃ suffix, (advance state).observations = state.observations ++ suffix := by
  cases result : state.outcome with
  | proved proof | refuted proof =>
    refine ⟨[], ?_⟩
    simp only [advance, result, List.append_nil]
  | unknown =>
    cases pending : state.pending with
    | done => refine ⟨[], ?_⟩; simp only [advance, result, pending, List.append_nil]
    | pause next => refine ⟨[], ?_⟩; simp only [advance, result, pending, State.observations, List.append_nil]
    | yield item next =>
      cases item with
      | observed value =>
        refine ⟨[value], ?_⟩
        simp only [advance, result, pending, State.observations, List.reverse_cons]
      | answered reply =>
        refine ⟨[], ?_⟩
        cases reply <;> simp only [advance, result, pending, State.observations, List.append_nil]

theorem resume_observations_prefix {Obs : Type v} {statement : Prop}
    (state : State Obs statement) (budget : Nat) :
    ∃ suffix, (resume budget state).observations = state.observations ++ suffix := by
  induction budget generalizing state with
  | zero => exact ⟨[], (List.append_nil _).symm⟩
  | succ budget ih =>
    cases result : state.outcome with
    | proved proof | refuted proof =>
      exact ⟨[], by simp only [resume, result, List.append_nil]⟩
    | unknown =>
      cases pending : state.pending with
      | done => exact ⟨[], by simp only [resume, result, pending, List.append_nil]⟩
      | pause next | yield item next =>
        simp only [resume, result, pending]
        obtain ⟨first, first_eq⟩ := advance_observations_prefix state
        obtain ⟨rest, rest_eq⟩ := ih (advance state)
        exact ⟨first ++ rest, by rw [rest_eq, first_eq, List.append_assoc]⟩

theorem resume_spent_le {Obs : Type v} {statement : Prop} (state : State Obs statement) (budget : Nat) :
    (resume budget state).spent ≤ state.spent + budget := by
  induction budget generalizing state with
  | zero => simp only [resume, Nat.add_zero, Nat.le_refl]
  | succ budget ih =>
    cases result : state.outcome with
    | proved proof | refuted proof => simp only [resume, result]; omega
    | unknown =>
      cases pending : state.pending with
      | done => simp only [resume, result, pending]; omega
      | pause next | yield item next =>
        simp only [resume, result, pending]
        have bound := ih (advance state)
        have step := advance_spent_le state
        omega

theorem resume_unknown_complete {Obs : Type v} {statement : Prop}
    (stream : Stream (Event Obs statement)) (complete : Decides stream)
    (reversed : List Obs) (spent budget : Nat) (enough : stream.workBound ≤ budget) :
    (resume budget ⟨stream, reversed, .unknown, spent⟩).outcome.Decided := by
  induction stream generalizing reversed spent budget with
  | done => obtain ⟨_, listed, _⟩ := complete; cases listed
  | pause next ih =>
    cases budget with
    | zero => simp only [Stream.workBound] at enough; omega
    | succ budget =>
      apply ih () complete reversed (spent + 1) budget
      simp only [Stream.workBound] at enough
      omega
  | yield item next ih =>
    cases budget with
    | zero => simp only [Stream.workBound] at enough; omega
    | succ budget =>
      cases item with
      | observed value =>
        apply ih () ((observed_decides value (next ())).mp complete) (value :: reversed) (spent + 1) budget
        simp only [Stream.workBound] at enough
        omega
      | answered reply =>
        cases reply with
        | proved proof =>
          have fixed := resume_conclusive (State.mk .done reversed (.proved proof) (spent + 1)) ⟨true, rfl⟩ budget
          simpa only [resume, advance, fixed] using (show (Outcome.proved proof).Decided from ⟨true, rfl⟩)
        | refuted refutation =>
          have fixed := resume_conclusive (State.mk .done reversed (.refuted refutation) (spent + 1)) ⟨false, rfl⟩ budget
          simpa only [resume, advance, fixed] using (show (Outcome.refuted refutation).Decided from ⟨false, rfl⟩)
        | unknown =>
          obtain ⟨result, listed, decided⟩ := complete
          simp only [Stream.flatten, List.mem_cons] at listed
          rcases listed with same | listed
          · cases same; obtain ⟨_, read⟩ := decided; cases read
          · apply ih () ⟨result, listed, decided⟩ reversed (spent + 1) budget
            simp only [Stream.workBound] at enough
            omega

end Mettapedia.OSLF.NativeTypes.Decision.Machine
