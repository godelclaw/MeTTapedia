import Mettapedia.OSLF.NativeTypes.Decision.Machine.Interface

open Mettapedia.OSLF.Framework

/-!
# Lazy continuations for the native formula machine

Observations pass through a continuation unchanged. Answer binding waits for
the first conclusive child, then cancels its remaining work. Every consumed
pause, observation or child answer remains a suspended stream transition.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Machine

open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Scheduling

universe u v w

inductive Event (Observation : Type v) (statement : Prop) where
  | observed (value : Observation)
  | answered (result : Outcome statement)

def Decides {Observation : Type v} {statement : Prop} (stream : Stream (Event Observation statement)) : Prop :=
  ∃ result, .answered result ∈ stream.flatten ∧ result.Decided

def finish {Observation : Type v} {statement : Prop} (result : Outcome statement) :
    Stream (Event Observation statement) := .yield (.answered result) fun _ => .done

theorem finish_decides {Observation : Type v} {statement : Prop} (result : Outcome statement)
    (decided : result.Decided) : Decides (finish (Observation := Observation) result) :=
  ⟨result, by simp [finish, Stream.flatten], decided⟩

def mapReply {Observation : Type v} {first second : Prop} (transform : Outcome first → Outcome second) :
    Stream (Event Observation first) → Stream (Event Observation second)
  | .done => .done
  | .pause next => .pause fun _ => mapReply transform (next ())
  | .yield (.observed value) next => .yield (.observed value) fun _ => mapReply transform (next ())
  | .yield (.answered result) next => .yield (.answered (transform result)) fun _ => mapReply transform (next ())

theorem mapReply_decides {Observation : Type v} {first second : Prop}
    (transform : Outcome first → Outcome second)
    (preserves : ∀ result, result.Decided → (transform result).Decided)
    (stream : Stream (Event Observation first)) (complete : Decides stream) :
    Decides (mapReply transform stream) := by
  induction stream with
  | done => obtain ⟨_, listed, _⟩ := complete; cases listed
  | pause next ih => exact ih () complete
  | yield item next ih =>
    obtain ⟨result, listed, decided⟩ := complete
    simp only [Stream.flatten, List.mem_cons] at listed
    cases item with
    | observed value =>
      rcases listed with impossible | listed
      · cases impossible
      · obtain ⟨other, selected, conclusive⟩ := ih () ⟨result, listed, decided⟩
        exact ⟨other, List.mem_cons_of_mem _ selected, conclusive⟩
    | answered head =>
      rcases listed with same | listed
      · cases same
        exact ⟨transform result, List.mem_cons_self, preserves result decided⟩
      · obtain ⟨other, selected, conclusive⟩ := ih () ⟨result, listed, decided⟩
        exact ⟨other, List.mem_cons_of_mem _ selected, conclusive⟩

def bindReply {Observation : Type v} {first second : Prop}
    (stream : Stream (Event Observation first)) (continuation : Outcome first → Stream (Event Observation second)) :
    Stream (Event Observation second) :=
  match stream with
  | .done => .pause fun _ => continuation .unknown
  | .pause next => .pause fun _ => bindReply (next ()) continuation
  | .yield (.observed value) next => .yield (.observed value) fun _ => bindReply (next ()) continuation
  | .yield (.answered result) next => .pause fun _ => match result with
    | .proved _ | .refuted _ => continuation result
    | .unknown => bindReply (next ()) continuation

theorem bindReply_decides {Observation : Type v} {first second : Prop}
    (stream : Stream (Event Observation first))
    (continuation : Outcome first → Stream (Event Observation second))
    (complete : Decides stream)
    (continues : ∀ result, result.Decided → Decides (continuation result)) :
    Decides (bindReply stream continuation) := by
  induction stream with
  | done => obtain ⟨_, listed, _⟩ := complete; cases listed
  | pause next ih => exact ih () complete
  | yield item next ih =>
    obtain ⟨result, listed, decided⟩ := complete
    simp only [Stream.flatten, List.mem_cons] at listed
    cases item with
    | observed value =>
      rcases listed with impossible | listed
      · cases impossible
      · obtain ⟨other, selected, conclusive⟩ := ih () ⟨result, listed, decided⟩
        exact ⟨other, List.mem_cons_of_mem _ selected, conclusive⟩
    | answered head =>
      cases head with
      | proved proof => exact continues (.proved proof) ⟨true, rfl⟩
      | refuted refutation => exact continues (.refuted refutation) ⟨false, rfl⟩
      | unknown =>
        rcases listed with same | listed
        · cases same
          obtain ⟨answer, decided⟩ := decided
          cases decided
        · exact ih () ⟨result, listed, decided⟩

end Mettapedia.OSLF.NativeTypes.Decision.Machine
