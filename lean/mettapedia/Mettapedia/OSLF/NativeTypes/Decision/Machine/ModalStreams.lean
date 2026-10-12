import Mettapedia.OSLF.NativeTypes.Decision.Machine.Streams

open Mettapedia.OSLF.Framework

/-!
# Suspended quantified traversal of actual receipts

Each receipt is retained before checking its continuation. Existence stops
at the first positive continuation and outgoing universality at the first
counterexample. The other polarities visit the complete suspended stream.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Machine

open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Scheduling

universe u v

theorem observed_decides {Obs : Type v} {statement : Prop}
    (value : Obs) (tail : Stream (Event Obs statement)) :
    Decides (.yield (.observed value) fun _ => tail) ↔ Decides tail := by
  constructor
  · rintro ⟨result, listed, decided⟩
    simp only [Stream.flatten, List.mem_cons] at listed
    rcases listed with impossible | listed
    · cases impossible
    · exact ⟨result, listed, decided⟩
  · rintro ⟨result, listed, decided⟩
    exact ⟨result, List.mem_cons_of_mem _ listed, decided⟩

def existsTasks {Item : Type u} {Obs : Type v} (predicate : Item → Prop)
    (stream : Stream Item)
    (observe : ∀ item, item ∈ stream.flatten → Obs)
    (children : ∀ item, item ∈ stream.flatten → Stream (Event Obs (predicate item))) :
    Stream (Event Obs (∃ item, item ∈ stream.flatten ∧ predicate item)) :=
  match stream with
  | .done => finish (.refuted (by simp [Stream.flatten]))
  | .pause next => .pause fun _ => existsTasks predicate (next ()) observe children
  | .yield item next =>
    .yield (.observed (observe item List.mem_cons_self)) fun _ =>
      bindReply (children item List.mem_cons_self) fun head =>
        match head with
        | .proved proof => finish (.proved ⟨item, List.mem_cons_self, proof⟩)
        | _ => mapReply
            (fun tail => Outcome.map (by simp [Stream.flatten, List.mem_cons]) (Outcome.disjunction head tail))
            (existsTasks predicate (next ())
              (fun other listed => observe other (List.mem_cons_of_mem _ listed))
              (fun other listed => children other (List.mem_cons_of_mem _ listed)))

def forallTasks {Item : Type u} {Obs : Type v} (predicate : Item → Prop)
    (stream : Stream Item)
    (observe : ∀ item, item ∈ stream.flatten → Obs)
    (children : ∀ item, item ∈ stream.flatten → Stream (Event Obs (predicate item))) :
    Stream (Event Obs (∀ item, item ∈ stream.flatten → predicate item)) :=
  match stream with
  | .done => finish (.proved (by simp [Stream.flatten]))
  | .pause next => .pause fun _ => forallTasks predicate (next ()) observe children
  | .yield item next =>
    .yield (.observed (observe item List.mem_cons_self)) fun _ =>
      bindReply (children item List.mem_cons_self) fun head =>
        match head with
        | .refuted refutation => finish (.refuted (fun universal => refutation (universal item List.mem_cons_self)))
        | _ => mapReply
            (fun tail => Outcome.map (by simp [Stream.flatten, List.mem_cons, forall_eq_or_imp])
              (Outcome.conjunction head tail))
            (forallTasks predicate (next ())
              (fun other listed => observe other (List.mem_cons_of_mem _ listed))
              (fun other listed => children other (List.mem_cons_of_mem _ listed)))

theorem existsTasks_complete {Item : Type u} {Obs : Type v} (predicate : Item → Prop)
    (stream : Stream Item)
    (observe : ∀ item, item ∈ stream.flatten → Obs)
    (children : ∀ item, item ∈ stream.flatten → Stream (Event Obs (predicate item)))
    (complete : ∀ item listed, Decides (children item listed)) :
    Decides (existsTasks predicate stream observe children) := by
  induction stream with
  | done => exact finish_decides _ ⟨false, rfl⟩
  | pause next ih => exact ih () observe children complete
  | yield item next ih =>
    apply (observed_decides _ _).mpr
    apply bindReply_decides
    · exact complete item List.mem_cons_self
    · intro head decided
      cases head with
      | proved proof => exact finish_decides _ ⟨true, rfl⟩
      | refuted refutation =>
        apply mapReply_decides
        · intro tail settled
          apply Outcome.map_decided
          exact Outcome.disjunction_decided (.refuted refutation) tail ⟨false, rfl⟩ settled
        · exact ih () _ _ (fun other listed => complete other (List.mem_cons_of_mem _ listed))
      | unknown => obtain ⟨_, decided⟩ := decided; cases decided

theorem forallTasks_complete {Item : Type u} {Obs : Type v} (predicate : Item → Prop)
    (stream : Stream Item)
    (observe : ∀ item, item ∈ stream.flatten → Obs)
    (children : ∀ item, item ∈ stream.flatten → Stream (Event Obs (predicate item)))
    (complete : ∀ item listed, Decides (children item listed)) :
    Decides (forallTasks predicate stream observe children) := by
  induction stream with
  | done => exact finish_decides _ ⟨true, rfl⟩
  | pause next ih => exact ih () observe children complete
  | yield item next ih =>
    apply (observed_decides _ _).mpr
    apply bindReply_decides
    · exact complete item List.mem_cons_self
    · intro head decided
      cases head with
      | proved proof =>
        apply mapReply_decides
        · intro tail settled
          apply Outcome.map_decided
          exact Outcome.conjunction_decided (.proved proof) tail ⟨true, rfl⟩ settled
        · exact ih () _ _ (fun other listed => complete other (List.mem_cons_of_mem _ listed))
      | refuted refutation => exact finish_decides _ ⟨false, rfl⟩
      | unknown => obtain ⟨_, decided⟩ := decided; cases decided

end Mettapedia.OSLF.NativeTypes.Decision.Machine
