import Mettapedia.OSLF.NativeTypes.Decision.Machine.Trace

open Mettapedia.OSLF.Framework

/-!
# Witness and coverage laws for consumed modal work

A positive existential answer has an observed receipt whose continuation
holds. A negative existential answer has observed every listed receipt and
refuted every continuation. The universal traversal has the dual laws.
These properties concern the executed trace, including its saved origins.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Machine

open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Scheduling
open scoped List

universe u v

/-- The exhaustive ordered receipt readout, used only in coverage laws. -/
def fullObservations {Item : Type u} {Obs : Type v} (stream : Stream Item)
    (observe : ∀ item, item ∈ stream.flatten → Obs) : List Obs :=
  stream.flatten.attach.map (fun item => observe item.val item.property)

theorem fullObservations_yield {Item : Type u} {Obs : Type v} (item : Item)
    (next : Unit → Stream Item)
    (observe : ∀ other, other ∈ (Stream.yield item next).flatten → Obs) :
    fullObservations (.yield item next) observe =
      observe item List.mem_cons_self :: fullObservations (next ())
        (fun other listed => observe other (List.mem_cons_of_mem _ listed)) := by
  simp only [fullObservations, Stream.flatten, List.attach_cons, List.map_cons, List.map_map]
  rfl

theorem existsTasks_trace {Item : Type u} {Obs : Type v} (predicate : Item → Prop)
    (stream : Stream Item) (observe : ∀ item, item ∈ stream.flatten → Obs)
    (children : ∀ item, item ∈ stream.flatten → Stream (Event Obs (predicate item)))
    (complete : ∀ item listed, Decides (children item listed))
    {seen : List Obs} {result : Outcome (∃ item, item ∈ stream.flatten ∧ predicate item)}
    (trace : Trace (existsTasks predicate stream observe children) seen result) :
    (result.answer = some true →
      ∃ item listed, observe item listed ∈ seen ∧ predicate item) ∧
    (result.answer = some false →
      ∀ item listed, observe item listed ∈ seen ∧ ¬ predicate item) := by
  induction stream generalizing seen with
  | done =>
    rw [existsTasks] at trace
    obtain ⟨rfl, rfl⟩ := trace.finish
    constructor
    · intro read; simp only [Outcome.answer, Bool.false_eq_true, Option.some.injEq] at read
    · intro _ item listed; cases listed
  | pause next ih =>
    cases trace with
    | paused tail => exact ih () observe children complete tail
  | yield item next ih =>
    cases trace with
    | observed _ tail =>
      obtain ⟨head, before, after, child, rest, same⟩ :=
        bindReply_trace _ _ (complete item List.mem_cons_self) tail
      rw [same]
      cases head with
      | proved proof =>
        obtain ⟨rfl, rfl⟩ := rest.finish
        constructor
        · intro _
          exact ⟨item, List.mem_cons_self, List.mem_cons_self, proof⟩
        · intro read; simp only [Outcome.answer, Bool.true_eq_false, Option.some.injEq] at read
      | refuted refutation =>
        obtain ⟨reply, tailTrace, result_eq⟩ := mapReply_trace _
          (fun reply => by cases reply <;> rfl) _ rest
        subst result
        obtain ⟨positive, negative⟩ := ih () _ _
          (fun other listed => complete other (List.mem_cons_of_mem _ listed)) tailTrace
        constructor
        · intro read
          have tailRead : reply.answer = some true := by
            cases reply <;> exact read
          obtain ⟨other, listed, observed, holds⟩ := positive tailRead
          exact ⟨other, List.mem_cons_of_mem _ listed,
            List.mem_cons_of_mem _ (List.mem_append_right before observed), holds⟩
        · intro read other listed
          have tailRead : reply.answer = some false := by
            cases reply <;> exact read
          simp only [Stream.flatten, List.mem_cons] at listed
          rcases listed with same | listed
          · subst other
            exact ⟨List.mem_cons_self, refutation⟩
          · obtain ⟨observed, absent⟩ := negative tailRead other listed
            exact ⟨List.mem_cons_of_mem _ (List.mem_append_right before observed), absent⟩
      | unknown => obtain ⟨_, impossible⟩ := child.decided; cases impossible

theorem forallTasks_trace {Item : Type u} {Obs : Type v} (predicate : Item → Prop)
    (stream : Stream Item) (observe : ∀ item, item ∈ stream.flatten → Obs)
    (children : ∀ item, item ∈ stream.flatten → Stream (Event Obs (predicate item)))
    (complete : ∀ item listed, Decides (children item listed))
    {seen : List Obs} {result : Outcome (∀ item, item ∈ stream.flatten → predicate item)}
    (trace : Trace (forallTasks predicate stream observe children) seen result) :
    (result.answer = some true →
      ∀ item listed, observe item listed ∈ seen ∧ predicate item) ∧
    (result.answer = some false →
      ∃ item listed, observe item listed ∈ seen ∧ ¬ predicate item) := by
  induction stream generalizing seen with
  | done =>
    rw [forallTasks] at trace
    obtain ⟨rfl, rfl⟩ := trace.finish
    constructor
    · intro _ item listed; cases listed
    · intro read; simp only [Outcome.answer, Bool.true_eq_false, Option.some.injEq] at read
  | pause next ih =>
    cases trace with
    | paused tail => exact ih () observe children complete tail
  | yield item next ih =>
    cases trace with
    | observed _ tail =>
      obtain ⟨head, before, after, child, rest, same⟩ :=
        bindReply_trace _ _ (complete item List.mem_cons_self) tail
      rw [same]
      cases head with
      | proved proof =>
        obtain ⟨reply, tailTrace, result_eq⟩ := mapReply_trace _
          (fun reply => by cases reply <;> rfl) _ rest
        subst result
        obtain ⟨positive, negative⟩ := ih () _ _
          (fun other listed => complete other (List.mem_cons_of_mem _ listed)) tailTrace
        constructor
        · intro read other listed
          have tailRead : reply.answer = some true := by
            cases reply <;> exact read
          simp only [Stream.flatten, List.mem_cons] at listed
          rcases listed with same | listed
          · subst other
            exact ⟨List.mem_cons_self, proof⟩
          · obtain ⟨observed, holds⟩ := positive tailRead other listed
            exact ⟨List.mem_cons_of_mem _ (List.mem_append_right before observed), holds⟩
        · intro read
          have tailRead : reply.answer = some false := by
            cases reply <;> exact read
          obtain ⟨other, listed, observed, absent⟩ := negative tailRead
          exact ⟨other, List.mem_cons_of_mem _ listed,
            List.mem_cons_of_mem _ (List.mem_append_right before observed), absent⟩
      | refuted refutation =>
        obtain ⟨rfl, rfl⟩ := rest.finish
        constructor
        · intro read; simp only [Outcome.answer, Bool.false_eq_true, Option.some.injEq] at read
        · intro _
          exact ⟨item, List.mem_cons_self, List.mem_cons_self, refutation⟩
      | unknown => obtain ⟨_, impossible⟩ := child.decided; cases impossible

/-- Every physical receipt, including duplicates, occurs in the saved order. -/
theorem existsTasks_ordered_coverage {Item : Type u} {Obs : Type v} (predicate : Item → Prop)
    (stream : Stream Item) (observe : ∀ item, item ∈ stream.flatten → Obs)
    (children : ∀ item, item ∈ stream.flatten → Stream (Event Obs (predicate item)))
    (complete : ∀ item listed, Decides (children item listed))
    {seen : List Obs} {result : Outcome (∃ item, item ∈ stream.flatten ∧ predicate item)}
    (trace : Trace (existsTasks predicate stream observe children) seen result)
    (read : result.answer = some false) : fullObservations stream observe <+ seen := by
  induction stream generalizing seen with
  | done => exact List.nil_sublist _
  | pause next ih =>
    cases trace with
    | paused tail => exact ih () observe children complete tail read
  | yield item next ih =>
    cases trace with
    | observed _ tail =>
      obtain ⟨head, before, after, child, rest, same⟩ :=
        bindReply_trace _ _ (complete item List.mem_cons_self) tail
      rw [fullObservations_yield, same]
      cases head with
      | proved proof =>
        obtain ⟨_, rfl⟩ := rest.finish
        simp only [Outcome.answer, Option.some.injEq, Bool.true_eq_false] at read
      | refuted refutation =>
        obtain ⟨reply, tailTrace, result_eq⟩ := mapReply_trace _
          (fun reply => by cases reply <;> rfl) _ rest
        rw [result_eq] at read
        have tailRead : reply.answer = some false := by cases reply <;> exact read
        exact ((ih () _ _ (fun other listed => complete other (List.mem_cons_of_mem _ listed))
          tailTrace tailRead).trans (List.sublist_append_right before after)).cons_cons _
      | unknown => obtain ⟨_, impossible⟩ := child.decided; cases impossible

/-- Universal truth preserves the complete ordered receipt sequence. -/
theorem forallTasks_ordered_coverage {Item : Type u} {Obs : Type v} (predicate : Item → Prop)
    (stream : Stream Item) (observe : ∀ item, item ∈ stream.flatten → Obs)
    (children : ∀ item, item ∈ stream.flatten → Stream (Event Obs (predicate item)))
    (complete : ∀ item listed, Decides (children item listed))
    {seen : List Obs} {result : Outcome (∀ item, item ∈ stream.flatten → predicate item)}
    (trace : Trace (forallTasks predicate stream observe children) seen result)
    (read : result.answer = some true) : fullObservations stream observe <+ seen := by
  induction stream generalizing seen with
  | done => exact List.nil_sublist _
  | pause next ih =>
    cases trace with
    | paused tail => exact ih () observe children complete tail read
  | yield item next ih =>
    cases trace with
    | observed _ tail =>
      obtain ⟨head, before, after, child, rest, same⟩ :=
        bindReply_trace _ _ (complete item List.mem_cons_self) tail
      rw [fullObservations_yield, same]
      cases head with
      | proved proof =>
        obtain ⟨reply, tailTrace, result_eq⟩ := mapReply_trace _
          (fun reply => by cases reply <;> rfl) _ rest
        rw [result_eq] at read
        have tailRead : reply.answer = some true := by cases reply <;> exact read
        exact ((ih () _ _ (fun other listed => complete other (List.mem_cons_of_mem _ listed))
          tailTrace tailRead).trans (List.sublist_append_right before after)).cons_cons _
      | refuted refutation =>
        obtain ⟨_, rfl⟩ := rest.finish
        simp only [Outcome.answer, Option.some.injEq, Bool.false_eq_true] at read
      | unknown => obtain ⟨_, impossible⟩ := child.decided; cases impossible

end Mettapedia.OSLF.NativeTypes.Decision.Machine
