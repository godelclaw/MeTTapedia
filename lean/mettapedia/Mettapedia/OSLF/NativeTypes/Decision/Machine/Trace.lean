import Mettapedia.OSLF.NativeTypes.Decision.Machine

open Mettapedia.OSLF.Framework

/-!
# Actual first-conclusive execution traces

These erased traces describe the stream transitions already taken by the
retained machine. Their observation lists preserve physical receipt order;
answer binding and reply mapping transport traces without replaying work.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Machine

open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Scheduling

universe u v w

inductive Trace {Obs : Type v} {statement : Prop} :
    Stream (Event Obs statement) → List Obs → Outcome statement → Prop where
  | answered (reply : Outcome statement) (decided : reply.Decided)
      (next : Unit → Stream (Event Obs statement)) :
      Trace (.yield (.answered reply) next) [] reply
  | paused {next : Unit → Stream (Event Obs statement)} {seen : List Obs}
      {reply : Outcome statement} (tail : Trace (next ()) seen reply) :
      Trace (.pause next) seen reply
  | observed (value : Obs) {next : Unit → Stream (Event Obs statement)}
      {seen : List Obs} {reply : Outcome statement} (tail : Trace (next ()) seen reply) :
      Trace (.yield (.observed value) next) (value :: seen) reply
  | unknown {next : Unit → Stream (Event Obs statement)} {seen : List Obs}
      {reply : Outcome statement} (tail : Trace (next ()) seen reply) :
      Trace (.yield (.answered .unknown) next) seen reply

theorem Trace.decided {Obs : Type v} {statement : Prop}
    {stream : Stream (Event Obs statement)} {seen : List Obs} {reply : Outcome statement}
    (trace : Trace stream seen reply) : reply.Decided := by
  induction trace with
  | answered _ decided _ => exact decided
  | paused _ ih | observed _ _ ih | unknown _ ih => exact ih

theorem Trace.finish {Obs : Type v} {statement : Prop} {seen : List Obs}
    {reply result : Outcome statement} (trace : Trace (finish (Observation := Obs) reply) seen result) :
    seen = [] ∧ result = reply := by
  cases trace with
  | answered => exact ⟨rfl, rfl⟩
  | unknown tail => cases tail

theorem resume_unknown_trace {Obs : Type v} {statement : Prop}
    (stream : Stream (Event Obs statement)) (reversed : List Obs) (spent budget : Nat)
    (settled : (resume budget ⟨stream, reversed, .unknown, spent⟩).outcome.Decided) :
    ∃ seen, Trace stream seen (resume budget ⟨stream, reversed, .unknown, spent⟩).outcome ∧
      (resume budget ⟨stream, reversed, .unknown, spent⟩).observations = reversed.reverse ++ seen := by
  induction budget generalizing stream reversed spent with
  | zero => obtain ⟨_, impossible⟩ := settled; cases impossible
  | succ budget ih =>
    cases stream with
    | done => obtain ⟨_, impossible⟩ := settled; cases impossible
    | pause next =>
      obtain ⟨seen, trace, readout⟩ := ih (next ()) reversed (spent + 1) settled
      exact ⟨seen, .paused trace, readout⟩
    | yield item next =>
      cases item with
      | observed value =>
        obtain ⟨seen, trace, readout⟩ := ih (next ()) (value :: reversed) (spent + 1) settled
        refine ⟨value :: seen, .observed value trace, ?_⟩
        simpa only [resume, advance, List.reverse_cons, List.append_assoc, List.singleton_append] using readout
      | answered reply =>
        cases reply with
        | proved proof =>
          have fixed := resume_conclusive
            (State.mk .done reversed (.proved proof) (spent + 1)) ⟨true, rfl⟩ budget
          refine ⟨[], ?_, ?_⟩
          · simpa only [resume, advance, fixed] using
              (Trace.answered (.proved proof) ⟨true, rfl⟩ next)
          · simp only [resume, advance, fixed, State.observations, List.append_nil]
        | refuted refutation =>
          have fixed := resume_conclusive
            (State.mk .done reversed (.refuted refutation) (spent + 1)) ⟨false, rfl⟩ budget
          refine ⟨[], ?_, ?_⟩
          · simpa only [resume, advance, fixed] using
              (Trace.answered (.refuted refutation) ⟨false, rfl⟩ next)
          · simp only [resume, advance, fixed, State.observations, List.append_nil]
        | unknown =>
          obtain ⟨seen, trace, readout⟩ := ih (next ()) reversed (spent + 1) settled
          exact ⟨seen, .unknown trace, readout⟩

theorem run_trace {system : Mettapedia.GSLT.GSLT.{u}}
    {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : CursorBackend.{u,v} system admitted) (leaves : Leaf → LeafBackend system admitted)
    (formula : Formula Leaf) (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat)
    (settled : (run backend leaves formula source sourceAdmitted budget).outcome.Decided) :
    Trace (tasks backend leaves formula source sourceAdmitted [])
      (run backend leaves formula source sourceAdmitted budget).observations
      (run backend leaves formula source sourceAdmitted budget).outcome := by
  obtain ⟨seen, trace, readout⟩ := resume_unknown_trace
    (tasks backend leaves formula source sourceAdmitted []) [] 0 budget settled
  simpa only [List.reverse_nil, List.nil_append] using readout ▸ trace

theorem bindReply_trace {Obs : Type v} {first second : Prop}
    (stream : Stream (Event Obs first))
    (continuation : Outcome first → Stream (Event Obs second)) (complete : Decides stream)
    {seen : List Obs} {result : Outcome second}
    (trace : Trace (bindReply stream continuation) seen result) :
    ∃ reply before after, Trace stream before reply ∧
      Trace (continuation reply) after result ∧ seen = before ++ after := by
  induction stream generalizing seen with
  | done => obtain ⟨_, impossible, _⟩ := complete; cases impossible
  | pause next ih =>
    cases trace with
    | paused tail =>
      obtain ⟨reply, before, after, child, rest, same⟩ := ih () complete tail
      exact ⟨reply, before, after, .paused child, rest, same⟩
  | yield item next ih =>
    cases item with
    | observed value =>
      cases trace with
      | observed _ tail =>
        obtain ⟨reply, before, after, child, rest, same⟩ :=
          ih () ((observed_decides value (next ())).mp complete) tail
        exact ⟨reply, value :: before, after, .observed value child, rest,
          by simp only [List.cons_append, same]⟩
    | answered reply =>
      cases trace with
      | paused tail =>
        cases reply with
        | proved proof =>
          exact ⟨.proved proof, [], seen, .answered _ ⟨true, rfl⟩ next, tail, rfl⟩
        | refuted refutation =>
          exact ⟨.refuted refutation, [], seen, .answered _ ⟨false, rfl⟩ next, tail, rfl⟩
        | unknown =>
          have tailComplete : Decides (next ()) := by
            obtain ⟨reply, listed, settled⟩ := complete
            simp only [Stream.flatten, List.mem_cons] at listed
            rcases listed with same | listed
            · cases same; obtain ⟨_, impossible⟩ := settled; cases impossible
            · exact ⟨reply, listed, settled⟩
          obtain ⟨reply, before, after, child, rest, same⟩ := ih () tailComplete tail
          exact ⟨reply, before, after, .unknown child, rest, same⟩

theorem mapReply_trace {Obs : Type v} {first second : Prop}
    (transform : Outcome first → Outcome second)
    (preserves : ∀ reply, (transform reply).answer = reply.answer)
    (stream : Stream (Event Obs first)) {seen : List Obs} {result : Outcome second}
    (trace : Trace (mapReply transform stream) seen result) :
    ∃ reply, Trace stream seen reply ∧ result = transform reply := by
  induction stream generalizing seen with
  | done => cases trace
  | pause next ih =>
    cases trace with
    | paused tail =>
      obtain ⟨reply, child, same⟩ := ih () tail
      exact ⟨reply, .paused child, same⟩
  | yield item next ih =>
    cases item with
    | observed value =>
      cases trace with
      | observed _ tail =>
        obtain ⟨reply, child, same⟩ := ih () tail
        exact ⟨reply, .observed value child, same⟩
    | answered reply =>
      change Trace (.yield (.answered (transform reply)) (fun _ => mapReply transform (next ()))) seen result at trace
      cases mapped : transform reply with
      | proved proof =>
        rw [mapped] at trace
        cases trace with
        | answered =>
          exact ⟨reply, .answered reply ⟨true, by rw [← preserves reply, mapped]; rfl⟩ next, mapped.symm⟩
      | refuted refutation =>
        rw [mapped] at trace
        cases trace with
        | answered =>
          exact ⟨reply, .answered reply ⟨false, by rw [← preserves reply, mapped]; rfl⟩ next, mapped.symm⟩
      | unknown =>
        rw [mapped] at trace
        have same : reply = .unknown := by
          have read := preserves reply
          rw [mapped] at read
          cases reply with
          | proved proof => change none = some true at read; cases read
          | refuted refutation => change none = some false at read; cases read
          | unknown => rfl
        subst reply
        cases trace with
        | answered _ settled => obtain ⟨_, impossible⟩ := settled; cases impossible
        | unknown tail =>
          obtain ⟨reply, child, same⟩ := ih () tail
          exact ⟨reply, .unknown child, same⟩

end Mettapedia.OSLF.NativeTypes.Decision.Machine
