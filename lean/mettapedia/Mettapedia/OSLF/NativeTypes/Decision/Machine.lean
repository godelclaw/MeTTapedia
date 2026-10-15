import Mettapedia.OSLF.NativeTypes.Decision.Machine.Meaning
import Mettapedia.OSLF.NativeTypes.Decision.Machine.State

open Mettapedia.OSLF.Framework

/-!
# A retained compositional native formula machine

Every formula inspection, primitive pause, receipt, child answer and final
answer consumes a transition from one shared state. Continuations are lazy;
settled Boolean branches and modal witnesses cancel unused work. Running
does not enumerate a complete frontier or compute the exhaustive bound.

The separately computable bound is the finite stream's actual transition
count. Its completeness follows from earned local step coverage, admitted
successor closure and the native certificates in primitive leaf streams.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Machine

open Mettapedia.GSLT GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core (Outcome Formula Test)
open Mettapedia.OSLF.NativeTypes.Decision.Scheduling (Stream)

universe u v w

def answerStream {Obs : Type v} {statement : Prop} :
    Stream (Outcome statement) → Stream (Event Obs statement)
  | .done => .done
  | .pause next => .pause fun _ => answerStream (next ())
  | .yield result next => .yield (.answered result) fun _ => answerStream (next ())

theorem answerStream_complete {Obs : Type v} {statement : Prop}
    (stream : Stream (Outcome statement))
    (complete : ∃ result, result ∈ stream.flatten ∧ result.Decided) :
    Decides (answerStream (Obs := Obs) stream) := by
  induction stream with
  | done => obtain ⟨_, listed, _⟩ := complete; cases listed
  | pause next ih => exact ih () complete
  | yield result next ih =>
    obtain ⟨other, listed, settled⟩ := complete
    simp only [Stream.flatten, List.mem_cons] at listed
    rcases listed with same | listed
    · subst other
      exact ⟨result, List.mem_cons_self, settled⟩
    · obtain ⟨found, member, decided⟩ := ih () ⟨other, listed, settled⟩
      exact ⟨found, List.mem_cons_of_mem _ member, decided⟩

def existsMeaning {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : CursorBackend.{u,v} system admitted) (predicate : EquationPredicate system)
    (source : system.Term) (sourceAdmitted : admitted source) :
    Outcome (∃ receipt, receipt ∈ (backend.tasks source).flatten ∧ predicate (backend.target source receipt)) →
      Outcome (semanticDiamond system predicate source)
  | .proved witness => .proved (by
    obtain ⟨receipt, listed, holds⟩ := witness
    exact (gsltDiamond_spec system predicate.1 source).mpr
      ⟨backend.target source receipt, backend.sound source receipt listed, holds⟩)
  | .refuted absent => .refuted (fun holds => by
    obtain ⟨actual, step, satisfies⟩ := (gsltDiamond_spec system predicate.1 source).mp holds
    obtain ⟨receipt, listed, related⟩ := backend.coverage source sourceAdmitted actual step
    exact absent ⟨receipt, listed, (predicate.2 related).mp satisfies⟩)
  | .unknown => .unknown

def forallMeaning {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : CursorBackend.{u,v} system admitted) (predicate : EquationPredicate system)
    (source : system.Term) (sourceAdmitted : admitted source) :
    Outcome (∀ receipt, receipt ∈ (backend.tasks source).flatten → predicate (backend.target source receipt)) →
      Outcome (Mettapedia.OSLF.NativeTypes.Semantics.Operational.outgoingUniversal system predicate source)
  | .proved universal => .proved (fun actual step => by
    obtain ⟨receipt, listed, related⟩ := backend.coverage source sourceAdmitted actual step
    exact (predicate.2 related).mpr (universal receipt listed))
  | .refuted counterexample => .refuted (fun universal =>
    counterexample (fun receipt listed => universal (backend.target source receipt)
      (backend.sound source receipt listed)))
  | .unknown => .unknown

theorem existsMeaning_decided {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : CursorBackend.{u,v} system admitted) (predicate : EquationPredicate system)
    (source : system.Term) (sourceAdmitted : admitted source)
    (result : Outcome (∃ receipt, receipt ∈ (backend.tasks source).flatten ∧ predicate (backend.target source receipt)))
    (decided : result.Decided) : (existsMeaning backend predicate source sourceAdmitted result).Decided := by
  cases result <;> simp_all [existsMeaning, Outcome.Decided, Outcome.answer]

theorem forallMeaning_decided {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : CursorBackend.{u,v} system admitted) (predicate : EquationPredicate system)
    (source : system.Term) (sourceAdmitted : admitted source)
    (result : Outcome (∀ receipt, receipt ∈ (backend.tasks source).flatten → predicate (backend.target source receipt)))
    (decided : result.Decided) : (forallMeaning backend predicate source sourceAdmitted result).Decided := by
  cases result <;> simp_all [forallMeaning, Outcome.Decided, Outcome.answer]

def tasks {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : CursorBackend.{u,v} system admitted) (leaves : Leaf → LeafBackend system admitted) :
    (formula : Formula Leaf) → (source : system.Term) → admitted source →
      List Nat → Stream (Event (Observation backend) (denotation leaves formula source))
  | formula, source, sourceAdmitted, location => .pause fun _ => match formula with
    | .atom leaf => bindReply (answerStream ((leaves leaf).tasks source)) finish
    | .top => finish (.proved True.intro)
    | .bottom => finish (.refuted id)
    | .conj left right =>
      bindReply (tasks backend leaves left source sourceAdmitted (location ++ [0])) fun first =>
        match first with
        | .refuted refutation => finish (.refuted (fun holds => refutation holds.1))
        | _ => mapReply (Outcome.conjunction first)
            (tasks backend leaves right source sourceAdmitted (location ++ [1]))
    | .disj left right =>
      bindReply (tasks backend leaves left source sourceAdmitted (location ++ [0])) fun first =>
        match first with
        | .proved proof => finish (.proved (.inl proof))
        | _ => mapReply (Outcome.disjunction first)
            (tasks backend leaves right source sourceAdmitted (location ++ [1]))
    | .neg formula => mapReply Outcome.negation (tasks backend leaves formula source sourceAdmitted (location ++ [0]))
    | .imp left right =>
      bindReply (tasks backend leaves left source sourceAdmitted (location ++ [0])) fun first =>
        match first with
        | .refuted refutation => finish (.proved (fun holds => False.elim (refutation holds)))
        | _ => mapReply (Outcome.implication first)
            (tasks backend leaves right source sourceAdmitted (location ++ [1]))
    | .possibility formula =>
      mapReply (existsMeaning backend (denotation leaves formula) source sourceAdmitted)
        (existsTasks (fun receipt => denotation leaves formula (backend.target source receipt))
          (backend.tasks source)
          (fun receipt listed => ⟨source, receipt, listed, location⟩)
          (fun receipt listed => tasks backend leaves formula (backend.target source receipt)
            (backend.target_admitted source sourceAdmitted receipt listed) (location ++ [0])))
    | .outgoingUniversal formula =>
      mapReply (forallMeaning backend (denotation leaves formula) source sourceAdmitted)
        (forallTasks (fun receipt => denotation leaves formula (backend.target source receipt))
          (backend.tasks source)
          (fun receipt listed => ⟨source, receipt, listed, location⟩)
          (fun receipt listed => tasks backend leaves formula (backend.target source receipt)
            (backend.target_admitted source sourceAdmitted receipt listed) (location ++ [0])))
termination_by formula => formula

theorem tasks_complete {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : CursorBackend.{u,v} system admitted) (leaves : Leaf → LeafBackend system admitted)
    (formula : Formula Leaf) (source : system.Term) (sourceAdmitted : admitted source) (location : List Nat) :
    Decides (tasks backend leaves formula source sourceAdmitted location) := by
  induction formula generalizing source location with
  | atom leaf =>
    rw [tasks]
    apply bindReply_decides
    · exact answerStream_complete _ ((leaves leaf).complete source sourceAdmitted)
    · exact fun result decided => finish_decides result decided
  | top => rw [tasks]; exact finish_decides _ ⟨true, rfl⟩
  | bottom => rw [tasks]; exact finish_decides _ ⟨false, rfl⟩
  | conj left right ihl ihr =>
    rw [tasks]
    apply bindReply_decides
    · exact ihl source sourceAdmitted _
    · intro first decided
      cases first with
      | proved proof =>
        apply mapReply_decides
        · exact fun other settled => Outcome.conjunction_decided (.proved proof) other ⟨true, rfl⟩ settled
        · exact ihr source sourceAdmitted _
      | refuted refutation => exact finish_decides _ ⟨false, rfl⟩
      | unknown => obtain ⟨_, read⟩ := decided; cases read
  | disj left right ihl ihr =>
    rw [tasks]
    apply bindReply_decides
    · exact ihl source sourceAdmitted _
    · intro first decided
      cases first with
      | proved proof => exact finish_decides _ ⟨true, rfl⟩
      | refuted refutation =>
        apply mapReply_decides
        · exact fun other settled => Outcome.disjunction_decided (.refuted refutation) other ⟨false, rfl⟩ settled
        · exact ihr source sourceAdmitted _
      | unknown => obtain ⟨_, read⟩ := decided; cases read
  | neg formula ih =>
    rw [tasks]
    exact mapReply_decides Outcome.negation Outcome.negation_decided _ (ih source sourceAdmitted _)
  | imp left right ihl ihr =>
    rw [tasks]
    apply bindReply_decides
    · exact ihl source sourceAdmitted _
    · intro first decided
      cases first with
      | proved proof =>
        apply mapReply_decides
        · exact fun other settled => Outcome.implication_decided (.proved proof) other ⟨true, rfl⟩ settled
        · exact ihr source sourceAdmitted _
      | refuted refutation => exact finish_decides _ ⟨true, rfl⟩
      | unknown => obtain ⟨_, read⟩ := decided; cases read
  | possibility formula ih =>
    rw [tasks]
    apply mapReply_decides
    · exact existsMeaning_decided backend (denotation leaves formula) source sourceAdmitted
    · apply existsTasks_complete
      exact fun receipt listed => ih (backend.target source receipt)
        (backend.target_admitted source sourceAdmitted receipt listed) _
  | outgoingUniversal formula ih =>
    rw [tasks]
    apply mapReply_decides
    · exact forallMeaning_decided backend (denotation leaves formula) source sourceAdmitted
    · apply forallTasks_complete
      exact fun receipt listed => ih (backend.target source receipt)
        (backend.target_admitted source sourceAdmitted receipt listed) _

def start {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : CursorBackend.{u,v} system admitted) (leaves : Leaf → LeafBackend system admitted)
    (formula : Formula Leaf) (source : system.Term) (sourceAdmitted : admitted source) :
    State (Observation backend) (denotation leaves formula source) :=
  startStream (tasks backend leaves formula source sourceAdmitted [])

def run {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : CursorBackend.{u,v} system admitted) (leaves : Leaf → LeafBackend system admitted)
    (formula : Formula Leaf) (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat) :
    State (Observation backend) (denotation leaves formula source) :=
  resume budget (start backend leaves formula source sourceAdmitted)

/-- This exhaustive operation is separate from starting or resuming work. -/
def totalBound {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : CursorBackend.{u,v} system admitted) (leaves : Leaf → LeafBackend system admitted)
    (formula : Formula Leaf) (source : system.Term) (sourceAdmitted : admitted source) : Nat :=
  (tasks backend leaves formula source sourceAdmitted []).workBound

theorem exact_run_resume {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : CursorBackend.{u,v} system admitted) (leaves : Leaf → LeafBackend system admitted)
    (formula : Formula Leaf) (source : system.Term) (sourceAdmitted : admitted source) (first more : Nat) :
    run backend leaves formula source sourceAdmitted (first + more) =
      resume more (run backend leaves formula source sourceAdmitted first) :=
  resume_add first more (start backend leaves formula source sourceAdmitted)

theorem spent_le_budget {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : CursorBackend.{u,v} system admitted) (leaves : Leaf → LeafBackend system admitted)
    (formula : Formula Leaf) (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat) :
    (run backend leaves formula source sourceAdmitted budget).spent ≤ budget := by
  simpa only [run, start, startStream, Nat.zero_add] using
    resume_spent_le (start backend leaves formula source sourceAdmitted) budget

theorem complete_at_bound {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : CursorBackend.{u,v} system admitted) (leaves : Leaf → LeafBackend system admitted)
    (formula : Formula Leaf) (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat)
    (enough : totalBound backend leaves formula source sourceAdmitted ≤ budget) :
    (run backend leaves formula source sourceAdmitted budget).outcome.Decided :=
  resume_unknown_complete _ (tasks_complete backend leaves formula source sourceAdmitted []) [] 0 budget enough

theorem positive {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : CursorBackend.{u,v} system admitted) (leaves : Leaf → LeafBackend system admitted)
    (formula : Formula Leaf) (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat)
    (read : (run backend leaves formula source sourceAdmitted budget).outcome.answer = some true) :
    denotation leaves formula source :=
  (run backend leaves formula source sourceAdmitted budget).outcome.positive read

theorem negative {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : CursorBackend.{u,v} system admitted) (leaves : Leaf → LeafBackend system admitted)
    (formula : Formula Leaf) (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat)
    (read : (run backend leaves formula source sourceAdmitted budget).outcome.answer = some false) :
    ¬ denotation leaves formula source :=
  (run backend leaves formula source sourceAdmitted budget).outcome.negative read

end Mettapedia.OSLF.NativeTypes.Decision.Machine
