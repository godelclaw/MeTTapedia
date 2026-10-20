import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SourceExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.QueryTransport

/-!
# Native questions answered by actual descent-program evaluations

The target computes source observations. The existing native checker consumes
their decoded receipts. Every completed target evaluation has exactly the
observation of the retained source session; this proves both preservation
and reflection, including completion provenance for negative answers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.QueryExecution

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open IndexedModal FiniteFocusChecking FocusMeaning
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open MeTTaIL CompleteExecution
open QueryTransport (sourceAt)

variable {installed : Joined.Installed} {ambient : List String}
  {question : FocusQuery.Question installed ambient}

def portable (_question : FocusQuery.Question installed ambient) : Bool :=
  installed.indexed.operational.Environment.provider.dynamicRelations.isEmpty

theorem portable_exact (question : FocusQuery.Question installed ambient) :
    portable question = true ↔
      installed.indexed.operational.Environment.provider.dynamicRelations = [] :=
  List.isEmpty_iff

def code (session : Discovery.Session question) (fuel : Nat)
    (position : Fin (Discovery.sources question).length) : Atom :=
  SourceExecution.resumeCode installed.indexed.operational.Environment (sourceAt question position)
    (DescentCodec.stateTerm (session.execution.runs position).state) fuel

/-- A client resumes directly from the returned wire snapshot. It need not
rerun the Lean reference scheduler to construct its next target expression. -/
def continue? (question : FocusQuery.Question installed ambient)
    (position : Fin (Discovery.sources question).length) (packet : Atom) (fuel : Nat) : Option Atom := do
  let observation ← QueryTransport.decodeSource? installed.indexed.operational.Environment
    (sourceAt question position) packet
  pure (SourceExecution.resumeCode installed.indexed.operational.Environment
    (sourceAt question position) observation.snapshot fuel)

@[simp] theorem continue?_observeSession (session : Discovery.Session question)
    (position : Fin (Discovery.sources question).length) (fuel : Nat) :
    continue? question position (QueryTransport.observeSession session position) fuel =
      some (code session fuel position) := by
  unfold continue? QueryTransport.observeSession
  rw [QueryTransport.decodeSource?_observe installed.indexed.operational.Environment
    (sourceAt question position) (session.execution.runs position).state]
  rfl

/-- Complete ordered results of the actual target evaluator, one per
computed candidate source. This relation contains no native verdict. -/
def Completes (before : Effects.State) (session : Discovery.Session question) (fuel : Nat)
    (packets : QueryTransport.Packets question) : Prop :=
  ∀ position, ∃ targetFuel, Eval.run descentLibrary.runtime targetFuel
    {state := before, control := .evaluate [] (code session fuel position)} =
      .complete before [packets position] [] []

theorem completes_iff (before : Effects.State) (session : Discovery.Session question) (fuel : Nat)
    (ready : portable question = true) (packets : QueryTransport.Packets question) :
    Completes before session fuel packets ↔
      packets = QueryTransport.observeSession (session.resume fuel) := by
  constructor
  · intro completed
    funext position
    have exactResult :=
      (SourceExecution.resume_completed_iff before installed.indexed.operational
        (sourceAt question position) ((portable_exact question).mp ready)
        (session.execution.runs position) fuel before [packets position] [] []).mp (completed position)
    exact (List.cons.inj exactResult.2.1).1
  · intro same
    subst packets
    intro position
    exact (SourceExecution.resume_completed_iff before installed.indexed.operational
      (sourceAt question position) ((portable_exact question).mp ready)
      (session.execution.runs position) fuel before _ [] []).mpr ⟨rfl, rfl, rfl, rfl⟩

/-- Every resumed source query has a completed target execution; logical
scheduler fuel is distinct from the evaluator fuel witnessing this fact. -/
theorem target_exists (before : Effects.State) (session : Discovery.Session question) (fuel : Nat)
    (ready : portable question = true) :
    ∃ packets, Completes before session fuel packets :=
  ⟨_, (completes_iff before session fuel ready _).mpr rfl⟩

theorem receive_exact (before : Effects.State) (session : Discovery.Session question) (fuel : Nat)
    (ready : portable question = true) (packets : QueryTransport.Packets question)
    (completed : Completes before session fuel packets) :
    QueryTransport.receive question packets = some (session.resume fuel).verdict := by
  rw [(completes_iff before session fuel ready packets).mp completed]
  exact QueryTransport.receive_observeSession _

theorem membership_exact (before : Effects.State) (session : Discovery.Session question) (fuel : Nat)
    (ready : portable question = true) (packets : QueryTransport.Packets question)
    (completed : Completes before session fuel packets) :
    QueryTransport.membership? question packets = (session.resume fuel).membership? := by
  rw [(completes_iff before session fuel ready packets).mp completed]
  exact QueryTransport.membership?_observeSession _

theorem native_membership_iff_target (before : Effects.State) (session : Discovery.Session question)
    (fuel : Nat) (ready : portable question = true)
    (enough : Discovery.completionBudget question ≤ fuel) :
    (∃ packets, Completes before session fuel packets ∧
      QueryTransport.receive question packets = some .proved) ↔ question.Meaning := by
  constructor
  · rintro ⟨packets, _, accepted⟩
    exact QueryTransport.receive_proved_sound question packets accepted
  · intro member
    obtain ⟨packets, completed⟩ := target_exists before session fuel ready
    refine ⟨packets, completed, ?_⟩
    rw [receive_exact before session fuel ready packets completed]
    exact congrArg some ((session.resume_proved_iff fuel enough).mpr member)

theorem native_nonmembership_iff_target (before : Effects.State) (session : Discovery.Session question)
    (fuel : Nat) (ready : portable question = true)
    (enough : Discovery.completionBudget question ≤ fuel)
    (admitted : FocusAdmitted installed question.index ambient question.focus) :
    (∃ packets, Completes before session fuel packets ∧
      QueryTransport.receive question packets = some .refuted) ↔ ¬ question.Meaning := by
  constructor
  · rintro ⟨packets, completed, rejected⟩
    exact QueryTransport.receive_refuted _ packets
      ((completes_iff before session fuel ready packets).mp completed) rejected
  · intro absent
    obtain ⟨packets, completed⟩ := target_exists before session fuel ready
    refine ⟨packets, completed, ?_⟩
    rw [receive_exact before session fuel ready packets completed]
    exact congrArg some ((session.resume fuel).refuted_iff.mpr
      ⟨admitted, session.resume_settled fuel enough, absent⟩)

theorem refuted_counterexample (before : Effects.State) (session : Discovery.Session question)
    (fuel : Nat) (ready : portable question = true) (packets : QueryTransport.Packets question)
    (completed : Completes before session fuel packets)
    (rejected : QueryTransport.receive question packets = some .refuted) :
    (QueryTransport.counterexample? (session.resume fuel) packets
      ((completes_iff before session fuel ready packets).mp completed)).isSome = true :=
  QueryTransport.counterexample?_returned _ packets _ rejected

theorem unfinished_unknown (before : Effects.State) (session : Discovery.Session question)
    (fuel : Nat) (ready : portable question = true) (packets : QueryTransport.Packets question)
    (completed : Completes before session fuel packets)
    (admitted : checkFocus installed question.index ambient question.focus = true)
    (unanswered : check question.parameters question.focus (session.resume fuel).certificate = false)
    (unfinished : (session.resume fuel).settled = false) :
    QueryTransport.receive question packets = some .unknown :=
  QueryTransport.receive_unfinished_unknown _ packets
    ((completes_iff before session fuel ready packets).mp completed) admitted unanswered unfinished

theorem receive_resume_add (before : Effects.State) (session : Discovery.Session question)
    (first extra : Nat) (ready : portable question = true)
    (whole split : QueryTransport.Packets question)
    (one : Completes before session (first + extra) whole)
    (two : Completes before (session.resume first) extra split) : whole = split := by
  rw [(completes_iff before session (first + extra) ready whole).mp one,
    (completes_iff before (session.resume first) extra ready split).mp two,
    session.resume_add]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.QueryExecution
