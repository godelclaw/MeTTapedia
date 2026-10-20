import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Source
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ExecutionResponses
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusQuery

/-!
# Automatic discovery for finite contextual native questions

A question fixes its indices, finite rely domains and dependent target before
execution. Its candidate sources are computed by filling the generated source
context with the proposed focus at each rely tuple. No source programs or
response certificates are supplied by the caller.

Each source retains its replay-certified scheduler state across resumption.
Successful readout uses the existing native membership checker and exposes
the same executable certified response family. A negative readout requires
all source agendas to drain; source coverage and its semantic force are
proved in `QueryLaws`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery

open Mettapedia.OSLF.MeTTaIL.Syntax
open FiniteFocusChecking FocusMeaning

variable {installed : Joined.Installed} {ambient : List String}

def sources (question : FocusQuery.Question installed ambient) : List Pattern :=
  (requests question.parameters).flatMap
    (Source.sources question.parameters question.focus)

theorem sources_length (question : FocusQuery.Question installed ambient) :
    (sources question).length ≤ (requests question.parameters).length := by
  have bound : ∀ values : List (RelyValues installed question.index ambient),
      (values.flatMap (Source.sources question.parameters question.focus)).length ≤ values.length := by
    intro values
    induction values with
    | nil => simp
    | cons values tail ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have single := Source.sources_length question.parameters question.focus values
      omega
  exact bound _

structure Session (question : FocusQuery.Question installed ambient) where
  execution : Execution.Batch installed question.index ambient (sources question)

def begin (question : FocusQuery.Question installed ambient) : Session question :=
  ⟨Execution.Batch.begin installed question.index ambient (sources question)⟩

namespace Session

variable {question : FocusQuery.Question installed ambient}

def resume (session : Session question) (fuel : Nat) : Session question :=
  ⟨session.execution.resume fuel⟩

def certificate (session : Session question) : List Witness :=
  session.execution.certificate

def settled (session : Session question) : Bool := session.execution.settled

def finish (session : Session question) : Session question :=
  ⟨session.execution.finish⟩

def membership? (session : Session question) :
    Option (CertifiedMembership question.parameters question.focus) :=
  verify? question.parameters question.focus session.certificate

end Session

inductive Verdict where
  | unknown
  | proved
  | refuted
  | illFormedFocus
  deriving DecidableEq, Repr

def Session.verdict {question : FocusQuery.Question installed ambient}
    (session : Session question) : Verdict :=
  if !checkFocus installed question.index ambient question.focus then .illFormedFocus
  else if FiniteFocusChecking.check question.parameters question.focus session.certificate then .proved
  else if session.settled then .refuted
  else .unknown

/-- This reference-tree cost bounds logical ticks, not physical execution
time. Ordinary `resume` does not need to compute this bound. -/
def completionBudget (question : FocusQuery.Question installed ambient) : Nat :=
  Execution.Batch.completionBudget installed question.index ambient (sources question)

def discover (question : FocusQuery.Question installed ambient) (fuel : Nat) : Session question :=
  (begin question).resume fuel

namespace Session

variable {question : FocusQuery.Question installed ambient}

theorem resume_add (session : Session question) (first extra : Nat) :
    session.resume (first + extra) = (session.resume first).resume extra := by
  cases session
  exact congrArg Session.mk (Execution.Batch.resume_add _ first extra)

@[simp] theorem resume_zero (session : Session question) : session.resume 0 = session := by
  cases session
  exact congrArg Session.mk (Execution.Batch.resume_zero _)

theorem certificate_sublist (session : Session question) (fuel : Nat) :
    session.certificate.Sublist (session.resume fuel).certificate :=
  session.execution.certificate_sublist fuel

theorem certificate_stable (session : Session question) (complete : session.settled = true) (fuel : Nat) :
    (session.resume fuel).certificate = session.certificate :=
  session.execution.certificate_stable complete fuel

theorem settled_preserved (session : Session question) (complete : session.settled = true) (fuel : Nat) :
    (session.resume fuel).settled = true := by
  apply ((session.execution.resume fuel).settled_exact).mpr
  intro position
  have drained := session.execution.settled_exact.mp complete position
  exact (congrArg (·.agenda) (session.execution.source_stable position drained fuel)).trans drained

theorem verdict_stable (session : Session question) (complete : session.settled = true) (fuel : Nat) :
    (session.resume fuel).verdict = session.verdict := by
  simp only [verdict, session.certificate_stable complete fuel,
    session.settled_preserved complete fuel, complete]

theorem resume_settled (session : Session question) (fuel : Nat)
    (enough : completionBudget question ≤ fuel) : (session.resume fuel).settled = true :=
  session.execution.resume_settled fuel enough

theorem finish_settled (session : Session question) : session.finish.settled = true :=
  session.execution.finish_settled

theorem resume_certificate (session : Session question) (fuel : Nat)
    (enough : completionBudget question ≤ fuel) :
    (session.resume fuel).certificate = session.finish.certificate :=
  session.execution.resume_certificate fuel enough

theorem proved_exact (session : Session question) :
    session.verdict = .proved ↔
      FiniteFocusChecking.check question.parameters question.focus session.certificate = true := by
  unfold verdict
  by_cases admitted : checkFocus installed question.index ambient question.focus = true
  · cases checked : FiniteFocusChecking.check question.parameters question.focus session.certificate <;>
      cases complete : session.settled <;> simp_all
  · have refused : checkFocus installed question.index ambient question.focus = false :=
      Bool.eq_false_iff.mpr admitted
    simp [refused, FiniteFocusChecking.check]

theorem proved (session : Session question) (accepted : session.verdict = .proved) : question.Meaning :=
  FiniteFocusChecking.check_sound question.parameters question.focus session.certificate
    (session.proved_exact.mp accepted)

theorem membership?_exact (session : Session question) :
    session.membership?.isSome = true ↔ session.verdict = .proved := by
  exact (verify?_exact question.parameters question.focus session.certificate).trans session.proved_exact.symm

theorem proved_preserved (session : Session question) (accepted : session.verdict = .proved) (fuel : Nat) :
    (session.resume fuel).verdict = .proved := by
  apply (session.resume fuel).proved_exact.mpr
  obtain ⟨admitted, covered⟩ :=
    (FiniteFocusChecking.check_exact _ _ _).mp (session.proved_exact.mp accepted)
  apply (FiniteFocusChecking.check_exact _ _ _).mpr
  refine ⟨admitted, fun values requested => ?_⟩
  obtain ⟨witness, present, valid⟩ := covered values requested
  exact ⟨witness, session.execution.certificate_preserved fuel witness present, valid⟩

theorem illFormedFocus_exact (session : Session question) :
    session.verdict = .illFormedFocus ↔ ¬ FocusAdmitted installed question.index ambient question.focus := by
  rw [← checkFocus_exact]
  cases admitted : checkFocus installed question.index ambient question.focus <;>
    cases checked : FiniteFocusChecking.check question.parameters question.focus session.certificate <;>
      cases complete : session.settled <;> simp_all [verdict]

theorem refuted_checks (session : Session question) :
    session.verdict = .refuted ↔
      checkFocus installed question.index ambient question.focus = true ∧
      FiniteFocusChecking.check question.parameters question.focus session.certificate = false ∧
      session.settled = true := by
  cases admitted : checkFocus installed question.index ambient question.focus <;>
    cases checked : FiniteFocusChecking.check question.parameters question.focus session.certificate <;>
      cases complete : session.settled <;> simp_all [verdict]

/-- The first admitted input not answered by the retained certificate. This
is only a search gap until exhaustive source coverage has been earned. -/
def missingRequest? (session : Session question) : Option (RelyValues installed question.index ambient) :=
  (requests question.parameters).find? fun values =>
    !session.execution.hasResponse question.parameters question.focus values

theorem missingRequest?_sound (session : Session question)
    (values : RelyValues installed question.index ambient)
    (found : session.missingRequest? = some values) :
    Requested question.parameters.meaning values ∧
      session.execution.hasResponse question.parameters question.focus values = false := by
  refine ⟨(requests_exact question.parameters values).mp (List.mem_of_find?_eq_some found), ?_⟩
  simpa using (List.find?_some found)

theorem refuted_missingRequest (session : Session question) (refuted : session.verdict = .refuted) :
    session.missingRequest?.isSome = true := by
  obtain ⟨admitted, rejected, _⟩ := session.refuted_checks.mp refuted
  have failed : (requests question.parameters).all (fun values =>
      session.execution.hasResponse question.parameters question.focus values) = false := by
    simpa only [FiniteFocusChecking.check, admitted, Bool.true_and, certificate,
      Execution.Batch.hasResponse] using rejected
  obtain ⟨values, member, missing⟩ := List.all_eq_false.mp failed
  apply List.find?_isSome.mpr
  exact ⟨values, member, by simpa using missing⟩

end Session

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery
