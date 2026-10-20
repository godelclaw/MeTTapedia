import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Query
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.SourceCompleteness

/-!
# Complete automatic finite contextual native membership

Reconstruction supplies every source that can satisfy an admitted request.
The independently complete scheduled executor supplies its full receipts.
The existing native response checker therefore decides the semantic family
after settlement, without caller-supplied source coverage or certificates.

A semantic counterexample retains a particular admitted input and proves
that no source firing can answer it. Failed evidence before settlement has
no such force.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Modal.NativeReceiptRechecking
open FiniteFocusChecking FocusMeaning

variable {installed : Joined.Installed} {ambient : List String}
  {question : FocusQuery.Question installed ambient}

theorem response_source_mem (question : FocusQuery.Question installed ambient)
    (values : RelyValues installed question.index ambient)
    (requested : Requested question.parameters.meaning values) (source : Pattern) (payload : Payload)
    (valid : SourceResponse question.parameters.meaning question.focus values source payload) :
    source ∈ sources question := by
  exact List.mem_flatMap.mpr ⟨values, (requests_exact question.parameters values).mpr requested,
    Source.response_source_mem question.parameters question.focus values source payload valid⟩

namespace Session

theorem check_exact (session : Session question) (complete : session.settled = true) :
    FiniteFocusChecking.check question.parameters question.focus session.certificate = true ↔
      question.Meaning := by
  constructor
  · exact FiniteFocusChecking.check_sound question.parameters question.focus session.certificate
  · intro member
    have specified := (inhabits_iff_source question.parameters.meaning question.focus).mp member
    apply (session.execution.check_exact complete question.parameters question.focus).mpr
    refine ⟨specified.1, fun values requested => ?_⟩
    obtain ⟨source, payload, response⟩ := specified.2 values requested
    exact ⟨source, response_source_mem question values requested source payload response, payload, response⟩

theorem proved_iff (session : Session question) (complete : session.settled = true) :
    session.verdict = .proved ↔ question.Meaning :=
  session.proved_exact.trans (session.check_exact complete)

theorem refuted (session : Session question) (rejected : session.verdict = .refuted) :
    ¬ question.Meaning := by
  obtain ⟨_, checked, complete⟩ := session.refuted_checks.mp rejected
  intro member
  have accepted := (session.check_exact complete).mpr member
  rw [checked] at accepted
  cases accepted

theorem refuted_iff (session : Session question) :
    session.verdict = .refuted ↔
      FocusAdmitted installed question.index ambient question.focus ∧
      session.settled = true ∧ ¬ question.Meaning := by
  constructor
  · intro rejected
    obtain ⟨admitted, _, complete⟩ := session.refuted_checks.mp rejected
    exact ⟨(checkFocus_exact _ _ _ _).mp admitted, complete, session.refuted rejected⟩
  · rintro ⟨admitted, complete, notMember⟩
    apply session.refuted_checks.mpr
    refine ⟨(checkFocus_exact _ _ _ _).mpr admitted, ?_, complete⟩
    exact Bool.eq_false_iff.mpr fun checked => notMember ((session.check_exact complete).mp checked)

theorem decided (session : Session question) (complete : session.settled = true)
    (admitted : FocusAdmitted installed question.index ambient question.focus) :
    session.verdict = .proved ∨ session.verdict = .refuted := by
  cases checked : FiniteFocusChecking.check question.parameters question.focus session.certificate
  · exact Or.inr (session.refuted_checks.mpr ⟨(checkFocus_exact _ _ _ _).mpr admitted, checked, complete⟩)
  · exact Or.inl (session.proved_exact.mpr checked)

/-- Every admitted finite question is semantically decided within its
computed source-execution tick bound. It is not a universal native-type
decidability statement, nor a physical runtime bound. -/
theorem resume_decided (session : Session question) (fuel : Nat)
    (enough : completionBudget question ≤ fuel)
    (admitted : FocusAdmitted installed question.index ambient question.focus) :
    (session.resume fuel).verdict = .proved ∨ (session.resume fuel).verdict = .refuted :=
  (session.resume fuel).decided (session.resume_settled fuel enough) admitted

theorem resume_proved_iff (session : Session question) (fuel : Nat)
    (enough : completionBudget question ≤ fuel) :
    (session.resume fuel).verdict = .proved ↔ question.Meaning :=
  (session.resume fuel).proved_iff (session.resume_settled fuel enough)

theorem finish_proved_iff (session : Session question) :
    session.finish.verdict = .proved ↔ question.Meaning :=
  session.finish.proved_iff session.finish_settled

theorem no_response (session : Session question) (complete : session.settled = true)
    (values : RelyValues installed question.index ambient)
    (requested : Requested question.parameters.meaning values)
    (missing : session.execution.hasResponse question.parameters question.focus values = false)
    (source : Pattern) (payload : Payload) :
    ¬ SourceResponse question.parameters.meaning question.focus values source payload := by
  intro valid
  exact session.execution.no_response complete question.parameters question.focus values missing source
    (response_source_mem question values requested source payload valid) payload valid

end Session

structure Counterexample (question : FocusQuery.Question installed ambient) where
  values : RelyValues installed question.index ambient
  requested : Requested question.parameters.meaning values
  noResponse : ∀ source payload,
    ¬ SourceResponse question.parameters.meaning question.focus values source payload

theorem Counterexample.not_member (counterexample : Counterexample question) : ¬ question.Meaning := by
  intro member
  obtain ⟨source, payload, response⟩ :=
    ((inhabits_iff_source question.parameters.meaning question.focus).mp member).2
      counterexample.values counterexample.requested
  exact counterexample.noResponse source payload response

namespace Session

/-- Extract the first unanswered admitted input only after its absence is
proved globally, including sources not explicitly listed by the caller. -/
def counterexample? (session : Session question) : Option (Counterexample question) :=
  if complete : session.settled = true then
    match found : session.missingRequest? with
    | none => none
    | some values =>
      let facts := session.missingRequest?_sound values found
      some ⟨values, facts.1, session.no_response complete values facts.1 facts.2⟩
  else none

theorem counterexample?_exact (session : Session question) :
    session.counterexample?.isSome = true ↔
      session.settled = true ∧ session.missingRequest?.isSome = true := by
  unfold counterexample?
  split
  · split <;> simp_all
  · simp_all

theorem refuted_counterexample (session : Session question) (rejected : session.verdict = .refuted) :
    session.counterexample?.isSome = true :=
  session.counterexample?_exact.mpr
    ⟨(session.refuted_checks.mp rejected).2.2, session.refuted_missingRequest rejected⟩

end Session

theorem discover_proved_iff (question : FocusQuery.Question installed ambient) (fuel : Nat)
    (enough : completionBudget question ≤ fuel) :
    (discover question fuel).verdict = .proved ↔ question.Meaning :=
  (begin question).resume_proved_iff fuel enough

theorem discover_decided (question : FocusQuery.Question installed ambient) (fuel : Nat)
    (enough : completionBudget question ≤ fuel)
    (admitted : FocusAdmitted installed question.index ambient question.focus) :
    (discover question fuel).verdict = .proved ∨ (discover question fuel).verdict = .refuted :=
  (begin question).resume_decided fuel enough admitted

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery
