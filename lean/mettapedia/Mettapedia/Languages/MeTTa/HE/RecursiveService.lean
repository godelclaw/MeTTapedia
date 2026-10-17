import Mettapedia.Languages.MeTTa.HE.RecursiveExecution

/-!
# The retained HE evaluator as a service machine

A host language may hand a request to the retained HE evaluator and receive one
value in reply. The evaluator's result occurrences are published as the
service's own events, and its completed result multiset determines the reply.
A single occurrence that reads as a value answers the request. Insufficient
evaluator or leaf depth suspends the retained configuration; it is not a
completed no-result reply. No occurrence,
several occurrences, or an occurrence that does not read as a value is a
failure: a reply never selects one result from several, so it does not depend
on the order of the results (`answer_perm`). A completed service run publishes
exactly the covered evaluator's results and replies with their answer
(`service_finished`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveService

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine RecursiveExecution
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Why an evaluation does not answer a request with one value. -/
inductive Failure where
  | noResult
  | several (count : Nat)
  | unreadable (value : Atom)
  deriving DecidableEq, Repr

variable {Value : Type} (decode : Atom → Option Value)

/-- The reply to a request, from the complete result multiset. -/
def answer : ResultSet → Reply Value Failure
  | [] => .faulted .noResult
  | [(value, _)] =>
      match decode value with
      | some read => .returned read
      | none => .faulted (.unreadable value)
  | results => .faulted (.several results.length)

theorem answer_of_two_le (results : ResultSet) (several : 2 ≤ results.length) :
    answer decode results = .faulted (.several results.length) := by
  match results, several with
  | _ :: _ :: _, _ => rfl

/-- The reply depends only on the result multiset, not on the order of its occurrences. -/
theorem answer_perm {first second : ResultSet} (perm : first.Perm second) :
    answer decode first = answer decode second := by
  have length := perm.length_eq
  match first, second, perm, length with
  | [], second, perm, _ => rw [perm.nil_eq]
  | [single], second, perm, _ => rw [List.singleton_perm.mp perm]
  | _ :: _ :: rest, second, _, length =>
      rw [answer_of_two_le decode _ (by simp), answer_of_two_le decode second (by simp at length; omega), length]

/-- The evaluator as a service: its results become service events, and its final
result history becomes the reply. -/
def service {Event : Type} (dispatch : GroundedDispatch) (embed : ResultPair → Event) :
    Machine Configuration Event (Reply Value Failure) Checked.ResourceRequest :=
  (Checked.machine dispatch).relabel embed (fun final => answer decode final.emitted) id

/-- **A completed service run publishes exactly the evaluator's results and
replies with their answer.** -/
theorem service_finished {Event : Type} (dispatch : GroundedDispatch) (embed : ResultPair → Event)
    (space : Space) (task : Task) (fuel : Nat) (events : List Event) (reply : Reply Value Failure)
    (finished : (service decode dispatch embed).run fuel (Configuration.initial space task) =
      (events, .finished reply)) :
    events = (task.denote space dispatch).map embed ∧ reply = answer decode (task.denote space dispatch) := by
  rw [service, Machine.run_relabel] at finished
  rcases ran : (Checked.machine dispatch).run fuel (Configuration.initial space task) with ⟨results, outcome⟩
  rw [ran] at finished
  cases outcome with
  | finished final =>
      simp only [Outcome.relabel, Prod.mk.injEq, Outcome.finished.injEq] at finished
      obtain ⟨rfl, rfl⟩ := finished
      obtain ⟨meaning, history, _⟩ := finished_results space dispatch task fuel results final
        (Checked.finished_refines dispatch fuel _ results final ran)
      subst meaning
      exact ⟨rfl, by rw [history]⟩
  | faulted => simp [Outcome.relabel] at finished
  | suspended _ _ => simp [Outcome.relabel] at finished
  | stuck _ => simp [Outcome.relabel] at finished
  | exhausted _ => simp [Outcome.relabel] at finished

end Mettapedia.Languages.MeTTa.HE.RecursiveService
