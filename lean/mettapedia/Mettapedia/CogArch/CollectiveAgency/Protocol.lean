import Mettapedia.CogArch.CollectiveAgency.Lifecycle
import Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
import Mettapedia.GSLT.Causality.OccurrenceHistory

/-!
# Typed operational presentation of a collective

A command retains the authenticated caller separately from the request.
The independently given submission rules agree in both directions with the
executable lifecycle. The existing indexed-polynomial protocol then supplies
its GSLT. Paths preserve every request occurrence, including declined,
blocked, stale and replayed attempts.

This is a typed operational presentation, not a textual serialization or a
native-runtime realization. The complete coalition is itself an agent at this
interface. Products below apply to genuinely separate states and resources;
physical resource sharing instead requires the arbitration in `Swarm`.
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.CollectiveAgency.Protocol

open Lifecycle
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.GSLT.Causality.OccurrenceHistory

variable {A Task Resource Fact : Type} [DecidableEq A] [DecidableEq Task]
  [DecidableEq Resource] [DecidableEq Fact] [Fintype Task]

inductive SubmissionStep (profile : ExitProfile) (s : Machine A Task Resource Fact)
    (principal : A) (r : Request A Task Resource Fact) : Machine A Task Resource Fact → Prop where
  | authenticated {t} : r.actor = principal → Lifecycle.Step profile s r t →
      SubmissionStep profile s principal r t
  | unauthenticated : r.actor ≠ principal → SubmissionStep profile s principal r
      { s with history := s.history ++ [(r, .blocked)] }

theorem submit_iff (profile : ExitProfile) (s t : Machine A Task Resource Fact)
    (principal : A) (r : Request A Task Resource Fact) :
    submit profile principal s r = t ↔ SubmissionStep profile s principal r t := by
  constructor
  · intro h
    by_cases auth : r.actor = principal
    · exact .authenticated auth ((execute_iff profile s t r).mp (by simpa [submit, auth] using h))
    · have eqt : { s with history := s.history ++ [(r, .blocked)] } = t := by
        simpa [submit, auth] using h
      exact eqt ▸ SubmissionStep.unauthenticated (s := s) auth
  · intro h
    cases h with
    | authenticated auth step => simpa [submit, auth] using (execute_iff profile s _ r).mpr step
    | unauthenticated mismatch => simp [submit, mismatch]

def sourceTheory (profile : ExitProfile) : GSLT where
  Term := Machine A Task Resource Fact
  equations := ⟨Eq, eq_equivalence⟩
  rewrites s t := ∃ principal request, SubmissionStep profile s principal request t
  rewrites_resp_left := by rintro _ _ _ rfl step; exact ⟨_, step, rfl⟩
  rewrites_resp_right := by rintro _ _ _ step rfl; exact step

def protocol (profile : ExitProfile) : ProtocolPolynomial (Machine A Task Resource Fact) where
  Shape := fun _ _ => A × Request A Task Resource Fact
  Position := fun _ => Unit
  next := fun {_} {s} command _ => submit profile command.1 s command.2

/-- Both preservation and reflection refer to the authored submission rules. -/
theorem operational_adequacy (profile : ExitProfile) (s t : Machine A Task Resource Fact) :
    (lts (protocol profile)).Step s t ↔ (sourceTheory profile).Step s t := by
  constructor
  · rintro ⟨move⟩
    cases move with
    | fire command response =>
      exact ⟨command.1, command.2, (submit_iff profile s _ command.1 command.2).mp rfl⟩
  · rintro ⟨principal, request, step⟩
    have equal := (submit_iff profile s t principal request).mpr step
    exact equal ▸ Nonempty.intro (Move.fire (protocol := protocol profile) (principal, request) ())

abbrev Presentation (profile : ExitProfile) := interaction (protocol (A := A) (Task := Task)
  (Resource := Resource) (Fact := Fact) profile)

def wordRun (profile : ExitProfile) (s : Machine A Task Resource Fact)
    (word : List (A × Request A Task Resource Fact)) : Machine A Task Resource Fact :=
  word.foldl (fun state command => submit profile command.1 state command.2) s

def wordPath (profile : ExitProfile) : (s : Machine A Task Resource Fact) →
    (word : List (A × Request A Task Resource Fact)) →
      OccurrencePath (Presentation profile) s (wordRun profile s word)
  | s, [] => OccurrencePath.refl (P := Presentation profile) s
  | s, command :: rest =>
      .cons ⟨(), Move.fire (protocol := protocol profile) command ()⟩
        (wordPath profile (submit profile command.1 s command.2) rest)

def entries (profile : ExitProfile) : {s t : Machine A Task Resource Fact} →
    OccurrencePath (Presentation profile) s t → List (A × Request A Task Resource Fact)
  | _, _, .refl _ => []
  | _, _, .cons occurrence rest =>
      (match occurrence.evidence with | .fire command _ => command) :: entries profile rest

theorem wordPath_entries (profile : ExitProfile) (s : Machine A Task Resource Fact)
    (word : List (A × Request A Task Resource Fact)) : entries profile (wordPath profile s word) = word := by
  induction word generalizing s with
  | nil => rfl
  | cons command rest ih => exact congrArg (command :: ·) (ih _)

theorem path_interpretation (profile : ExitProfile) {s t : Machine A Task Resource Fact}
    (path : OccurrencePath (Presentation profile) s t) : wordRun profile s (entries profile path) = t := by
  refine OccurrencePath.rec
    (motive := fun source target trace => wordRun profile source (entries profile trace) = target)
    (fun _ => rfl) ?_ path
  intro source middle target occurrence rest ih
  obtain ⟨site, move⟩ := occurrence
  cases move with
  | fire command response =>
    cases response
    exact ih

theorem exact_request_count (profile : ExitProfile) (s : Machine A Task Resource Fact)
    (word : List (A × Request A Task Resource Fact)) :
    (entries profile (wordPath profile s word)).length = word.length := by rw [wordPath_entries]

/-- Disjoint component states compose without a central decision maker. -/
def productStep (leftProfile rightProfile : ExitProfile)
    (s : Machine A Task Resource Fact × Machine A Task Resource Fact)
    (command : Sum (A × Request A Task Resource Fact) (A × Request A Task Resource Fact)) :=
  match command with
  | .inl c => (submit leftProfile c.1 s.1 c.2, s.2)
  | .inr c => (s.1, submit rightProfile c.1 s.2 c.2)

theorem independent_collectives_commute (leftProfile rightProfile : ExitProfile)
    (s : Machine A Task Resource Fact × Machine A Task Resource Fact)
    (left right : A × Request A Task Resource Fact) :
    productStep leftProfile rightProfile (productStep leftProfile rightProfile s (.inl left)) (.inr right) =
      productStep leftProfile rightProfile (productStep leftProfile rightProfile s (.inr right)) (.inl left) := rfl

theorem unrelated_coalition_preserved (leftProfile rightProfile : ExitProfile)
    (s : Machine A Task Resource Fact × Machine A Task Resource Fact)
    (left : A × Request A Task Resource Fact) :
    (productStep leftProfile rightProfile s (.inl left)).2 = s.2 := rfl

end Mettapedia.CogArch.CollectiveAgency.Protocol
