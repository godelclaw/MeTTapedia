import Mettapedia.CogArch.CollectiveAgency.Lifecycle
import Mettapedia.PLN.Evidence.RevisionMemory

/-!
# An inference team across successive episodes

Two agents form a team, publish an identified report, decline and hand over
work, discharge the obligation with a witness, and dissolve. A subsequent
team retains the report but must obtain fresh consent and grants. Published
testimony remains testimony; this example does not treat membership or voting
as a truth oracle.

All examples run the admission interpreter. None supplies an arbitrary final
state as a substitute for an execution.
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.CollectiveAgency.InferenceHive

open Lifecycle

abbrev Fact := Memory.Content Bool Unit Nat
abbrev Hive := Machine Bool Unit Unit Fact
abbrev Action := Command Bool Unit Unit Fact

def start : Hive := ⟨initial (fun _ => false), ∅, []⟩

/-- A client obtains the current scope before submitting its own request. -/
def issue (s : Hive) (actor : Bool) (nonce : Nat) (command : Action) : Hive :=
  submit .commitmentBound actor s ⟨actor, s.body.generation, s.body.revision, nonce, command⟩

def script (s : Hive) (actions : List (Bool × Nat × Action)) : Hive :=
  actions.foldl (fun state action => issue state action.1 action.2.1 action.2.2) s

def formation : List (Bool × Nat × Action) :=
  [(false, 0, .propose (.form {false, true})),
   (false, 1, .consent), (true, 0, .consent), (false, 2, .form {false, true})]

def collaboration : List (Bool × Nat × Action) :=
  [(false, 3, .grant () false),
   (false, 4, .contribute 7 (.observation true)),
   (false, 5, .accept ()), (true, 1, .refuse ()),
   (false, 6, .offer () true), (true, 2, .takeOver () false),
   (false, 7, .withdraw), (true, 3, .discharge () ⟨.achieved, 42⟩),
   (true, 4, .propose .dissolve), (true, 5, .approve), (true, 6, .dissolve)]

def episode := formation ++ collaboration
def formed := script start formation
def retired := script start episode
def renewed := script retired (formation ++ [(false, 3, .grant () false)])
def twice := script retired episode

theorem formed_with_each_consent :
    formed.body.live = true ∧ formed.body.members = {false, true} ∧
    formed.history.map Prod.snd = [.accepted, .accepted, .accepted, .accepted] := by decide

theorem full_episode :
    retired.body.generation = 1 ∧ retired.body.live = false ∧
    retired.body.members = ∅ ∧ retired.body.grants () = none ∧
    retired.body.commitments () = .discharged ⟨.achieved, 42⟩ ∧
    retired.body.responsible () = some true ∧
    retired.history.map Prod.snd =
      [.accepted, .accepted, .accepted, .accepted, .accepted, .accepted,
       .accepted, .declined, .accepted, .accepted, .accepted, .accepted,
       .accepted, .accepted, .accepted] := by decide

theorem durable_report :
    retired.body.knowledge = {((false, 7), .observation true)} ∧
    renewed.body.knowledge = retired.body.knowledge := by decide

theorem renewal_requires_new_grant :
    Authorized renewed.body false 1 () ∧ ¬ Authorized renewed.body false 0 () := by decide

theorem recurring_episodes :
    twice.body.generation = 2 ∧ twice.history.length = 30 ∧
    twice.body.knowledge = retired.body.knowledge ∧ twice.body.live = false := by decide +kernel

def working := issue formed false 5 (.accept ())
def exitRequest : Request Bool Unit Unit Fact := ⟨false, 0, 1, 6, .withdraw⟩

theorem exit_profiles_differ :
    (execute .immediate working exitRequest).body.members = {true} ∧
    (execute .immediate working exitRequest).body.commitments () = .active ∧
    (execute .immediate working exitRequest).body.responsible () = some false ∧
    (execute .commitmentBound working exitRequest).body.members = {false, true} := by decide

theorem refusal_does_not_discharge :
    (issue working true 1 (.refuse ())).body.commitments () = .active ∧
    (issue working true 1 (.refuse ())).history.getLast? =
      some (⟨true, 0, 1, 1, .refuse ()⟩, .declined) := by decide

theorem missing_consent_refused :
    (script start [(false, 0, .propose (.form {false, true})),
      (false, 1, .consent), (false, 2, .form {false, true})]).body.live = false := by decide

theorem membership_is_not_resource_ownership :
    ¬ Allowed .commitmentBound formed.body true (.grant () true) := by decide

theorem unilateral_handover_refused :
    (issue working true 2 (.takeOver () false)).body.responsible () = some false := by decide

theorem previous_adoption_offer_cannot_revive :
    let next := script working [(false, 6, .offer () true),
      (false, 7, .discharge () ⟨.achieved, 42⟩), (false, 8, .accept ()),
      (true, 2, .takeOver () false)]
    next.body.commitments () = .active ∧ next.body.responsible () = some false ∧
      next.body.offers = ∅ := by decide

theorem last_departure_allows_reformation :
    let emptyTeam := script formed [(false, 7, .withdraw), (true, 1, .withdraw)]
    emptyTeam.body.live = false ∧ emptyTeam.body.generation = 1 ∧
      (script emptyTeam formation).body.live = true ∧
      (script emptyTeam formation).body.generation = 1 := by decide +kernel

theorem stale_scope_refused :
    (execute .commitmentBound renewed ⟨false, 0, 1, 99, .accept ()⟩).body.commitments () =
      renewed.body.commitments () ∧
    (execute .commitmentBound renewed ⟨false, 0, 1, 99, .accept ()⟩).history.getLast? =
      some (⟨false, 0, 1, 99, .accept ()⟩, .stale) := by decide

theorem majority_cannot_replace_consent :
    let proposed := issue formed false 8 (.propose (.admit true))
    let approved := script proposed [(false, 9, .approve), (true, 4, .approve)]
    Majority approved.body ∧ ¬ Allowed .commitmentBound approved.body false (.admit true) := by decide

theorem collective_vote_cannot_bypass_commitments :
    let approved := script working [(false, 8, .propose .dissolve),
      (false, 9, .approve), (true, 4, .approve)]
    Majority approved.body ∧ ¬ Allowed .commitmentBound approved.body false .dissolve ∧
      Allowed .immediate approved.body false .dissolve := by decide

theorem repeated_ballots_do_not_add_voters :
    let approved := script formed [(false, 8, .propose .dissolve),
      (false, 9, .approve), (false, 10, .approve), (false, 11, .approve)]
    approved.body.approvals.card = 1 ∧ ¬ Majority approved.body := by decide

theorem old_proposal_consent_refused :
    let proposed := issue formed false 8 (.propose (.admit true))
    let attempted := submit .commitmentBound true proposed ⟨true, 0, 1, 9, .consent⟩
    true ∉ attempted.body.consents ∧ attempted.history.getLast? =
      some (⟨true, 0, 1, 9, .consent⟩, .stale) := by decide

theorem impersonated_consent_refused :
    let proposed := issue formed false 8 (.propose (.admit true))
    let attempted := submit .commitmentBound false proposed ⟨true, 0, 2, 9, .consent⟩
    true ∉ attempted.body.consents ∧ (0, true, 9) ∉ attempted.seen := by decide

theorem conflicting_reports_are_not_resolved_by_voting :
    let s := script formed [(false, 4, .contribute 7 (.observation true)),
      (false, 10, .contribute 7 (.observation false))]
    ((false, 7), .observation true) ∈ s.body.knowledge ∧
    ((false, 7), .observation false) ∈ s.body.knowledge := by decide

/-- Identified observations pool by union, the existing PLN ledger regime. -/
theorem identified_evidence_replay (ledger : Finset Bool) (observation : Bool) :
    Mettapedia.PLN.Evidence.RevisionMemory.Identified.deliver
      (Mettapedia.PLN.Evidence.RevisionMemory.Identified.deliver ledger observation) observation =
    Mettapedia.PLN.Evidence.RevisionMemory.Identified.deliver ledger observation := by
  simp [Mettapedia.PLN.Evidence.RevisionMemory.Identified.deliver]

end Mettapedia.CogArch.CollectiveAgency.InferenceHive
