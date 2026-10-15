import Mettapedia.Cybernetics.IntentionCoherence
import Mettapedia.Cybernetics.StructurePreservingRepair
import Mettapedia.Ethics.TargetCenteredVirtue

/-!
# Recipient-centered care and authorized becoming

Care scope, authority and participation are distinct.  A concrete event
retains received decisions; possible consent or a helper's success claim does
not supply a decision in that event.  The care criterion requires an
authenticated recipient decision, continued presence, preservation of
available choices, and an outcome acceptable from the recipient's resulting
position.  All requirements remain recipient-indexed.

Values may change through authorized participation.  The repair bridge reuses
`StructurePreservingRepair.Repair`, with its exact concrete change retained.
An invariant can preserve subject presence and decision capacity without
freezing every preference.  Care histories reuse the existing proof-relevant
`Individuation.Process` and preserve recipient capacities under composition.

The controls construct an approved preference-changing repair, show that the
same displayed endpoint without a recipient decision fails participation,
reject forged helper decisions and erasure, and retain capacity for later
recipient-authorized revision.  A coordinated intermediate care scope gives
a countermodel to deriving universal care from intention coherence alone;
it is not a model of developmental convergence or an empirical refutation of
a proposed moral attractor.

This is an explicit mathematical reconstruction of Z. Goertzel's *Good and
Evil* (2024), especially recipient self-determination, together with the open
individuation account of D. Weinbaum and V. Veitas (2015), arXiv:1505.06366.
It assigns no phenomenal scalar or consciousness status to its participants.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.RecipientCenteredCare

open Mettapedia.Cybernetics
open Mettapedia.Cybernetics.Individuation
open Mettapedia.Cybernetics.StructurePreservingRepair

universe u

/-- The recipient's interface remains distinct from a helper's evaluation. -/
structure Interface (State Recipient : Type u) (Choice : Recipient → Type u)
    (Decision : Type u) where
  Present : State → Recipient → Prop
  available : State → (recipient : Recipient) → Set (Choice recipient)
  Accepts : State → (recipient : Recipient) → Choice recipient → Prop
  Authenticates : Recipient → Decision → Prop
  Approves : Decision → State → State → Prop

/-- An event retains its concrete change and the decisions actually received
from each recipient.  Lists preserve multiplicity and order. -/
structure Event {State Value Misfit : Type u}
    (problem : Problem.{u, u, u, u} State Value Misfit)
    (Recipient Decision : Type u) (source target : State) where
  change : problem.Change source target
  received : Recipient → List Decision

namespace Interface

variable {State Recipient Decision Value Misfit : Type u}
    {Choice : Recipient → Type u}
  (interface : Interface State Recipient Choice Decision)
  {problem : Problem.{u, u, u, u} State Value Misfit}
  {source target : State}

/-- Participation requires a matching authenticated decision in this event,
not merely the existence of a decision that could have been given. -/
def Participates (scope : Set Recipient)
    (event : Event problem Recipient Decision source target) : Prop :=
  ∀ recipient ∈ scope, ∃ decision ∈ event.received recipient,
    interface.Authenticates recipient decision ∧
      interface.Approves decision source target

/-- Presence and the full declared choice interface survive.  Value
preferences are not required to remain equal. -/
def PreservesAgency (scope : Set Recipient) (source target : State) : Prop :=
  ∀ recipient ∈ scope, interface.Present source recipient ∧
    interface.Present target recipient ∧
    interface.available source recipient ⊆ interface.available target recipient

/-- Every cared-for recipient has an available acceptable outcome according
to their resulting position.  There is no global score in this criterion. -/
def Acceptable (scope : Set Recipient) (target : State) : Prop :=
  ∀ recipient ∈ scope, ∃ choice ∈ interface.available target recipient,
    interface.Accepts target recipient choice

/-- Recipient-centered action combines recorded participation, retained
agency and recipient-indexed outcome acceptance. -/
def RecipientCentered (scope : Set Recipient)
    (event : Event problem Recipient Decision source target) : Prop :=
  interface.Participates scope event ∧
    interface.PreservesAgency scope source target ∧
    interface.Acceptable scope target

/-- Absence of a recipient's decision cannot be repaired by a helper's claim
that the endpoint is acceptable. -/
theorem missing_decision_blocks_participation {scope : Set Recipient}
    (event : Event problem Recipient Decision source target) {recipient : Recipient}
    (caredFor : recipient ∈ scope) (missing : event.received recipient = []) :
    ¬ interface.Participates scope event := by
  intro participation
  rcases participation recipient caredFor with ⟨decision, received, _, _⟩
  simp [missing] at received

/-- A recipient can be erased even when a helper's separate report says
success; such a target violates this agency criterion. -/
theorem absent_target_blocks_agency {scope : Set Recipient} {recipient : Recipient}
    (caredFor : recipient ∈ scope) (absent : ¬ interface.Present target recipient) :
    ¬ interface.PreservesAgency scope source target := by
  intro agency
  exact absent (agency recipient caredFor).2.1

/-- A capability lost at the target remains visible recipient by recipient. -/
theorem lost_choice_blocks_agency {scope : Set Recipient} {recipient : Recipient}
    {choice : Choice recipient} (caredFor : recipient ∈ scope)
    (before : choice ∈ interface.available source recipient)
    (lost : choice ∉ interface.available target recipient) :
    ¬ interface.PreservesAgency scope source target := by
  intro agency
  exact lost ((agency recipient caredFor).2.2 before)

/-- Agency preservation composes without identifying recipient preferences. -/
theorem preservesAgency_comp {scope : Set Recipient} {middle : State}
    (first : interface.PreservesAgency scope source middle)
    (last : interface.PreservesAgency scope middle target) :
    interface.PreservesAgency scope source target := by
  intro recipient caredFor
  exact ⟨(first recipient caredFor).1, (last recipient caredFor).2.1,
    ((first recipient caredFor).2.2).trans ((last recipient caredFor).2.2)⟩

end Interface

/-- A care certificate reuses the existing repair theorem and identifies its
change with the exact witnessed event, rather than validating a different
change with the same endpoint. -/
structure CertifiedRepair {State Recipient Decision Value Misfit : Type u}
    {Choice : Recipient → Type u}
    {problem : Problem.{u, u, u, u} State Value Misfit}
    (interface : Interface State Recipient Choice Decision) (scope : Set Recipient)
    {source target : State} (event : Event problem Recipient Decision source target) where
  scope_nonempty : scope.Nonempty
  repair : {repair : Repair problem source target // repair.evidence = event.change}
  recipientCentered : interface.RecipientCentered scope event

/-- The recorded care histories use the existing process abstraction. -/
def processTheory {State Recipient Decision Value Misfit : Type u}
    {Choice : Recipient → Type u}
    (problem : Problem.{u, u, u, u} State Value Misfit)
    (interface : Interface State Recipient Choice Decision) (scope : Set Recipient) :
    Mettapedia.Cybernetics.Individuation.Theory State Recipient where
  Step source target :=
    Σ event : Event problem Recipient Decision source target,
      CertifiedRepair interface scope event
  Closed := interface.Present
  Agrees source target recipient :=
    interface.available source recipient = interface.available target recipient

/-- Every nonempty care history retains every admitted source choice. -/
theorem process_preserves_choices {State Recipient Decision Value Misfit : Type u}
    {Choice : Recipient → Type u}
    {problem : Problem.{u, u, u, u} State Value Misfit}
    {interface : Interface State Recipient Choice Decision} {scope : Set Recipient}
    {source target : State} {steps : Nat}
    (history : Process (processTheory problem interface scope) steps source target)
    {recipient : Recipient} (caredFor : recipient ∈ scope) :
    interface.available source recipient ⊆ interface.available target recipient := by
  induction history with
  | refl => exact Set.Subset.rfl
  | snoc history event ih =>
      exact ih.trans ((event.2.recipientCentered.2.1 recipient caredFor).2.2)

/-- The target-centered virtue interface records participation as the mode
and recipient agency and acceptance as the target. -/
inductive CareValue
  | participation
  | agency
  | recipientAcceptance
  deriving DecidableEq, Repr

def careVirtue {State Recipient Decision Value Misfit : Type u}
    {Choice : Recipient → Type u}
    {problem : Problem.{u, u, u, u} State Value Misfit}
    (interface : Interface State Recipient Choice Decision) (scope : Set Recipient)
    (source target : State) :
    TargetCenteredVirtue.VirtueSpec Recipient Unit
      (Event problem Recipient Decision source target) CareValue where
  valence := .virtue
  field _ := scope.Nonempty
  basis := {.participation, .agency, .recipientAcceptance}
  basis_nonempty := ⟨.participation, by simp⟩
  mode _ _ event := interface.Participates scope event
  target _ _ _ := interface.PreservesAgency scope source target ∧
    interface.Acceptable scope target

/-! ## Concrete recipient-mediated revision and countermodels -/

namespace Controls

inductive Person
  | self
  | ally
  | outsider
  deriving DecidableEq, Repr

inductive Choice
  | rest
  | explore
  deriving DecidableEq, Repr

structure Position where
  present : Bool
  canRevise : Bool
  preference : Choice
  blocked : Bool
  version : Nat
  deriving DecidableEq, Repr

abbrev World := Person → Position

/-- The recipient's endorsed revision changes preference and removes the
represented blockage, retaining presence and revision capacity. -/
def revise (world : World) (recipient : Person) (choice : Choice) : World :=
  Function.update world recipient
    { world recipient with
      preference := choice
      blocked := false
      version := (world recipient).version + 1 }

def erase (world : World) (recipient : Person) : World :=
  Function.update world recipient
    { world recipient with
      present := false
      canRevise := false
      blocked := false
      version := (world recipient).version + 1 }

inductive Change : World → World → Type
  | recipientRevision (world : World) (recipient : Person) (choice : Choice) :
      Change world (revise world recipient choice)
  | unilateralImposition (world : World) (recipient : Person) (choice : Choice) :
      Change world (revise world recipient choice)
  | erasure (world : World) (recipient : Person) : Change world (erase world recipient)

/-- The conserved observation records subject presence and revision capacity,
not an exact frozen preference. -/
def problem : Problem World (Person → Bool × Bool) Person where
  valuedObservation := { observe world recipient :=
    ((world recipient).present, (world recipient).canRevise) }
  HasMisfit world recipient := (world recipient).blocked = true
  Change := Change

structure Decision where
  signer : Person
  recipient : Person
  previousPosition : Position
  selected : Choice
  deriving DecidableEq, Repr

def approval (world : World) (recipient : Person) (choice : Choice) : Decision where
  signer := recipient
  recipient := recipient
  previousPosition := world recipient
  selected := choice

def interface : Interface World Person (fun _ => Choice) Decision where
  Present world recipient := (world recipient).present = true
  available world recipient := {choice |
    (world recipient).present = true ∧ (world recipient).canRevise = true ∧
      (choice = .rest ∨ choice = .explore)}
  Accepts world recipient choice := choice = (world recipient).preference
  Authenticates recipient decision :=
    decision.signer = recipient ∧ decision.recipient = recipient
  Approves decision source target :=
    decision.previousPosition = source decision.recipient ∧
    target = revise source decision.recipient decision.selected

def initial : World := fun _ => ⟨true, true, .rest, true, 0⟩

def approvedEvent (world : World) (recipient : Person) (choice : Choice) :
    Event problem Person Decision world (revise world recipient choice) where
  change := .recipientRevision world recipient choice
  received observed := if observed = recipient then [approval world recipient choice] else []

def unilateralEvent (world : World) (recipient : Person) (choice : Choice) :
    Event problem Person Decision world (revise world recipient choice) where
  change := .unilateralImposition world recipient choice
  received _ := []

def erasedEvent (world : World) (recipient : Person) :
    Event problem Person Decision world (erase world recipient) where
  change := .erasure world recipient
  received _ := []

theorem approved_participates (world : World) (recipient : Person) (choice : Choice) :
    interface.Participates {recipient} (approvedEvent world recipient choice) := by
  intro observed member
  have equal : observed = recipient := Set.mem_singleton_iff.1 member
  subst observed
  refine ⟨approval world recipient choice, ?_, ?_, ?_⟩
  · simp [approvedEvent]
  · simp [interface, approval]
  · simp [interface, approval]

theorem revision_preserves_agency (world : World) (recipient : Person) (choice : Choice)
    (present : (world recipient).present = true)
    (capacity : (world recipient).canRevise = true) :
    interface.PreservesAgency {recipient} world (revise world recipient choice) := by
  intro observed member
  have equal : observed = recipient := Set.mem_singleton_iff.1 member
  subst observed
  simp [interface, revise, present, capacity]

theorem revision_is_acceptable (world : World) (recipient : Person) (choice : Choice)
    (present : (world recipient).present = true)
    (capacity : (world recipient).canRevise = true) :
    interface.Acceptable {recipient} (revise world recipient choice) := by
  intro observed member
  have equal : observed = recipient := Set.mem_singleton_iff.1 member
  subst observed
  refine ⟨choice, ?_, ?_⟩
  · cases choice <;> simp [interface, revise, present, capacity]
  · simp [interface, revise]

theorem approved_recipientCentered (world : World) (recipient : Person) (choice : Choice)
    (present : (world recipient).present = true)
    (capacity : (world recipient).canRevise = true) :
    interface.RecipientCentered {recipient} (approvedEvent world recipient choice) :=
  ⟨approved_participates world recipient choice,
    revision_preserves_agency world recipient choice present capacity,
    revision_is_acceptable world recipient choice present capacity⟩

theorem revision_preserves_invariant (world : World) (recipient : Person) (choice : Choice) :
    problem.valuedObservation.observe (revise world recipient choice) =
      problem.valuedObservation.observe world := by
  funext observed
  by_cases equal : observed = recipient
  · subst observed
    simp [problem, revise]
  · simp [problem, revise, equal]

theorem revision_strictly_reduces_misfits (world : World) (recipient : Person)
    (choice : Choice) (blocked : (world recipient).blocked = true) :
    problem.misfits (revise world recipient choice) ⊂ problem.misfits world := by
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · intro observed misfit
    by_cases equal : observed = recipient
    · subst observed
      simp [Problem.misfits, problem, revise] at misfit
    · simpa [Problem.misfits, problem, revise, equal] using misfit
  · intro equal
    have old : recipient ∈ problem.misfits world := blocked
    have new : recipient ∈ problem.misfits (revise world recipient choice) := equal ▸ old
    simp [Problem.misfits, problem, revise] at new

def approvedRepair (world : World) (recipient : Person) (choice : Choice)
    (present : (world recipient).present = true)
    (capacity : (world recipient).canRevise = true)
    (blocked : (world recipient).blocked = true) :
    CertifiedRepair interface {recipient} (approvedEvent world recipient choice) where
  scope_nonempty := ⟨recipient, by simp⟩
  repair := ⟨{
    evidence := .recipientRevision world recipient choice
    preservesValue := revision_preserves_invariant world recipient choice
    strictlyReducesMisfit := revision_strictly_reduces_misfits world recipient choice blocked }, rfl⟩
  recipientCentered := approved_recipientCentered world recipient choice present capacity

theorem approved_preference_change_is_care :
    Nonempty (CertifiedRepair interface {.ally} (approvedEvent initial .ally .explore)) ∧
    (revise initial .ally .explore .ally).preference ≠ (initial .ally).preference := by
  refine ⟨⟨approvedRepair initial .ally .explore rfl rfl rfl⟩, ?_⟩
  simp [revise, initial]

theorem same_endpoint_without_participation_fails :
    interface.Acceptable {.ally} (revise initial .ally .explore) ∧
    ¬ interface.RecipientCentered {.ally} (unilateralEvent initial .ally .explore) := by
  refine ⟨revision_is_acceptable initial .ally .explore rfl rfl, ?_⟩
  intro care
  exact interface.missing_decision_blocks_participation
    (unilateralEvent initial .ally .explore) (recipient := .ally) (by simp) rfl care.1

theorem erasure_is_not_recipientCentered :
    ¬ interface.RecipientCentered {.ally} (erasedEvent initial .ally) := by
  intro care
  apply interface.absent_target_blocks_agency (recipient := .ally) (by simp) _ care.2.1
  simp [interface, erase]

/-- The recipient can authorize another value revision after the repair;
removing the initial blockage has not frozen the new preference. -/
theorem subsequent_authorized_revision_remains_available (choice : Choice) :
    interface.RecipientCentered {.ally}
      (approvedEvent (revise initial .ally .explore) .ally choice) := by
  apply approved_recipientCentered
  · simp [revise, initial]
  · simp [revise, initial]

theorem approved_event_hits_care_target :
    (careVirtue interface {.ally} initial (revise initial .ally .explore)).ActionHitsTarget
      .self () (approvedEvent initial .ally .explore) := by
  refine ⟨?_, approved_participates _ _ _, ?_⟩
  · exact ⟨.ally, by simp⟩
  · exact (approved_recipientCentered initial .ally .explore rfl rfl).2

/-- A helper can submit a decision with their own signature, but that cannot
authenticate as the affected recipient's decision. -/
def forgedDecision : Decision :=
  { approval initial .ally .explore with signer := .self }

def forgedEvent : Event problem Person Decision initial (revise initial .ally .explore) where
  change := .unilateralImposition initial .ally .explore
  received observed := if observed = .ally then [forgedDecision] else []

theorem helper_signature_cannot_replace_recipient_decision :
    ¬ interface.RecipientCentered {.ally} forgedEvent := by
  intro care
  rcases care.1 .ally (by simp) with ⟨decision, received, authenticated, _⟩
  have same : decision = forgedDecision := by simpa [forgedEvent] using received
  subst decision
  simp [interface, forgedDecision, approval] at authenticated

/-- An earlier decision records the earlier recipient position.  Replaying
that receipt after an authorized change cannot license another event. -/
def staleEvent : Event problem Person Decision (revise initial .ally .explore)
    (revise (revise initial .ally .explore) .ally .rest) where
  change := .recipientRevision (revise initial .ally .explore) .ally .rest
  received observed := if observed = .ally then [approval initial .ally .explore] else []

theorem stale_position_blocks_participation :
    ¬ interface.Participates {.ally} staleEvent := by
  intro participation
  rcases participation .ally (by simp) with ⟨decision, received, _, licensed⟩
  have same : decision = approval initial .ally .explore := by
    simpa [staleEvent] using received
  subst decision
  have previous := licensed.1
  have preferenceEqual := congrArg Position.preference previous
  simp [approval, revise, initial] at preferenceEqual

/-- A local version increments even when a preference is revised back to its
earlier value.  An old approval therefore cannot become current by cycling
preferences through the same displayed choice. -/
theorem old_approval_cannot_license_after_revision (world : World) (recipient : Person)
    (revisedChoice requestedChoice : Choice) (target : World) :
    ¬ interface.Approves (approval world recipient requestedChoice)
      (revise world recipient revisedChoice) target := by
  intro licensed
  have versions := congrArg Position.version licensed.1
  simp [approval, revise] at versions

/-- Consecutive recipient revisions retain their chronological updates. -/
def reviseMany (world : World) (recipient : Person) : List Choice → World
  | [] => world
  | choice :: tail => reviseMany (revise world recipient choice) recipient tail

theorem revision_history_increments_version (world : World) (recipient : Person)
    (choices : List Choice) :
    (reviseMany world recipient choices recipient).version =
      (world recipient).version + choices.length := by
  induction choices generalizing world with
  | nil => simp [reviseMany]
  | cons choice tail ih =>
      simp [reviseMany, ih, revise, Nat.add_comm, Nat.add_left_comm]

/-- No nonempty history of recipient revisions can resurrect an old decision,
even if it eventually returns to the original preference. -/
theorem old_approval_cannot_survive_revision_history (world : World) (recipient : Person)
    (choices : List Choice) (nonempty : choices ≠ []) (requested : Choice) (target : World) :
    ¬ interface.Approves (approval world recipient requested)
      (reviseMany world recipient choices) target := by
  intro licensed
  have versions := congrArg Position.version licensed.1
  simp only [approval, revision_history_increments_version] at versions
  have emptyLength : choices.length = 0 := by omega
  exact nonempty (List.length_eq_zero_iff.1 emptyLength)

/-- A change to an unrelated recipient does not invalidate this local
recipient's decision.  The declared boundary distinguishes framing from
stale use of the affected recipient's own earlier position. -/
theorem unrelated_change_preserves_decision (world : World) (recipient other : Person)
    (position : Position) (choice : Choice) (unrelated : recipient ≠ other) :
    interface.Authenticates recipient (approval world recipient choice) ∧
    interface.Approves (approval world recipient choice)
      (Function.update world other position)
      (revise (Function.update world other position) recipient choice) := by
  simp [interface, approval, unrelated]

/-! ## Coherence, care scope and authority remain distinct -/

open Mettapedia.Cybernetics.IntentionCoherence

def scopedPlan (scope : Finset Person) : Plan Person where
  standing := scope
  predecessors _ := ∅

def selfishScope : Finset Person := {.self}

def intermediateScope : Finset Person := {.self, .ally}

def universalScope : Finset Person := {.self, .ally, .outsider}

theorem selfish_plan_is_coherent : (scopedPlan selfishScope).CoherentAt ∅ := by
  apply Plan.ordered_cover_is_coherent _ ∅ [.self]
  · simp [Plan.Ordered, Plan.Ready, scopedPlan, selfishScope]
  · intro person intended
    simp only [scopedPlan, selfishScope, Finset.mem_singleton] at intended
    exact .inr (by simp [intended])

theorem intermediate_plan_is_coherent : (scopedPlan intermediateScope).CoherentAt ∅ := by
  apply Plan.ordered_cover_is_coherent _ ∅ [.self, .ally]
  · simp [Plan.Ordered, Plan.Ready, scopedPlan, intermediateScope]
  · intro person intended
    exact Or.inr (by simpa [scopedPlan, intermediateScope] using intended)

/-- Completing two distinct standing intentions does not force a third
recipient into the care scope.  Coherence alone has no such implication. -/
theorem coherent_intermediate_scope_exists :
    (scopedPlan intermediateScope).CoherentAt ∅ ∧
    intermediateScope ≠ selfishScope ∧ intermediateScope ≠ universalScope ∧
    Plan.run ∅ [.self, .ally] = intermediateScope := by
  refine ⟨intermediate_plan_is_coherent, ?_, ?_, ?_⟩
  · intro equal
    have member : Person.ally ∈ intermediateScope := by simp [intermediateScope]
    rw [equal] at member
    simp [selfishScope] at member
  · intro equal
    have member : Person.outsider ∈ universalScope := by simp [universalScope]
    rw [← equal] at member
    simp [intermediateScope] at member
  · ext person
    cases person <;> simp [Plan.run, intermediateScope]

def HasAuthority (person : Person) : Prop := person = .self

theorem care_membership_does_not_confer_authority :
    Person.ally ∈ intermediateScope ∧ ¬ HasAuthority .ally := by
  simp [intermediateScope, HasAuthority]

end Controls
end Mettapedia.Ethics.RecipientCenteredCare
