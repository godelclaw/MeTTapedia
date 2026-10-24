import Mettapedia.GSLT.LanguageDef.InteractionEventAuthority
import Mettapedia.Machines.BranchLocalNeed.ExecutionMachine
import Mettapedia.Machines.Cursor.Protocol

/-!
# Occurrence-authenticated interaction authority for reference Need

The reference transition returns a list rather than a set. A semantic
event is therefore an exact list occurrence: its index and `getElem?` proof
retain duplicate alternatives even when two successors are equal.

This module exposes that existing machine relation as an interaction
presentation and hence as a SemanticService authority.  It does not introduce a second
evaluator. The optional full-endpoint certificate checker below is parameterized
by an exact endpoint identity, since a reference machine contains an extensional
heap function. Its injective-key hypothesis is separate from current ownership
and dependency validation. Discovery and ordinary execution do not require
serializing or hashing the heap; an unproved digest does not satisfy that
certificate checker's identity hypothesis.

Bounded discovery is a separate cursor over an explicit finite enumeration.
It is not part of `step`. The provider keeps the remaining suffix and the
source index. One request conses a fresh reverse buffer and projects it
once. A later request keeps that live cursor and starts a new buffer. The
view is not an owner, a selector, or a permission. Current authority stays
an owned runtime obligation. `actionIntent` reads a perform effect from the
action.
-/

namespace Mettapedia.Machines.BranchLocalNeed.NeedInteractionAuthority

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InteractionEventAuthority
open Mettapedia.Machines.BranchLocalNeed.NeedReference

universe uAuthority uIdentity

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect :
  Type*}

abbrev AuthorityMachine :=
  Machine Origin Local Resume Rule Value StableFault RetryableFault Effect

/-- Endpoint erasure of the occurrence-sensitive reference transition. -/
def machineTheory
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    GSLT where
  Term := AuthorityMachine
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => Nonempty (StepOccurrence spec source target)
  rewrites_resp_left := by
    intro source source' target equal edge
    subst source'
    exact ⟨target, edge, rfl⟩
  rewrites_resp_right := by
    intro source target target' edge equal
    subst target'
    exact edge

/-- Type-valued evidence for one exact position in the list-valued machine
transition. -/
structure OccurrenceEvidence
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (index : Nat) (source target : AuthorityMachine) : Type where
  successorAt : (step spec source)[index]? = some target

/-- A recording execution admits exactly the reference occurrence at the
same list position. Full readback supplies the reverse implication; this
does not identify distinct occurrences with equal endpoints. -/
theorem recording_occurrence_iff
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (index : Nat) (source target : AuthorityMachine) :
    (NeedExecution.step spec (NeedExecution.projectMachine true source))[index]? =
        some (NeedExecution.projectMachine true target) ↔
      Nonempty (OccurrenceEvidence spec index source target) := by
  rw [← NeedExecution.project_step_commutes, List.getElem?_map]
  constructor
  · intro recorded
    cases original : (step spec source)[index]? with
    | none => simp [original] at recorded
    | some next =>
        have same : NeedExecution.projectMachine true next =
            NeedExecution.projectMachine true target := by
          simpa only [original, Option.map_some, Option.some.injEq] using recorded
        have endpoints : next = target := by
          have readback := congrArg NeedExecution.CoreMachine.readback? same
          simpa only [NeedExecution.readback_projectMachine, Option.some.injEq] using readback
        exact ⟨⟨endpoints ▸ original⟩⟩
  · rintro ⟨occurrence⟩
    simp only [occurrence.successorAt, Option.map_some]

/-- Exact list occurrence is the interaction site. -/
def machinePresentation
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    InteractionPresentation (machineTheory spec) where
  Site := Nat
  Event := OccurrenceEvidence spec
  sound := by
    intro site _source _target occurrence
    exact ⟨{ index := site, successorAt := occurrence.successorAt }⟩

/-- The presentation neither invents nor loses machine-step occurrences. -/
theorem machinePresentation_complete
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (machinePresentation spec).Complete := by
  intro source target edge
  rcases edge with ⟨occurrence⟩
  exact ⟨⟨occurrence.index, ⟨occurrence.successorAt⟩⟩⟩

/-- Repackage an existing reference-machine occurrence as an enabled
interaction event without recomputing the successor list. -/
def StepOccurrence.toEnabled
    {spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {source target : AuthorityMachine}
    (occurrence : StepOccurrence spec source target) :
    (machinePresentation spec).Enabled source where
  site := occurrence.index
  target := target
  evidence := ⟨occurrence.successorAt⟩

/-- A concrete reference realization supplies the exact identity used to replay
machine endpoints. -/
abbrev MachineIdentity
    (Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*) :=
  ExactEndpointIdentity.{uIdentity}
    (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)

/-- Local SemanticService authority for one exact reference-machine occurrence. -/
def nikStepAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId)
    (identity : MachineIdentity.{uIdentity} Origin Local Resume Rule Value
      StableFault RetryableFault Effect)
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :=
  stepAuthorityByIdentity authorityId identity (machinePresentation spec)

theorem nikStepAuthority_complete {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId)
    (identity : MachineIdentity.{uIdentity} Origin Local Resume Rule Value
      StableFault RetryableFault Effect)
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (nikStepAuthority authorityId identity spec).Complete :=
  by
    change (stepAuthorityByIdentity authorityId identity
      (machinePresentation spec)).Complete
    exact stepAuthorityByIdentity_complete authorityId identity
      (machinePresentation_complete spec)

/-- Free finite-trace SemanticService closure of the exact occurrence authority. -/
def nikFiniteTraceAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId)
    (identity : MachineIdentity.{uIdentity} Origin Local Resume Rule Value
      StableFault RetryableFault Effect)
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :=
  finiteTraceAuthorityByIdentity authorityId identity
    (machinePresentation spec)

/-- With an exact endpoint identity, Lean-native certificate existence is
equivalent to finite occurrence-sensitive reference reachability. -/
theorem nikFiniteTraceAuthority_correspondence
    {AuthorityId : Type uAuthority} (authorityId : AuthorityId)
    (identity : MachineIdentity.{uIdentity} Origin Local Resume Rule Value
      StableFault RetryableFault Effect)
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (claim : TraceClaim (machineTheory spec)) :
    (Exists fun certificate :
        (nikFiniteTraceAuthority authorityId identity spec).Certificate =>
      (nikFiniteTraceAuthority authorityId identity spec).check claim
        certificate = true) ↔ claim.Meaning :=
  by
    change (Exists fun certificate :
        (finiteTraceAuthorityByIdentity authorityId identity
          (machinePresentation spec)).Certificate =>
      (finiteTraceAuthorityByIdentity authorityId identity
        (machinePresentation spec)).check claim certificate = true) ↔
      claim.Meaning
    exact finiteTraceAuthorityByIdentity_correspondence authorityId identity
      (machinePresentation_complete spec) claim

/-- Readout of one action. `Action.perform` contributes its effect and every
other constructor contributes none. -/
def actionIntent
    (action :
      Action Origin Local Resume Value StableFault RetryableFault Effect) :
    Option Effect :=
  match action with
  | .perform effect _ => some effect
  | .done _ => none
  | .demand _ _ => none
  | .allocate _ _ => none
  | .resample _ _ => none

/-- `actionIntent` on `Action.perform` is the stored effect. -/
theorem actionIntent_perform
    (effect : Effect) (next : Local) :
    actionIntent
        (Action.perform (Origin := Origin) (Local := Local) (Resume := Resume)
          (Value := Value) (StableFault := StableFault)
          (RetryableFault := RetryableFault) (Effect := Effect) effect next) =
      some effect :=
  rfl

/-! ## Bounded discovery of one finite enumerated source

The provider state is the remaining suffix and the next source index. Each
request conses one reverse buffer and projects it once, either when the
provider reports exhaustion or when the allowance stops. A later request
keeps that cursor and starts from an empty buffer. `step` does not run this
cursor. The ready-item allowance counts those provider steps. Preparing an
input profile lies outside it.
-/

section Discovery

set_option autoImplicit false

open _root_.CategoryTheory
open Mettapedia.Machines.Cursor
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

universe u

/-- A displayed occurrence. Equal targets at different indices stay distinct.
This record has no owner and no advance operation. -/
structure OccurrenceDescriptor (Target : Type u) : Type u where
  index : Nat
  target : Target

/-- One suffix step. The reply carries the source index of that step.
Exhaustion reports the live cursor and does not invent a further target. -/
inductive DiscoveryReply (Target : Type u) : Type u where
  | item (index : Nat) (target : Target)
  | exhausted (cursor : Nat)

/-- The forward buffer of one finished request, projected once. -/
structure DiscoveryResult (Target : Type u) : Type u where
  yielded : List (OccurrenceDescriptor Target)
  cursor : Nat

/-- `ask` holds only the current request, in reverse. `finished` is the one
projection at provider exhaustion. Earlier requests are not retained here. -/
inductive DiscoveryState (Target : Type u) : Type u where
  | ask (reversed : List (OccurrenceDescriptor Target))
  | finished (result : DiscoveryResult Target)

/-- The capability index stays `PUnit`. The source cursor lives in the
provider, so a request asks only for the next remaining target. -/
abbrev discoveryProtocol (Target : Type u) :
    IndexedPolynomial PUnit.{u + 1} (fun _ => PUnit.{u + 1}) where
  Shape _ _ := PUnit.{u + 1}
  Position _ := DiscoveryReply Target
  next _ _ := .unit

/-- Live suffix of one captured finite profile. -/
structure SourceCursor (Target : Type u) : Type u where
  index : Nat
  rest : List Target

/-- Serve the head of the remaining suffix. This does not call `step` or an
action, and it does not rescan a prefix. -/
def discoveryProvider {Target : Type u} :
    Provider (discoveryProtocol Target) where
  State _ _ := SourceCursor Target
  step cursor _ :=
    match cursor.rest with
    | [] => ⟨.exhausted cursor.index, cursor⟩
    | head :: tail =>
        ⟨.item cursor.index head, ⟨cursor.index + 1, tail⟩⟩

/-- Cons the current reply onto this request's reverse buffer. Project that
buffer once when the provider reports exhaustion. -/
def discoveryClient {Target : Type u} :
    Client (P := discoveryProtocol Target)
      (Return := fun _ _ => DiscoveryResult Target) where
  V _ _ := DiscoveryState Target
  str := fun _ _ =>
    ↾(fun state =>
      match state with
      | .finished result =>
          ⟨.inl result, fun impossible => nomatch impossible⟩
      | .ask reversed =>
          ⟨.inr .unit, fun reply =>
            match reply with
            | .item index target =>
                .ask (⟨index, target⟩ :: reversed)
            | .exhausted cursor =>
                .finished ⟨reversed.reverse, cursor⟩⟩)

def discoveryCharge {Target : Type u} :
    Charge (discoveryProvider (Target := Target)) :=
  fun _ _ => 1

/-- One bounded request. `reversed` is only this request's buffer. -/
abbrev discover {Target : Type u} (fuel : Nat)
    (reversed : List (OccurrenceDescriptor Target))
    (cursor : SourceCursor Target) :
    Nat × Outcome (discoveryProvider (Target := Target))
      (discoveryClient (Target := Target)) PUnit.unit :=
  Mettapedia.Machines.Cursor.advance (discoveryProvider (Target := Target))
    (discoveryClient (Target := Target))
    (discoveryCharge (Target := Target)) fuel (base := PUnit.unit)
    ⟨.unit, .ask reversed, cursor⟩

/-- Read-only result of one discovery request. A paused `ask` projects its
reverse buffer once; a finished request is already projected. -/
structure DiscoveryView (Target : Type u) : Type u where
  yielded : List (OccurrenceDescriptor Target)
  cursor : Nat
  exhausted : Bool

def readDiscovery {Target : Type u} :
    Outcome (discoveryProvider (Target := Target))
      (discoveryClient (Target := Target)) PUnit.unit →
      DiscoveryView Target
  | .done ⟨_, result, cursor⟩ =>
      { yielded := result.yielded, cursor := cursor.index, exhausted := true }
  | .paused ⟨_, .finished result, cursor⟩ =>
      { yielded := result.yielded, cursor := cursor.index, exhausted := true }
  | .paused ⟨_, .ask reversed, cursor⟩ =>
      { yielded := reversed.reverse, cursor := cursor.index, exhausted := false }

/-- The provider cursor retained by a finished or paused request. -/
def retainedCursor {Target : Type u} :
    Outcome (discoveryProvider (Target := Target))
      (discoveryClient (Target := Target)) PUnit.unit → SourceCursor Target
  | .done ⟨_, _, cursor⟩ => cursor
  | .paused ⟨_, _, cursor⟩ => cursor

/-- Ordered enumeration of a suffix. This is not the cursor. -/
def orderedOccurrences {Target : Type u} :
    Nat → List Target → List (OccurrenceDescriptor Target)
  | _, [] => []
  | index, head :: tail =>
      ⟨index, head⟩ :: orderedOccurrences (index + 1) tail

/-- A finished client state is exhaustion. Spare allowance does not ask again
and does not move the provider cursor. -/
theorem readDiscovery_finished {Target : Type u} (fuel : Nat)
    (result : DiscoveryResult Target) (cursor : SourceCursor Target) :
    readDiscovery
        (Mettapedia.Machines.Cursor.advance discoveryProvider discoveryClient
          discoveryCharge fuel (base := PUnit.unit)
          ⟨.unit, .finished result, cursor⟩).2 =
      { yielded := result.yielded, cursor := cursor.index, exhausted := true } := by
  cases fuel with
  | zero => rfl
  | succ _ => rfl

theorem retained_finished {Target : Type u} (fuel : Nat)
    (result : DiscoveryResult Target) (cursor : SourceCursor Target) :
    retainedCursor
        (Mettapedia.Machines.Cursor.advance discoveryProvider discoveryClient
          discoveryCharge fuel (base := PUnit.unit)
          ⟨.unit, .finished result, cursor⟩).2 = cursor := by
  cases fuel with
  | zero => rfl
  | succ _ => rfl

/-- One cons from a nonempty suffix. The charge is the provider step. -/
theorem advance_cons {Target : Type u} (fuel index : Nat) (head : Target)
    (tail : List Target) (reversed : List (OccurrenceDescriptor Target)) :
    discover (fuel + 1) reversed ⟨index, head :: tail⟩ =
      let rest :=
        discover fuel (⟨index, head⟩ :: reversed) ⟨index + 1, tail⟩
      (1 + rest.1, rest.2) := rfl

/-- The empty suffix is an explicit exhaustion reply. The reverse buffer is
projected once into the finished request. -/
theorem advance_nil {Target : Type u} (fuel index : Nat)
    (reversed : List (OccurrenceDescriptor Target)) :
    discover (fuel + 1) reversed ⟨index, []⟩ =
      let rest :=
        Mettapedia.Machines.Cursor.advance discoveryProvider discoveryClient
          discoveryCharge fuel (base := PUnit.unit)
          ⟨.unit, .finished ⟨reversed.reverse, index⟩, ⟨index, []⟩⟩
      (1 + rest.1, rest.2) := rfl

/-- Any split of one request's allowance resumes the same reverse buffer and
the same provider cursor. -/
theorem discovery_splits {Target : Type u} (earlier later : Nat)
    (reversed : List (OccurrenceDescriptor Target))
    (cursor : SourceCursor Target) :
    discover (earlier + later) reversed cursor =
      Mettapedia.Machines.Cursor.resume discoveryProvider discoveryClient
        discoveryCharge later (discover earlier reversed cursor) :=
  Mettapedia.Machines.Cursor.advance_add discoveryProvider discoveryClient
    discoveryCharge earlier later ⟨.unit, .ask reversed, cursor⟩

/-- A finished client has already returned. Further allowance inside the
request adds no provider charge, which is the same fact as `resume_done`
for a completed outcome. -/
private theorem finished_request_charge {Target : Type u} (fuel : Nat)
    (result : DiscoveryResult Target) (cursor : SourceCursor Target) :
    (Mettapedia.Machines.Cursor.advance (discoveryProvider (Target := Target))
        (discoveryClient (Target := Target))
        (discoveryCharge (Target := Target)) fuel (base := PUnit.unit)
        ⟨.unit, .finished result, cursor⟩).1 = 0 := by
  cases fuel <;> rfl

/-- Charged provider work of one request over an already supplied suffix.
Each served item costs one, and the exhaustion probe costs one. Preparing
an input profile lies outside this ready-item allowance. Allowance past the
probe adds nothing. -/
theorem discovery_charged {Target : Type u} (fuel index : Nat)
    (rest : List Target) (reversed : List (OccurrenceDescriptor Target)) :
    (discover fuel reversed ⟨index, rest⟩).1 =
      min fuel (rest.length + 1) := by
  induction fuel generalizing index rest reversed with
  | zero =>
      rw [Nat.zero_min]
      rfl
  | succ fuel inductionHypothesis =>
      cases rest with
      | nil =>
          rw [advance_nil]
          dsimp only
          rw [finished_request_charge, Nat.add_zero, List.length_nil]
          omega
      | cons head tail =>
          rw [advance_cons]
          dsimp only
          rw [inductionHypothesis, List.length_cons]
          omega

/-- Resuming a request that has already returned keeps the outcome and the
charged work. This is `Cursor.resume_done` for that completed discovery. -/
theorem discovery_spare_resume {Target : Type u} (later fuel index : Nat)
    (rest : List Target) (reversed : List (OccurrenceDescriptor Target))
    (spare : rest.length + 1 < fuel) :
    Mettapedia.Machines.Cursor.resume (discoveryProvider (Target := Target))
        (discoveryClient (Target := Target))
        (discoveryCharge (Target := Target)) later
        (discover fuel reversed ⟨index, rest⟩) =
      discover fuel reversed ⟨index, rest⟩ := by
  induction fuel generalizing index rest reversed with
  | zero => exact (Nat.not_lt_zero _ spare).elim
  | succ fuel inductionHypothesis =>
      cases rest with
      | nil =>
          cases fuel with
          | zero =>
              rw [List.length_nil] at spare
              exact (Nat.lt_irrefl _ spare).elim
          | succ fuel =>
              rw [advance_nil]
              dsimp only
              exact Mettapedia.Machines.Cursor.resume_done
                (discoveryProvider (Target := Target))
                (discoveryClient (Target := Target))
                (discoveryCharge (Target := Target)) later
                (1 +
                  (Mettapedia.Machines.Cursor.advance
                    (discoveryProvider (Target := Target))
                    (discoveryClient (Target := Target))
                    (discoveryCharge (Target := Target)) (fuel + 1)
                    (base := PUnit.unit)
                    ⟨.unit, .finished ⟨reversed.reverse, index⟩, ⟨index, []⟩⟩).1)
                ⟨.unit, ⟨reversed.reverse, index⟩, ⟨index, []⟩⟩
      | cons head tail =>
          rw [advance_cons]
          dsimp only
          have inner : tail.length + 1 < fuel := by
            rw [List.length_cons] at spare
            exact Nat.lt_of_succ_lt_succ spare
          rw [Mettapedia.Machines.Cursor.resume_add_charge
                (discoveryProvider (Target := Target))
                (discoveryClient (Target := Target))
                (discoveryCharge (Target := Target)) later 1
                (discover fuel (⟨index, head⟩ :: reversed) ⟨index + 1, tail⟩),
              inductionHypothesis (index + 1) tail
                (⟨index, head⟩ :: reversed) inner]

/-- Zero allowance performs no lookup. An empty display is not exhaustion,
including when the remaining suffix is already empty. -/
theorem zero_allowance_is_not_exhaustion {Target : Type u}
    (reversed : List (OccurrenceDescriptor Target))
    (cursor : SourceCursor Target) :
    readDiscovery (discover 0 reversed cursor).2 =
      { yielded := reversed.reverse, cursor := cursor.index,
        exhausted := false } := rfl

private theorem prefix_split {α : Type u} (items : List α) (earlier later : Nat) :
    items.take earlier ++ (items.drop earlier).take later =
      items.take (earlier + later) := by
  rw [List.take_drop]
  simpa only [List.take_take, Nat.min_eq_left (Nat.le_add_right earlier later)]
    using List.take_append_drop earlier (items.take (earlier + later))

private theorem orderedOccurrences_length {Target : Type u}
    (index : Nat) (entries : List Target) :
    (orderedOccurrences index entries).length = entries.length := by
  induction entries generalizing index with
  | nil => rfl
  | cons _ tail inductionHypothesis =>
      rw [orderedOccurrences, List.length_cons, inductionHypothesis,
        List.length_cons]

theorem orderedOccurrences_drop {Target : Type u}
    (index count : Nat) (entries : List Target) :
    (orderedOccurrences index entries).drop count =
      orderedOccurrences (index + count) (entries.drop count) := by
  induction entries generalizing index count with
  | nil =>
      cases count with
      | zero => rfl
      | succ _ => rfl
  | cons _ tail inductionHypothesis =>
      cases count with
      | zero => rfl
      | succ count =>
          rw [orderedOccurrences]
          have shifted : (index + 1) + count = index + (count + 1) := by
            rw [Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc]
          rw [← shifted]
          exact inductionHypothesis (index + 1) count

private theorem min_covered (earlier later n : Nat) :
    min earlier n + min later (n - min earlier n) = min (earlier + later) n := by
  omega

/-- The displayed request is the ordered suffix prefix. Exhaustion is a
provider reply after the last item, not equality of the allowance with the
suffix length, and not an empty display. -/
theorem discovery_view_agrees {Target : Type u} (fuel index : Nat)
    (rest : List Target) (reversed : List (OccurrenceDescriptor Target)) :
    (readDiscovery (discover fuel reversed ⟨index, rest⟩).2).yielded =
        reversed.reverse ++
          (orderedOccurrences index rest).take (min fuel rest.length) ∧
      (readDiscovery (discover fuel reversed ⟨index, rest⟩).2).cursor =
        index + min fuel rest.length ∧
      ((readDiscovery (discover fuel reversed ⟨index, rest⟩).2).exhausted =
          true ↔ rest.length < fuel) := by
  induction fuel generalizing index rest reversed with
  | zero =>
      rw [Nat.zero_min, List.take_zero, List.append_nil, Nat.add_zero]
      refine ⟨rfl, rfl, ?_⟩
      constructor
      · intro bad
        exact Bool.noConfusion bad
      · intro bad
        exact (Nat.not_lt_zero rest.length bad).elim
  | succ fuel inductionHypothesis =>
      cases rest with
      | nil =>
          rw [advance_nil]
          have viewed :=
            readDiscovery_finished fuel ⟨reversed.reverse, index⟩ ⟨index, []⟩
          rw [viewed, List.length_nil, Nat.min_eq_right (Nat.zero_le _),
            List.take_zero, List.append_nil, Nat.add_zero]
          refine ⟨rfl, rfl, ?_⟩
          constructor
          · intro _
            exact Nat.succ_pos fuel
          · intro _
            rfl
      | cons head tail =>
          rw [advance_cons]
          dsimp only
          obtain ⟨yieldedEq, cursorEq, exhaustedIff⟩ :=
            inductionHypothesis (index + 1) tail (⟨index, head⟩ :: reversed)
          refine ⟨?_, ?_, ?_⟩
          · simpa only [List.reverse_cons, List.append_assoc, orderedOccurrences,
              List.length_cons, Nat.succ_min_succ, List.take_succ_cons,
              List.singleton_append] using yieldedEq
          · simpa only [List.length_cons, Nat.succ_min_succ, Nat.add_assoc,
              Nat.add_left_comm, Nat.add_comm] using cursorEq
          · simpa only [List.length_cons, Nat.succ_lt_succ_iff] using exhaustedIff

/-- A request leaves the unconsumed suffix and the index of its head. The
current reverse buffer is not part of that cursor. -/
theorem retained_cursor {Target : Type u} (fuel index : Nat)
    (rest : List Target) (reversed : List (OccurrenceDescriptor Target)) :
    retainedCursor (discover fuel reversed ⟨index, rest⟩).2 =
      ⟨index + min fuel rest.length, rest.drop (min fuel rest.length)⟩ := by
  induction fuel generalizing index rest reversed with
  | zero =>
      rw [Nat.zero_min, Nat.add_zero]
      rfl
  | succ fuel inductionHypothesis =>
      cases rest with
      | nil =>
          rw [advance_nil, retained_finished, List.length_nil,
            Nat.min_eq_right (Nat.zero_le _), Nat.add_zero]
          rfl
      | cons head tail =>
          rw [advance_cons, inductionHypothesis]
          simp only [List.length_cons, Nat.succ_min_succ, List.drop_succ_cons,
            Nat.add_left_comm, Nat.add_comm]

/-- Two requests that share only the retained cursor return separate
prefixes. Their concatenation is the ordered enumeration of the profile
they jointly consume. -/
theorem requests_concatenate {Target : Type u}
    (earlier later index : Nat) (entries : List Target) :
    (readDiscovery (discover earlier [] ⟨index, entries⟩).2).yielded ++
        (readDiscovery
          (discover later []
            (retainedCursor (discover earlier [] ⟨index, entries⟩).2)).2).yielded =
      (orderedOccurrences index entries).take
        (min (earlier + later) entries.length) ∧
    (readDiscovery (discover earlier [] ⟨index, entries⟩).2).cursor =
      index + min earlier entries.length ∧
    (readDiscovery
        (discover later []
          (retainedCursor (discover earlier [] ⟨index, entries⟩).2)).2).cursor =
      index + min (earlier + later) entries.length ∧
    ((readDiscovery (discover earlier [] ⟨index, entries⟩).2).exhausted =
        true ↔ entries.length < earlier) ∧
    ((readDiscovery
        (discover later []
          (retainedCursor
            (discover earlier [] ⟨index, entries⟩).2)).2).exhausted = true ↔
      (entries.drop (min earlier entries.length)).length < later) := by
  have kept := retained_cursor earlier index entries []
  rw [kept]
  obtain ⟨firstYielded, firstCursor, firstExhausted⟩ :=
    discovery_view_agrees earlier index entries []
  obtain ⟨secondYielded, secondCursor, secondExhausted⟩ :=
    discovery_view_agrees later (index + min earlier entries.length)
      (entries.drop (min earlier entries.length)) []
  refine ⟨?_, firstCursor, ?_, firstExhausted, secondExhausted⟩
  · rw [firstYielded, secondYielded]
    simp only [List.reverse_nil, List.nil_append]
    rw [← orderedOccurrences_drop, List.length_drop, prefix_split, min_covered]
  · rw [secondCursor, List.length_drop, Nat.add_assoc, min_covered]

/-- Membership in the independent enumeration gives the actual source
lookup, including when the enumeration begins at a nonzero index. -/
theorem orderedOccurrences_mem_lookup {Target : Type u} (index : Nat)
    (entries : List Target) (descriptor : OccurrenceDescriptor Target)
    (present : descriptor ∈ orderedOccurrences index entries) :
    index ≤ descriptor.index ∧
      entries[descriptor.index - index]? = some descriptor.target := by
  induction entries generalizing index with
  | nil => simp [orderedOccurrences] at present
  | cons head tail inductionHypothesis =>
      change descriptor ∈ ⟨index, head⟩ :: orderedOccurrences (index + 1) tail at present
      rcases List.mem_cons.mp present with same | later
      · subst descriptor
        simp
      · obtain ⟨lower, lookup⟩ := inductionHypothesis (index + 1) later
        refine ⟨by omega, ?_⟩
        have shift : descriptor.index - index =
            (descriptor.index - (index + 1)) + 1 := by omega
        simpa only [shift, List.getElem?_cons_succ] using lookup

/-- Every displayed descriptor comes from the captured finite source.
This derives its lookup evidence from the actual bounded request. -/
theorem discovered_descriptor_lookup {Target : Type u} (fuel : Nat)
    (entries : List Target) (descriptor : OccurrenceDescriptor Target)
    (present : descriptor ∈
      (readDiscovery (discover fuel [] ⟨0, entries⟩).2).yielded) :
    entries[descriptor.index]? = some descriptor.target := by
  have displayedPrefix := (discovery_view_agrees fuel 0 entries []).1
  rw [displayedPrefix] at present
  simp only [List.reverse_nil, List.nil_append] at present
  have lookup := (orderedOccurrences_mem_lookup 0 entries descriptor
    (List.mem_of_mem_take present)).2
  simpa only [Nat.sub_zero] using lookup

/-- The fresh second request, over the cursor the first request retained,
is the next page of the original ordered profile. -/
theorem retained_page {Target : Type u} (earlier later index : Nat)
    (entries : List Target) :
    (readDiscovery
        (discover later []
          (retainedCursor (discover earlier [] ⟨index, entries⟩).2)).2).yielded =
      ((orderedOccurrences index entries).take
          (min (earlier + later) entries.length)).drop
        (min earlier entries.length) := by
  have joint := (requests_concatenate earlier later index entries).1
  have first := (discovery_view_agrees earlier index entries []).1
  simp only [List.reverse_nil, List.nil_append] at first
  rw [first] at joint
  let page :=
    (orderedOccurrences index entries).take (min earlier entries.length)
  have lengthEq : page.length = min earlier entries.length := by
    unfold page
    rw [List.length_take, orderedOccurrences_length,
      Nat.min_eq_left (Nat.min_le_right earlier entries.length)]
  have dropped := congrArg (fun items => items.drop page.length) joint
  rw [List.drop_append_length, lengthEq] at dropped
  exact dropped

/-- A descriptor returned by that fresh second request carries its lookup in
the original profile. The caller does not supply the lookup. -/
theorem paged_descriptor_lookup {Target : Type u}
    (earlier later index : Nat) (entries : List Target)
    (descriptor : OccurrenceDescriptor Target)
    (present : descriptor ∈
      (readDiscovery
        (discover later []
          (retainedCursor (discover earlier [] ⟨index, entries⟩).2)).2).yielded) :
    index ≤ descriptor.index ∧
      entries[descriptor.index - index]? = some descriptor.target := by
  have joint := (requests_concatenate earlier later index entries).1
  have inPage : descriptor ∈
      (readDiscovery (discover earlier [] ⟨index, entries⟩).2).yielded ++
        (readDiscovery
          (discover later []
            (retainedCursor
              (discover earlier [] ⟨index, entries⟩).2)).2).yielded :=
    List.mem_append_right _ present
  rw [joint] at inPage
  exact orderedOccurrences_mem_lookup index entries descriptor
    (List.mem_of_mem_take inPage)

end Discovery

/-- A profile entry that is the reference list at that index is a reference
occurrence. The cursor does not manufacture this proof. -/
theorem enumerated_descriptor_is_occurrence
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {captured target : AuthorityMachine} {entries : List AuthorityMachine}
    (agrees : entries = step spec captured) (index : Nat)
    (atIndex : entries[index]? = some target) :
    Nonempty (StepOccurrence spec captured target) :=
  ⟨{ index := index, successorAt := agrees ▸ atIndex }⟩

/-- A descriptor actually displayed from the reference profile supplies its
own source-occurrence evidence. No execution permission follows from it. -/
theorem discovered_descriptor_is_occurrence
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (captured : AuthorityMachine) (fuel : Nat)
    (descriptor : OccurrenceDescriptor AuthorityMachine)
    (present : descriptor ∈
      (readDiscovery (discover fuel [] ⟨0, step spec captured⟩).2).yielded) :
    Nonempty (StepOccurrence spec captured descriptor.target) :=
  enumerated_descriptor_is_occurrence spec rfl descriptor.index
    (discovered_descriptor_lookup fuel (step spec captured) descriptor present)

/-- A descriptor from a fresh second request over the retained cursor is a
source occurrence of the original profile. The lookup is derived from that
request. This evidence is source-local. Native permission remains the
separate runtime authority, and preparing the input profile lies outside
the ready-item allowance. -/
theorem paged_descriptor_is_occurrence
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (captured : AuthorityMachine) (earlier later : Nat)
    (descriptor : OccurrenceDescriptor AuthorityMachine)
    (present : descriptor ∈
      (readDiscovery
        (discover later []
          (retainedCursor
            (discover earlier [] ⟨0, step spec captured⟩).2)).2).yielded) :
    Nonempty (StepOccurrence spec captured descriptor.target) := by
  have lookup := paged_descriptor_lookup earlier later 0
    (step spec captured) descriptor present
  exact enumerated_descriptor_is_occurrence spec rfl descriptor.index
    (by simpa only [Nat.sub_zero] using lookup.2)

/-- One catalog revision presents this spec. Discovery does not choose it. -/
def discoveryCatalog
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    InteractionPresentation.Catalog (machineTheory spec) where
  Revision := Unit
  presentationAt _ := machinePresentation spec

/-- Memory is unchanged by a selected occurrence. The handler grants no
permission and does not advance any owner. -/
def retainMemory
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    InteractionPresentation.Handler (discoveryCatalog spec) Unit where
  resume memory _ := memory

set_option linter.style.haveILetI false in
/-- Identity validation and the selector are separate from the discovery view.
A different live endpoint fails the existing identity check. Heap functions
are not hashed, and the failure does not grant or revoke an execution right. -/
theorem different_live_source_fails_validation
    (identity : MachineIdentity Origin Local Resume Rule Value StableFault
      RetryableFault Effect)
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {captured live target : AuthorityMachine} (index : Nat)
    (evidence : OccurrenceEvidence spec index captured target)
    (different : identity.identify live ≠ identity.identify captured) :
    checkEventCertificateByIdentity identity
        (⟨live, target⟩ : StepClaim (machineTheory spec))
        (⟨captured, (⟨index, target, evidence⟩ :
          (machinePresentation spec).Enabled captured)⟩ :
          EventCertificate (machinePresentation spec)) = false := by
  letI := identity.decEq
  unfold checkEventCertificateByIdentity
  apply decide_eq_false
  intro same
  exact different same.1

set_option linter.style.haveILetI false in
/-- Source-step soundness of one checked occurrence. A passing identity check
identifies the live endpoint with the captured source, and a selector that
returns that occurrence has the presentation target as its source step.
This is not an execution right. Current authority remains a separate owned
runtime obligation, and the discovery view is not that authority. -/
theorem checked_identity_source_step_sound
    (identity : MachineIdentity Origin Local Resume Rule Value StableFault
      RetryableFault Effect)
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {captured live target : AuthorityMachine} (index : Nat)
    (evidence : OccurrenceEvidence spec index captured target)
    (selector :
      InteractionPresentation.Selector (discoveryCatalog spec) Unit)
    (accepted :
      checkEventCertificateByIdentity identity
        (⟨live, target⟩ : StepClaim (machineTheory spec))
        (⟨captured, (⟨index, target, evidence⟩ :
          (machinePresentation spec).Enabled captured)⟩ :
          EventCertificate (machinePresentation spec)) = true)
    (chooses :
      selector.choose () () captured =
        some ⟨⟨index, target, evidence⟩⟩) :
    identity.identify live = identity.identify captured ∧
      InteractionPresentation.tick selector (retainMemory spec) ()
          { term := captured, memory := () } =
        some { term := target, memory := () } ∧
      (machineTheory spec).Step captured target := by
  letI := identity.decEq
  unfold checkEventCertificateByIdentity at accepted
  have endpoints := of_decide_eq_true accepted
  refine ⟨endpoints.1, ?_, (machinePresentation spec).sound evidence⟩
  unfold InteractionPresentation.tick
  rw [chooses, retainMemory]
  rfl

/-! ## Occurrence canaries -/

namespace Canary

def demoSpec : Spec Unit Unit Unit Unit Unit Unit Unit Unit where
  alternatives := fun _ => []
  action := fun _ => .done (.value ())
  afterDemand := fun _ _ => ()
  afterAllocation := fun _ _ => ()

def demoWorld : World Unit Unit Unit Unit Unit Unit where
  lineage := 0
  path := []
  heap := Heap.empty
  receipts := ReceiptGraph.empty
  nextCell := 0
  nextEvaluator := 0

def start : Machine Unit Unit Unit Unit Unit Unit Unit Unit where
  world := demoWorld
  control := .run () []

def next : Machine Unit Unit Unit Unit Unit Unit Unit Unit :=
  finished start demoWorld (.returned (.value ()) []) 0 0 0 0

def firstOccurrence : StepOccurrence demoSpec start next where
  index := 0
  successorAt := rfl

theorem occurrence_is_presented :
    Nonempty ((machinePresentation demoSpec).Event (0 : Nat) start next) :=
  ⟨⟨firstOccurrence.successorAt⟩⟩

/-- Negative canary: a singleton transition has no second occurrence. -/
theorem no_second_occurrence :
    (step demoSpec start)[1]? = none :=
  rfl

/-- The bounded source request constructs the first occurrence evidence. -/
theorem displayed_source_occurrence :
    Nonempty (StepOccurrence demoSpec start next) := by
  apply discovered_descriptor_is_occurrence demoSpec start 1 ⟨0, next⟩
  exact List.mem_cons_self

/-- Zero allowance on two available targets displays nothing and is not
exhaustion. -/
theorem zero_prefix_is_not_exhaustion :
    readDiscovery (discover 0 [] ⟨0, [start, start]⟩).2 =
      { yielded := [], cursor := 0, exhausted := false } :=
  rfl

/-- Zero allowance on an empty suffix is still not exhaustion. -/
theorem zero_allowance_on_empty_is_not_exhaustion :
    readDiscovery (discover
      (Target := Machine Unit Unit Unit Unit Unit Unit Unit Unit) 0 [] ⟨0, []⟩).2 =
      { yielded := [], cursor := 0, exhausted := false } :=
  rfl

/-- One lookup displays the first target and retains the cursor. The hidden
second target means this prefix is not exhaustion. -/
theorem partial_prefix_is_not_exhaustion :
    readDiscovery (discover 1 [] ⟨0, [start, start]⟩).2 =
      { yielded := [⟨0, start⟩], cursor := 1, exhausted := false } := by
  rw [advance_cons]
  rfl

/-- The allowance that equals the profile length returns the whole prefix and
does not report exhaustion. Exhaustion needs one probe past the last item. -/
theorem full_prefix_without_probe_is_not_exhaustion :
    readDiscovery (discover 2 [] ⟨0, [start, start]⟩).2 =
      { yielded := [⟨0, start⟩, ⟨1, start⟩], cursor := 2,
        exhausted := false } := by
  rw [advance_cons, advance_cons]
  rfl

/-- Two equal targets remain two source indices. Confirming exhaustion takes
one probe after the last displayed target. -/
theorem duplicate_successors_keep_distinct_indices :
    readDiscovery (discover 3 [] ⟨0, [start, start]⟩).2 =
      { yielded := [⟨0, start⟩, ⟨1, start⟩], cursor := 2,
        exhausted := true } ∧
      (⟨0, start⟩ : OccurrenceDescriptor _).target =
        (⟨1, start⟩ : OccurrenceDescriptor _).target ∧
      (⟨0, start⟩ : OccurrenceDescriptor _).index ≠
        (⟨1, start⟩ : OccurrenceDescriptor _).index := by
  refine ⟨?_, rfl, ?_⟩
  · rw [advance_cons, advance_cons, advance_nil]
    rfl
  · decide

/-- A second request starts from the retained suffix and an empty buffer.
The two returned prefixes concatenate to the ordered profile. -/
theorem fresh_request_concatenates_prefixes :
    (readDiscovery (discover 1 [] ⟨0, [start, start]⟩).2).yielded ++
        (readDiscovery
          (discover 2 []
            (retainedCursor (discover 1 [] ⟨0, [start, start]⟩).2)).2).yielded =
      [⟨0, start⟩, ⟨1, start⟩] ∧
      (readDiscovery
          (discover 2 []
            (retainedCursor (discover 1 [] ⟨0, [start, start]⟩).2)).2).yielded =
        [⟨1, start⟩] ∧
      (readDiscovery (discover 1 [] ⟨0, [start, start]⟩).2).exhausted = false ∧
      (readDiscovery
          (discover 2 []
            (retainedCursor (discover 1 [] ⟨0, [start, start]⟩).2)).2).exhausted =
        true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Canary

#print axioms actionIntent_perform
#print axioms discovery_view_agrees
#print axioms discovery_splits
#print axioms zero_allowance_is_not_exhaustion
#print axioms retained_cursor
#print axioms requests_concatenate
#print axioms discovery_charged
#print axioms discovery_spare_resume
#print axioms retained_page
#print axioms orderedOccurrences_mem_lookup
#print axioms discovered_descriptor_lookup
#print axioms discovered_descriptor_is_occurrence
#print axioms paged_descriptor_lookup
#print axioms paged_descriptor_is_occurrence
#print axioms enumerated_descriptor_is_occurrence
#print axioms different_live_source_fails_validation
#print axioms checked_identity_source_step_sound
#print axioms Canary.zero_prefix_is_not_exhaustion
#print axioms Canary.zero_allowance_on_empty_is_not_exhaustion
#print axioms Canary.partial_prefix_is_not_exhaustion
#print axioms Canary.full_prefix_without_probe_is_not_exhaustion
#print axioms Canary.duplicate_successors_keep_distinct_indices
#print axioms Canary.fresh_request_concatenates_prefixes
#print axioms Canary.displayed_source_occurrence

end Mettapedia.Machines.BranchLocalNeed.NeedInteractionAuthority
