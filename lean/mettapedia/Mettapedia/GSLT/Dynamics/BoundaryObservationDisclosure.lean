import Mettapedia.GSLT.Dynamics.ScriptedBackup
import Mettapedia.GSLT.Contracts.SocietyControls
import Mettapedia.Machines.Cursor.ReadOnlyQuery

/-!
# Boundary input observations do not recover component activity

Direct execution and a checked recorded player inhabit one independently
formed transition system. Every input word has the same boundary readout
from the corresponding valid initial states. Along a recorded input the
actual activity readout distinguishes evaluation from a table read.

Thus component activity does not factor through complete boundary input
behaviour. This compares the declared abstract operations; it does not
identify arbitrary internal interventions with external input probes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.BoundaryObservationDisclosure

open Mettapedia.GSLT.ScriptedBackup Mettapedia.GSLT.PrivilegedView
open Mettapedia.GSLT.Core.NonFactorization

universe u v w

variable {State : Type u} {Input : Type v} [DecidableEq Input]

abbrev Implementation (State : Type u) (Input : Type v) := Sum State (Player State Input)

def transition (step : State → Input → State) :
    Implementation State Input → Input → Implementation State Input
  | .inl state, input => .inl (step state input)
  | .inr player, input => .inr (backupStep step player input)

def surface {Output : Type w} (observe : State → Output) : Implementation State Input → Output
  | .inl state => observe state
  | .inr player => observe player.current

def componentActivity (step : State → Input → State) :
    Implementation State Input → Input → Activity
  | .inl _, _ => .evaluate
  | .inr player, input => (advance step player input).2

theorem direct_run (step : State → Input → State) (inputs : List Input) (state : State) :
    inputs.foldl (transition step) (.inl state) = .inl (inputs.foldl step state) := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input rest inductionHypothesis => exact inductionHypothesis _

theorem backup_run (step : State → Input → State) (inputs : List Input)
    (player : Player State Input) :
    inputs.foldl (transition step) (.inr player) =
      .inr (inputs.foldl (backupStep step) player) := by
  induction inputs generalizing player with
  | nil => rfl
  | cons input rest inductionHypothesis => exact inductionHypothesis _

theorem boundary_agreement (step : State → Input → State) {Output : Type w}
    (observe : State → Output) (player : Player State Input) (valid : Coherent step player) :
    wordBehaviour (transition step) (surface observe) (.inl player.current) =
      wordBehaviour (transition step) (surface observe) (.inr player) := by
  funext inputs
  unfold wordBehaviour
  rw [direct_run, backup_run]
  exact (congrArg observe (run_current step inputs valid)).symm

def recordedPlayer (step : State → Input → State) (state : State) (inputs : List Input) :
    Player State Input := ⟨state, record step state inputs, false⟩

omit [DecidableEq Input] in
theorem recorded_coherent (step : State → Input → State) (state : State) (inputs : List Input) :
    Coherent step (recordedPlayer step state inputs) := fun _ => record_valid step state inputs

theorem recorded_boundary_agreement (step : State → Input → State) {Output : Type w}
    (observe : State → Output) (state : State) (inputs : List Input) :
    wordBehaviour (transition step) (surface observe) (.inl state) =
      wordBehaviour (transition step) (surface observe) (.inr (recordedPlayer step state inputs)) :=
  boundary_agreement step observe _ (recorded_coherent step state inputs)

theorem recorded_activity_separates (step : State → Input → State)
    (state : State) (input : Input) :
    componentActivity step (.inl state) input ≠
      componentActivity step (.inr (recordedPlayer step state [input])) input := by
  simp only [componentActivity, recordedPlayer, record, advance, Bool.false_eq_true,
    ↓reduceIte]
  decide

def activitySeparator (step : State → Input → State) {Output : Type w}
    (observe : State → Output) (state : State) (input : Input) :
    NonTrivialFiber (wordBehaviour (transition step) (surface observe)) (componentActivity step) where
  left := .inl state
  right := .inr (recordedPlayer step state [input])
  sameShadow := recorded_boundary_agreement step observe state [input]
  differentValue := fun same => recorded_activity_separates step state input (congrFun same input)

theorem boundary_does_not_recover_activity (step : State → Input → State) {Output : Type w}
    (observe : State → Output) (state : State) (input : Input) :
    ¬ Factors (wordBehaviour (transition step) (surface observe)) (componentActivity step) :=
  (activitySeparator step observe state input).not_factors

theorem actual_bool_control :
    wordBehaviour (transition Controls.write) (surface id) (.inl false) =
      wordBehaviour (transition Controls.write) (surface id)
        (.inr (recordedPlayer Controls.write false [false])) ∧
    componentActivity Controls.write (.inl false) false = .evaluate ∧
    componentActivity Controls.write
      (.inr (recordedPlayer Controls.write false [false])) false = .tableRead := by
  exact ⟨recorded_boundary_agreement _ _ _ _, rfl, rfl⟩

/-! ## Scoped observation and separately authorized disclosure

This finite service profile uses the existing scoped source and primitive
cursor. Receipt and disclosure logs are protocol state, not truth evidence.
Current host principals and lease frontiers are trusted service inputs; no
network authentication, timing noninterference or C refinement is asserted.
-/

namespace SpaceService

open Mettapedia.Machines
open Mettapedia.GSLT.Contracts.Society
open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

variable {size : Nat}

abbrev Scope := ScopedRecords.Scope Nat Nat
abbrev Source := ScopedRecords.Source Nat Nat Nat Nat Nat
abbrev Reply := ScopedRecords.FullReply Nat Nat Nat Nat Nat
abbrev Stamp := ScopedRecords.Stamp Nat Nat Nat

inductive Resource (size : Nat) where
  | read (scope : Scope)
  | forward (origin recipient : Fin size) (scope : Scope)
  | govern
  deriving DecidableEq

structure ReadReceipt (size : Nat) where
  reader : Fin size
  scope : Scope
  policyEpoch : Nat
  source : Source
  reply : Reply

structure Disclosure (size : Nat) where
  receipt : Nat
  origin : Fin size
  sender : Fin size
  recipient : Fin size
  readEpoch : Nat
  sendEpoch : Nat
  scope : Scope
  payload : Reply
  deriving DecidableEq

structure Change (size : Nat) where
  author : Fin size
  parent : Nat
  beforeEpoch : Nat
  afterEpoch : Nat
  beforeMembers : Finset (Fin size)
  afterMembers : Finset (Fin size)

structure ServiceState (size : Nat) where
  peer : Peer.State size
  authority : World Nat (Resource size) (Fin size)
  source : Source
  receipts : List (ReadReceipt size) := []
  disclosed : List (Disclosure size) := []
  changes : List (Change size) := []

inductive Request (size : Nat) where
  | read (scope : Scope)
  | forward (receipt : Nat) (recipient : Fin size)
  | amend (parent epoch : Nat) (members : Finset (Fin size))

inductive Refusal where
  | denied
  deriving DecidableEq

def Response : Request size → Type
  | .read _ => Except Refusal (Nat × Reply)
  | .forward _ _ | .amend _ _ _ => Except Refusal Unit

def handle (state : ServiceState size) (resource : Resource size) : Handle Nat (Resource size) :=
  ⟨state.peer.service, resource, state.peer.epoch⟩

/-- Replies contain only server-issued read data. A forward looks up the
original receipt; the requester supplies no sender, payload or origin epoch. -/
def step (contents : Nat → Stamp → Nat) (principal : Fin size)
    (state : ServiceState size) (request : Request size) : ServiceState size × Response request :=
  match request with
  | .read scope =>
      if principal ∈ state.peer.members ∧ authorizedB state.authority.frontier principal (handle state (.read scope)) = true then
        let receipt : ReadReceipt size :=
          ⟨principal, scope, state.peer.epoch, state.source, ScopedRecords.observe contents state.source scope⟩
        ({state with receipts := state.receipts ++ [receipt]},
          .ok (state.receipts.length, ScopedRecords.observe contents state.source scope))
      else (state, .error .denied)
  | .forward id recipient =>
      match state.receipts[id]? with
      | none => (state, .error .denied)
      | some receipt =>
          if principal ∈ state.peer.members ∧ recipient ∈ state.peer.members ∧
              authorizedB state.authority.frontier principal
                (handle state (.forward receipt.reader recipient receipt.scope)) = true then
            let delivery : Disclosure size :=
              ⟨id, receipt.reader, principal, recipient, receipt.policyEpoch, state.peer.epoch, receipt.scope,
                receipt.reply⟩
            ({state with disclosed := state.disclosed ++ [delivery]}, .ok ())
          else (state, .error .denied)
  | .amend parent epoch members =>
      if principal ∈ state.peer.members ∧ parent = state.changes.length ∧ state.peer.epoch < epoch ∧
          authorizedB state.authority.frontier principal (handle state .govern) = true then
        let change : Change size := ⟨principal, parent, state.peer.epoch, epoch, state.peer.members, members⟩
        let nextPeer : Peer.State size := {state.peer with epoch := epoch, members := members}
        ({state with peer := nextPeer, changes := state.changes ++ [change]}, .ok ())
      else (state, .error .denied)

/-- Operational failure remains outside the protocol's explicit refusals.
The model handler is total; a native allocator/transport needs its own fault
realization and may not translate failure into a successful empty match. -/
def primitive (contents : Nat → Stamp → Nat) (principal : Fin size)
    (state : ServiceState size) (request : Request size) : ServiceState size × Except Unit (Response request) :=
  let result := step contents principal state request
  (result.1, .ok result.2)

abbrev provider (contents : Nat → Stamp → Nat) (principal : Fin size) :=
  Mettapedia.Machines.Cursor.PrimitiveProgram.provider (primitive contents principal)

/-- An owner's explicit, current lease may be lent only for this forwarding
call. The existing scoped borrow restores the original frontier afterwards;
an authorized disclosure effect, if any, remains in the returned state. -/
def borrowForward (contents : Nat → Stamp → Nat) (lender borrower : Fin size)
    (lease : Lease Nat (Resource size) (Fin size)) (state : ServiceState size) (receipt : Nat) (recipient : Fin size) :
    ServiceState size × Except Refusal Unit :=
  if lease.holder = lender ∧ lease ∈ state.authority.frontier ∧ borrower ∈ state.peer.members then
    let borrowedCall := withBorrow state.authority.frontier lease borrower fun during =>
      step contents borrower {state with authority := {state.authority with frontier := during}} (.forward receipt recipient)
    ({borrowedCall.during.1 with authority := {borrowedCall.during.1.authority with frontier := borrowedCall.after}}, borrowedCall.during.2)
  else (state, .error .denied)

theorem borrow_does_not_persist_authority (contents : Nat → Stamp → Nat) (lender borrower : Fin size)
    (lease : Lease Nat (Resource size) (Fin size)) (state : ServiceState size) (receipt : Nat) (recipient : Fin size) :
    (borrowForward contents lender borrower lease state receipt recipient).1.authority.frontier = state.authority.frontier := by
  unfold borrowForward
  split <;> rfl

/-- A successful read really records this exact current scoped observation.
The empty list is an observed absence, distinct from the denial constructor. -/
theorem read_admitted (contents : Nat → Stamp → Nat) (principal : Fin size) (state next : ServiceState size)
    (scope : Scope) (id : Nat) (reply : Reply)
    (accepted : step contents principal state (.read scope) = (next, .ok (id, reply))) :
    Authorized state.authority.frontier principal (handle state (.read scope)) ∧
      id = state.receipts.length ∧ reply = ScopedRecords.observe contents state.source scope ∧
      next.receipts = state.receipts ++
        [⟨principal, scope, state.peer.epoch, state.source, ScopedRecords.observe contents state.source scope⟩] := by
  dsimp only [step] at accepted
  split at accepted
  · rename_i permitted
    have same := Prod.mk.inj accepted
    have values := Prod.mk.inj (Except.ok.inj same.2)
    exact ⟨permitted.2, values.1.symm, values.2.symm, by rw [← same.1]⟩
  · cases Prod.mk.inj accepted |>.2

theorem forward_admitted (contents : Nat → Stamp → Nat) (principal : Fin size) (state next : ServiceState size)
    (id : Nat) (recipient : Fin size)
    (accepted : step contents principal state (.forward id recipient) = (next, .ok ())) :
    ∃ receipt, state.receipts[id]? = some receipt ∧
      Authorized state.authority.frontier principal (handle state (.forward receipt.reader recipient receipt.scope)) ∧
      next.disclosed = state.disclosed ++
        [⟨id, receipt.reader, principal, recipient, receipt.policyEpoch, state.peer.epoch, receipt.scope,
          receipt.reply⟩] ∧ next.receipts = state.receipts := by
  dsimp only [step] at accepted
  split at accepted
  · cases Prod.mk.inj accepted |>.2
  · rename_i receipt found
    split at accepted
    · rename_i permitted
      have same := Prod.mk.inj accepted
      exact ⟨receipt, found, permitted.2.2, by rw [← same.1], by rw [← same.1]⟩
    · cases Prod.mk.inj accepted |>.2

/-- Forwarding uses the recorded full reply. Changing the query provider
cannot change the payload of an already issued receipt. -/
theorem forwarding_does_not_reexecute_observation (first second : Nat → Stamp → Nat)
    (principal : Fin size) (state : ServiceState size) (id : Nat) (recipient : Fin size) :
    step first principal state (.forward id recipient) = step second principal state (.forward id recipient) := rfl

theorem amendment_requires_authority_and_history (contents : Nat → Stamp → Nat) (principal : Fin size)
    (state next : ServiceState size) (parent epoch : Nat) (members : Finset (Fin size))
    (accepted : step contents principal state (.amend parent epoch members) = (next, .ok ())) :
    Authorized state.authority.frontier principal (handle state .govern) ∧
      parent = state.changes.length ∧ state.peer.epoch < epoch ∧ next.peer.epoch = epoch ∧ next.peer.members = members ∧
      next.peer.sent = state.peer.sent ∧ next.peer.commitments = state.peer.commitments ∧
      next.receipts = state.receipts ∧ next.disclosed = state.disclosed ∧
      state.changes <+: next.changes := by
  dsimp only [step] at accepted
  split at accepted
  · rename_i permitted
    cases (Prod.mk.inj accepted).1
    exact ⟨permitted.2.2.2, permitted.2.1, permitted.2.2.1, rfl, rfl, rfl, rfl, rfl, rfl,
      List.prefix_append _ _⟩
  · cases Prod.mk.inj accepted |>.2

/-- Receipt integrity is established by the read handler and preserved by
actual subsequent service transitions, including denied requests and epoch
changes. Arbitrary externally constructed initial receipts are not certified. -/
def GenuineReceipts (contents : Nat → Stamp → Nat) (state : ServiceState size) : Prop :=
  ∀ receipt ∈ state.receipts, receipt.reply = ScopedRecords.observe contents receipt.source receipt.scope

theorem step_preserves_genuine_receipts (contents : Nat → Stamp → Nat) (principal : Fin size)
    (state : ServiceState size) (request : Request size) (before : GenuineReceipts contents state) :
    GenuineReceipts contents (step contents principal state request).1 := by
  cases request with
  | read scope =>
      dsimp only [step]
      split
      · intro receipt member
        rcases List.mem_append.mp member with previous | fresh
        · exact before receipt previous
        · cases List.mem_singleton.mp fresh
          rfl
      · exact before
  | forward id recipient =>
      dsimp only [step]
      split
      · exact before
      · split <;> exact before
  | amend parent epoch members =>
      dsimp only [step]
      split <;> exact before

def IssuedStep (contents : Nat → Stamp → Nat) (before after : ServiceState size) : Prop :=
  ∃ principal request, (step contents principal before request).1 = after

theorem reached_receipts_are_actual_observations (contents : Nat → Stamp → Nat)
    (start finish : ServiceState size) (empty : start.receipts = [])
    (trace : Relation.ReflTransGen (IssuedStep contents) start finish) : GenuineReceipts contents finish := by
  induction trace with
  | refl => intro receipt member; simp only [empty, List.not_mem_nil] at member
  | tail _ issued ih =>
      obtain ⟨principal, request, rfl⟩ := issued
      exact step_preserves_genuine_receipts contents principal _ request ih

theorem actual_forward_uses_an_original_scoped_observation (contents : Nat → Stamp → Nat)
    (start state next : ServiceState size) (empty : start.receipts = [])
    (trace : Relation.ReflTransGen (IssuedStep contents) start state)
    (principal : Fin size) (id : Nat) (recipient : Fin size)
    (accepted : step contents principal state (.forward id recipient) = (next, .ok ())) :
    ∃ receipt, state.receipts[id]? = some receipt ∧
      Authorized state.authority.frontier principal (handle state (.forward receipt.reader recipient receipt.scope)) ∧
      next.disclosed = state.disclosed ++
        [⟨id, receipt.reader, principal, recipient, receipt.policyEpoch, state.peer.epoch, receipt.scope,
          ScopedRecords.observe contents receipt.source receipt.scope⟩] := by
  obtain ⟨receipt, found, authorized, disclosed, _⟩ := forward_admitted contents principal state next id recipient accepted
  have genuine := reached_receipts_are_actual_observations contents start state empty trace receipt (List.mem_of_getElem? found)
  exact ⟨receipt, found, authorized, by simpa only [genuine] using disclosed⟩

/-- One normal client program performs the read and then requests forwarding.
The two independent refusal boundaries remain visible in its returned value. -/
def readThenForward (scope : Scope) (recipient : Fin size) :
    Prog (Request size) Response (Except Refusal (Reply × Except Refusal Unit)) :=
  .call (.read scope) fun result =>
    match result with
    | .error reason => .ret (.error reason)
    | .ok (id, reply) => .call (.forward id recipient) fun forwarded => .ret (.ok (reply, forwarded))

def disclosureRoot (service : Nat) (message : Disclosure size) : Nat :=
  Encodable.encode (service, message.readEpoch, message.origin.val, message.receipt)

/-- Forwarding records retain the original read occurrence as their atomic
root. A new forwarder or recipient does not create another observation trial. -/
def provenancePacket (service task context : Nat) (message : Disclosure size) :
    Provenance.Packet Nat
      (Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation.Reliance.Scope Nat Nat Nat Nat) Nat :=
  ⟨message.sender.val, ⟨message.origin.val, task, context, message.readEpoch⟩,
    {disclosureRoot service message}, [message.origin.val, message.sender.val, message.recipient.val]⟩

theorem forwarding_preserves_original_observation_root (service : Nat) (first second : Disclosure size)
    (sameOrigin : first.origin = second.origin) (sameReadEpoch : first.readEpoch = second.readEpoch)
    (sameReceipt : first.receipt = second.receipt) (task context : Nat) :
    (provenancePacket service task context first).roots = (provenancePacket service task context second).roots := by
  simp only [provenancePacket, disclosureRoot, sameOrigin, sameReadEpoch, sameReceipt]

namespace Controls

def absent : Scope := .key 1 [99]
def source : Source := ⟨17, 4, [((1, [10, 0]), 1), ((1, [10, 1]), 1)]⟩
def contents (_epoch : Nat) (_stamp : Stamp) : Nat := 42
def readLease : Lease Nat (Resource 3) (Fin 3) := ⟨⟨21, .read absent, 3⟩, 0, .owned⟩
def forwardLease : Lease Nat (Resource 3) (Fin 3) := ⟨⟨21, .forward 0 1 absent, 3⟩, 0, .owned⟩
def adminLease : Lease Nat (Resource 3) (Fin 3) := ⟨⟨21, .govern, 3⟩, 2, .owned⟩
def readOnly : ServiceState 3 := {peer := Peer.initial 3 21 3, authority := ⟨{readLease, adminLease}, []⟩, source := source}
def allowed : ServiceState 3 := {peer := Peer.initial 3 21 3, authority := ⟨{readLease, forwardLease, adminLease}, []⟩, source := source}
def readOnlyCaptured := (step contents 0 readOnly (.read absent)).1
def captured := (step contents 0 allowed (.read absent)).1
def forwarded := (step contents 0 captured (.forward 0 1)).1

def responseTag {Request : Type} : Except Refusal Request → Bool
  | .ok _ => true
  | .error _ => false

theorem actual_absence_read_does_not_authorize_its_forward :
    (step contents 0 readOnly (.read absent)).2 = .ok (0, (17, [])) ∧
      responseTag (step contents 0 readOnlyCaptured (.forward 0 1)).2 = false ∧
      (step contents 0 readOnlyCaptured (.forward 0 1)).1.disclosed = [] ∧
      responseTag (step contents 0 readOnlyCaptured (.forward 999 1)).2 = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem actual_authorized_forward_discloses_the_original_absence :
    responseTag (step contents 0 captured (.forward 0 1)).2 = true ∧
      forwarded.disclosed.map (fun message => (message.origin.val, message.sender.val, message.recipient.val,
        message.readEpoch, message.sendEpoch, message.payload)) = [(0, 0, 1, 3, 3, (17, []))] := ⟨rfl, rfl⟩

def changedSource : ServiceState 3 :=
  {captured with source := ⟨17, 5, source.entries ++ [((1, [99]), 1)]⟩}

theorem historical_disclosure_does_not_reexecute_the_query :
    ScopedRecords.observe contents changedSource.source absent = (17, [(((1, [99]), 1), 42)]) ∧
      ((step (fun _ _ => 999) 0 changedSource (.forward 0 1)).1.disclosed.map Disclosure.payload) = [(17, [])] := by decide

def borrowed := borrowForward contents 0 2 forwardLease captured 0 1
def borrowedRead := borrowForward contents 0 2 readLease readOnlyCaptured 0 1

theorem delimited_forward_borrow_keeps_effect_but_no_permission :
    responseTag borrowed.2 = true ∧ borrowed.1.disclosed.map Disclosure.sender = [2] ∧
      borrowed.1.authority.frontier = captured.authority.frontier ∧
      responseTag (step contents 2 borrowed.1 (.forward 0 1)).2 = false ∧
      responseTag borrowedRead.2 = false := by
  refine ⟨by decide, by decide, borrow_does_not_persist_authority _ _ _ _ _ _ _, by decide, by decide⟩

def amended := (step contents 2 forwarded (.amend 0 4 {0, 2})).1

theorem authorized_epoch_membership_change_keeps_history_and_revokes_old_handles :
    responseTag (step contents 2 forwarded (.amend 0 4 {0, 2})).2 = true ∧
      amended.peer.epoch = 4 ∧ amended.peer.members = {0, 2} ∧
      amended.disclosed = forwarded.disclosed ∧
      amended.receipts.map ReadReceipt.policyEpoch = [3] ∧
      amended.changes.map Change.beforeEpoch = [3] ∧
      responseTag (step contents 0 amended (.read absent)).2 = false := by decide

theorem unauthorized_or_stale_history_changes_are_refused :
    responseTag (step contents 0 forwarded (.amend 0 4 {0, 2})).2 = false ∧
      responseTag (step contents 2 forwarded (.amend 1 4 {0, 2})).2 = false ∧
      responseTag (step contents 2 forwarded (.amend 0 3 {0, 2})).2 = false := by decide


open Mettapedia.Machines.Cursor

abbrev Answer := Except Refusal (Reply × Except Refusal Unit)
abbrev client := PrimitiveProgram.client (Request 3) Response Answer Unit
abbrev Saved := Nat × Outcome (provider contents (0 : Fin 3)) client PUnit.unit

def run (fuel : Nat) (state : ServiceState 3) : Saved :=
  Mettapedia.Machines.Cursor.advance (provider contents (0 : Fin 3)) client (fun _ _ => 1) fuel
    ⟨PUnit.unit, .ok (readThenForward absent (1 : Fin 3)), state⟩

def clientView (saved : Saved) : Nat × Nat × Nat × List Reply :=
  let decoded := PrimitiveProgram.readOutcome (primitive contents (0 : Fin 3)) saved.2
  let status := match decoded.1 with
    | .inr _ => 2
    | .inl (.error _) => 3
    | .inl (.ok (.error _)) => 4
    | .inl (.ok (.ok (_, .ok _))) => 0
    | .inl (.ok (.ok (_, .error _))) => 1
  (saved.1, status, decoded.2.receipts.length, decoded.2.disclosed.map Disclosure.payload)

/-- The unit invoice counts requests in this selected protocol. It does not
price allocation, proof checking, transport, or a concurrent admin request. -/
theorem actual_cursor_client_keeps_forward_denial_separate_from_absence :
    clientView (run 3 allowed) = (2, 0, 1, [(17, [])]) ∧
      clientView (run 3 readOnly) = (2, 1, 1, []) ∧
      clientView (run 1 allowed) = (1, 2, 1, []) := ⟨rfl, rfl, rfl⟩

theorem actual_disclosure_client_split_resume_keeps_full_residual :
    Mettapedia.Machines.Cursor.resume (provider contents (0 : Fin 3)) client (fun _ _ => 1) 2 (run 1 allowed) =
      run 3 allowed :=
  (Mettapedia.Machines.Cursor.advance_add (provider contents (0 : Fin 3)) client (fun _ _ => 1) 1 2
    ⟨PUnit.unit, .ok (readThenForward absent (1 : Fin 3)), allowed⟩).symm

/-- An independently authorized policy transition occurs while the original
client is paused. Mapping the current service world asserts no commutation
with that change: the resumed request must really check the new epoch. -/
def amendedCut : Saved :=
  let cut := run 1 allowed
  (cut.1, Outcome.mapState client
    (fun state => (step contents (2 : Fin 3) state (.amend 0 4 {0, 2})).1) cut.2)

def resumedAfterAmend : Saved :=
  Mettapedia.Machines.Cursor.resume (provider contents (0 : Fin 3)) client (fun _ _ => 1) 2 amendedCut

theorem authorized_amendment_between_read_and_forward_refuses_new_disclosure :
    clientView resumedAfterAmend = (2, 1, 1, []) ∧
      (PrimitiveProgram.readOutcome (primitive contents (0 : Fin 3)) resumedAfterAmend.2).2.peer.epoch = 4 ∧
      (PrimitiveProgram.readOutcome (primitive contents (0 : Fin 3)) resumedAfterAmend.2).2.receipts.map
        ReadReceipt.policyEpoch = [3] := ⟨rfl, rfl, rfl⟩

def votingState : ServiceState 4 :=
  {peer := Peer.Controls.good,
    authority := ⟨{⟨⟨17, .govern, 3⟩, 2, .owned⟩}, []⟩, source := source}
def votingAmended := (step contents (2 : Fin 4) votingState (.amend 0 4 {0, 1, 2})).1

theorem new_epoch_cannot_freshen_old_authenticated_votes :
    Peer.decideLocal 3 (Peer.localView votingState.peer 0 9 11 [0, 1, 2]) = some true ∧
      votingAmended.peer.sent = votingState.peer.sent ∧
      votingAmended.peer.sent.length = 6 ∧
      Peer.decideLocal 3 (Peer.localView votingAmended.peer 0 9 11 [0, 1, 2]) = none := by decide

abbrev AnalysisScope := Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation.Reliance.Scope Nat Nat Nat Nat
def analysisScope : AnalysisScope := ⟨0, 9, 11, 3⟩
def originalRoot : Nat := Encodable.encode (21, 3, 0, (0 : Nat))
def evidenceRegistry : Provenance.Registry AnalysisScope Nat :=
  ⟨fun root => if root = originalRoot then analysisScope else {analysisScope with task := 10},
    fun root => if root = originalRoot then some true else none⟩
def forwardedPackets :=
  (borrowed.1.disclosed ++ forwarded.disclosed).map (provenancePacket 21 9 11)

theorem actual_disclosures_from_two_forwarders_share_one_registered_observation :
    forwardedPackets.map Provenance.Packet.reporter = [2, 0] ∧
      Provenance.roots evidenceRegistry analysisScope forwardedPackets = {originalRoot} ∧
      Provenance.aggregateView evidenceRegistry analysisScope forwardedPackets = (⟨1, 0⟩, ∅) := by
  simp only [Provenance.aggregateView, Provenance.aggregateRoots_eq_sum]
  decide

end Controls

end SpaceService

end Mettapedia.GSLT.BoundaryObservationDisclosure
