import VerifiedFrontier

/-!
# MinimalKernel — a weakest-sufficient agent commit core

This file refines the verified-frontier architecture around five operational
obligations:

* a decision receipt binds an effect to the exact projected request;
* protected promotion fails closed while the last-known-good runtime stays live;
* finite autonomous work yields, and pending human input preempts it;
* verified knowledge is admitted only with an observation receipt; and
* bounded syntactic non-progress becomes observable.

The word *minimal* is semantic here.  A condition is weaker when it admits
more candidate executions.  The canonical commit condition is proved to be
the weakest (most permissive) sound gate: every other sound gate admits a
subset of its executions.  This avoids equating source length with semantic
simplicity.

The coordinate results are deliberately called observational irredundancy,
not global syntactic minimality.  For each distinction we exhibit a behavior
that becomes possible, or an observation that becomes impossible, when that
distinction is erased.
-/

namespace MinimalKernel

abbrev Frontier := Nat
abbrev ContextDigest := Nat
abbrev ControllerRevision := Nat
abbrev ProposalDigest := Nat
abbrev EffectKey := Nat
abbrev Target := Nat
abbrev Claim := Nat
abbrev EvidenceDigest := Nat

/-! ## Decision receipts -/

/-- The exact request projection supplied to one controller invocation. -/
structure RequestView where
  frontier : Frontier
  contextDigest : ContextDigest
  controllerRevision : ControllerRevision
deriving Repr, DecidableEq

structure EffectPlan where
  key : EffectKey
  digest : ProposalDigest
deriving Repr, DecidableEq

/-- A receipt binds the proposed effect to the request bytes supplied to the
controller.  In an implementation this record is issued by the harness, not by
the payload being checked. -/
structure DecisionReceipt where
  request : RequestView
  effectKey : EffectKey
  proposalDigest : ProposalDigest
deriving Repr, DecidableEq

structure Decision where
  plan : EffectPlan
  receipt : DecisionReceipt
deriving Repr, DecidableEq

structure ObservationReceipt where
  claim : Claim
  evidenceDigest : EvidenceDigest
deriving Repr, DecidableEq

inductive DecisionEvent
  | issued (receipt : DecisionReceipt)
  | committed (key : EffectKey)
  | observed (receipt : ObservationReceipt)
deriving Repr, DecidableEq

structure DecisionState where
  request : RequestView
  log : List DecisionEvent
deriving Repr, DecidableEq

/-- The only decision constructor used by the transition system: the
controller receives the current request projection, and the harness binds its
result to that projection. -/
def invoke (controller : RequestView → EffectPlan) (state : DecisionState) :
    Decision :=
  let plan := controller state.request
  { plan := plan
    receipt :=
      { request := state.request
        effectKey := plan.key
        proposalDigest := plan.digest } }

/-- Issuance is a protected harness transition.  The exact receipt is appended
to the sole decision/effect event log before it can authorize a commit. -/
def invokeAndRecord (controller : RequestView → EffectPlan)
    (state : DecisionState) : Decision × DecisionState :=
  let decision := invoke controller state
  (decision, { state with log := state.log ++ [.issued decision.receipt] })

def ReceiptIssued (state : DecisionState) (decision : Decision) : Prop :=
  .issued decision.receipt ∈ state.log

def ReceiptCurrent (state : DecisionState) (decision : Decision) : Prop :=
  decision.receipt.request = state.request

def ReceiptExact (decision : Decision) : Prop :=
  decision.receipt.effectKey = decision.plan.key ∧
    decision.receipt.proposalDigest = decision.plan.digest

def EffectFresh (state : DecisionState) (decision : Decision) : Prop :=
  .committed decision.plan.key ∉ state.log

/-- The safety contract for an externally visible effect. -/
def SafeCommit (state : DecisionState) (decision : Decision) : Prop :=
  ReceiptIssued state decision ∧ ReceiptCurrent state decision ∧
    ReceiptExact decision ∧ EffectFresh state decision

/-- The canonical gate contains no policy beyond the safety contract. -/
def CanonicalGate (state : DecisionState) (decision : Decision) : Prop :=
  SafeCommit state decision

def commitDecision (state : DecisionState) (decision : Decision)
    (_ : CanonicalGate state decision) : DecisionState :=
  { state with log := state.log ++ [.committed decision.plan.key] }

theorem invocation_receipt_binds_exact_current_request
    (controller : RequestView → EffectPlan) (state : DecisionState) :
    (invoke controller state).receipt.request = state.request ∧
      (invoke controller state).receipt.effectKey =
        (invoke controller state).plan.key ∧
      (invoke controller state).receipt.proposalDigest =
        (invoke controller state).plan.digest := by
  simp [invoke]

/-- This is the precise, machine-checkable interpretation of “the model saw
the context”: the current request projection was the argument to the
controller invocation.  It does not claim that an opaque controller made
psychological use of every supplied byte. -/
theorem invocation_consumes_current_projection
    (controller : RequestView → EffectPlan) (state : DecisionState) :
    invoke controller state =
      let plan := controller state.request
      { plan := plan
        receipt :=
          { request := state.request
            effectKey := plan.key
            proposalDigest := plan.digest } } := by
  rfl

theorem recorded_invocation_has_issued_exact_current_receipt
    (controller : RequestView → EffectPlan) (state : DecisionState) :
    let result := invokeAndRecord controller state
    ReceiptIssued result.2 result.1 ∧
      ReceiptCurrent result.2 result.1 ∧ ReceiptExact result.1 := by
  simp [invokeAndRecord, invoke, ReceiptIssued, ReceiptCurrent, ReceiptExact]

theorem recorded_invocation_is_committable_when_effect_is_fresh
    (controller : RequestView → EffectPlan) (state : DecisionState)
    (fresh : .committed (controller state.request).key ∉ state.log) :
    let result := invokeAndRecord controller state
    CanonicalGate result.2 result.1 := by
  simp [invokeAndRecord, invoke, CanonicalGate, SafeCommit, ReceiptIssued,
    ReceiptCurrent, ReceiptExact, EffectFresh, fresh]

theorem changed_context_invalidates_old_receipt
    (state : DecisionState) (decision : Decision)
    (current : decision.receipt.request = state.request)
    (newDigest : ContextDigest) (changed : newDigest ≠ state.request.contextDigest) :
    let next : DecisionState :=
      { state with
        request := { state.request with contextDigest := newDigest } }
    ¬ ReceiptCurrent next decision := by
  dsimp [ReceiptCurrent]
  intro equal
  have digestEqual := congrArg RequestView.contextDigest equal
  simp [current] at digestEqual
  exact changed digestEqual.symm

theorem semantic_effect_key_is_exactly_once
    (state : DecisionState) (decision : Decision)
    (certificate : CanonicalGate state decision) :
    ¬ EffectFresh (commitDecision state decision certificate) decision := by
  simp [EffectFresh, commitDecision]

/-- Two syntactically different proposals with the same semantic effect key
cannot both commit. -/
theorem same_key_replay_is_rejected
    (state : DecisionState) (first replay : Decision)
    (certificate : CanonicalGate state first)
    (sameKey : replay.plan.key = first.plan.key) :
    ¬ EffectFresh (commitDecision state first certificate) replay := by
  simp [EffectFresh, commitDecision, sameKey]

theorem invoke_record_is_append_only
    (controller : RequestView → EffectPlan) (state : DecisionState) :
    state.log.IsPrefix (invokeAndRecord controller state).2.log := by
  simp [invokeAndRecord, List.IsPrefix]

theorem decision_commit_is_append_only
    (state : DecisionState) (decision : Decision)
    (certificate : CanonicalGate state decision) :
    state.log.IsPrefix (commitDecision state decision certificate).log := by
  simp [commitDecision, List.IsPrefix]

theorem unissued_receipt_cannot_commit :
    let request : RequestView := ⟨7, 11, 3⟩
    let plan : EffectPlan := ⟨5, 19⟩
    let decision : Decision :=
      { plan := plan
        receipt := ⟨request, plan.key, plan.digest⟩ }
    let state : DecisionState := ⟨request, []⟩
    ¬ CanonicalGate state decision := by
  simp [CanonicalGate, SafeCommit, ReceiptIssued]

def IssuanceBlindGate (state : DecisionState) (decision : Decision) : Prop :=
  ReceiptCurrent state decision ∧ ReceiptExact decision ∧
    EffectFresh state decision

theorem issuance_erasure_accepts_fabricated_receipt :
    let request : RequestView := ⟨7, 11, 3⟩
    let plan : EffectPlan := ⟨5, 19⟩
    let decision : Decision :=
      { plan := plan
        receipt := ⟨request, plan.key, plan.digest⟩ }
    let state : DecisionState := ⟨request, []⟩
    IssuanceBlindGate state decision ∧ ¬ CanonicalGate state decision := by
  simp [IssuanceBlindGate, ReceiptCurrent, ReceiptExact, EffectFresh,
    CanonicalGate, SafeCommit, ReceiptIssued]

/-- Digest-only replay protection misses semantic replays whose serialization
changes while their externally visible effect identity stays the same. -/
def DigestFresh (committedDigests : List ProposalDigest)
    (plan : EffectPlan) : Prop :=
  plan.digest ∉ committedDigests

theorem digest_only_dedup_allows_same_semantic_effect_twice :
    let first : EffectPlan := ⟨5, 19⟩
    let replay : EffectPlan := ⟨5, 20⟩
    first.key = replay.key ∧ DigestFresh [first.digest] replay := by
  exact ⟨rfl, by simp [DigestFresh]⟩

/-! ## Weakest-sufficient gate -/

abbrev Gate := DecisionState → Decision → Prop

def Sound (gate : Gate) : Prop :=
  ∀ state decision, gate state decision → SafeCommit state decision

def Complete (gate : Gate) : Prop :=
  ∀ state decision, SafeCommit state decision → gate state decision

/-- `left` is semantically weaker than `right` when it accepts every execution
that `right` accepts, and possibly more. -/
def WeakerThan (left right : Gate) : Prop :=
  ∀ state decision, right state decision → left state decision

theorem canonical_gate_is_sound : Sound CanonicalGate := by
  intro state decision accepted
  exact accepted

theorem canonical_gate_is_complete : Complete CanonicalGate := by
  intro state decision safe
  exact safe

/-- Among sound gates, the canonical safety predicate is maximally weak: no
other sound gate can safely admit a behavior that it rejects. -/
theorem canonical_gate_is_weakest_sound (gate : Gate) (sound : Sound gate) :
    WeakerThan CanonicalGate gate := by
  intro state decision accepted
  exact sound state decision accepted

theorem sound_and_complete_gate_is_extensionally_canonical
    (gate : Gate) (sound : Sound gate) (complete : Complete gate) :
    ∀ state decision, gate state decision ↔ CanonicalGate state decision := by
  intro state decision
  exact ⟨sound state decision, complete state decision⟩

/-! A frontier number alone is not a decision receipt.  If context identity is
erased, a proposal can be relabelled with the current frontier even though its
content was produced from different request bytes. -/

structure FrontierOnlyReceipt where
  frontier : Frontier
  effectKey : EffectKey
  proposalDigest : ProposalDigest
deriving Repr, DecidableEq

def FrontierOnlyAccepts (state : DecisionState) (plan : EffectPlan)
    (receipt : FrontierOnlyReceipt) : Prop :=
  receipt.frontier = state.request.frontier ∧
    receipt.effectKey = plan.key ∧ receipt.proposalDigest = plan.digest

instance (state : DecisionState) (plan : EffectPlan)
    (receipt : FrontierOnlyReceipt) :
    Decidable (FrontierOnlyAccepts state plan receipt) := by
  unfold FrontierOnlyAccepts
  infer_instance

theorem frontier_only_receipt_allows_context_relabel :
    let oldRequest : RequestView := ⟨7, 11, 3⟩
    let newRequest : RequestView := ⟨7, 12, 3⟩
    let state : DecisionState := ⟨newRequest, []⟩
    let stalePlan : EffectPlan := ⟨5, 19⟩
    let relabelled : FrontierOnlyReceipt := ⟨7, 5, 19⟩
    oldRequest.contextDigest ≠ newRequest.contextDigest ∧
      FrontierOnlyAccepts state stalePlan relabelled := by
  decide

/-! ## Fail-closed promotion, fail-alive runtime -/

structure MutationProposal where
  target : Target
  basedOnRevision : Nat
  digest : ProposalDigest
deriving Repr, DecidableEq

structure Runtime where
  revision : Target → Nat
  installedDigest : Target → ProposalDigest
  running : Bool

inductive ValidationResult
  | passed (checkedDigest : ProposalDigest)
  | rejected
  | infraError
deriving Repr, DecidableEq

def PromoteSafe (runtime : Runtime) (proposal : MutationProposal)
    (checkedDigest : ProposalDigest) : Prop :=
  proposal.basedOnRevision = runtime.revision proposal.target ∧
    proposal.digest = checkedDigest

instance (runtime : Runtime) (proposal : MutationProposal)
    (checkedDigest : ProposalDigest) :
    Decidable (PromoteSafe runtime proposal checkedDigest) := by
  unfold PromoteSafe
  infer_instance

def install (runtime : Runtime) (proposal : MutationProposal)
    (checkedDigest : ProposalDigest)
    (_ : PromoteSafe runtime proposal checkedDigest) : Runtime :=
  { revision := fun target =>
      if target = proposal.target then runtime.revision target + 1
      else runtime.revision target
    installedDigest := fun target =>
      if target = proposal.target then proposal.digest
      else runtime.installedDigest target
    running := runtime.running }

/-- Rejection and infrastructure failure are observations, not deployments.
Only a proof-carrying `passed` result can call `install`. -/
def resolveValidation (runtime : Runtime) (proposal : MutationProposal) :
    ValidationResult → Runtime
  | .passed checkedDigest =>
      if certificate : PromoteSafe runtime proposal checkedDigest then
        install runtime proposal checkedDigest certificate
      else runtime
  | .rejected => runtime
  | .infraError => runtime

theorem rejection_preserves_last_known_good
    (runtime : Runtime) (proposal : MutationProposal) :
    resolveValidation runtime proposal .rejected = runtime := by
  rfl

theorem infrastructure_failure_preserves_last_known_good
    (runtime : Runtime) (proposal : MutationProposal) :
    resolveValidation runtime proposal .infraError = runtime := by
  rfl

theorem validation_failure_cannot_kill_running_kernel
    (runtime : Runtime) (proposal : MutationProposal)
    (alive : runtime.running = true) :
    (resolveValidation runtime proposal .infraError).running = true ∧
      (resolveValidation runtime proposal .rejected).running = true := by
  exact ⟨alive, alive⟩

theorem valid_promotion_installs_exact_digest_and_preserves_liveness
    (runtime : Runtime) (proposal : MutationProposal)
    (checkedDigest : ProposalDigest)
    (safe : PromoteSafe runtime proposal checkedDigest) :
    let next := resolveValidation runtime proposal (.passed checkedDigest)
    next.installedDigest proposal.target = proposal.digest ∧
      next.running = runtime.running := by
  simp [resolveValidation, safe, install]

/-- Erasing the last-known-good distinction permits an infrastructure outage
to be confused with a verdict and to kill the runtime. -/
def naiveResolve (runtime : Runtime) : ValidationResult → Runtime
  | .infraError => { runtime with running := false }
  | _ => runtime

theorem naive_infrastructure_failure_can_kill_kernel :
    let runtime : Runtime :=
      { revision := fun _ => 0
        installedDigest := fun _ => 7
        running := true }
    (naiveResolve runtime .infraError).running = false := by
  rfl

/-! ## Finite autonomous work and human preemption -/

structure Schedule where
  pendingHuman : Nat
  budget : Nat
deriving Repr, DecidableEq

def autonomousStep (state : Schedule) : Schedule :=
  if state.pendingHuman = 0 then
    match state.budget with
    | 0 => state
    | n + 1 => { state with budget := n }
  else state

def autonomousSteps : Nat → Schedule → Schedule
  | 0, state => state
  | n + 1, state => autonomousSteps n (autonomousStep state)

def atQuietPoint (state : Schedule) : Prop :=
  state.budget = 0

theorem pending_human_preempts_autonomy (state : Schedule)
    (pending : state.pendingHuman ≠ 0) :
    autonomousStep state = state := by
  simp [autonomousStep, pending]

theorem exhausted_budget_yields (state : Schedule)
    (exhausted : state.budget = 0) :
    autonomousStep state = state := by
  simp [autonomousStep, exhausted]

theorem finite_budget_reaches_quiet_point (budget : Nat) :
    atQuietPoint (autonomousSteps budget ⟨0, budget⟩) := by
  induction budget with
  | zero => simp [atQuietPoint, autonomousSteps]
  | succ budget ih =>
      simpa [autonomousSteps, autonomousStep] using ih

/-- Without a finite budget coordinate, an autonomous transition may remain
enabled forever in a quiet environment. -/
structure UnboundedSchedule where
  pendingHuman : Nat
deriving Repr, DecidableEq

def unboundedAutonomousStep (state : UnboundedSchedule) : UnboundedSchedule :=
  state

def unboundedAutonomousSteps : Nat → UnboundedSchedule → UnboundedSchedule
  | 0, state => state
  | n + 1, state => unboundedAutonomousSteps n (unboundedAutonomousStep state)

theorem unbounded_autonomy_has_no_internal_quiet_countdown (steps : Nat) :
    let state : UnboundedSchedule := ⟨0⟩
    unboundedAutonomousSteps steps state = state := by
  induction steps with
  | zero => rfl
  | succ steps ih => simpa [unboundedAutonomousSteps,
      unboundedAutonomousStep] using ih

/-! ## Evidence barrier -/

structure Knowledge where
  verified : List Claim
deriving Repr, DecidableEq

def EvidenceClosed (log : List DecisionEvent) (knowledge : Knowledge) : Prop :=
  ∀ claim, claim ∈ knowledge.verified →
    ∃ receipt, .observed receipt ∈ log ∧ receipt.claim = claim

def emptyKnowledge : Knowledge := ⟨[]⟩

def admitVerified (state : DecisionState) (knowledge : Knowledge)
    (receipt : ObservationReceipt) : DecisionState × Knowledge :=
  ({ state with log := state.log ++ [.observed receipt] },
    { verified := knowledge.verified ++ [receipt.claim] })

theorem empty_knowledge_is_evidence_closed (log : List DecisionEvent) :
    EvidenceClosed log emptyKnowledge := by
  simp [EvidenceClosed, emptyKnowledge]

theorem evidence_admission_preserves_closure (state : DecisionState)
    (knowledge : Knowledge) (receipt : ObservationReceipt)
    (closed : EvidenceClosed state.log knowledge) :
    let next := admitVerified state knowledge receipt
    EvidenceClosed next.1.log next.2 := by
  dsimp [admitVerified]
  unfold EvidenceClosed
  intro claim member
  have memberCases :
      claim ∈ knowledge.verified ∨ claim ∈ [receipt.claim] :=
    List.mem_append.mp member
  cases memberCases with
  | inl old =>
      obtain ⟨oldReceipt, oldMember, same⟩ := closed claim old
      exact ⟨oldReceipt, List.mem_append_left _ oldMember, same⟩
  | inr new =>
      have same : claim = receipt.claim := by simpa using new
      exact ⟨receipt, by simp, same.symm⟩

theorem newly_verified_claim_has_exact_receipt
    (state : DecisionState) (knowledge : Knowledge)
    (receipt : ObservationReceipt) :
    receipt.claim ∈ (admitVerified state knowledge receipt).2.verified ∧
      .observed receipt ∈ (admitVerified state knowledge receipt).1.log := by
  simp [admitVerified]

theorem evidence_admission_is_append_only
    (state : DecisionState) (knowledge : Knowledge)
    (receipt : ObservationReceipt) :
    state.log.IsPrefix (admitVerified state knowledge receipt).1.log := by
  simp [admitVerified, List.IsPrefix]

def naiveVerify (knowledge : Knowledge) (claim : Claim) : Knowledge :=
  { knowledge with verified := knowledge.verified ++ [claim] }

theorem evidence_erasure_permits_silent_false_success :
    let knowledge := naiveVerify emptyKnowledge 42
    42 ∈ knowledge.verified ∧ ¬ EvidenceClosed [] knowledge := by
  simp [naiveVerify, emptyKnowledge, EvidenceClosed]

/-! ## Bounded syntactic non-progress -/

/-- A countdown monitor observes one deliberately narrow condition: a bounded
run of transitions that report no progress.  It does not decide semantic
stuckness or whether a difficult task should be abandoned. -/
structure ProgressMonitor where
  remaining : Nat
  stuck : Bool
deriving Repr, DecidableEq

def noProgress : ProgressMonitor → ProgressMonitor
  | ⟨0, _⟩ => ⟨0, true⟩
  | ⟨n + 1, stuck⟩ => ⟨n, stuck⟩

def noProgressSteps : Nat → ProgressMonitor → ProgressMonitor
  | 0, monitor => monitor
  | n + 1, monitor => noProgressSteps n (noProgress monitor)

def progress (threshold : Nat) (_ : ProgressMonitor) : ProgressMonitor :=
  ⟨threshold, false⟩

theorem bounded_nonprogress_becomes_observable (bound : Nat) :
    (noProgressSteps (bound + 1) ⟨bound, false⟩).stuck = true := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
      simpa [noProgressSteps, noProgress] using ih

theorem observed_progress_resets_detector (threshold : Nat)
    (monitor : ProgressMonitor) :
    progress threshold monitor = ⟨threshold, false⟩ := by
  rfl

/-- Erasing the counter makes every finite stagnation history observationally
identical to the initial state. -/
def blindNoProgress (flag : Bool) : Bool := flag

def blindNoProgressSteps : Nat → Bool → Bool
  | 0, flag => flag
  | n + 1, flag => blindNoProgressSteps n (blindNoProgress flag)

theorem counter_erasure_hides_every_finite_stagnation (steps : Nat) :
    blindNoProgressSteps steps false = false := by
  induction steps with
  | zero => rfl
  | succ steps ih => simpa [blindNoProgressSteps, blindNoProgress] using ih

/-! ## One product state, orthogonal policies -/

/-- The product is a single authoritative kernel state.  Iter-style
development, PettaClaw-style life scheduling, and coding-agent episodic policy
are transition policies over this state rather than independent loops. -/
structure State where
  decision : DecisionState
  runtime : Runtime
  schedule : Schedule
  knowledge : Knowledge
  monitor : ProgressMonitor

def updateDecision (state : State) (next : DecisionState) : State :=
  { state with decision := next }

def updateSchedule (state : State) (next : Schedule) : State :=
  { state with schedule := next }

def updateKnowledge (state : State) (next : Knowledge) : State :=
  { state with knowledge := next }

theorem decision_and_schedule_updates_commute (state : State)
    (decision : DecisionState) (schedule : Schedule) :
    updateSchedule (updateDecision state decision) schedule =
      updateDecision (updateSchedule state schedule) decision := by
  rfl

theorem decision_and_knowledge_updates_commute (state : State)
    (decision : DecisionState) (knowledge : Knowledge) :
    updateKnowledge (updateDecision state decision) knowledge =
      updateDecision (updateKnowledge state knowledge) decision := by
  rfl

/-! ## Conservative fusion -/

/-- Iter contributes development, PettaClaw contributes persistent life, and
the coding-agent policy contributes receipt-driven episodes.  They share the
single kernel above without collapsing protected coordinates. -/
structure Fused (K D L : Type) where
  coordinates : ProtectedPlasticity.Coordinates K D L
  core : State

def reviseDevelopment {K D L : Type} (state : Fused K D L)
    (change : D → D) : Fused K D L :=
  { state with
    coordinates := ProtectedPlasticity.revise state.coordinates change }

def evolveLife {K D L : Type} (state : Fused K D L)
    (change : L → L) : Fused K D L :=
  { state with
    coordinates := ProtectedPlasticity.evolve state.coordinates change }

def updateCore {K D L : Type} (state : Fused K D L)
    (change : State → State) : Fused K D L :=
  { state with core := change state.core }

theorem arbitrary_development_preserves_kernel_life_and_core {K D L : Type}
    (state : Fused K D L) (change : D → D) :
    let next := reviseDevelopment state change
    next.coordinates.kernel = state.coordinates.kernel ∧
      next.coordinates.life = state.coordinates.life ∧
      next.core = state.core := by
  exact ⟨rfl, rfl, rfl⟩

theorem core_and_development_commute {K D L : Type}
    (state : Fused K D L) (development : D → D)
    (core : State → State) :
    updateCore (reviseDevelopment state development) core =
      reviseDevelopment (updateCore state core) development := by
  rfl

theorem core_and_life_commute {K D L : Type}
    (state : Fused K D L) (life : L → L) (core : State → State) :
    updateCore (evolveLife state life) core =
      evolveLife (updateCore state core) life := by
  rfl

end MinimalKernel

/-! ## Axiom audit -/
#print axioms MinimalKernel.invocation_receipt_binds_exact_current_request
#print axioms MinimalKernel.recorded_invocation_has_issued_exact_current_receipt
#print axioms MinimalKernel.recorded_invocation_is_committable_when_effect_is_fresh
#print axioms MinimalKernel.changed_context_invalidates_old_receipt
#print axioms MinimalKernel.semantic_effect_key_is_exactly_once
#print axioms MinimalKernel.unissued_receipt_cannot_commit
#print axioms MinimalKernel.issuance_erasure_accepts_fabricated_receipt
#print axioms MinimalKernel.digest_only_dedup_allows_same_semantic_effect_twice
#print axioms MinimalKernel.canonical_gate_is_weakest_sound
#print axioms MinimalKernel.sound_and_complete_gate_is_extensionally_canonical
#print axioms MinimalKernel.frontier_only_receipt_allows_context_relabel
#print axioms MinimalKernel.infrastructure_failure_preserves_last_known_good
#print axioms MinimalKernel.validation_failure_cannot_kill_running_kernel
#print axioms MinimalKernel.finite_budget_reaches_quiet_point
#print axioms MinimalKernel.evidence_admission_preserves_closure
#print axioms MinimalKernel.evidence_admission_is_append_only
#print axioms MinimalKernel.evidence_erasure_permits_silent_false_success
#print axioms MinimalKernel.bounded_nonprogress_becomes_observable
#print axioms MinimalKernel.counter_erasure_hides_every_finite_stagnation
#print axioms MinimalKernel.decision_and_schedule_updates_commute
#print axioms MinimalKernel.arbitrary_development_preserves_kernel_life_and_core
#print axioms MinimalKernel.core_and_development_commute
