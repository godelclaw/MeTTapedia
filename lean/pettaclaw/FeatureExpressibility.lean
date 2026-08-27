import WeakSelfHostingCore
import MinimalKernel

/-!
# FeatureExpressibility — requested behaviors above the weak core

This file answers an architectural question rather than adding kernel laws:

> Can an agent realize the requested behavior as a replaceable extension,
> policy, or observer while `WeakSelfHostingCore` remains unchanged?

Each positive result supplies a concrete witness to the weak runner.  These are
existential adequacy results, not claims that every opaque controller behaves
well.  The duplicate-send example makes that boundary explicit: recorded
metadata supports a no-replay policy, but cannot force an arbitrary controller
to use the metadata.
-/

namespace FeatureExpressibility

open WeakSelfHostingCore

/-! ## One runner hosts Agent, Iter, and Coding transitions -/

def hostedAgentWake {K : Type} (heartbeat : Nat) (event : Claws.Ev) :
    ProtectedPlasticity.Fusion K → Outcome (ProtectedPlasticity.Fusion K) :=
  hostTransformation
    (fun state => ProtectedPlasticity.step heartbeat state (.wake event))

theorem agent_wake_is_expressible {K : Type} (heartbeat : Nat)
    (event : Claws.Ev) (state : ProtectedPlasticity.Fusion K) :
    resolve state (hostedAgentWake heartbeat event state) =
      ProtectedPlasticity.step heartbeat state (.wake event) := by
  rfl

def hostedIterTransformation (transformation : IterArchitecture.Transformation) :
    IterArchitecture.Boundary → Outcome IterArchitecture.Boundary :=
  hostTransformation
    (fun boundary =>
      IterArchitecture.applyTransformation boundary transformation)

theorem iter_transformation_is_expressible
    (transformation : IterArchitecture.Transformation)
    (boundary : IterArchitecture.Boundary) :
    resolve boundary (hostedIterTransformation transformation boundary) =
      IterArchitecture.applyTransformation boundary transformation := by
  rfl

def hostedCodingEvent {K L : Type} (execute : CodingAgent.Executor)
    (event : CodingAgent.Event) :
    ProtectedPlasticity.Coordinates K CodingAgent.State L →
      Outcome (ProtectedPlasticity.Coordinates K CodingAgent.State L) :=
  hostTransformation
    (fun state => CodingAgent.hostedCodingStep execute state event)

theorem coding_event_is_expressible {K L : Type}
    (execute : CodingAgent.Executor) (event : CodingAgent.Event)
    (state : ProtectedPlasticity.Coordinates K CodingAgent.State L) :
    resolve state (hostedCodingEvent execute event state) =
      CodingAgent.hostedCodingStep execute state event := by
  rfl

/-! ## Human attention and timing are policies -/

def hostedHumanEvent (event : ContextAttention.HumanEvent) :
    ContextAttention.State → Outcome ContextAttention.State :=
  hostTransformation (fun state => ContextAttention.receive state event)

theorem human_attention_is_expressible (event : ContextAttention.HumanEvent)
    (state : ContextAttention.State) :
    resolve state (hostedHumanEvent event state) =
      ContextAttention.receive state event := by
  rfl

def hostedAutonomousStep :
    MinimalKernel.Schedule → Outcome MinimalKernel.Schedule :=
  hostTransformation MinimalKernel.autonomousStep

theorem bounded_autonomous_policy_is_expressible
    (state : MinimalKernel.Schedule) :
    resolve state (hostedAutonomousStep state) =
      MinimalKernel.autonomousStep state := by
  rfl

/-! ## Receipts and evidence are optional policies, not root machinery -/

def hostedReceiptIssuance
    (controller : MinimalKernel.RequestView → MinimalKernel.EffectPlan) :
    MinimalKernel.DecisionState → Outcome MinimalKernel.DecisionState :=
  hostTransformation
    (fun state => (MinimalKernel.invokeAndRecord controller state).2)

theorem decision_receipt_policy_is_expressible
    (controller : MinimalKernel.RequestView → MinimalKernel.EffectPlan)
    (state : MinimalKernel.DecisionState) :
    resolve state (hostedReceiptIssuance controller state) =
      (MinimalKernel.invokeAndRecord controller state).2 := by
  rfl

abbrev EvidenceState := MinimalKernel.DecisionState × MinimalKernel.Knowledge

def hostedEvidenceAdmission (receipt : MinimalKernel.ObservationReceipt) :
    EvidenceState → Outcome EvidenceState :=
  hostTransformation
    (fun state => MinimalKernel.admitVerified state.1 state.2 receipt)

theorem evidence_barrier_policy_is_expressible
    (receipt : MinimalKernel.ObservationReceipt) (state : EvidenceState) :
    resolve state (hostedEvidenceAdmission receipt state) =
      MinimalKernel.admitVerified state.1 state.2 receipt := by
  rfl

/-! ## Stuck and wellbeing measurements are non-authoritative observers -/

def observe {State Metric : Type} (metric : State → Metric) (state : State) :
    Metric × Outcome State :=
  (metric state, .success state)

theorem arbitrary_observer_is_noninterfering {State Metric : Type}
    (metric : State → Metric) (state : State) :
    (observe metric state).1 = metric state ∧
      resolve state (observe metric state).2 = state := by
  exact ⟨rfl, rfl⟩

def nonProgressMetric (monitor : MinimalKernel.ProgressMonitor) : Bool :=
  monitor.stuck

theorem stuck_signal_is_an_observer
    (monitor : MinimalKernel.ProgressMonitor) :
    resolve monitor (observe nonProgressMetric monitor).2 = monitor := by
  rfl

/-! ## Correct context metadata supports, but does not force, no-replay -/

structure SendView where
  proposed : Option Nat
  observedSent : List Nat
deriving Repr, DecidableEq

def recordSent (effect : Nat) (view : SendView) : SendView :=
  { view with observedSent := view.observedSent ++ [effect] }

def metadataAwareProposal (view : SendView) : Option Nat :=
  match view.proposed with
  | none => none
  | some effect =>
      if effect ∈ view.observedSent then none else some effect

def hostedSentObservation (effect : Nat) : SendView → Outcome SendView :=
  hostTransformation (recordSent effect)

theorem sent_observation_is_expressible (effect : Nat) (view : SendView) :
    resolve view (hostedSentObservation effect view) = recordSent effect view := by
  rfl

/-- A controller policy that uses the observation metadata does not propose the
same effect again.  No kernel duplicate checker is involved. -/
theorem metadata_supports_no_replay (effect : Nat) (view : SendView) :
    metadataAwareProposal
      (recordSent effect { view with proposed := some effect }) = none := by
  simp [metadataAwareProposal, recordSent]

/-- An opaque controller may ignore perfectly supplied metadata.  Therefore a
universal no-duplicate guarantee, if required, belongs in an effect adapter;
it cannot be derived from context visibility alone. -/
def replayingController (effect : Nat) (_ : SendView) : Option Nat :=
  some effect

theorem metadata_does_not_control_an_arbitrary_controller
    (effect : Nat) (view : SendView) :
    replayingController effect (recordSent effect view) = some effect := by
  rfl

end FeatureExpressibility

/-! ## Axiom audit -/

#print axioms FeatureExpressibility.agent_wake_is_expressible
#print axioms FeatureExpressibility.iter_transformation_is_expressible
#print axioms FeatureExpressibility.coding_event_is_expressible
#print axioms FeatureExpressibility.human_attention_is_expressible
#print axioms FeatureExpressibility.bounded_autonomous_policy_is_expressible
#print axioms FeatureExpressibility.decision_receipt_policy_is_expressible
#print axioms FeatureExpressibility.evidence_barrier_policy_is_expressible
#print axioms FeatureExpressibility.arbitrary_observer_is_noninterfering
#print axioms FeatureExpressibility.metadata_supports_no_replay
#print axioms FeatureExpressibility.metadata_does_not_control_an_arbitrary_controller
