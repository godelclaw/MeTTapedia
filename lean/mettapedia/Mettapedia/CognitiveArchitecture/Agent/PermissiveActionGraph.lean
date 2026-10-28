import Mathlib.Data.Finset.Basic

/-!
# Permissive action graphs with witnessed coordination

This is a small scheduling interface inspired by the chain/coordination
distinction in Commons and Pekker's Model of Hierarchical Complexity
(doi:10.1080/02604020802301204).  It is not a formalization of that complete
theory.

Certified chain actions may be reordered when their transition functions are
proved to commute.  Coordination actions instead require a current
observation receipt.  Unclassified actions remain executable in their
original order; absence of a chain certificate removes reorder permission,
not agency.

Every proposed node also says whether it depends on the operator-stimulus
frontier from which it was produced.  A new stimulus invalidates precisely
those unexecuted nodes; explicitly independent nodes remain eligible.  This
is a dependency rule, not a fixed batch-size or mode policy.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.PermissiveActionGraph

universe uNode uAction uRevision uReceipt uWorld

inductive Kind where
  | certifiedChain
  | coordination
  | unspecified
deriving Repr, DecidableEq

/-- One proposed effect with explicit scheduling dependencies. -/
structure Node
    (NodeId : Type uNode) (Action : Type uAction)
    (Revision : Type uRevision) (Receipt : Type uReceipt) where
  id : NodeId
  action : Action
  dependsOn : Finset NodeId
  issuedAt : Revision
  dependsOnStimulus : Bool := true
  kind : Kind := .unspecified
  observationReceipt : Option Receipt := none

/-- The broker state needed to decide whether a node is currently eligible. -/
structure ExecutionState
    (NodeId : Type uNode) (Revision : Type uRevision)
    (Receipt : Type uReceipt) where
  completed : Finset NodeId
  currentRevision : Revision
  availableReceipts : Finset Receipt

def DependenciesMet
    {NodeId : Type uNode} {Action : Type uAction}
    {Revision : Type uRevision} {Receipt : Type uReceipt}
    [DecidableEq NodeId]
    (state : ExecutionState NodeId Revision Receipt)
    (node : Node NodeId Action Revision Receipt) : Prop :=
  node.dependsOn ⊆ state.completed

/-- Stimulus-independent nodes do not become stale merely because the
operator frontier advanced. -/
def FrontierCurrent
    {NodeId : Type uNode} {Action : Type uAction}
    {Revision : Type uRevision} {Receipt : Type uReceipt}
    (state : ExecutionState NodeId Revision Receipt)
    (node : Node NodeId Action Revision Receipt) : Prop :=
  node.dependsOnStimulus = false ∨ node.issuedAt = state.currentRevision

/-- Only coordination nodes require an observation receipt.  Unspecified
nodes preserve the legacy sequential behavior. -/
def ObservationMet
    {NodeId : Type uNode} {Action : Type uAction}
    {Revision : Type uRevision} {Receipt : Type uReceipt}
    [DecidableEq Receipt]
    (state : ExecutionState NodeId Revision Receipt)
    (node : Node NodeId Action Revision Receipt) : Prop :=
  node.kind = .coordination →
    ∃ receipt, node.observationReceipt = some receipt ∧
      receipt ∈ state.availableReceipts

def Ready
    {NodeId : Type uNode} {Action : Type uAction}
    {Revision : Type uRevision} {Receipt : Type uReceipt}
    [DecidableEq NodeId] [DecidableEq Receipt]
    (state : ExecutionState NodeId Revision Receipt)
    (node : Node NodeId Action Revision Receipt) : Prop :=
  DependenciesMet state node ∧ FrontierCurrent state node ∧
    ObservationMet state node

/-- A new operator stimulus changes only the current frontier.  It does not
erase completed effects or unrelated receipts. -/
def observeStimulus
    {NodeId : Type uNode} {Revision : Type uRevision}
    {Receipt : Type uReceipt}
    (state : ExecutionState NodeId Revision Receipt) (revision : Revision) :
    ExecutionState NodeId Revision Receipt :=
  { state with currentRevision := revision }

/-- A dependent node issued against an old frontier is no longer ready. -/
theorem new_stimulus_invalidates_dependent_node
    {NodeId : Type uNode} {Action : Type uAction}
    {Revision : Type uRevision} {Receipt : Type uReceipt}
    [DecidableEq NodeId] [DecidableEq Receipt]
    (state : ExecutionState NodeId Revision Receipt)
    (node : Node NodeId Action Revision Receipt)
    (dependent : node.dependsOnStimulus = true)
    (stale : node.issuedAt ≠ state.currentRevision) :
    ¬ Ready state node := by
  rintro ⟨_, current, _⟩
  rcases current with independent | current
  · simp_all
  · exact stale current

/-- A stimulus-independent ready node remains ready after an arbitrary
frontier change. -/
theorem independent_node_survives_new_stimulus
    {NodeId : Type uNode} {Action : Type uAction}
    {Revision : Type uRevision} {Receipt : Type uReceipt}
    [DecidableEq NodeId] [DecidableEq Receipt]
    (state : ExecutionState NodeId Revision Receipt)
    (node : Node NodeId Action Revision Receipt)
    (independent : node.dependsOnStimulus = false)
    (ready : Ready state node) (revision : Revision) :
    Ready (observeStimulus state revision) node := by
  rcases ready with ⟨dependencies, _, observation⟩
  exact ⟨dependencies, Or.inl independent, observation⟩

/-- A coordination node cannot run without its named current receipt. -/
theorem coordination_without_receipt_not_ready
    {NodeId : Type uNode} {Action : Type uAction}
    {Revision : Type uRevision} {Receipt : Type uReceipt}
    [DecidableEq NodeId] [DecidableEq Receipt]
    (state : ExecutionState NodeId Revision Receipt)
    (node : Node NodeId Action Revision Receipt)
    (coordination : node.kind = .coordination)
    (missing : ∀ receipt, node.observationReceipt = some receipt →
      receipt ∉ state.availableReceipts) :
    ¬ Ready state node := by
  rintro ⟨_, _, observation⟩
  obtain ⟨receipt, named, available⟩ := observation coordination
  exact missing receipt named available

/-- Two transitions form a certified chain when their order has no effect on
the resulting world. -/
def Commute {Action : Type uAction} {World : Type uWorld}
    (step : Action → World → World) (left right : Action) : Prop :=
  ∀ world, step left (step right world) = step right (step left world)

structure ChainCertificate
    {Action : Type uAction} {World : Type uWorld}
    (step : Action → World → World) (left right : Action) : Prop where
  commute : Commute step left right

/-- A chain certificate is exactly the permission needed to swap two effects;
the scheduler need not impose a universal one-command policy. -/
theorem certified_chain_may_swap
    {Action : Type uAction} {World : Type uWorld}
    (step : Action → World → World) (left right : Action)
    (certificate : ChainCertificate step left right) (world : World) :
    step left (step right world) = step right (step left world) :=
  certificate.commute world

end Mettapedia.CognitiveArchitecture.Agent.PermissiveActionGraph

#print axioms Mettapedia.CognitiveArchitecture.Agent.PermissiveActionGraph.new_stimulus_invalidates_dependent_node
#print axioms Mettapedia.CognitiveArchitecture.Agent.PermissiveActionGraph.independent_node_survives_new_stimulus
#print axioms Mettapedia.CognitiveArchitecture.Agent.PermissiveActionGraph.coordination_without_receipt_not_ready
#print axioms Mettapedia.CognitiveArchitecture.Agent.PermissiveActionGraph.certified_chain_may_swap
