import Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra

/-!
# An agent using a MeTTa space

An AtomSpace is a space in MeTTa.  This module does not assign it an
architectural status such as authoritative, derived, private, or shared.
Those are choices made by the agent program using the space.

The formal question here is narrower: what becomes possible when goals,
evidence, and their relations inhabit one MeTTa space?  The example uses the
space and query algebras of `SpaceQueryAlgebra`:

* atoms have bag multiplicity;
* spaces compose by pointwise union;
* query legs are constraints on variable bindings;
* a conjunction of query legs is their simultaneous meet.

The final theorem witnesses a strict compositional gain.  A life-oriented
process contributes a goal and its outstanding evidence need.  A
coding-oriented process contributes an artifact and a support relation.
Neither contribution answers the joined query alone; their union does.  This
is the useful kernel of the proposed agent integration: processes can meet by
writing and querying typed atoms in the same MeTTa space, without a bespoke
host-language join protocol.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.AgentMeTTaSpace

open Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra

/-! ## Agent atoms placed in a MeTTa space -/

inductive GoalId where
  | focus
  | background
  deriving DecidableEq

inductive EvidenceId where
  | testReceipt
  | reviewReceipt
  deriving DecidableEq

/-- A deliberately small vocabulary for the integration witness. -/
inductive AgentAtom where
  | goal : GoalId → AgentAtom
  | needsEvidence : GoalId → AgentAtom
  | evidence : EvidenceId → AgentAtom
  | supports : EvidenceId → GoalId → AgentAtom
  deriving DecidableEq

/-- The agent uses an ordinary MeTTa multiset space of `AgentAtom`s. -/
abbrev AgentSpace := MSpace AgentAtom

/-- A singleton bag-space. -/
def singletonSpace (atom : AgentAtom) : AgentSpace :=
  fun candidate => if candidate = atom then 1 else 0

/-- Adding an atom is union with its singleton space. -/
def addAtom (space : AgentSpace) (atom : AgentAtom) : AgentSpace :=
  sUnion space (singletonSpace atom)

/-- Independent additions commute at the space level. -/
theorem addAtom_comm (space : AgentSpace) (left right : AgentAtom) :
    addAtom (addAtom space left) right =
      addAtom (addAtom space right) left := by
  unfold addAtom
  rw [sUnion_assoc, sUnion_assoc]
  congr 1
  exact sUnion_comm _ _

/-! ## Query bindings and conjunctive legs -/

/-- A binding proposed by a relational query. -/
structure Binding where
  goal : GoalId
  evidence : EvidenceId
  deriving DecidableEq

def goalLeg (space : AgentSpace) : Query Binding :=
  fun binding => 0 < space (.goal binding.goal)

def needLeg (space : AgentSpace) : Query Binding :=
  fun binding => 0 < space (.needsEvidence binding.goal)

def evidenceLeg (space : AgentSpace) : Query Binding :=
  fun binding => 0 < space (.evidence binding.evidence)

def supportLeg (space : AgentSpace) : Query Binding :=
  fun binding => 0 < space (.supports binding.evidence binding.goal)

/-- One query joins the goal, need, evidence, and support relation. -/
def actionableQuery (space : AgentSpace) : Query Binding :=
  foldConj
    [goalLeg space, needLeg space, evidenceLeg space, supportLeg space]

/-- Zariuq's fold theorem applies directly: sequential query evaluation is
only an implementation schedule for the simultaneous conjunction. -/
theorem actionableQuery_eq_meet (space : AgentSpace) :
    actionableQuery space =
      meetAll
        [goalLeg space, needLeg space, evidenceLeg space, supportLeg space] :=
  foldConj_eq_meet _

/-! ## Two agent processes meeting in one space -/

/-- A life-oriented process contributes the active goal and its open need. -/
def lifeContribution : AgentSpace :=
  sUnion
    (singletonSpace (.goal .focus))
    (singletonSpace (.needsEvidence .focus))

/-- A coding-oriented process contributes a test receipt and what it supports. -/
def codingContribution : AgentSpace :=
  sUnion
    (singletonSpace (.evidence .testReceipt))
    (singletonSpace (.supports .testReceipt .focus))

/-- Both processes use the same MeTTa space by ordinary space union. -/
def combinedSpace : AgentSpace :=
  sUnion lifeContribution codingContribution

def focusTestBinding : Binding :=
  ⟨.focus, .testReceipt⟩

/-- The combined space answers the four-leg join. -/
theorem combined_space_answers_join :
    actionableQuery combinedSpace focusTestBinding := by
  simp [actionableQuery, foldConj, conj, unitQ, goalLeg, needLeg,
    evidenceLeg, supportLeg, combinedSpace, lifeContribution,
    codingContribution, singletonSpace, sUnion, focusTestBinding]

/-- The life contribution alone lacks the evidence leg. -/
theorem life_space_misses_join :
    ¬ actionableQuery lifeContribution focusTestBinding := by
  simp [actionableQuery, foldConj, conj, unitQ, goalLeg, needLeg,
    evidenceLeg, supportLeg, lifeContribution, singletonSpace, sUnion,
    focusTestBinding]

/-- The coding contribution alone lacks the goal leg. -/
theorem coding_space_misses_join :
    ¬ actionableQuery codingContribution focusTestBinding := by
  simp [actionableQuery, foldConj, conj, unitQ, goalLeg, needLeg,
    evidenceLeg, supportLeg, codingContribution, singletonSpace, sUnion,
    focusTestBinding]

/-- Strict compositional gain from using one space: neither contributor can
answer alone, while their union can answer by variable-sharing conjunction. -/
theorem one_space_strict_join_gain :
    actionableQuery combinedSpace focusTestBinding ∧
    ¬ actionableQuery lifeContribution focusTestBinding ∧
    ¬ actionableQuery codingContribution focusTestBinding :=
  ⟨combined_space_answers_join, life_space_misses_join,
    coding_space_misses_join⟩

/-- Contribution order is irrelevant to the resulting MeTTa space. -/
theorem contribution_order_independent :
    sUnion lifeContribution codingContribution =
      sUnion codingContribution lifeContribution :=
  sUnion_comm _ _

end Mettapedia.CognitiveArchitecture.GodelClaw.AgentMeTTaSpace

#print axioms Mettapedia.CognitiveArchitecture.GodelClaw.AgentMeTTaSpace.addAtom_comm
#print axioms Mettapedia.CognitiveArchitecture.GodelClaw.AgentMeTTaSpace.actionableQuery_eq_meet
#print axioms Mettapedia.CognitiveArchitecture.GodelClaw.AgentMeTTaSpace.one_space_strict_join_gain
#print axioms Mettapedia.CognitiveArchitecture.GodelClaw.AgentMeTTaSpace.contribution_order_independent
