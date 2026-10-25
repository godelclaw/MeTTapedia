import Mettapedia.Logic.FinitaryRuleSystem.ListBranchedDerivation

/-!
# Canaries for list-branched finite replay

The positive example has two differently labelled premises in a fixed order.
The negative examples swap those premises or contract them to one.  Exact
conversion preserves the accepted certificate, while replay rejects both
changes.  Thus neither branch order nor branch multiplicity is silently
quotiented by the list/indexed equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem
namespace ListBranchedDerivationCanary

inductive OrderedPairJudgment where
  | left
  | right
  | joined
deriving DecidableEq

inductive OrderedPairWitness where
  | leftAxiom
  | rightAxiom
  | join
deriving DecidableEq

inductive OrderedPairRule :
    List OrderedPairJudgment → OrderedPairJudgment → Prop where
  | leftAxiom : OrderedPairRule [] .left
  | rightAxiom : OrderedPairRule [] .right
  | join : OrderedPairRule [.left, .right] .joined

def orderedPairIsInstance (witness : OrderedPairWitness)
    (premises : List OrderedPairJudgment)
    (conclusion : OrderedPairJudgment) : Bool :=
  match witness with
  | .leftAxiom => decide (premises = [] ∧ conclusion = .left)
  | .rightAxiom => decide (premises = [] ∧ conclusion = .right)
  | .join => decide (premises = [.left, .right] ∧ conclusion = .joined)

abbrev orderedPairInterface : RuleWitness OrderedPairRule where
  W := OrderedPairWitness
  isInstance := orderedPairIsInstance
  sound witness premises conclusion accepted := by
    cases witness <;> simp only [orderedPairIsInstance, decide_eq_true_eq] at accepted <;>
      obtain ⟨rfl, rfl⟩ := accepted <;> constructor
  complete premises conclusion rule := by
    cases rule with
    | leftAxiom => exact ⟨.leftAxiom, by decide⟩
    | rightAxiom => exact ⟨.rightAxiom, by decide⟩
    | join => exact ⟨.join, by decide⟩

open ListBranchedDerivation

abbrev Certificate := ListBranchedDerivation OrderedPairJudgment orderedPairInterface.W

def leftLeaf : Certificate := .node .left .leftAxiom []

def rightLeaf : Certificate := .node .right .rightAxiom []

/-- Positive control: the authored order and multiplicity are accepted. -/
def orderedTree : Certificate := .node .joined .join [leftLeaf, rightLeaf]

/-- Negative control: exchanging the two premises changes the rule instance. -/
def swappedTree : Certificate := .node .joined .join [rightLeaf, leftLeaf]

/-- Negative control: contraction changes a two-premise rule to one premise. -/
def contractedTree : Certificate := .node .joined .join [leftLeaf]

attribute [local simp] leftLeaf rightLeaf orderedTree swappedTree contractedTree orderedPairIsInstance
attribute [local simp] ListNodeAlgebra.witnessTrace ListNodeAlgebra.witnessTraceAlgebra

theorem orderedTree_accepted : orderedTree.valid orderedPairInterface = true := by
  simp [valid_node orderedPairInterface]

theorem swappedTree_rejected : swappedTree.valid orderedPairInterface = false := by
  simp [valid_node orderedPairInterface]

theorem contractedTree_rejected : contractedTree.valid orderedPairInterface = false := by
  simp [valid_node orderedPairInterface]

theorem orderedTree_has_three_nodes : orderedTree.nodeCount = 3 := by simp

theorem contractedTree_has_two_nodes : contractedTree.nodeCount = 2 := by simp

/-- The nontrivial certificate survives both representation changes exactly. -/
theorem orderedTree_roundtrip :
    ofIndexed (toIndexed orderedTree) = orderedTree :=
  ofIndexed_toIndexed orderedTree

/-- Exact replay agrees after conversion to indexed branching. -/
theorem orderedTree_indexed_accepted :
    (toIndexed orderedTree).valid orderedPairInterface = true :=
  (valid_toIndexed orderedPairInterface orderedTree).trans orderedTree_accepted

/-- The initial fold computes the same root and replay result. -/
theorem orderedTree_replay_is_fold :
    (ListNodeAlgebra.fold
      (ListNodeAlgebra.replayAlgebra orderedPairInterface) orderedTree).down =
      (.joined, true) := by
  rw [ListNodeAlgebra.fold_replay, orderedTree_accepted]
  rfl

/-- Order sensitivity is observable at replay, not merely in raw syntax. -/
theorem order_is_not_quotiented :
    orderedTree.valid orderedPairInterface ≠
      swappedTree.valid orderedPairInterface := by
  simp only [orderedTree_accepted, swappedTree_rejected]; decide

/-- Multiplicity sensitivity is observable at replay. -/
theorem multiplicity_is_not_quotiented :
    orderedTree.valid orderedPairInterface ≠
      contractedTree.valid orderedPairInterface := by
  simp only [orderedTree_accepted, contractedTree_rejected]; decide

/-- Duplicate child occurrences are valid syntax even when this particular rule rejects them. -/
def duplicatedTree : Certificate := .node .joined .join [leftLeaf, leftLeaf]

theorem orderedTree_witnessTrace :
    ListNodeAlgebra.witnessTrace orderedTree = [.join, .leftAxiom, .rightAxiom] := by simp

theorem duplicatedTree_retains_both_occurrences :
    ListNodeAlgebra.witnessTrace duplicatedTree = [.join, .leftAxiom, .leftAxiom] := by simp [duplicatedTree]

theorem swappedTree_changes_trace :
    ListNodeAlgebra.witnessTrace swappedTree ≠ ListNodeAlgebra.witnessTrace orderedTree := by simp

theorem duplicatedTree_roundtrip : ofIndexed (toIndexed duplicatedTree) = duplicatedTree :=
  ofIndexed_toIndexed duplicatedTree

/-- Deduplication fails node compatibility: separate child occurrences can repeat a witness. -/
theorem deduplication_breaks_node_compatibility :
    let A := ListNodeAlgebra.witnessTraceAlgebra (J := OrderedPairJudgment) (W := OrderedPairWitness)
    let children : List A.Carrier := [ULift.up [.leftAxiom], ULift.up [.leftAxiom]]
    (A.node .joined .join children).down.dedup ≠
      (A.node .joined .join (children.map fun trace => ULift.up trace.down.dedup)).down := by decide

end ListBranchedDerivationCanary
end Mettapedia.Logic.FinitaryRuleSystem
