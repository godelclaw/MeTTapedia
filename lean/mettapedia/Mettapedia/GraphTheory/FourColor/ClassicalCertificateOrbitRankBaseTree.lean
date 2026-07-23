import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankTransferClosure
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateExactTraceEnumeration

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankBaseTree

open ClassicalCertificateOrbitRankResponseSearch
open ClassicalCertificateOrbitRankTransferClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateRankVectorDag
open ClassicalCertificateTraceTree

variable {length : Nat}

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

/-- A trace node whose empty language is represented by the canonical empty
constructor. -/
def compactNode (red blue purple : TraceTree) : TraceTree :=
  if red = .empty ∧ blue = .empty ∧ purple = .empty then
    .empty
  else .node red blue purple

@[simp] theorem compactNode_accepts_nil (red blue purple : TraceTree) :
    (compactNode red blue purple).accepts [] = false := by
  cases red <;> cases blue <;> cases purple <;>
    simp [compactNode, TraceTree.accepts]

@[simp] theorem compactNode_accepts_cons (red blue purple : TraceTree)
    (symbol : TraceSymbol) (word : List TraceSymbol) :
    (compactNode red blue purple).accepts (symbol :: word) =
      match symbol with
      | .red => red.accepts word
      | .blue => blue.accepts word
      | .purple => purple.accepts word := by
  cases red <;> cases blue <;> cases purple <;> cases symbol <;>
    simp [compactNode, TraceTree.accepts, TraceTree.child]

/-- Convert the selected leaves of a hash-consed fixed-height trace DAG to an
ordinary semantic trace tree. -/
def selectedTraceTree : (length : Nat) → TraceCode → Nat →
    (Nat → Bool) → TraceTree
  | 0, code, root, select =>
      match code.nodeAt root with
      | .leaf value => if select value then .leaf else .empty
      | _ => .empty
  | length + 1, code, root, select =>
      match code.nodeAt root with
      | .node red blue purple =>
          compactNode
            (selectedTraceTree length code red select)
            (selectedTraceTree length code blue select)
            (selectedTraceTree length code purple select)
      | _ => .empty

theorem selectedTraceTree_accepts_iff
    (code : TraceCode) (root : Nat) (select : Nat → Bool)
    (word : TraceWord length) :
    (selectedTraceTree length code root select).accepts word.toList = true ↔
      ∃ value,
        code.lookup length root word.toList = some value ∧
          select value = true := by
  induction length generalizing root with
  | zero =>
      have hword : word = List.Vector.nil := Subsingleton.elim _ _
      subst word
      cases hnode : code.nodeAt root with
      | empty =>
          simp [selectedTraceTree, TraceCode.lookup, TraceTree.accepts, hnode]
      | leaf value =>
          cases hselect : select value <;>
            simp [selectedTraceTree, TraceCode.lookup, TraceTree.accepts,
              hnode, hselect]
      | node red blue purple =>
          simp [selectedTraceTree, TraceCode.lookup, TraceTree.accepts, hnode]
  | succ length ih =>
      rw [← List.Vector.cons_head_tail word]
      cases hsymbol : word.head <;>
        cases hnode : code.nodeAt root <;>
          simp [selectedTraceTree, TraceCode.lookup, TraceTree.accepts,
            hnode, ih]

/-- The rank-zero representatives for one configuration, viewed as an exact
trace language. -/
def rankZeroTree (table : Table length) (config : Nat) : TraceTree :=
  selectedTraceTree length table.orbitCode table.orbitRoot fun vector =>
    decide (table.ranks.rankAt? vector config = some 0)

theorem rankZeroTree_accepts_iff (table : Table length) (config : Nat)
    (word : TraceWord length) :
    (rankZeroTree table config).accepts word.toList = true ↔
      ∃ vector,
        table.vectorAt? word = some vector ∧
          table.ranks.rankAt? vector config = some 0 := by
  rw [rankZeroTree, selectedTraceTree_accepts_iff]
  simp [Table.vectorAt?]

/-- Structural inclusion of the rank-zero trie in a semantic base trie. -/
def baseTreeCoverageChecker (table : Table length) (config : Nat)
    (baseTree : TraceTree) : Bool :=
  ClassicalCertificateExactTraceEnumeration.TraceTree.subset
    (rankZeroTree table config) baseTree

theorem baseCoverage_of_tree_checker (table : Table length) (config : Nat)
    (baseTree : TraceTree)
    (hchecker : baseTreeCoverageChecker table config baseTree = true) :
    BaseCoverage table config fun word => baseTree.accepts word.toList := by
  intro word vector hlookup hrank
  apply ClassicalCertificateExactTraceEnumeration.TraceTree.accepts_of_subset
    (rankZeroTree table config) baseTree hchecker word.toList
  exact (rankZeroTree_accepts_iff table config word).2
    ⟨vector, hlookup, hrank⟩

end ClassicalCertificateOrbitRankBaseTree

end Mettapedia.GraphTheory.FourColor
