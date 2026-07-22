import Mettapedia.GraphTheory.FourColor.ClassicalCertificateTraceResponseRankSummary

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateTraceResponseRankSummaryDag

open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateTraceResponseRankSummary

variable {length : Nat}

structure NodeCode where
  state : State
  bound : Nat
  children : List Nat
  deriving DecidableEq, Repr

structure Code where
  nodeCount : Nat
  nodeGroups : Array (Array (Array NodeCode))
  layerRoots : List Nat
  deriving DecidableEq, Repr

namespace Code

def nodeChunkSize : Nat := 128
def nodeGroupSize : Nat := 4096
def nodeBlockSize : Nat := 512

def nodeAt? (code : Code) (index : Nat) : Option NodeCode :=
  (code.nodeGroups[index / nodeGroupSize]?).bind fun group =>
    (group[(index % nodeGroupSize) / nodeChunkSize]?).bind fun chunk =>
      chunk[index % nodeChunkSize]?

def nodeBlockCount (code : Code) : Nat :=
  (code.nodeCount + nodeBlockSize - 1) / nodeBlockSize

def layerRoot (code : Code) (layer : Nat) : Nat :=
  code.layerRoots.getD layer 0

end Code

/-- Validate backward child pointers, their exact expected states, and the
maximum of their already-stored bounds. -/
def childrenBound? (code : Code) (index : Nat) :
    List State → List Nat → Option Nat
  | [], [] => some 0
  | expected :: expecteds, child :: children =>
      if child < index then
        match code.nodeAt? child with
        | some childNode =>
            if childNode.state = expected then
              match childrenBound? code index expecteds children with
              | some tailBound => some (max childNode.bound tailBound)
              | none => none
            else none
        | none => none
      else none
  | _, _ => none

def nodeEntryBoolean
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (code : Code) (index : Nat) : Bool :=
  if index < code.nodeCount then
    match code.nodeAt? index with
    | none => false
    | some node =>
        match unfoldState certificate node.state with
        | .inl result =>
            decide (result = some node.bound) && decide (node.children = [])
        | .inr expected =>
            decide (childrenBound? code index expected node.children =
              some node.bound)
  else true

def nodeBlockBoolean
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (code : Code) (block : Nat) : Bool :=
  (List.range Code.nodeBlockSize).all fun offset =>
    nodeEntryBoolean certificate code (block * Code.nodeBlockSize + offset)

def checker
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (code : Code) : Bool :=
  (List.range code.nodeBlockCount).all
    (nodeBlockBoolean certificate code)

theorem nodeEntryBoolean_of_checker_true
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (code : Code) (hchecker : checker certificate code = true)
    (index : Nat) (hindex : index < code.nodeCount) :
    nodeEntryBoolean certificate code index = true := by
  have hblock : index / Code.nodeBlockSize < code.nodeBlockCount := by
    simp only [Code.nodeBlockSize, Code.nodeBlockCount]
    omega
  have hblockValid := (List.all_eq_true.1 hchecker)
    (index / Code.nodeBlockSize) (List.mem_range.2 hblock)
  have hoffset : index % Code.nodeBlockSize < Code.nodeBlockSize :=
    Nat.mod_lt _ (by decide)
  have hentry := (List.all_eq_true.1 hblockValid)
    (index % Code.nodeBlockSize) (List.mem_range.2 hoffset)
  have hindexEq : index / Code.nodeBlockSize * Code.nodeBlockSize +
      index % Code.nodeBlockSize = index := by
    simpa [Nat.mul_comm] using Nat.div_add_mod index Code.nodeBlockSize
  simpa [nodeBlockBoolean, hindexEq] using hentry

theorem combine_evaluate_of_childrenBound_eq_some
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (code : Code) (index : Nat) (expected : List State)
    (children : List Nat) (bound : Nat)
    (hchildren : childrenBound? code index expected children = some bound)
    (prior : ∀ child, child < index → ∀ childNode,
      code.nodeAt? child = some childNode →
        evaluate certificate childNode.state = some childNode.bound) :
    combineSummaries (expected.map (evaluate certificate)) = some bound := by
  induction expected generalizing children bound with
  | nil =>
      cases children with
      | nil => simpa [childrenBound?, combineSummaries] using hchildren
      | cons child children => simp [childrenBound?] at hchildren
  | cons state expected ih =>
      cases children with
      | nil => simp [childrenBound?] at hchildren
      | cons child children =>
          by_cases hchild : child < index
          · cases hchildNode : code.nodeAt? child with
            | none => simp [childrenBound?, hchild, hchildNode] at hchildren
            | some childNode =>
                by_cases hstate : childNode.state = state
                · cases htail : childrenBound? code index expected children with
                  | none =>
                      simp [childrenBound?, hchild, hchildNode, hstate, htail]
                        at hchildren
                  | some tailBound =>
                      have hbound : max childNode.bound tailBound = bound := by
                        have hsome : some (max childNode.bound tailBound) =
                            some bound := by
                          simpa [childrenBound?, hchild, hchildNode, hstate,
                            htail] using hchildren
                        exact Option.some.inj hsome
                      have hhead : evaluate certificate state =
                          some childNode.bound := by
                        simpa [hstate] using
                          prior child hchild childNode hchildNode
                      have htailEvaluate := ih children tailBound htail
                      simpa [combineSummaries, hhead, htailEvaluate, hbound]
                · simp [childrenBound?, hchild, hchildNode, hstate] at hchildren
          · simp [childrenBound?, hchild] at hchildren

/-- Every node of a checked backward summary DAG evaluates to its stored
successful bound. -/
theorem evaluate_eq_some_of_checker_true
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (code : Code) (hchecker : checker certificate code = true)
    (index : Nat) (hindex : index < code.nodeCount)
    (node : NodeCode) (hnode : code.nodeAt? index = some node) :
    evaluate certificate node.state = some node.bound := by
  induction index using Nat.strong_induction_on generalizing node with
  | h index ih =>
      have hentry := nodeEntryBoolean_of_checker_true certificate code
        hchecker index hindex
      simp only [nodeEntryBoolean, hindex, hnode] at hentry
      cases hunfold : unfoldState certificate node.state with
      | inl result =>
          have hparts : result = some node.bound ∧ node.children = [] := by
            simpa [hunfold] using hentry
          rw [evaluate_eq_of_unfoldState_eq_inl certificate node.state result
            hunfold, hparts.1]
      | inr expected =>
          have hchildren : childrenBound? code index expected node.children =
              some node.bound := by
            exact of_decide_eq_true (by simpa [hunfold] using hentry)
          apply evaluate_eq_of_unfoldState_eq_inr certificate node.state
            expected node.bound hunfold
          apply combine_evaluate_of_childrenBound_eq_some certificate code
            index expected node.children node.bound hchildren
          intro child hchild childNode hchildNode
          exact ih child hchild (Nat.lt_trans hchild hindex) childNode
            hchildNode

/-- A checked rank-free summary node validates the original product at every
layer not below its stored bound. -/
theorem productBoolean_eq_true_of_checker_true
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (code : Code) (hchecker : checker certificate code = true)
    (index : Nat) (hindex : index < code.nodeCount)
    (node : NodeCode) (hnode : code.nodeAt? index = some node)
    (layer : Nat) (hbound : node.bound ≤ layer) :
    ClassicalCertificateTraceResponseProduct.productBoolean certificate layer
      node.state.remaining node.state.sourceRoot node.state.responseRoot
        node.state.stack = true := by
  have hsummary := evaluate_eq_some_of_checker_true certificate code hchecker
    index hindex node hnode
  exact productBoolean_eq_true_of_rankSummary_eq_some certificate layer
    node.state.remaining node.state.sourceRoot node.state.responseRoot
      node.state.stack node.bound (by simpa [evaluate] using hsummary) hbound

end ClassicalCertificateTraceResponseRankSummaryDag

end Mettapedia.GraphTheory.FourColor
