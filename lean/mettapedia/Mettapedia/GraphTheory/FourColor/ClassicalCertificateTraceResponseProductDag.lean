import Mettapedia.GraphTheory.FourColor.ClassicalCertificateTraceResponseProduct

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateTraceResponseProductDag

open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateTraceResponseProduct

variable {length : Nat}

structure NodeCode where
  state : State
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

/-- Check that a stored child list points backward to precisely the expected
successor states. -/
def childrenBoolean (code : Code) (index : Nat) :
    List State → List Nat → Bool
  | [], [] => true
  | expected :: expecteds, child :: children =>
      decide (child < index) &&
        match code.nodeAt? child with
        | some childNode =>
            decide (childNode.state = expected) &&
              childrenBoolean code index expecteds children
        | none => false
  | _, _ => false

def nodeEntryBoolean
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (code : Code) (index : Nat) : Bool :=
  if index < code.nodeCount then
    match code.nodeAt? index with
    | none => false
    | some node =>
        match unfoldState certificate node.state with
        | .inl value => value && decide (node.children = [])
        | .inr expected => childrenBoolean code index expected node.children
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

theorem derivations_of_childrenBoolean_true
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (code : Code) (index : Nat) (expected : List State)
    (children : List Nat)
    (hchildren : childrenBoolean code index expected children = true)
    (prior : ∀ child, child < index → ∀ childNode,
      code.nodeAt? child = some childNode →
        Derivation certificate childNode.state) :
    ∀ state ∈ expected, Derivation certificate state := by
  induction expected generalizing children with
  | nil => simp
  | cons state expected ih =>
      cases children with
      | nil => simp [childrenBoolean] at hchildren
      | cons child children =>
          have hparts : decide (child < index) = true ∧
              (match code.nodeAt? child with
              | some childNode =>
                  decide (childNode.state = state) &&
                    childrenBoolean code index expected children
              | none => false) = true := by
            simpa [childrenBoolean] using hchildren
          cases hchildNode : code.nodeAt? child with
          | none => simp [hchildNode] at hparts
          | some childNode =>
              have hlocal : decide (childNode.state = state) = true ∧
                  childrenBoolean code index expected children = true := by
                simpa [hchildNode] using hparts.2
              have hstate : childNode.state = state :=
                of_decide_eq_true hlocal.1
              have hderivation := prior child
                (of_decide_eq_true hparts.1) childNode hchildNode
              intro requested hrequested
              rcases List.mem_cons.1 hrequested with rfl | htail
              · simpa [hstate] using hderivation
              · exact ih children hlocal.2 requested htail

/-- A checked backward product DAG unfolds to a finite semantic derivation at
every stored node. -/
theorem derivation_of_checker_true
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (code : Code) (hchecker : checker certificate code = true)
    (index : Nat) (hindex : index < code.nodeCount)
    (node : NodeCode) (hnode : code.nodeAt? index = some node) :
    Derivation certificate node.state := by
  induction index using Nat.strong_induction_on generalizing node with
  | h index ih =>
      have hentry := nodeEntryBoolean_of_checker_true certificate code
        hchecker index hindex
      simp only [nodeEntryBoolean, hindex, hnode] at hentry
      cases hunfold : unfoldState certificate node.state with
      | inl value =>
          have hparts : value = true ∧ node.children = [] := by
            simpa [hunfold] using hentry
          exact .result hunfold hparts.1
      | inr expected =>
          have hchildren :
              childrenBoolean code index expected node.children = true := by
            simpa [hunfold] using hentry
          apply Derivation.children hunfold
          apply derivations_of_childrenBoolean_true certificate code index
            expected node.children hchildren
          intro child hchild childNode hchildNode
          exact ih child hchild (Nat.lt_trans hchild hindex) childNode
            hchildNode

theorem evaluate_eq_true_of_checker_true
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (code : Code) (hchecker : checker certificate code = true)
    (index : Nat) (hindex : index < code.nodeCount)
    (node : NodeCode) (hnode : code.nodeAt? index = some node) :
    evaluate certificate node.state = true :=
  (derivation_of_checker_true certificate code hchecker index hindex node
    hnode).evaluate_eq_true

end ClassicalCertificateTraceResponseProductDag

end Mettapedia.GraphTheory.FourColor
