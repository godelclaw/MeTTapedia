import Mettapedia.GraphTheory.FourColor.ClassicalCertificateLayeredKempe

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateTraceDag

open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceTree
open ClassicalCertificateTreeRankedKempe

/-- One node of an externally hash-consed ternary trace DAG. -/
inductive NodeCode where
  | empty
  | leaf
  | node (red blue purple : Nat)
  deriving DecidableEq, Repr

/-- A two-level table permits identical suffix tries, and suffixes shared
between closure layers, to be represented once.  Fixed-size chunks keep
kernel reduction of a lookup local instead of unfolding the entire table. -/
structure Code where
  chunks : Array (Array NodeCode)
  deriving DecidableEq, Repr

def chunkSize : Nat := 64

def nodeAt (code : Code) (index : Nat) : NodeCode :=
  ((code.chunks[index / chunkSize]?).bind fun chunk =>
    chunk[index % chunkSize]?).getD .empty

/-- Materialize an indexed root to exactly the declared trace length.  Bad
indices, wrong-height leaves, and wrong-height nodes decode to the empty
language, so arbitrary external tables remain semantically safe. -/
def materialize : Nat → Code → Nat → TraceTree
  | 0, code, root =>
      match nodeAt code root with
      | NodeCode.leaf => .leaf
      | _ => .empty
  | length + 1, code, root =>
      match nodeAt code root with
      | NodeCode.node red blue purple =>
          .node (materialize length code red)
            (materialize length code blue)
            (materialize length code purple)
      | _ => .empty

/-- Fixed-length membership evaluated directly against the indexed table. -/
def accepts : Nat → Code → Nat → List TraceSymbol → Bool
  | 0, code, root, [] =>
      match nodeAt code root with
      | .leaf => true
      | _ => false
  | 0, _, _, _ :: _ => false
  | _ + 1, _, _, [] => false
  | length + 1, code, root, symbol :: word =>
      match nodeAt code root with
      | .node red blue purple =>
          let child :=
            match symbol with
            | .red => red
            | .blue => blue
            | .purple => purple
          accepts length code child word
      | _ => false

/-- Direct indexed membership agrees with ordinary trace-tree membership. -/
theorem accepts_eq_materialize (length : Nat) (code : Code) (root : Nat)
    (word : List TraceSymbol) :
    accepts length code root word =
      (materialize length code root).accepts word := by
  induction length generalizing root word with
  | zero =>
      cases word with
      | nil =>
          cases hnode : nodeAt code root <;>
            simp [accepts, materialize, TraceTree.accepts, hnode]
      | cons symbol word =>
          cases hnode : nodeAt code root <;>
            simp [accepts, materialize, TraceTree.accepts, hnode]
  | succ length ih =>
      cases word with
      | nil =>
          cases hnode : nodeAt code root <;>
            simp [accepts, materialize, TraceTree.accepts, hnode]
      | cons symbol word =>
          cases hnode : nodeAt code root with
          | empty =>
              simp [accepts, materialize, TraceTree.accepts, hnode]
          | leaf =>
              simp [accepts, materialize, TraceTree.accepts, hnode]
          | node red blue purple =>
              cases symbol <;>
                simp [accepts, materialize, TraceTree.accepts,
                  TraceTree.child, hnode, ih]
/-- Enumerate a root directly from the hash-consed table, without first
expanding shared suffixes into an ordinary tree. -/
def acceptedWords : (length : Nat) → Code → Nat →
    List (TraceWord length)
  | 0, code, root =>
      match nodeAt code root with
      | .leaf => [⟨[], rfl⟩]
      | _ => []
  | length + 1, code, root =>
      match nodeAt code root with
      | .node red blue purple =>
          (acceptedWords length code red).map (prependSymbol .red) ++
            (acceptedWords length code blue).map (prependSymbol .blue) ++
            (acceptedWords length code purple).map (prependSymbol .purple)
      | _ => []

/-- Direct DAG enumeration denotes exactly the same fixed-length language as
materialization. -/
theorem acceptedWords_eq_materialize (length : Nat) (code : Code)
    (root : Nat) :
    acceptedWords length code root =
      ClassicalCertificateTreeRankedKempe.acceptedWords length
        (materialize length code root) := by
  induction length generalizing root with
  | zero =>
      cases hnode : nodeAt code root <;>
        simp [acceptedWords, materialize,
          ClassicalCertificateTreeRankedKempe.acceptedWords, hnode]
  | succ length ih =>
      cases hnode : nodeAt code root with
      | empty =>
          simp [acceptedWords, materialize,
            ClassicalCertificateTreeRankedKempe.acceptedWords, hnode]
      | leaf =>
          simp [acceptedWords, materialize,
            ClassicalCertificateTreeRankedKempe.acceptedWords, hnode]
      | node red blue purple =>
          simp [acceptedWords, materialize,
            ClassicalCertificateTreeRankedKempe.acceptedWords, hnode, ih]

theorem mem_acceptedWords_iff {length : Nat} (code : Code) (root : Nat)
    (word : TraceWord length) :
    word ∈ acceptedWords length code root ↔
      (materialize length code root).accepts word.toList = true := by
  rw [acceptedWords_eq_materialize]
  exact ClassicalCertificateTreeRankedKempe.mem_acceptedWords_iff _ _

theorem mem_acceptedWords_iff_accepts {length : Nat} (code : Code)
    (root : Nat) (word : TraceWord length) :
    word ∈ acceptedWords length code root ↔
      accepts length code root word.toList = true := by
  rw [mem_acceptedWords_iff, accepts_eq_materialize]

end ClassicalCertificateTraceDag

end Mettapedia.GraphTheory.FourColor
