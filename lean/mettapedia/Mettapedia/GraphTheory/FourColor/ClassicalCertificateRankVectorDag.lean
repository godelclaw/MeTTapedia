import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePackedRankVector
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateRankedKempe

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateRankVectorDag

open ClassicalCertificateKempeClosure
open ClassicalCertificateTraceTree

/-- A hash-consed ternary trace language whose leaves carry packed rank-vector
indices. -/
inductive TraceNodeCode where
  | empty
  | leaf (rankVector : Nat)
  | node (red blue purple : Nat)
  deriving DecidableEq, Repr

structure TraceCode where
  chunks : Array (Array TraceNodeCode)
  deriving DecidableEq, Repr

def traceChunkSize : Nat := 64

def TraceCode.nodeAt (code : TraceCode) (index : Nat) : TraceNodeCode :=
  ((code.chunks[index / traceChunkSize]?).bind fun chunk =>
    chunk[index % traceChunkSize]?).getD .empty

def TraceCode.lookup : Nat → TraceCode → Nat → List TraceSymbol → Option Nat
  | 0, code, root, [] =>
      match code.nodeAt root with
      | .leaf rankVector => some rankVector
      | _ => none
  | 0, _, _, _ :: _ => none
  | _ + 1, _, _, [] => none
  | length + 1, code, root, symbol :: word =>
      match code.nodeAt root with
      | .node red blue purple =>
          let child :=
            match symbol with
            | .red => red
            | .blue => blue
            | .purple => purple
          lookup length code child word
      | _ => none

/-- A hash-consed four-way chromogram language whose leaves carry packed
rank-vector indices. -/
inductive ResponseNodeCode where
  | empty
  | leaf (rankVector : Nat)
  | node (push skip popSame popOpposite : Nat)
  deriving DecidableEq, Repr

structure ResponseCode where
  chunks : Array (Array ResponseNodeCode)
  deriving DecidableEq, Repr

def responseChunkSize : Nat := 192

def ResponseCode.nodeAt (code : ResponseCode) (index : Nat) :
    ResponseNodeCode :=
  ((code.chunks[index / responseChunkSize]?).bind fun chunk =>
    chunk[index % responseChunkSize]?).getD .empty

def ResponseNodeCode.child (push skip popSame popOpposite : Nat) :
    ChromogramStep → Nat
  | .push => push
  | .skip => skip
  | .popSame => popSame
  | .popOpposite => popOpposite

def ResponseCode.child? (code : ResponseCode) :
    Option Nat → ChromogramStep → Option Nat
  | none, _ => none
  | some root, step =>
      match code.nodeAt root with
      | .node push skip popSame popOpposite =>
          some (ResponseNodeCode.child push skip popSame popOpposite step)
      | _ => none

def ResponseCode.lookup : ResponseCode → Nat → Chromogram → Option Nat
  | code, root, [] =>
      match code.nodeAt root with
      | .leaf rankVector => some rankVector
      | _ => none
  | code, root, step :: gram =>
      match code.nodeAt root with
      | .node push skip popSame popOpposite =>
          lookup code
            (ResponseNodeCode.child push skip popSame popOpposite step) gram
      | _ => none

def ResponseCode.lookup? (code : ResponseCode) :
    Option Nat → Chromogram → Option Nat
  | none, _ => none
  | some root, gram => code.lookup root gram

@[simp] theorem ResponseCode.lookup?_cons
    (code : ResponseCode) (root : Option Nat)
    (step : ChromogramStep) (gram : Chromogram) :
    code.lookup? root (step :: gram) =
      code.lookup? (code.child? root step) gram := by
  cases root with
  | none => rfl
  | some root =>
      cases hnode : code.nodeAt root <;>
        simp [ResponseCode.lookup?, ResponseCode.lookup,
          ResponseCode.child?, hnode]

end ClassicalCertificateRankVectorDag

end Mettapedia.GraphTheory.FourColor
