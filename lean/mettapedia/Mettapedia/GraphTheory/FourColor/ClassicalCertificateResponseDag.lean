import Mettapedia.GraphTheory.FourColor.ClassicalCertificateTraceDag

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateResponseDag

open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceTree

/-- A node of a four-way chromogram dictionary.  A leaf indexes one validated
response value. -/
inductive NodeCode where
  | empty
  | leaf (valueIndex : Nat)
  | node (push skip popSame popOpposite : Nat)
  deriving DecidableEq, Repr

/-- Rank and base-three trace code shared by all chromograms that choose the
same response. -/
structure ValueCode where
  rank : Nat
  wordCode : Nat
  deriving DecidableEq, Repr

/-- Chunked storage keeps table lookup local during kernel reduction. -/
structure Code where
  chunks : Array (Array NodeCode)
  values : Array (Array ValueCode)
  deriving DecidableEq, Repr

def chunkSize : Nat := 192

def nodeAt (code : Code) (index : Nat) : NodeCode :=
  ((code.chunks[index / chunkSize]?).bind fun chunk =>
    chunk[index % chunkSize]?).getD .empty

def valueBound (code : Code) : Nat :=
  code.values.size * chunkSize

def valueAt? (code : Code) (index : Nat) : Option ValueCode :=
  (code.values[index / chunkSize]?).bind fun chunk =>
    chunk[index % chunkSize]?

def child (push skip popSame popOpposite : Nat) :
    ChromogramStep → Nat
  | .push => push
  | .skip => skip
  | .popSame => popSame
  | .popOpposite => popOpposite

/-- Deterministic lookup of the response-value index attached to a
chromogram. -/
def lookup (code : Code) : Nat → Chromogram → Option Nat
  | root, [] =>
      match nodeAt code root with
      | .leaf valueIndex => some valueIndex
      | _ => none
  | root, step :: gram =>
      match nodeAt code root with
      | .node push skip popSame popOpposite =>
          lookup code (child push skip popSame popOpposite step) gram
      | _ => none

def digitSymbol : Nat → TraceSymbol
  | 0 => .red
  | 1 => .blue
  | _ => .purple

def decodeReverse : Nat → Nat → List TraceSymbol
  | 0, _ => []
  | length + 1, wordCode =>
      digitSymbol (wordCode % 3) :: decodeReverse length (wordCode / 3)

@[simp] theorem decodeReverse_length (length wordCode : Nat) :
    (decodeReverse length wordCode).length = length := by
  induction length generalizing wordCode with
  | zero => rfl
  | succ length ih => simp [decodeReverse, ih]

def decodeWord (length wordCode : Nat) : List TraceSymbol :=
  (decodeReverse length wordCode).reverse

@[simp] theorem decodeWord_length (length wordCode : Nat) :
    (decodeWord length wordCode).length = length := by
  simp [decodeWord]

def decodedTraceWord (length wordCode : Nat) : TraceWord length :=
  ⟨decodeWord length wordCode, decodeWord_length length wordCode⟩

end ClassicalCertificateResponseDag

end Mettapedia.GraphTheory.FourColor
