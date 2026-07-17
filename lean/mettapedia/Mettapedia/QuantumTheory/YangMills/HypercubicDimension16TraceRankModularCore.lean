import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateCore
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankModularDataP1000000007
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankModularDataP1000000009

/-!
# Sparse prime-field replay core for the eight-field trace rank

The two modular witnesses store independently computed normalized sparse
bases.  Replay uses the integer relation rows and reduction traces shared with
the exact rational certificate, but performs every coefficient operation
modulo the stated prime.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankModularCertificate

open HypercubicDimension16TraceRankCertificateData
open HypercubicDimension16TraceRankModularData

abbrev ExactModularRow := List (Nat × Nat)

@[reducible] def intResidue (prime : Nat) : Int → Nat
  | .ofNat value => value % prime
  | .negSucc value => (prime - ((value + 1) % prime)) % prime

@[reducible] def decodeIntegerModularRow
    (prime : Nat) (row : IntegerSparseRow) : ExactModularRow :=
  row.toList.map fun entry => (entry.1, intResidue prime entry.2)

@[reducible] def decodeModularSparseRow
    (row : ModularSparseRow) : ExactModularRow :=
  row.toList

@[reducible] def maxModularSupportColumn : ExactModularRow → Option Nat
  | [] => none
  | (column, _) :: remaining =>
      match maxModularSupportColumn remaining with
      | none => some column
      | some finalColumn => some finalColumn

@[reducible] def modularCoefficientAt (column : Nat) :
    ExactModularRow → Nat
  | [] => 0
  | (entryColumn, coefficient) :: remaining =>
      if column = entryColumn then coefficient
      else if column < entryColumn then 0
      else modularCoefficientAt column remaining

@[reducible] def modularAddAt (prime column delta : Nat) :
    ExactModularRow → ExactModularRow
  | [] =>
      let reduced := delta % prime
      if reduced = 0 then [] else [(column, reduced)]
  | entry :: remaining =>
      if column < entry.1 then
        let reduced := delta % prime
        if reduced = 0 then entry :: remaining
        else (column, reduced) :: entry :: remaining
      else if entry.1 < column then
        entry :: modularAddAt prime column delta remaining
      else
        let updated := (entry.2 + delta) % prime
        if updated = 0 then remaining else (column, updated) :: remaining

@[reducible] def modularSubtractScaled (prime : Nat)
    (row : ExactModularRow) (coefficient : Nat)
    (basis : ExactModularRow) : ExactModularRow :=
  basis.foldl (fun current entry =>
    let product := (coefficient * entry.2) % prime
    modularAddAt prime entry.1 ((prime - product) % prime) current) row

@[reducible] def modularSparseRowWellFormed (prime : Nat) :
    ExactModularRow → Bool
  | [] => true
  | entry :: remaining =>
      decide (entry.2 ≠ 0) && decide (entry.2 < prime) &&
        match remaining with
        | [] => true
        | next :: _ => decide (entry.1 < next.1) &&
            modularSparseRowWellFormed prime remaining

@[reducible] def modularSparseRowScalarEqual (prime scalar : Nat) :
    ExactModularRow → ExactModularRow → Bool
  | [], [] => true
  | left :: leftRemaining, right :: rightRemaining =>
      decide (left.1 = right.1) &&
        decide (left.2 = (scalar * right.2) % prime) &&
        modularSparseRowScalarEqual prime scalar leftRemaining rightRemaining
  | _, _ => false

@[reducible] def replayModularReductionStep (prime : Nat)
    (basisRow? : Nat → Option ModularSparseRow) (rowIndex : Nat)
    (state : Option ExactModularRow) (basisIndex : Nat) :
    Option ExactModularRow := do
  if basisIndex < rowIndex then pure () else none
  let current ← state
  let basisData ← basisRow? basisIndex
  let pivot ← pivotColumn? basisIndex
  let basis := decodeModularSparseRow basisData
  if maxModularSupportColumn current = some pivot then pure () else none
  if maxModularSupportColumn basis = some pivot then pure () else none
  let coefficient := modularCoefficientAt pivot current
  if coefficient ≠ 0 then
    pure (modularSubtractScaled prime current coefficient basis)
  else none

@[reducible] def replaySelectedRowModular (prime : Nat)
    (basisRow? : Nat → Option ModularSparseRow)
    (stepRow? : Nat → Option (Array Nat)) (rowIndex : Nat) : Bool :=
  match selectedIntegerRow? rowIndex, basisRow? rowIndex,
      stepRow? rowIndex, pivotColumn? rowIndex with
  | some integerData, some expectedData, some steps, some pivot =>
      let integerRow := decodeIntegerModularRow prime integerData
      let expectedRow := decodeModularSparseRow expectedData
      decide (pivot < ambientColumnCount) &&
        modularSparseRowWellFormed prime expectedRow &&
        match steps.foldl
            (replayModularReductionStep prime basisRow? rowIndex)
            (some integerRow) with
        | none => false
        | some reduced =>
            if maxModularSupportColumn reduced = some pivot then
              let coefficient := modularCoefficientAt pivot reduced
              decide (coefficient ≠ 0) &&
                modularSparseRowScalarEqual prime coefficient reduced expectedRow
            else false
  | _, _, _, _ => false

@[reducible] def modularReplaySelectedRowP1000000007 (rowIndex : Nat) : Bool :=
  replaySelectedRowModular 1000000007
    HypercubicDimension16TraceRankModularDataP1000000007.modularBasisRow?
    HypercubicDimension16TraceRankModularDataP1000000007.modularReplayStepRow?
    rowIndex

@[reducible] def modularReplayRangeCheckP1000000007
    (start count : Nat) : Bool :=
  (List.range count).all fun offset =>
    modularReplaySelectedRowP1000000007 (start + offset)

@[reducible] def modularReplaySelectedRowP1000000009 (rowIndex : Nat) : Bool :=
  replaySelectedRowModular 1000000009
    HypercubicDimension16TraceRankModularDataP1000000009.modularBasisRow?
    HypercubicDimension16TraceRankModularDataP1000000009.modularReplayStepRow?
    rowIndex

@[reducible] def modularReplayRangeCheckP1000000009
    (start count : Nat) : Bool :=
  (List.range count).all fun offset =>
    modularReplaySelectedRowP1000000009 (start + offset)

end HypercubicDimension16TraceRankModularCertificate
end YangMills
end QuantumTheory
end Mettapedia
