import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataRows
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataBasis
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataReplay
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataPartition

/-!
# Sparse exact replay core for the eight-field trace-relation rank witness

The certificate stores integer relation rows, their normalized rational
echelon rows, and the indices of the already-established pivots used in each
reduction. Replay uses explicit numerator-denominator pairs with exact integer
arithmetic; no rank or pivot is accepted as metadata.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankCertificate

open HypercubicDimension16TraceRankCertificateData

abbrev ExactFraction := Int × Int
abbrev ExactSparseRow := List (Nat × ExactFraction)

@[reducible] def fractionZero : ExactFraction := (0, 1)

@[reducible] def fractionOfInt (value : Int) : ExactFraction := (value, 1)

@[reducible] def fractionOfEncoded (numerator : Int)
    (denominator : Nat) : ExactFraction :=
  (numerator, Int.ofNat denominator)

@[reducible] def fractionIsZero (value : ExactFraction) : Bool :=
  decide (value.1 = 0)

@[reducible] def fractionEqual (left right : ExactFraction) : Bool :=
  decide (left.1 * right.2 = right.1 * left.2)

@[reducible] def fractionAdd (left right : ExactFraction) : ExactFraction :=
  (left.1 * right.2 + right.1 * left.2, left.2 * right.2)

@[reducible] def fractionNeg (value : ExactFraction) : ExactFraction :=
  (-value.1, value.2)

@[reducible] def fractionMul (left right : ExactFraction) : ExactFraction :=
  (left.1 * right.1, left.2 * right.2)

@[reducible] def fractionDiv (left right : ExactFraction) : ExactFraction :=
  (left.1 * right.2, left.2 * right.1)

@[reducible] def decodeIntegerSparseRow (row : IntegerSparseRow) : ExactSparseRow :=
  row.toList.map fun entry => (entry.1, fractionOfInt entry.2)

@[reducible] def decodeRationalSparseRow (row : RationalSparseRow) : ExactSparseRow :=
  row.toList.map fun entry =>
    (entry.1, fractionOfEncoded entry.2.1 entry.2.2)

@[reducible] def maxSupportColumn : ExactSparseRow → Option Nat
  | [] => none
  | (column, _) :: remaining =>
      match maxSupportColumn remaining with
      | none => some column
      | some finalColumn => some finalColumn

@[reducible] def coefficientAt (column : Nat) : ExactSparseRow → ExactFraction
  | [] => fractionZero
  | (entryColumn, coefficient) :: remaining =>
      if column = entryColumn then coefficient
      else if column < entryColumn then fractionZero
      else coefficientAt column remaining

@[reducible] def addAt (column : Nat) (delta : ExactFraction) :
    ExactSparseRow → ExactSparseRow
  | [] => if fractionIsZero delta then [] else [(column, delta)]
  | entry :: remaining =>
      if column < entry.1 then
        if fractionIsZero delta then entry :: remaining
        else (column, delta) :: entry :: remaining
      else if entry.1 < column then
        entry :: addAt column delta remaining
      else
        let updated := fractionAdd entry.2 delta
        if fractionIsZero updated then remaining else (column, updated) :: remaining

@[reducible] def subtractScaled (row : ExactSparseRow) (coefficient : ExactFraction)
    (basis : ExactSparseRow) : ExactSparseRow :=
  basis.foldl (fun current entry =>
    addAt entry.1 (fractionNeg (fractionMul coefficient entry.2)) current) row

@[reducible] def normalizeRow (coefficient : ExactFraction)
    (row : ExactSparseRow) : ExactSparseRow :=
  row.map fun entry => (entry.1, fractionDiv entry.2 coefficient)

@[reducible] def exactSparseRowEqual : ExactSparseRow → ExactSparseRow → Bool
  | [], [] => true
  | left :: leftRemaining, right :: rightRemaining =>
      decide (left.1 = right.1) && fractionEqual left.2 right.2 &&
        exactSparseRowEqual leftRemaining rightRemaining
  | _, _ => false

@[reducible] def fractionRegular (value : ExactFraction) : Bool :=
  !decide (value.1 = 0) && !decide (value.2 = 0)

@[reducible] def exactSparseRowWellFormed : ExactSparseRow → Bool
  | [] => true
  | entry :: remaining =>
      fractionRegular entry.2 &&
        match remaining with
        | [] => true
        | next :: _ => decide (entry.1 < next.1) &&
            exactSparseRowWellFormed remaining

@[reducible] def replayReductionStep (rowIndex : Nat)
    (state : Option ExactSparseRow) (basisIndex : Nat) :
    Option ExactSparseRow := do
  if basisIndex < rowIndex then pure () else none
  let current ← state
  let basisData ← normalizedRationalBasisRow? basisIndex
  let pivot ← pivotColumn? basisIndex
  let basis := decodeRationalSparseRow basisData
  if maxSupportColumn current = some pivot then pure () else none
  if maxSupportColumn basis = some pivot then pure () else none
  let coefficient := coefficientAt pivot current
  if !fractionIsZero coefficient then
    pure (subtractScaled current coefficient basis)
  else none

@[reducible] def replaySelectedRow (rowIndex : Nat) : Bool :=
  match selectedIntegerRow? rowIndex,
      normalizedRationalBasisRow? rowIndex,
      rationalReplayStepRow? rowIndex, pivotColumn? rowIndex with
  | some integerData, some expectedData, some steps, some pivot =>
      let integerRow := decodeIntegerSparseRow integerData
      let expectedRow := decodeRationalSparseRow expectedData
      decide (pivot < ambientColumnCount) &&
        decide (columnOwner? pivot = some rowIndex) &&
        exactSparseRowWellFormed integerRow &&
        exactSparseRowWellFormed expectedRow &&
        let reduced := steps.foldl
          (replayReductionStep rowIndex) (some integerRow)
        match reduced with
        | none => false
        | some row =>
            if maxSupportColumn row = some pivot then
              let coefficient := coefficientAt pivot row
              let normalized := normalizeRow coefficient row
              !fractionIsZero coefficient &&
                exactSparseRowWellFormed normalized &&
                exactSparseRowEqual normalized expectedRow
            else false
  | _, _, _, _ => false

@[reducible] def rationalReplayRangeCheck (start count : Nat) : Bool :=
  (List.range count).all fun offset => replaySelectedRow (start + offset)

@[reducible] def freeColumnCheck (freeIndex : Nat) : Bool :=
  match freeColumn? freeIndex with
  | none => false
  | some column =>
      decide (column < ambientColumnCount) &&
        decide (columnOwner? column = some (selectedRowCount + freeIndex))

@[reducible] def freeColumnsCheck : Bool :=
  (List.range 98).all freeColumnCheck

@[reducible] def certificateShapeCheck : Bool :=
  selectedIntegerRowsSizeCheck &&
    normalizedRationalBasisSizeCheck &&
    rationalReplayStepsSizeCheck &&
    pivotColumnsSizeCheck &&
    freeColumnsSizeCheck &&
    selectedRowCount = 45 * 256 + 36 &&
    ambientColumnCount - selectedRowCount = 98 &&
    freeColumnsCheck

end HypercubicDimension16TraceRankCertificate
end YangMills
end QuantumTheory
end Mettapedia
