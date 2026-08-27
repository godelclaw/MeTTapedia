import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessData
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChart
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitExecutableSignature
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataRows

/-!
# Transparent replay predicates for selected standard trace rows

Each selected sparse row is reconstructed from a valid labeled eight-field
sector.  Every term carries an explicit standard hypercubic code and an
explicit simultaneous field permutation taking it to a checked chart
representative.  The final predicate also recomputes the signed sparse
coordinate row and compares it with the independent rational-rank payload.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceWitnessExecutable

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDCharacterCensus
open HypercubicDimension16PhysicalTraceWitnessTypes
open HypercubicDimension16PhysicalTraceWitnessData
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitExecutableSignature
open HypercubicDimension16TraceRankCertificateData

def emptyCoordinateWitness : EncodedOrbitCoordinateWitness where
  coefficient := 0
  representative := 0
  permutation := 0
  reflection := 0
  renameForward := #[]
  renameBackward := #[]

def emptyPhysicalTraceWitness : EncodedPhysicalTraceWitness where
  kind := 0
  sourceCode := #[]
  first := 0
  second := 0
  third := 0
  coordinates := #[]

@[reducible] def physicalTraceWitness (index : Fin 11556) :
    EncodedPhysicalTraceWitness :=
  (encodedPhysicalTraceWitness? index.1).getD emptyPhysicalTraceWitness

@[reducible] def coordinateWitness
    (witness : EncodedPhysicalTraceWitness) (term : Nat) :
    EncodedOrbitCoordinateWitness :=
  witness.coordinates.getD term emptyCoordinateWitness

@[reducible] def encodedFieldRenameForward
    (coordinate : EncodedOrbitCoordinateWitness) (field : Fin 8) : Fin 8 :=
  Fin.ofNat 8 (coordinate.renameForward.getD field.1 0)

@[reducible] def encodedFieldRenameBackward
    (coordinate : EncodedOrbitCoordinateWitness) (field : Fin 8) : Fin 8 :=
  Fin.ofNat 8 (coordinate.renameBackward.getD field.1 0)

abbrev EncodedFieldRenameValid
    (coordinate : EncodedOrbitCoordinateWitness) : Prop :=
  coordinate.renameForward.size = 8 ∧
    coordinate.renameBackward.size = 8 ∧
    (∀ field : Fin 8, coordinate.renameForward.getD field.1 0 < 8) ∧
    (∀ field : Fin 8, coordinate.renameBackward.getD field.1 0 < 8) ∧
    (∀ field : Fin 8,
      encodedFieldRenameBackward coordinate
          (encodedFieldRenameForward coordinate field) = field) ∧
    (∀ field : Fin 8,
      encodedFieldRenameForward coordinate
          (encodedFieldRenameBackward coordinate field) = field)

@[reducible] def encodedSiteFirst
    (witness : EncodedPhysicalTraceWitness) : Fin 8 :=
  Fin.ofNat 8 witness.first

@[reducible] def encodedSiteSecond
    (witness : EncodedPhysicalTraceWitness) : Fin 8 :=
  Fin.ofNat 8 witness.second

@[reducible] def encodedSiteThird
    (witness : EncodedPhysicalTraceWitness) : Fin 8 :=
  Fin.ofNat 8 witness.third

/-- The six standard permutations in the fundamental `2 x 2` trace
identity, evaluated without constructing proof-bearing equivalences. -/
@[reducible] def encodedFundamentalRewire
    (witness : EncodedPhysicalTraceWitness) (term : Nat)
    (field : Fin 8) : Fin 8 :=
  let first := encodedSiteFirst witness
  let second := encodedSiteSecond witness
  let third := encodedSiteThird witness
  match term with
  | 0 => field
  | 1 => if field = first then second else if field = second then first else field
  | 2 => if field = first then third else if field = third then first else field
  | 3 => if field = second then third else if field = third then second else field
  | 4 =>
      if field = first then second
      else if field = second then third
      else if field = third then first
      else field
  | _ =>
      if field = first then third
      else if field = second then first
      else if field = third then second
      else field

/-- Forward trace map of one literal term of the selected standard row. -/
@[reducible] def encodedPhysicalTermTraceForward
    (witness : EncodedPhysicalTraceWitness) (term : Nat)
    (field : Fin 8) : Fin 8 :=
  if witness.kind = 0 then encodedTraceForward witness.sourceCode field
  else encodedFundamentalRewire witness term
    (encodedTraceForward witness.sourceCode field)

@[reducible] def encodedCoordinateRepresentative
    (coordinate : EncodedOrbitCoordinateWitness) :
    PositiveRepresentativeIndex :=
  Fin.ofNat 11654 coordinate.representative

@[reducible] def encodedCoordinateHypercubic
    (coordinate : EncodedOrbitCoordinateWitness) : Hypercubic4 :=
  decodedHypercubicCharacterElement
    (Fin.ofNat 24 coordinate.permutation)
    (Fin.ofNat 16 coordinate.reflection)

/-- Direct equality check saying that the raw relation term, after the stored
field relabeling, is the stored chart representative after the stored
literal hypercubic action. -/
abbrev EncodedCoordinateOrbitValid
    (witness : EncodedPhysicalTraceWitness) (term : Nat)
    (coordinate : EncodedOrbitCoordinateWitness) : Prop :=
  coordinate.representative < 11654 ∧
    coordinate.permutation < 24 ∧
    coordinate.reflection < 16 ∧
    EncodedFieldRenameValid coordinate ∧
    (∀ field : Fin 8,
      encodedFieldRenameForward coordinate
          (encodedPhysicalTermTraceForward witness term
            (encodedFieldRenameBackward coordinate field)) =
        encodedTraceForward
          (positiveRepresentativeCode
            (encodedCoordinateRepresentative coordinate)) field) ∧
    (∀ field : Fin 8,
      encodedPlane witness.sourceCode
          (encodedFieldRenameBackward coordinate field) =
        planeAction (encodedCoordinateHypercubic coordinate)
          (encodedPlane
            (positiveRepresentativeCode
              (encodedCoordinateRepresentative coordinate)) field))

@[reducible] def expectedPhysicalTermCoefficient
    (witness : EncodedPhysicalTraceWitness) (term : Nat) : Int :=
  if witness.kind = 0 then 1
  else match term with
    | 0 => 1
    | 1 | 2 | 3 => -1
    | _ => 1

@[reducible] def encodedCoordinateTensorSign
    (coordinate : EncodedOrbitCoordinateWitness) : Int :=
  ∏ field : Fin 8,
    planeTensorSign (encodedCoordinateHypercubic coordinate)
      (encodedPlane
        (positiveRepresentativeCode
          (encodedCoordinateRepresentative coordinate)) field)

@[reducible] def encodedCoordinateIntegerVector
    (coordinate : EncodedOrbitCoordinateWitness) : Nat →₀ Int :=
  Finsupp.single coordinate.representative
    (coordinate.coefficient * encodedCoordinateTensorSign coordinate)

@[reducible] def encodedPhysicalWitnessIntegerVector
    (witness : EncodedPhysicalTraceWitness) : Nat →₀ Int :=
  witness.coordinates.foldl
    (fun total coordinate => total + encodedCoordinateIntegerVector coordinate) 0

@[reducible] def encodedSelectedIntegerVector (index : Fin 11556) :
    Nat →₀ Int :=
  ((selectedIntegerRow? index.1).getD #[]).foldl
    (fun total entry => total + Finsupp.single entry.1 entry.2) 0

/-- Transparent coefficient fold for the witness-side sparse description. -/
@[reducible] def encodedPhysicalWitnessIntegerCoefficient
    (witness : EncodedPhysicalTraceWitness) (column : Nat) : Int :=
  witness.coordinates.foldl
    (fun total coordinate =>
      if coordinate.representative = column then
        total + coordinate.coefficient *
          encodedCoordinateTensorSign coordinate
      else total) 0

/-- Transparent coefficient fold for the independent selected-row payload. -/
@[reducible] def encodedSelectedIntegerCoefficient
    (index : Fin 11556) (column : Nat) : Int :=
  ((selectedIntegerRow? index.1).getD #[]).foldl
    (fun total entry =>
      if entry.1 = column then total + entry.2 else total) 0

/-- Executable pointwise replay on every column appearing in either sparse
description.  A separate structural theorem promotes these finite checks to
equality of the two `Finsupp` vectors. -/
@[reducible] def encodedPhysicalTraceWitnessVectorReplayValid
    (index : Fin 11556) : Prop :=
  let witness := physicalTraceWitness index
  let selected := (selectedIntegerRow? index.1).getD #[]
  (witness.coordinates.toList.all fun coordinate =>
      decide (encodedPhysicalWitnessIntegerCoefficient witness
          coordinate.representative =
        encodedSelectedIntegerCoefficient index coordinate.representative)) = true ∧
    (selected.toList.all fun entry =>
      decide (encodedPhysicalWitnessIntegerCoefficient witness entry.1 =
        encodedSelectedIntegerCoefficient index entry.1)) = true

abbrev EncodedPhysicalTraceWitnessValid (index : Fin 11556) : Prop :=
  let witness := physicalTraceWitness index
  EncodedRepresentativeValid witness.sourceCode ∧
    ((witness.kind = 0 ∧ witness.coordinates.size = 1 ∧
        encodedTraceForward witness.sourceCode 0 = 0) ∨
      (witness.kind = 2 ∧ witness.coordinates.size = 6 ∧
        witness.first < 8 ∧ witness.second < 8 ∧ witness.third < 8 ∧
        witness.first ≠ witness.second ∧ witness.first ≠ witness.third ∧
        witness.second ≠ witness.third)) ∧
    (∀ term : Fin witness.coordinates.size,
      let coordinate := coordinateWitness witness term.1
      coordinate.coefficient = expectedPhysicalTermCoefficient witness term.1 ∧
        EncodedCoordinateOrbitValid witness term.1 coordinate) ∧
    encodedPhysicalTraceWitnessVectorReplayValid index

end HypercubicDimension16PhysicalTraceWitnessExecutable
end YangMills
end QuantumTheory
end Mettapedia
