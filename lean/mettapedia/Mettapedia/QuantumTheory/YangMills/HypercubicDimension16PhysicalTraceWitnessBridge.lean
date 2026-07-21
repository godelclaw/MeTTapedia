import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessCertificate
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessSemantics
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceFiniteQuotient

/-!
# Selected sparse rows belong to the standard trace submodule

Every selected integer row is decoded as either a literal one-letter
traceless relation or a literal six-term fundamental `2 x 2` trace relation.
The equality is proved after the independently defined Reynolds projection;
the finite sparse payload supplies orbit transports, not new relations.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceWitnessBridge

open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceWitnessTypes
open HypercubicDimension16PhysicalTraceWitnessExecutable
open HypercubicDimension16PhysicalTraceWitnessCertificate
open HypercubicDimension16PhysicalTraceWitnessSemantics
open HypercubicDimension16TraceRankCertificate
open HypercubicDimension16TraceRankCertificateData
open HypercubicDimension16TraceRankSemantics
open HypercubicDimension16TraceRankTheorem
open HypercubicDimension16TraceFiniteQuotient
open HypercubicDimension16TraceOrbitChartCore

theorem integerFoldToRational
    (entries : List (Nat × Int)) (initial : Nat →₀ Int) :
    integerToRationalFinsupp
        (entries.foldl
          (fun total entry => total + Finsupp.single entry.1 entry.2)
          initial) =
      integerToRationalFinsupp initial +
        sparseRowValue
          (entries.map
            (fun entry => (entry.1, fractionOfInt entry.2))) := by
  induction entries generalizing initial with
  | nil => simp
  | cons entry remaining induction =>
      rw [List.foldl_cons, induction]
      simp only [List.map_cons, sparseRowValue_cons,
        fractionValue_ofInt]
      rw [map_add]
      simp [integerToRationalFinsupp]
      module

theorem integerArrayFoldToRational (entries : Array (Nat × Int)) :
    integerToRationalFinsupp
        (entries.foldl
          (fun total entry => total + Finsupp.single entry.1 entry.2) 0) =
      sparseRowValue (decodeIntegerSparseRow entries) := by
  have hfold := integerFoldToRational entries.toList 0
  simpa only [decodeIntegerSparseRow, map_zero, zero_add,
    ← Array.foldl_toList] using hfold

theorem encodedSelectedIntegerVector_toRational
    (index : Fin 11556) :
    integerToRationalFinsupp (encodedSelectedIntegerVector index) =
      selectedRawVector index := by
  let evidence := rowEvidence index
  have hdata :
      (selectedIntegerRow? index.1).getD #[] = evidence.integerData := by
    rw [evidence.integerLookup]
    rfl
  rw [encodedSelectedIntegerVector, hdata, selectedRawVector,
    selectedRawRow]
  exact integerArrayFoldToRational evidence.integerData

theorem integerChartReynolds_selectedIntegerVector
    (index : Fin 11556) :
    integerChartReynolds (encodedSelectedIntegerVector index) =
      rationalChartReynolds (selectedRawVector index) := by
  rw [integerChartReynolds, encodedSelectedIntegerVector_toRational]

theorem witnessTraceLabelsValid_of_payload
    (witness : EncodedPhysicalTraceWitness)
    (hshape :
      (witness.kind = 0 ∧ witness.coordinates.size = 1 ∧
          encodedTraceForward witness.sourceCode 0 = 0) ∨
        (witness.kind = 2 ∧ witness.coordinates.size = 6 ∧
          witness.first < 8 ∧ witness.second < 8 ∧ witness.third < 8 ∧
          witness.first ≠ witness.second ∧
          witness.first ≠ witness.third ∧
          witness.second ≠ witness.third)) :
    WitnessTraceLabelsValid witness := by
  rcases hshape with hzero | hfundamental
  · exact Or.inl hzero.1
  · right
    refine ⟨?_, ?_, ?_⟩
    · exact finOfNatEight_ne_of_lt_of_ne hfundamental.2.2.1
        hfundamental.2.2.2.1 hfundamental.2.2.2.2.2.1
    · exact finOfNatEight_ne_of_lt_of_ne hfundamental.2.2.1
        hfundamental.2.2.2.2.1 hfundamental.2.2.2.2.2.2.1
    · exact finOfNatEight_ne_of_lt_of_ne hfundamental.2.2.2.1
        hfundamental.2.2.2.2.1 hfundamental.2.2.2.2.2.2.2

theorem encodedPhysicalWitnessIntegerVector_eq_single
    (witness : EncodedPhysicalTraceWitness)
    (hsize : witness.coordinates.size = 1) :
    encodedPhysicalWitnessIntegerVector witness =
      encodedCoordinateIntegerVector (coordinateWitness witness 0) := by
  rw [encodedPhysicalWitnessIntegerVector,
    witnessCoordinates_eq_single witness hsize]
  simp

theorem encodedPhysicalWitnessIntegerVector_eq_six
    (witness : EncodedPhysicalTraceWitness)
    (hsize : witness.coordinates.size = 6) :
    encodedPhysicalWitnessIntegerVector witness =
      encodedCoordinateIntegerVector (coordinateWitness witness 0) +
      encodedCoordinateIntegerVector (coordinateWitness witness 1) +
      encodedCoordinateIntegerVector (coordinateWitness witness 2) +
      encodedCoordinateIntegerVector (coordinateWitness witness 3) +
      encodedCoordinateIntegerVector (coordinateWitness witness 4) +
      encodedCoordinateIntegerVector (coordinateWitness witness 5) := by
  rw [encodedPhysicalWitnessIntegerVector,
    witnessCoordinates_eq_six witness hsize]
  rw [← Array.foldl_toList]
  simp

theorem selectedPhysicalTraceRow_reynolds
    (index : Fin 11556) :
    ∃ generator : FieldEightTraceGenerator,
      fieldEightReynoldsToInvariant
          (fieldEightPhysicalTraceRow generator) =
        integerChartReynolds (encodedSelectedIntegerVector index) := by
  let witness := physicalTraceWitness index
  have hvalid : EncodedPhysicalTraceWitnessValid index :=
    physicalTraceWitness_valid index
  change EncodedRepresentativeValid witness.sourceCode ∧ _ at hvalid
  rcases hvalid with ⟨sourceValid, hshape, hterms, hreplay⟩
  have hvector :
      encodedPhysicalWitnessIntegerVector witness =
        encodedSelectedIntegerVector index :=
    encodedPhysicalTraceWitnessVectorReplayValid_sound index hreplay
  have hlabels : WitnessTraceLabelsValid witness :=
    witnessTraceLabelsValid_of_payload witness hshape
  rw [← hvector]
  rcases hshape with hzero | hfundamental
  · rcases hzero with ⟨hkind, hsize, hfixed⟩
    have hkind' : witness.kind = 0 := hkind
    have hsize' : witness.coordinates.size = 1 := hsize
    have hzero_lt : 0 < witness.coordinates.size := by
      rw [hsize']
      decide
    let term0 : Fin witness.coordinates.size := ⟨0, hzero_lt⟩
    have hterm0 := hterms term0
    change (coordinateWitness witness 0).coefficient =
          expectedPhysicalTermCoefficient witness 0 ∧
        EncodedCoordinateOrbitValid witness 0
          (coordinateWitness witness 0) at hterm0
    have hcoordinate :=
      integerChartReynolds_encodedCoordinateIntegerVector witness sourceValid
        hlabels 0 (coordinateWitness witness 0) hterm0.1 hterm0.2
    refine ⟨decodedTracelessGenerator witness sourceValid hfixed, ?_⟩
    rw [encodedPhysicalWitnessIntegerVector_eq_single witness hsize',
      hcoordinate]
    simp [decodedTracelessGenerator, fieldEightPhysicalTraceRow,
      decodedPhysicalWitnessTerm, hkind',
      expectedPhysicalTermCoefficient]
  · rcases hfundamental with
      ⟨hkind, hsize, hfirst_lt, hsecond_lt, hthird_lt,
        hfirstSecond, hfirstThird, hsecondThird⟩
    have hkind' : witness.kind = 2 := hkind
    have hsize' : witness.coordinates.size = 6 := hsize
    have hterm (term : Fin 6) :
        (coordinateWitness witness term.1).coefficient =
            expectedPhysicalTermCoefficient witness term.1 ∧
          EncodedCoordinateOrbitValid witness term.1
            (coordinateWitness witness term.1) := by
      have hterm_lt : term.1 < witness.coordinates.size := by
        rw [hsize']
        exact term.isLt
      let payloadTerm : Fin witness.coordinates.size :=
        ⟨term.1, hterm_lt⟩
      simpa [payloadTerm] using hterms payloadTerm
    have hcoordinate (term : Fin 6) :=
      integerChartReynolds_encodedCoordinateIntegerVector witness sourceValid
        hlabels term.1 (coordinateWitness witness term.1)
          (hterm term).1 (hterm term).2
    let generator := decodedFundamentalGenerator witness sourceValid
      hfirst_lt hsecond_lt hthird_lt hfirstSecond hfirstThird hsecondThird
    refine ⟨generator, ?_⟩
    have hcoordinateNat (term : Nat) (hterm_lt : term < 6) :
        integerChartReynolds
            (encodedCoordinateIntegerVector (coordinateWitness witness term)) =
          (expectedPhysicalTermCoefficient witness term : ℚ) •
            orbitReynoldsVector
              (Quotient.mk _
                (decodedPhysicalWitnessTerm witness sourceValid term)) := by
      simpa using hcoordinate ⟨term, hterm_lt⟩
    rw [encodedPhysicalWitnessIntegerVector_eq_six witness hsize']
    simp only [integerChartReynolds_add]
    rw [hcoordinateNat 0 (by decide), hcoordinateNat 1 (by decide),
      hcoordinateNat 2 (by decide), hcoordinateNat 3 (by decide),
      hcoordinateNat 4 (by decide), hcoordinateNat 5 (by decide)]
    norm_num [expectedPhysicalTermCoefficient, hkind']
    have hphysical :
        fieldEightPhysicalTraceRow generator =
          fieldEightOrbitSingle
              (decodedPhysicalWitnessTerm witness sourceValid 0) -
            fieldEightOrbitSingle
              (decodedPhysicalWitnessTerm witness sourceValid 1) -
            fieldEightOrbitSingle
              (decodedPhysicalWitnessTerm witness sourceValid 2) -
            fieldEightOrbitSingle
              (decodedPhysicalWitnessTerm witness sourceValid 3) +
            fieldEightOrbitSingle
              (decodedPhysicalWitnessTerm witness sourceValid 4) +
            fieldEightOrbitSingle
              (decodedPhysicalWitnessTerm witness sourceValid 5) := by
      simp [generator, decodedFundamentalGenerator,
        fieldEightPhysicalTraceRow, decodedPhysicalWitnessTerm, hkind',
        encodedFundamentalTraceOrder, fieldEightFundamentalCycleForward,
        fieldEightFundamentalCycleBackward]
    rw [hphysical]
    simp only [map_add, map_sub,
      fieldEightReynoldsToInvariant_fieldEightOrbitSingle]
    module

end HypercubicDimension16PhysicalTraceWitnessBridge
end YangMills
end QuantumTheory
end Mettapedia
