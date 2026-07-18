import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldEightPhysicalTrace
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessExecutable
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitBasis
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartSignCertificate

/-!
# Semantic decoding of the selected standard trace witnesses

The finite payload records only standard labeled trace sectors, literal
hypercubic elements, and simultaneous field relabelings.  This file decodes
those data into the genuine carrier and relates them to the standard
eight-field trace operator without defining a relation by its coordinates.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceWitnessSemantics

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDCharacterCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16TraceOrbitChart
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitBasis
open HypercubicDimension16TraceOrbitExecutableSignature
open HypercubicDimension16TraceRankCertificateData
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceWitnessTypes
open HypercubicDimension16PhysicalTraceWitnessExecutable

/-! ## Proof-bearing decoders -/

/-- A valid fixed-width source code decoded into the standard labeled
eight-field derivative-free carrier. -/
def decodedPhysicalWitnessSource
    (witness : EncodedPhysicalTraceWitness)
    (valid : EncodedRepresentativeValid witness.sourceCode) :
    LabeledLocalWordSector 8 0 :=
  { trace :=
      { toFun := encodedTraceForward witness.sourceCode
        invFun := encodedTraceBackward witness.sourceCode
        left_inv := valid.2.2.2.2.1
        right_inv := valid.2.2.2.2.2 }
    decoration :=
      ⟨fun field =>
        { plane := encodedPlane witness.sourceCode field
          derivativeCount := 0
          derivativeAxis := Fin.elim0 }, by simp⟩ }

@[simp] theorem decodedPhysicalWitnessSource_trace_apply
    (witness : EncodedPhysicalTraceWitness)
    (valid : EncodedRepresentativeValid witness.sourceCode)
    (field : Fin 8) :
    (decodedPhysicalWitnessSource witness valid).trace field =
      encodedTraceForward witness.sourceCode field := by
  rfl

@[simp] theorem decodedPhysicalWitnessSource_plane
    (witness : EncodedPhysicalTraceWitness)
    (valid : EncodedRepresentativeValid witness.sourceCode)
    (field : Fin 8) :
    ((decodedPhysicalWitnessSource witness valid).decoration.1 field).plane =
      encodedPlane witness.sourceCode field := by
  rfl

/-- A checked simultaneous field relabeling. -/
def decodedCoordinateFieldRename
    (coordinate : EncodedOrbitCoordinateWitness)
    (valid : EncodedFieldRenameValid coordinate) : Equiv.Perm (Fin 8) where
  toFun := encodedFieldRenameForward coordinate
  invFun := encodedFieldRenameBackward coordinate
  left_inv := valid.2.2.2.2.1
  right_inv := valid.2.2.2.2.2

@[simp] theorem decodedCoordinateFieldRename_apply
    (coordinate : EncodedOrbitCoordinateWitness)
    (valid : EncodedFieldRenameValid coordinate) (field : Fin 8) :
    decodedCoordinateFieldRename coordinate valid field =
      encodedFieldRenameForward coordinate field := by
  rfl

@[simp] theorem decodedCoordinateFieldRename_symm_apply
    (coordinate : EncodedOrbitCoordinateWitness)
    (valid : EncodedFieldRenameValid coordinate) (field : Fin 8) :
    (decodedCoordinateFieldRename coordinate valid).symm field =
      encodedFieldRenameBackward coordinate field := by
  rfl

/-! ## The six standard terms of a fundamental trace row -/

def encodedFundamentalTraceOrder
    (witness : EncodedPhysicalTraceWitness) (term : Nat)
    (sourceTrace : Equiv.Perm (Fin 8)) : Equiv.Perm (Fin 8) :=
  let first := encodedSiteFirst witness
  let second := encodedSiteSecond witness
  let third := encodedSiteThird witness
  match term with
  | 0 => sourceTrace
  | 1 => sourceTrace.trans (Equiv.swap first second)
  | 2 => sourceTrace.trans (Equiv.swap first third)
  | 3 => sourceTrace.trans (Equiv.swap second third)
  | 4 => sourceTrace.trans
      ((Equiv.swap second third).trans (Equiv.swap first second))
  | _ => sourceTrace.trans
      ((Equiv.swap first second).trans (Equiv.swap second third))

theorem encodedFundamentalTraceOrder_apply
    (witness : EncodedPhysicalTraceWitness) (term : Nat)
    (sourceTrace : Equiv.Perm (Fin 8))
    (hfirstSecond : encodedSiteFirst witness ≠ encodedSiteSecond witness)
    (hfirstThird : encodedSiteFirst witness ≠ encodedSiteThird witness)
    (hsecondThird : encodedSiteSecond witness ≠ encodedSiteThird witness)
    (field : Fin 8) :
    encodedFundamentalTraceOrder witness term sourceTrace field =
      encodedFundamentalRewire witness term (sourceTrace field) := by
  unfold encodedFundamentalTraceOrder encodedFundamentalRewire
  split <;> simp only [Equiv.trans_apply, Equiv.swap_apply_def] <;>
    split_ifs <;> simp_all

/-- The literal source term represented by one coordinate witness. -/
def decodedPhysicalWitnessTerm
    (witness : EncodedPhysicalTraceWitness)
    (valid : EncodedRepresentativeValid witness.sourceCode)
    (term : Nat) : LabeledLocalWordSector 8 0 :=
  let source := decodedPhysicalWitnessSource witness valid
  if witness.kind = 0 then source
  else setFieldEightTraceOrder source
    (encodedFundamentalTraceOrder witness term source.trace)

/-- Kind zero has no distinguished triple; every nonzero kind used by the
semantic decoder carries three distinct encoded labels. -/
abbrev WitnessTraceLabelsValid
    (witness : EncodedPhysicalTraceWitness) : Prop :=
  witness.kind = 0 ∨
    (encodedSiteFirst witness ≠ encodedSiteSecond witness ∧
      encodedSiteFirst witness ≠ encodedSiteThird witness ∧
      encodedSiteSecond witness ≠ encodedSiteThird witness)

@[simp] theorem decodedPhysicalWitnessTerm_plane
    (witness : EncodedPhysicalTraceWitness)
    (valid : EncodedRepresentativeValid witness.sourceCode)
    (term : Nat) (field : Fin 8) :
    ((decodedPhysicalWitnessTerm witness valid term).decoration.1 field).plane =
      encodedPlane witness.sourceCode field := by
  by_cases hkind : witness.kind = 0 <;>
    simp [decodedPhysicalWitnessTerm, setFieldEightTraceOrder, hkind]

theorem decodedPhysicalWitnessTerm_trace_apply
    (witness : EncodedPhysicalTraceWitness)
    (valid : EncodedRepresentativeValid witness.sourceCode)
    (hlabels : WitnessTraceLabelsValid witness)
    (term : Nat) (field : Fin 8) :
    (decodedPhysicalWitnessTerm witness valid term).trace field =
      encodedPhysicalTermTraceForward witness term field := by
  by_cases hkind : witness.kind = 0
  · simp [decodedPhysicalWitnessTerm, encodedPhysicalTermTraceForward,
      hkind]
  · rcases hlabels with hzero | ⟨hfirstSecond, hfirstThird, hsecondThird⟩
    · exact False.elim (hkind hzero)
    · simp [decodedPhysicalWitnessTerm, encodedPhysicalTermTraceForward,
        hkind, setFieldEightTraceOrder,
        encodedFundamentalTraceOrder_apply witness term _ hfirstSecond
          hfirstThird hsecondThird]

/-! ## Each stored coordinate is a standard orbit equality -/

/-- At zero derivative degree, a local field letter is determined by its
oriented plane. -/
theorem localFieldLetter_zero_ext (left right : LocalFieldLetter 0)
    (hplane : left.plane = right.plane) : left = right := by
  rcases left with ⟨leftPlane, leftCount, leftAxis⟩
  rcases right with ⟨rightPlane, rightCount, rightAxis⟩
  dsimp at hplane
  subst rightPlane
  have hleft : leftCount = 0 := Fin.eq_zero leftCount
  have hright : rightCount = 0 := Fin.eq_zero rightCount
  subst leftCount
  subst rightCount
  have haxis : leftAxis = rightAxis := by
    funext position
    exact Fin.elim0 position
  subst rightAxis
  rfl

theorem decodedPhysicalWitnessTerm_relabel_eq
    (witness : EncodedPhysicalTraceWitness)
    (sourceValid : EncodedRepresentativeValid witness.sourceCode)
    (hlabels : WitnessTraceLabelsValid witness)
    (term : Nat) (coordinate : EncodedOrbitCoordinateWitness)
    (coordinateValid :
      EncodedCoordinateOrbitValid witness term coordinate) :
    (decodedPhysicalWitnessTerm witness sourceValid term).relabel
        (decodedCoordinateFieldRename coordinate
          coordinateValid.2.2.2.1) =
      (decodedPositiveRepresentative
        (encodedCoordinateRepresentative coordinate)).hypercubicAct
          (encodedCoordinateHypercubic coordinate) := by
  apply LabeledLocalWordSector.ext
  · apply Equiv.ext
    intro field
    simp only [LabeledLocalWordSector.relabel, Equiv.trans_apply,
      decodedCoordinateFieldRename_apply,
      decodedCoordinateFieldRename_symm_apply,
      decodedPhysicalWitnessTerm_trace_apply witness sourceValid
        hlabels,
      LabeledLocalWordSector.hypercubicAct, decodedPositiveRepresentative]
    change encodedFieldRenameForward coordinate
          (encodedPhysicalTermTraceForward witness term
            (encodedFieldRenameBackward coordinate field)) =
        encodedTraceForward
          (positiveRepresentativeCode
            (encodedCoordinateRepresentative coordinate)) field
    exact coordinateValid.2.2.2.2.1 field
  · apply Subtype.ext
    funext field
    apply localFieldLetter_zero_ext
    · simp only [LabeledLocalWordSector.relabel,
        LocalWordDecoration.relabel,
        LabeledLocalWordSector.hypercubicAct,
        LocalWordDecoration.hypercubicAct,
        LocalFieldLetter.hypercubicAct,
        decodedCoordinateFieldRename_symm_apply,
        decodedPhysicalWitnessTerm_plane,
        decodedPositiveRepresentative]
      change encodedPlane witness.sourceCode
            (encodedFieldRenameBackward coordinate field) =
          planeAction (encodedCoordinateHypercubic coordinate)
            (encodedPlane
              (positiveRepresentativeCode
                (encodedCoordinateRepresentative coordinate)) field)
      exact coordinateValid.2.2.2.2.2 field

theorem decodedPhysicalWitnessTerm_orbit_eq
    (witness : EncodedPhysicalTraceWitness)
    (sourceValid : EncodedRepresentativeValid witness.sourceCode)
    (hlabels : WitnessTraceLabelsValid witness)
    (term : Nat) (coordinate : EncodedOrbitCoordinateWitness)
    (coordinateValid :
      EncodedCoordinateOrbitValid witness term coordinate) :
    (Quotient.mk _
        (decodedPhysicalWitnessTerm witness sourceValid term) :
        FieldEightOrbitCarrier) =
      (positiveRepresentativeTarget
          (encodedCoordinateRepresentative coordinate)).hypercubicAct
        (encodedCoordinateHypercubic coordinate) := by
  have hsector := decodedPhysicalWitnessTerm_relabel_eq witness sourceValid
    hlabels term coordinate coordinateValid
  have hrelation :
      MulAction.orbitRel (Equiv.Perm (Fin 8))
        (LabeledLocalWordSector 8 0)
        ((decodedPositiveRepresentative
          (encodedCoordinateRepresentative coordinate)).hypercubicAct
            (encodedCoordinateHypercubic coordinate))
        (decodedPhysicalWitnessTerm witness sourceValid term) := by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨decodedCoordinateFieldRename coordinate
      coordinateValid.2.2.2.1, hsector⟩
  exact (Quotient.sound hrelation).symm

theorem encodedCoordinateTensorSign_eq_one_or_neg_one
    (coordinate : EncodedOrbitCoordinateWitness) :
    encodedCoordinateTensorSign coordinate = 1 ∨
      encodedCoordinateTensorSign coordinate = -1 := by
  classical
  unfold encodedCoordinateTensorSign
  induction (Finset.univ : Finset (Fin 8)) using Finset.induction_on with
  | empty => simp
  | @insert field remaining hnotmem inductionHypothesis =>
      rw [Finset.prod_insert hnotmem]
      rcases planeTensorSign_eq_one_or_neg_one
          (encodedCoordinateHypercubic coordinate)
          (encodedPlane
            (positiveRepresentativeCode
              (encodedCoordinateRepresentative coordinate)) field) with
        hfield | hfield <;>
      rcases inductionHypothesis with hremaining | hremaining
      · left
        rw [hfield, hremaining]
        norm_num
      · right
        rw [hfield, hremaining]
        norm_num
      · right
        rw [hfield, hremaining]
        norm_num
      · left
        rw [hfield, hremaining]
        norm_num

theorem encodedCoordinateTensorSign_cast
    (coordinate : EncodedOrbitCoordinateWitness) :
    (encodedCoordinateTensorSign coordinate : ℚ) =
      (positiveRepresentativeTarget
        (encodedCoordinateRepresentative coordinate)).tensorSign
          (encodedCoordinateHypercubic coordinate) := by
  rw [← HypercubicDimension16TraceOrbitChartSignCertificate.directRepresentativeTensorSign_eq]
  unfold encodedCoordinateTensorSign directRepresentativeTensorSign
  norm_cast

/-- Reynolds vector attached to an arbitrary genuine field-label orbit. -/
def orbitReynoldsVector (target : FieldEightOrbitCarrier) :
    sectorFieldOrbitInvariantSubmodule 8 0 :=
  ⟨sectorFieldOrbitReynolds 8 0 (Finsupp.single target 1),
    sectorFieldOrbitReynolds_invariant 8 0 _⟩

@[simp] theorem orbitReynoldsVector_positiveRepresentative
    (index : PositiveRepresentativeIndex) :
    orbitReynoldsVector (positiveRepresentativeTarget index) =
      positiveRepresentativeReynoldsVector index := by
  rfl

/-- One coordinate witness identifies the Reynolds class of its literal
physical term with the signed checked chart vector. -/
theorem orbitReynoldsVector_decodedPhysicalWitnessTerm
    (witness : EncodedPhysicalTraceWitness)
    (sourceValid : EncodedRepresentativeValid witness.sourceCode)
    (hlabels : WitnessTraceLabelsValid witness)
    (term : Nat) (coordinate : EncodedOrbitCoordinateWitness)
    (coordinateValid :
      EncodedCoordinateOrbitValid witness term coordinate) :
    orbitReynoldsVector
        (Quotient.mk _
          (decodedPhysicalWitnessTerm witness sourceValid term)) =
      (encodedCoordinateTensorSign coordinate : ℚ) •
        positiveRepresentativeReynoldsVector
          (encodedCoordinateRepresentative coordinate) := by
  let representative :=
    positiveRepresentativeTarget
      (encodedCoordinateRepresentative coordinate)
  let h := encodedCoordinateHypercubic coordinate
  let termOrbit : FieldEightOrbitCarrier :=
    Quotient.mk _ (decodedPhysicalWitnessTerm witness sourceValid term)
  have horbit : termOrbit = representative.hypercubicAct h := by
    exact decodedPhysicalWitnessTerm_orbit_eq witness sourceValid
      hlabels term coordinate coordinateValid
  have haverage := sectorFieldOrbitReynolds_action h
    (Finsupp.single representative 1)
  have haction :
      signedSectorFieldOrbitAction h 8 0
          (Finsupp.single representative 1) =
        representative.tensorSign h • Finsupp.single termOrbit 1 := by
    rw [signedSectorFieldOrbitAction_single, one_mul, horbit]
    simp
  rw [haction, LinearMap.map_smul] at haverage
  have hsign : representative.tensorSign h = 1 ∨
      representative.tensorSign h = -1 := by
    rw [← encodedCoordinateTensorSign_cast]
    exact_mod_cast encodedCoordinateTensorSign_eq_one_or_neg_one coordinate
  apply Subtype.ext
  change sectorFieldOrbitReynolds 8 0 (Finsupp.single termOrbit 1) = _
  rw [encodedCoordinateTensorSign_cast]
  change _ = representative.tensorSign h •
    sectorFieldOrbitReynolds 8 0 (Finsupp.single representative 1)
  rcases hsign with hpositive | hnegative
  · rw [hpositive] at haverage ⊢
    simpa using haverage
  · rw [hnegative] at haverage ⊢
    simpa only [neg_one_smul, neg_neg] using congrArg Neg.neg haverage

/-! ## Coordinate synthesis and literal standard generators -/

/-- Evaluation of a sparse `Finsupp` fold is the corresponding transparent
integer coefficient fold. -/
theorem finsuppSingleFold_apply {α : Type*} (entries : List α)
    (key : α → Nat) (coefficient : α → Int)
    (initial : Nat →₀ Int) (column : Nat) :
    (entries.foldl
        (fun total entry =>
          total + Finsupp.single (key entry) (coefficient entry))
        initial) column =
      entries.foldl
        (fun total entry =>
          if key entry = column then total + coefficient entry else total)
        (initial column) := by
  induction entries generalizing initial with
  | nil => rfl
  | cons entry remaining induction =>
      rw [List.foldl_cons, List.foldl_cons, induction]
      by_cases hkey : key entry = column <;> simp [hkey]

theorem encodedPhysicalWitnessIntegerVector_apply
    (witness : EncodedPhysicalTraceWitness) (column : Nat) :
    encodedPhysicalWitnessIntegerVector witness column =
      encodedPhysicalWitnessIntegerCoefficient witness column := by
  unfold encodedPhysicalWitnessIntegerVector
    encodedPhysicalWitnessIntegerCoefficient
  simpa only [← Array.foldl_toList, Finsupp.zero_apply] using
    (finsuppSingleFold_apply witness.coordinates.toList
      (fun coordinate => coordinate.representative)
      (fun coordinate => coordinate.coefficient *
        encodedCoordinateTensorSign coordinate) 0 column)

theorem encodedSelectedIntegerVector_apply
    (index : Fin 11556) (column : Nat) :
    encodedSelectedIntegerVector index column =
      encodedSelectedIntegerCoefficient index column := by
  unfold encodedSelectedIntegerVector encodedSelectedIntegerCoefficient
  simpa only [← Array.foldl_toList, Finsupp.zero_apply] using
    (finsuppSingleFold_apply
      ((selectedIntegerRow? index.1).getD #[]).toList
      Prod.fst Prod.snd 0 column)

theorem integerKeyFold_eq_initial_of_not_mem {α : Type*}
    (entries : List α) (key : α → Nat) (coefficient : α → Int)
    (column : Nat) (initial : Int)
    (houtside : ∀ entry ∈ entries, key entry ≠ column) :
    entries.foldl
        (fun total entry =>
          if key entry = column then total + coefficient entry else total)
        initial = initial := by
  induction entries generalizing initial with
  | nil => rfl
  | cons entry remaining induction =>
      rw [List.foldl_cons, if_neg (houtside entry (by simp))]
      apply induction
      intro next hmem
      exact houtside next (List.mem_cons_of_mem entry hmem)

/-- The finite point checks on every key appearing in either sparse payload
promote to equality of the semantic `Finsupp` vectors. -/
theorem encodedPhysicalTraceWitnessVectorReplayValid_sound
    (index : Fin 11556)
    (hreplay : encodedPhysicalTraceWitnessVectorReplayValid index) :
    encodedPhysicalWitnessIntegerVector (physicalTraceWitness index) =
      encodedSelectedIntegerVector index := by
  let witness := physicalTraceWitness index
  let selected := (selectedIntegerRow? index.1).getD #[]
  change
    (witness.coordinates.toList.all fun coordinate =>
      decide (encodedPhysicalWitnessIntegerCoefficient witness
          coordinate.representative =
        encodedSelectedIntegerCoefficient index
          coordinate.representative)) = true ∧
      (selected.toList.all fun entry =>
        decide (encodedPhysicalWitnessIntegerCoefficient witness entry.1 =
          encodedSelectedIntegerCoefficient index entry.1)) = true at hreplay
  change encodedPhysicalWitnessIntegerVector witness =
    encodedSelectedIntegerVector index
  apply Finsupp.ext
  intro column
  rw [encodedPhysicalWitnessIntegerVector_apply,
    encodedSelectedIntegerVector_apply]
  rcases hreplay with ⟨hcoordinates, hselected⟩
  have hcoordinateEqual (coordinate : EncodedOrbitCoordinateWitness)
      (hmem : coordinate ∈ witness.coordinates.toList) :
      encodedPhysicalWitnessIntegerCoefficient witness
          coordinate.representative =
        encodedSelectedIntegerCoefficient index
          coordinate.representative := by
    exact of_decide_eq_true
      ((List.all_eq_true.mp hcoordinates) coordinate hmem)
  have hselectedEqual (entry : Nat × Int)
      (hmem : entry ∈ selected.toList) :
      encodedPhysicalWitnessIntegerCoefficient witness entry.1 =
        encodedSelectedIntegerCoefficient index entry.1 := by
    exact of_decide_eq_true
      ((List.all_eq_true.mp hselected) entry hmem)
  by_cases hcoordinate :
      ∃ coordinate ∈ witness.coordinates.toList,
        coordinate.representative = column
  · rcases hcoordinate with ⟨coordinate, hmem, hcolumn⟩
    rw [← hcolumn]
    exact hcoordinateEqual coordinate hmem
  by_cases hentry : ∃ entry ∈ selected.toList, entry.1 = column
  · rcases hentry with ⟨entry, hmem, hcolumn⟩
    rw [← hcolumn]
    exact hselectedEqual entry hmem
  · have hphysicalZero :
        encodedPhysicalWitnessIntegerCoefficient witness column = 0 := by
      unfold encodedPhysicalWitnessIntegerCoefficient
      rw [← Array.foldl_toList]
      apply integerKeyFold_eq_initial_of_not_mem
      intro coordinate hmem hcolumn
      exact hcoordinate ⟨coordinate, hmem, hcolumn⟩
    have hselectedZero :
        encodedSelectedIntegerCoefficient index column = 0 := by
      unfold encodedSelectedIntegerCoefficient
      change selected.foldl
          (fun total entry =>
            if entry.1 = column then total + entry.2 else total) 0 = 0
      rw [← Array.foldl_toList]
      apply integerKeyFold_eq_initial_of_not_mem
      intro entry hmem hcolumn
      exact hentry ⟨entry, hmem, hcolumn⟩
    rw [hphysicalZero, hselectedZero]

/-- Coefficientwise inclusion of an integer sparse vector into rational
coordinates. -/
def integerToRationalFinsupp :
    (Nat →₀ Int) →+ (Nat →₀ ℚ) :=
  Finsupp.mapRange.addMonoidHom (Int.castAddHom ℚ)

/-- Interpret a natural-index sparse vector in the checked Reynolds chart.
Out-of-range natural indices are reduced by `Fin.ofNat`; every use below is
separately certified to lie below `11654`. -/
def rationalChartReynolds (value : Nat →₀ ℚ) :
    sectorFieldOrbitInvariantSubmodule 8 0 :=
  Finsupp.linearCombination ℚ
      (fun column : Nat =>
        positiveRepresentativeReynoldsVector (Fin.ofNat 11654 column))
    value

@[simp] theorem rationalChartReynolds_zero :
    rationalChartReynolds 0 = 0 := by
  simp [rationalChartReynolds]

@[simp] theorem rationalChartReynolds_add
    (left right : Nat →₀ ℚ) :
    rationalChartReynolds (left + right) =
      rationalChartReynolds left + rationalChartReynolds right := by
  unfold rationalChartReynolds
  rw [map_add]

def integerChartReynolds (value : Nat →₀ Int) :
    sectorFieldOrbitInvariantSubmodule 8 0 :=
  rationalChartReynolds (integerToRationalFinsupp value)

@[simp] theorem integerChartReynolds_zero :
    integerChartReynolds 0 = 0 := by
  simp [integerChartReynolds, rationalChartReynolds,
    integerToRationalFinsupp]

@[simp] theorem integerChartReynolds_add
    (left right : Nat →₀ Int) :
    integerChartReynolds (left + right) =
      integerChartReynolds left + integerChartReynolds right := by
  unfold integerChartReynolds rationalChartReynolds
  rw [map_add, map_add]

@[simp] theorem integerChartReynolds_single
    (column : Nat) (coefficient : Int) :
    integerChartReynolds (Finsupp.single column coefficient) =
      (coefficient : ℚ) •
        positiveRepresentativeReynoldsVector (Fin.ofNat 11654 column) := by
  simp [integerChartReynolds, rationalChartReynolds,
    integerToRationalFinsupp]

theorem array_eq_single_getD {α : Type*} (values : Array α)
    (fallback : α) (hsize : values.size = 1) :
    values = #[values.getD 0 fallback] := by
  apply Array.ext
  · simpa using hsize
  · intro index hleft hright
    have hindex : index = 0 := by omega
    subst index
    simpa using (Array.getElem_eq_getD fallback)

theorem array_eq_six_getD {α : Type*} (values : Array α)
    (fallback : α) (hsize : values.size = 6) :
    values = #[values.getD 0 fallback, values.getD 1 fallback,
      values.getD 2 fallback, values.getD 3 fallback,
      values.getD 4 fallback, values.getD 5 fallback] := by
  apply Array.ext
  · simpa using hsize
  · intro index hleft hright
    have hindex : index < 6 := by simpa [hsize] using hleft
    interval_cases index <;>
      simpa using (Array.getElem_eq_getD fallback)

theorem witnessCoordinates_eq_single
    (witness : EncodedPhysicalTraceWitness)
    (hsize : witness.coordinates.size = 1) :
    witness.coordinates = #[coordinateWitness witness 0] := by
  exact array_eq_single_getD witness.coordinates emptyCoordinateWitness hsize

theorem witnessCoordinates_eq_six
    (witness : EncodedPhysicalTraceWitness)
    (hsize : witness.coordinates.size = 6) :
    witness.coordinates = #[coordinateWitness witness 0,
      coordinateWitness witness 1, coordinateWitness witness 2,
      coordinateWitness witness 3, coordinateWitness witness 4,
      coordinateWitness witness 5] := by
  exact array_eq_six_getD witness.coordinates emptyCoordinateWitness hsize

theorem finOfNatEight_ne_of_lt_of_ne {left right : Nat}
    (hleft : left < 8) (hright : right < 8) (hne : left ≠ right) :
    Fin.ofNat 8 left ≠ Fin.ofNat 8 right := by
  intro hequal
  apply hne
  have hvalue := congrArg Fin.val hequal
  simpa [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt hleft,
    Nat.mod_eq_of_lt hright] using hvalue

/-- The singleton site decoded from a valid kind-zero witness. -/
def decodedTracelessGenerator
    (witness : EncodedPhysicalTraceWitness)
    (sourceValid : EncodedRepresentativeValid witness.sourceCode)
    (hfixed : encodedTraceForward witness.sourceCode 0 = 0) :
    FieldEightTraceGenerator :=
  .traceless
    { sector := decodedPhysicalWitnessSource witness sourceValid
      field := 0
      singleton := hfixed }

/-- The three distinct labels decoded from a valid fundamental witness. -/
def decodedFundamentalLabel
    (witness : EncodedPhysicalTraceWitness)
    (hfirst_lt : witness.first < 8)
    (hsecond_lt : witness.second < 8)
    (hthird_lt : witness.third < 8)
    (hfirstSecond : witness.first ≠ witness.second)
    (hfirstThird : witness.first ≠ witness.third)
    (hsecondThird : witness.second ≠ witness.third) : Fin 3 ↪ Fin 8 where
  toFun := ![encodedSiteFirst witness, encodedSiteSecond witness,
    encodedSiteThird witness]
  inj' := by
    intro left right hequal
    fin_cases left <;> fin_cases right
    · rfl
    · exfalso
      apply hfirstSecond
      have hvalue := congrArg Fin.val hequal
      simpa [encodedSiteFirst, encodedSiteSecond, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt hfirst_lt, Nat.mod_eq_of_lt hsecond_lt] using hvalue
    · exfalso
      apply hfirstThird
      have hvalue := congrArg Fin.val hequal
      simpa [encodedSiteFirst, encodedSiteThird, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt hfirst_lt, Nat.mod_eq_of_lt hthird_lt] using hvalue
    · exfalso
      apply hfirstSecond
      have hvalue := congrArg Fin.val hequal.symm
      simpa [encodedSiteFirst, encodedSiteSecond, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt hfirst_lt, Nat.mod_eq_of_lt hsecond_lt] using hvalue
    · rfl
    · exfalso
      apply hsecondThird
      have hvalue := congrArg Fin.val hequal
      simpa [encodedSiteSecond, encodedSiteThird, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt hsecond_lt, Nat.mod_eq_of_lt hthird_lt] using hvalue
    · exfalso
      apply hfirstThird
      have hvalue := congrArg Fin.val hequal.symm
      simpa [encodedSiteFirst, encodedSiteThird, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt hfirst_lt, Nat.mod_eq_of_lt hthird_lt] using hvalue
    · exfalso
      apply hsecondThird
      have hvalue := congrArg Fin.val hequal.symm
      simpa [encodedSiteSecond, encodedSiteThird, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt hsecond_lt, Nat.mod_eq_of_lt hthird_lt] using hvalue
    · rfl

@[simp] theorem decodedFundamentalLabel_zero
    (witness : EncodedPhysicalTraceWitness) (h1 h2 h3 h12 h13 h23) :
    decodedFundamentalLabel witness h1 h2 h3 h12 h13 h23 0 =
      encodedSiteFirst witness := rfl

@[simp] theorem decodedFundamentalLabel_one
    (witness : EncodedPhysicalTraceWitness) (h1 h2 h3 h12 h13 h23) :
    decodedFundamentalLabel witness h1 h2 h3 h12 h13 h23 1 =
      encodedSiteSecond witness := rfl

@[simp] theorem decodedFundamentalLabel_two
    (witness : EncodedPhysicalTraceWitness) (h1 h2 h3 h12 h13 h23) :
    decodedFundamentalLabel witness h1 h2 h3 h12 h13 h23 2 =
      encodedSiteThird witness := rfl

/-- The six-term fundamental generator decoded from a valid kind-two
witness. -/
def decodedFundamentalGenerator
    (witness : EncodedPhysicalTraceWitness)
    (sourceValid : EncodedRepresentativeValid witness.sourceCode)
    (hfirst_lt : witness.first < 8)
    (hsecond_lt : witness.second < 8)
    (hthird_lt : witness.third < 8)
    (hfirstSecond : witness.first ≠ witness.second)
    (hfirstThird : witness.first ≠ witness.third)
    (hsecondThird : witness.second ≠ witness.third) :
    FieldEightTraceGenerator :=
  .fundamental
    { sector := decodedPhysicalWitnessSource witness sourceValid
      label := decodedFundamentalLabel witness hfirst_lt hsecond_lt hthird_lt
        hfirstSecond hfirstThird hsecondThird }

@[simp] theorem fieldEightReynoldsToInvariant_fieldEightOrbitSingle
    (sector : LabeledLocalWordSector 8 0) :
    fieldEightReynoldsToInvariant (fieldEightOrbitSingle sector) =
      orbitReynoldsVector (Quotient.mk _ sector) := by
  rfl

/-- One checked coordinate has exactly the Reynolds meaning asserted by its
integer sparse entry. -/
theorem integerChartReynolds_encodedCoordinateIntegerVector
    (witness : EncodedPhysicalTraceWitness)
    (sourceValid : EncodedRepresentativeValid witness.sourceCode)
    (hlabels : WitnessTraceLabelsValid witness)
    (term : Nat) (coordinate : EncodedOrbitCoordinateWitness)
    (hcoefficient : coordinate.coefficient =
      expectedPhysicalTermCoefficient witness term)
    (coordinateValid :
      EncodedCoordinateOrbitValid witness term coordinate) :
    integerChartReynolds (encodedCoordinateIntegerVector coordinate) =
      (expectedPhysicalTermCoefficient witness term : ℚ) •
        orbitReynoldsVector
          (Quotient.mk _
            (decodedPhysicalWitnessTerm witness sourceValid term)) := by
  rw [orbitReynoldsVector_decodedPhysicalWitnessTerm witness sourceValid
    hlabels term coordinate coordinateValid]
  simp [encodedCoordinateIntegerVector, hcoefficient, smul_smul]

end HypercubicDimension16PhysicalTraceWitnessSemantics
end YangMills
end QuantumTheory
end Mettapedia
