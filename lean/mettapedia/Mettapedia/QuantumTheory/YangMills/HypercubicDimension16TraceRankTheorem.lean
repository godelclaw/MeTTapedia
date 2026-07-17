import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificate
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankSemantics
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Rational rank theorem for the sparse trace-relation certificate

The chunked computational replay is lifted here to uniform semantic evidence
and then to a linear-independence theorem in the rational coordinate module.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankTheorem

open HypercubicDimension16TraceRankCertificate
open HypercubicDimension16TraceRankCertificateData
open HypercubicDimension16TraceRankSemantics

theorem replaySelectedRow_of_range {start count offset : Nat}
    (hcheck : rationalReplayRangeCheck start count = true)
    (hoffset : offset < count) :
    replaySelectedRow (start + offset) = true := by
  apply List.all_eq_true.mp hcheck
  exact List.mem_range.mpr hoffset

theorem replaySelectedRow_certificate {rowIndex : Nat}
    (hrowIndex : rowIndex < selectedRowCount) :
    replaySelectedRow rowIndex = true := by
  norm_num [selectedRowCount] at hrowIndex
  let chunk := rowIndex / 256
  have hchunk : chunk ≤ 45 := by
    dsimp [chunk]
    omega
  have hdecomposition :
      256 * chunk + rowIndex % 256 = rowIndex := by
    simpa [chunk] using Nat.div_add_mod rowIndex 256
  interval_cases chunk
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_000 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_001 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_002 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_003 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_004 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_005 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_006 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_007 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_008 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_009 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_010 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_011 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_012 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_013 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_014 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_015 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_016 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_017 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_018 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_019 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_020 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_021 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_022 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_023 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_024 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_025 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_026 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_027 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_028 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_029 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_030 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_031 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_032 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_033 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_034 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_035 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_036 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_037 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_038 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_039 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_040 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_041 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_042 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_043 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_044 (by omega)
  · rw [← hdecomposition]
    exact replaySelectedRow_of_range rationalReplayRangeCheck_045 (by omega)

structure ReplayEvidence (rowIndex : Nat) where
  integerData : IntegerSparseRow
  expectedData : RationalSparseRow
  steps : Array Nat
  pivot : Nat
  reduced : ExactSparseRow
  integerLookup : selectedIntegerRow? rowIndex = some integerData
  expectedLookup : normalizedRationalBasisRow? rowIndex = some expectedData
  stepsLookup : rationalReplayStepRow? rowIndex = some steps
  pivotLookup : pivotColumn? rowIndex = some pivot
  pivot_lt : pivot < ambientColumnCount
  pivotOwner : columnOwner? pivot = some rowIndex
  integerWellFormed :
    exactSparseRowWellFormed (decodeIntegerSparseRow integerData) = true
  expectedWellFormed :
    exactSparseRowWellFormed (decodeRationalSparseRow expectedData) = true
  reductionReplay :
    steps.foldl (replayReductionStep rowIndex)
      (some (decodeIntegerSparseRow integerData)) = some reduced
  reducedMaxSupport : maxSupportColumn reduced = some pivot
  pivotCoefficientNonzero :
    fractionIsZero (coefficientAt pivot reduced) = false
  normalizedWellFormed :
    exactSparseRowWellFormed
      (normalizeRow (coefficientAt pivot reduced) reduced) = true
  normalizedEqual :
    exactSparseRowEqual
      (normalizeRow (coefficientAt pivot reduced) reduced)
      (decodeRationalSparseRow expectedData) = true

theorem replaySelectedRow_evidence {rowIndex : Nat}
    (hcheck : replaySelectedRow rowIndex = true) :
    Nonempty (ReplayEvidence rowIndex) := by
  unfold replaySelectedRow at hcheck
  generalize hinteger : selectedIntegerRow? rowIndex = integerOption at hcheck
  generalize hexpected :
    normalizedRationalBasisRow? rowIndex = expectedOption at hcheck
  generalize hsteps : rationalReplayStepRow? rowIndex = stepsOption at hcheck
  generalize hpivot : pivotColumn? rowIndex = pivotOption at hcheck
  cases integerOption with
  | none => simp at hcheck
  | some integerData =>
      cases expectedOption with
      | none => simp at hcheck
      | some expectedData =>
          cases stepsOption with
          | none => simp at hcheck
          | some steps =>
              cases pivotOption with
              | none => simp at hcheck
              | some pivot =>
                  simp only at hcheck
                  generalize hreduced :
                    steps.foldl (replayReductionStep rowIndex)
                      (some (decodeIntegerSparseRow integerData)) =
                        reducedOption at hcheck
                  cases reducedOption with
                  | none =>
                      simp at hcheck
                  | some reduced =>
                      by_cases hmax : maxSupportColumn reduced = some pivot
                      · have hparts :
                            pivot < ambientColumnCount ∧
                            columnOwner? pivot = some rowIndex ∧
                            exactSparseRowWellFormed
                              (decodeIntegerSparseRow integerData) = true ∧
                            exactSparseRowWellFormed
                              (decodeRationalSparseRow expectedData) = true ∧
                            (coefficientAt pivot reduced).1 ≠ 0 ∧
                            exactSparseRowWellFormed
                              (normalizeRow (coefficientAt pivot reduced) reduced) = true ∧
                            exactSparseRowEqual
                              (normalizeRow (coefficientAt pivot reduced) reduced)
                              (decodeRationalSparseRow expectedData) = true := by
                          simpa [hmax, and_assoc] using hcheck
                        have hcoefficientNonzero :
                            fractionIsZero (coefficientAt pivot reduced) = false := by
                          simpa [fractionIsZero] using hparts.2.2.2.2.1
                        exact ⟨⟨integerData, expectedData, steps, pivot, reduced,
                          hinteger, hexpected, hsteps, hpivot,
                          hparts.1, hparts.2.1, hparts.2.2.1,
                          hparts.2.2.2.1, hreduced, hmax,
                          hcoefficientNonzero, hparts.2.2.2.2.2.1,
                          hparts.2.2.2.2.2.2⟩⟩
                      · simp [hmax] at hcheck

def rowEvidence (rowIndex : Fin selectedRowCount) :
    ReplayEvidence (rowIndex : Nat) :=
  Classical.choice <| replaySelectedRow_evidence <|
    replaySelectedRow_certificate rowIndex.isLt

def selectedRawRow (rowIndex : Fin selectedRowCount) : ExactSparseRow :=
  decodeIntegerSparseRow (rowEvidence rowIndex).integerData

def normalizedBasisRow (rowIndex : Fin selectedRowCount) : ExactSparseRow :=
  decodeRationalSparseRow (rowEvidence rowIndex).expectedData

def selectedRawVector (rowIndex : Fin selectedRowCount) : Nat →₀ ℚ :=
  sparseRowValue (selectedRawRow rowIndex)

def normalizedBasisVector (rowIndex : Fin selectedRowCount) : Nat →₀ ℚ :=
  sparseRowValue (normalizedBasisRow rowIndex)

def certifiedPivot (rowIndex : Fin selectedRowCount) : Nat :=
  (rowEvidence rowIndex).pivot

theorem normalizedBasisRow_wellFormed (rowIndex : Fin selectedRowCount) :
    exactSparseRowWellFormed (normalizedBasisRow rowIndex) = true :=
  (rowEvidence rowIndex).expectedWellFormed

theorem normalizedBasisRow_maxSupport (rowIndex : Fin selectedRowCount) :
    maxSupportColumn (normalizedBasisRow rowIndex) =
      some (certifiedPivot rowIndex) := by
  have hmax := exactSparseRowEqual_maxSupport
    (rowEvidence rowIndex).normalizedEqual
  rw [maxSupportColumn_normalize,
    (rowEvidence rowIndex).reducedMaxSupport] at hmax
  exact hmax.symm

theorem certifiedPivot_injective : Function.Injective certifiedPivot := by
  intro left right hpivot
  apply Fin.ext
  have hpivot' :
      (rowEvidence left).pivot = (rowEvidence right).pivot := by
    simpa [certifiedPivot] using hpivot
  have howner :
      some (left : Nat) = some (right : Nat) := by
    rw [← (rowEvidence left).pivotOwner, hpivot',
      (rowEvidence right).pivotOwner]
  exact Option.some.inj howner

theorem normalizedBasisVector_pivot_ne_zero
    (rowIndex : Fin selectedRowCount) :
    normalizedBasisVector rowIndex (certifiedPivot rowIndex) ≠ 0 := by
  rcases exactSparseRowWellFormed_sound
      (normalizedBasisRow_wellFormed rowIndex) with
    ⟨hvalid, hstrict, hnumerator⟩
  exact sparseRowValue_apply_max_ne_zero hstrict hvalid hnumerator
    (normalizedBasisRow_maxSupport rowIndex)

theorem normalizedBasisVector_above_pivot
    (rowIndex : Fin selectedRowCount) (column : Nat)
    (habove : certifiedPivot rowIndex < column) :
    normalizedBasisVector rowIndex column = 0 := by
  rcases exactSparseRowWellFormed_sound
      (normalizedBasisRow_wellFormed rowIndex) with
    ⟨_, hstrict, _⟩
  exact sparseRowValue_apply_eq_zero_above_max hstrict
    (normalizedBasisRow_maxSupport rowIndex) habove

theorem normalizedBasisVector_linearIndependent :
    LinearIndependent ℚ normalizedBasisVector :=
  linearIndependent_of_distinct_maxSupport certifiedPivot_injective
    normalizedBasisVector_pivot_ne_zero normalizedBasisVector_above_pivot

structure ReductionStepEvidence (rowIndex basisIndex : Nat)
    (current next : ExactSparseRow) where
  basisData : RationalSparseRow
  pivot : Nat
  basis_lt : basisIndex < rowIndex
  basisLookup : normalizedRationalBasisRow? basisIndex = some basisData
  pivotLookup : pivotColumn? basisIndex = some pivot
  currentMaxSupport : maxSupportColumn current = some pivot
  basisMaxSupport :
    maxSupportColumn (decodeRationalSparseRow basisData) = some pivot
  coefficientNonzero :
    fractionIsZero (coefficientAt pivot current) = false
  next_eq : next = subtractScaled current (coefficientAt pivot current)
    (decodeRationalSparseRow basisData)

theorem replayReductionStep_evidence {rowIndex basisIndex : Nat}
    {current next : ExactSparseRow}
    (hstep : replayReductionStep rowIndex (some current) basisIndex = some next) :
    Nonempty (ReductionStepEvidence rowIndex basisIndex current next) := by
  unfold replayReductionStep at hstep
  generalize hbasis :
    normalizedRationalBasisRow? basisIndex = basisOption at hstep
  generalize hpivot : pivotColumn? basisIndex = pivotOption at hstep
  by_cases hlt : basisIndex < rowIndex
  · cases basisOption with
    | none => simp [hlt] at hstep
    | some basisData =>
        cases pivotOption with
        | none => simp [hlt] at hstep
        | some pivot =>
            let basis := decodeRationalSparseRow basisData
            by_cases hcurrentMax : maxSupportColumn current = some pivot
            · by_cases hbasisMax : maxSupportColumn basis = some pivot
              · by_cases hcoefficient :
                    fractionIsZero (coefficientAt pivot current) = false
                · have hnext :
                      subtractScaled current (coefficientAt pivot current) basis =
                        next := by
                    have hparts :
                        (coefficientAt pivot current).1 ≠ 0 ∧
                        subtractScaled current (coefficientAt pivot current) basis =
                          next := by
                      simpa [hlt, hcurrentMax, hbasisMax, hcoefficient, basis]
                        using hstep
                    exact hparts.2
                  exact ⟨⟨basisData, pivot, hlt, hbasis, hpivot,
                    hcurrentMax, hbasisMax, hcoefficient, hnext.symm⟩⟩
                · have hzero :
                      fractionIsZero (coefficientAt pivot current) = true := by
                    cases hvalue : fractionIsZero (coefficientAt pivot current) <;>
                      simp_all
                  have hparts :
                      (coefficientAt pivot current).1 ≠ 0 ∧
                      subtractScaled current (coefficientAt pivot current) basis =
                        next := by
                    simpa [hlt, hcurrentMax, hbasisMax, basis] using hstep
                  exact (hparts.1
                    ((fractionIsZero_eq_true_iff _).mp hzero)).elim
              · simp [hlt, hbasisMax, basis] at hstep
            · simp [hlt, hcurrentMax] at hstep
  · simp [hlt] at hstep

def selectedRawSpan : Submodule ℚ (Nat →₀ ℚ) :=
  Submodule.span ℚ (Set.range selectedRawVector)

theorem selectedRawVector_mem_span (rowIndex : Fin selectedRowCount) :
    selectedRawVector rowIndex ∈ selectedRawSpan :=
  Submodule.subset_span ⟨rowIndex, rfl⟩

theorem replayReductionStep_preserves_rawSpan
    (rowIndex : Fin selectedRowCount) {basisIndex : Nat}
    {current next : ExactSparseRow}
    (hstep : replayReductionStep (rowIndex : Nat) (some current) basisIndex =
      some next)
    (hcurrentValid : SparseRowValid current)
    (hcurrentMem : sparseRowValue current ∈ selectedRawSpan)
    (hprevious : ∀ previous : Fin selectedRowCount,
      (previous : Nat) < (rowIndex : Nat) →
        normalizedBasisVector previous ∈ selectedRawSpan) :
    SparseRowValid next ∧ sparseRowValue next ∈ selectedRawSpan := by
  let evidence := Classical.choice (replayReductionStep_evidence hstep)
  let previous : Fin selectedRowCount :=
    ⟨basisIndex, lt_trans evidence.basis_lt rowIndex.isLt⟩
  have hdata :
      evidence.basisData = (rowEvidence previous).expectedData := by
    apply Option.some.inj
    rw [← evidence.basisLookup,
      (rowEvidence previous).expectedLookup]
  have hbasisRow :
      decodeRationalSparseRow evidence.basisData =
        normalizedBasisRow previous := by
    simp [normalizedBasisRow, hdata]
  have hbasisValid :
      SparseRowValid (decodeRationalSparseRow evidence.basisData) := by
    rw [hbasisRow]
    exact (exactSparseRowWellFormed_sound
      (normalizedBasisRow_wellFormed previous)).1
  have hbasisMem :
      sparseRowValue (decodeRationalSparseRow evidence.basisData) ∈
        selectedRawSpan := by
    rw [hbasisRow]
    exact hprevious previous evidence.basis_lt
  have hcoefficientValid :
      FractionValid (coefficientAt evidence.pivot current) :=
    fractionValid_coefficientAt hcurrentValid evidence.pivot
  constructor
  · rw [evidence.next_eq]
    exact sparseRowValid_subtractScaled hcurrentValid hcoefficientValid hbasisValid
  · rw [evidence.next_eq,
      sparseRowValue_subtractScaled hcurrentValid hcoefficientValid hbasisValid]
    exact selectedRawSpan.sub_mem hcurrentMem
      (selectedRawSpan.smul_mem (fractionValue (coefficientAt evidence.pivot current))
        hbasisMem)

@[simp] theorem replayReductionStep_none (rowIndex basisIndex : Nat) :
    replayReductionStep rowIndex none basisIndex = none := by
  simp [replayReductionStep]

theorem replayReductionStepsList_none (rowIndex : Nat) :
    ∀ steps : List Nat,
      steps.foldl (replayReductionStep rowIndex) none = none
  | [] => rfl
  | basisIndex :: remaining => by
      simp only [List.foldl_cons, replayReductionStep_none]
      exact replayReductionStepsList_none rowIndex remaining

theorem replayReductionStepsList_preserves_rawSpan
    (rowIndex : Fin selectedRowCount) :
    ∀ {steps : List Nat} {initial final : ExactSparseRow},
      steps.foldl (replayReductionStep (rowIndex : Nat)) (some initial) =
        some final →
      SparseRowValid initial →
      sparseRowValue initial ∈ selectedRawSpan →
      (∀ previous : Fin selectedRowCount,
        (previous : Nat) < (rowIndex : Nat) →
          normalizedBasisVector previous ∈ selectedRawSpan) →
      SparseRowValid final ∧ sparseRowValue final ∈ selectedRawSpan
  | [], initial, final, hfold, hinitialValid, hinitialMem, _ => by
      simp only [List.foldl_nil, Option.some.injEq] at hfold
      subst final
      exact ⟨hinitialValid, hinitialMem⟩
  | basisIndex :: remaining, initial, final, hfold,
      hinitialValid, hinitialMem, hprevious => by
      simp only [List.foldl_cons] at hfold
      generalize hfirst :
        replayReductionStep (rowIndex : Nat) (some initial) basisIndex =
          firstOption at hfold
      cases firstOption with
      | none =>
          rw [replayReductionStepsList_none] at hfold
          simp at hfold
      | some intermediate =>
          rcases replayReductionStep_preserves_rawSpan rowIndex hfirst
              hinitialValid hinitialMem hprevious with
            ⟨hintermediateValid, hintermediateMem⟩
          exact replayReductionStepsList_preserves_rawSpan rowIndex hfold
            hintermediateValid hintermediateMem hprevious

theorem replayReductionSteps_preserves_rawSpan
    (rowIndex : Fin selectedRowCount) {steps : Array Nat}
    {initial final : ExactSparseRow}
    (hfold : steps.foldl (replayReductionStep (rowIndex : Nat)) (some initial) =
      some final)
    (hinitialValid : SparseRowValid initial)
    (hinitialMem : sparseRowValue initial ∈ selectedRawSpan)
    (hprevious : ∀ previous : Fin selectedRowCount,
      (previous : Nat) < (rowIndex : Nat) →
        normalizedBasisVector previous ∈ selectedRawSpan) :
    SparseRowValid final ∧ sparseRowValue final ∈ selectedRawSpan := by
  have hfoldList :
      steps.toList.foldl (replayReductionStep (rowIndex : Nat)) (some initial) =
        some final := by
    simpa only [← Array.foldl_toList] using hfold
  exact replayReductionStepsList_preserves_rawSpan rowIndex hfoldList
    hinitialValid hinitialMem hprevious

theorem normalizedBasisVector_mem_selectedRawSpan
    (rowIndex : Fin selectedRowCount) :
    normalizedBasisVector rowIndex ∈ selectedRawSpan := by
  have hall : ∀ n (hn : n < selectedRowCount),
      normalizedBasisVector ⟨n, hn⟩ ∈ selectedRawSpan := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n inductionHypothesis =>
        intro hn
        let current : Fin selectedRowCount := ⟨n, hn⟩
        let evidence := rowEvidence current
        have hinitialValid : SparseRowValid (selectedRawRow current) := by
          simpa [selectedRawRow, evidence] using
            (exactSparseRowWellFormed_sound evidence.integerWellFormed).1
        have hprevious : ∀ previous : Fin selectedRowCount,
            (previous : Nat) < (current : Nat) →
              normalizedBasisVector previous ∈ selectedRawSpan := by
          intro previous hprevious
          have hprevious' : (previous : Nat) < n := by
            simpa [current] using hprevious
          simpa using inductionHypothesis (previous : Nat) hprevious'
            previous.isLt
        have hfold :
            evidence.steps.foldl (replayReductionStep (current : Nat))
                (some (selectedRawRow current)) = some evidence.reduced := by
          simpa [selectedRawRow, evidence] using evidence.reductionReplay
        rcases replayReductionSteps_preserves_rawSpan current hfold
            hinitialValid (selectedRawVector_mem_span current) hprevious with
          ⟨hreducedValid, hreducedMem⟩
        have hcoefficientValid :
            FractionValid (coefficientAt evidence.pivot evidence.reduced) :=
          fractionValid_coefficientAt hreducedValid evidence.pivot
        have hcoefficientNumerator :
            (coefficientAt evidence.pivot evidence.reduced).1 ≠ 0 :=
          (fractionIsZero_eq_false_iff _).mp evidence.pivotCoefficientNonzero
        have hnormalizedMem :
            sparseRowValue
                (normalizeRow (coefficientAt evidence.pivot evidence.reduced)
                  evidence.reduced) ∈ selectedRawSpan := by
          rw [sparseRowValue_normalize hreducedValid hcoefficientValid
            hcoefficientNumerator]
          exact selectedRawSpan.smul_mem
            (fractionValue (coefficientAt evidence.pivot evidence.reduced))⁻¹
            hreducedMem
        have hnormalizedValid :
            SparseRowValid
              (normalizeRow (coefficientAt evidence.pivot evidence.reduced)
                evidence.reduced) :=
          (exactSparseRowWellFormed_sound evidence.normalizedWellFormed).1
        have hexpectedValid :
            SparseRowValid (decodeRationalSparseRow evidence.expectedData) :=
          (exactSparseRowWellFormed_sound evidence.expectedWellFormed).1
        have hequal := exactSparseRowEqual_sound hnormalizedValid hexpectedValid
          evidence.normalizedEqual
        change sparseRowValue (decodeRationalSparseRow evidence.expectedData) ∈
          selectedRawSpan
        rw [← hequal]
        exact hnormalizedMem
  simpa using hall (rowIndex : Nat) rowIndex.isLt

def normalizedBasisSpan : Submodule ℚ (Nat →₀ ℚ) :=
  Submodule.span ℚ (Set.range normalizedBasisVector)

theorem normalizedBasisSpan_le_selectedRawSpan :
    normalizedBasisSpan ≤ selectedRawSpan := by
  apply Submodule.span_le.mpr
  rintro vector ⟨rowIndex, rfl⟩
  exact normalizedBasisVector_mem_selectedRawSpan rowIndex

theorem selectedRawVector_linearIndependent :
    LinearIndependent ℚ selectedRawVector := by
  letI : Module.Finite ℚ
      (Submodule.span ℚ (Set.range selectedRawVector)) := by
    exact Module.Finite.span_of_finite ℚ (Set.finite_range selectedRawVector)
  rw [linearIndependent_iff_card_le_finrank_span]
  rw [← finrank_span_eq_card normalizedBasisVector_linearIndependent]
  exact Submodule.finrank_mono normalizedBasisSpan_le_selectedRawSpan

theorem selectedRawSpan_finrank :
    Module.finrank ℚ selectedRawSpan = 11556 := by
  change Module.finrank ℚ
      (Submodule.span ℚ (Set.range selectedRawVector)) = 11556
  rw [finrank_span_eq_card selectedRawVector_linearIndependent]
  norm_num [selectedRowCount]

end HypercubicDimension16TraceRankTheorem
end YangMills
end QuantumTheory
end Mettapedia
