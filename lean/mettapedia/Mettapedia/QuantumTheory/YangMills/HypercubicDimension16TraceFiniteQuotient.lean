import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankTheorem
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Finite ambient quotient for the sparse trace-relation certificate

The exact sparse rows are transported from the auxiliary natural-coordinate
module to the genuine finite coordinate module.  Rank--nullity then computes
the quotient by the span of the selected rows.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceFiniteQuotient

open HypercubicDimension16TraceRankCertificate
open HypercubicDimension16TraceRankCertificateData
open HypercubicDimension16TraceRankSemantics
open HypercubicDimension16TraceRankTheorem

theorem selectedRawRow_wellFormed (rowIndex : Fin selectedRowCount) :
    exactSparseRowWellFormed (selectedRawRow rowIndex) = true := by
  simpa [selectedRawRow] using (rowEvidence rowIndex).integerWellFormed

theorem selectedRawRow_maxSupport_lt_ambient
    (rowIndex : Fin selectedRowCount) :
    ∃ pivot, maxSupportColumn (selectedRawRow rowIndex) = some pivot ∧
      pivot < ambientColumnCount := by
  let evidence := rowEvidence rowIndex
  have hfold :
      evidence.steps.toList.foldl
          (replayReductionStep (rowIndex : Nat))
          (some (selectedRawRow rowIndex)) = some evidence.reduced := by
    simpa only [selectedRawRow, evidence, ← Array.foldl_toList] using
      evidence.reductionReplay
  cases hsteps : evidence.steps.toList with
  | nil =>
      simp only [hsteps, List.foldl_nil, Option.some.injEq] at hfold
      refine ⟨evidence.pivot, ?_, evidence.pivot_lt⟩
      rw [hfold]
      exact evidence.reducedMaxSupport
  | cons basisIndex remaining =>
      simp only [hsteps, List.foldl_cons] at hfold
      generalize hfirst :
        replayReductionStep (rowIndex : Nat)
          (some (selectedRawRow rowIndex)) basisIndex = firstOption at hfold
      cases firstOption with
      | none =>
          rw [replayReductionStepsList_none] at hfold
          simp at hfold
      | some intermediate =>
          let stepEvidence :=
            Classical.choice (replayReductionStep_evidence hfirst)
          let previous : Fin selectedRowCount :=
            ⟨basisIndex, lt_trans stepEvidence.basis_lt rowIndex.isLt⟩
          have hpivot :
              stepEvidence.pivot = (rowEvidence previous).pivot := by
            apply Option.some.inj
            rw [← stepEvidence.pivotLookup,
              (rowEvidence previous).pivotLookup]
          refine ⟨stepEvidence.pivot, stepEvidence.currentMaxSupport, ?_⟩
          rw [hpivot]
          exact (rowEvidence previous).pivot_lt

theorem selectedRawRow_columns_lt_ambient
    (rowIndex : Fin selectedRowCount) {entry : Nat × ExactFraction}
    (hentry : entry ∈ selectedRawRow rowIndex) :
    entry.1 < ambientColumnCount := by
  rcases selectedRawRow_maxSupport_lt_ambient rowIndex with
    ⟨pivot, hpivot, hpivotLt⟩
  rcases exactSparseRowWellFormed_sound
      (selectedRawRow_wellFormed rowIndex) with ⟨_, hstrict, _⟩
  exact lt_of_le_of_lt
    (sparseColumn_le_maxSupport hstrict hpivot hentry) hpivotLt

theorem selectedRawVector_support_subset_ambient
    (rowIndex : Fin selectedRowCount) :
    ↑(selectedRawVector rowIndex).support ⊆
      Set.range (fun column : Fin ambientColumnCount => (column : Nat)) := by
  intro column hcolumn
  have hcolumnLt : column < ambientColumnCount := by
    by_contra hnotLt
    have hambientLe : ambientColumnCount ≤ column := Nat.le_of_not_gt hnotLt
    have hcolumns : ∀ entry ∈ selectedRawRow rowIndex,
        entry.1 < column := by
      intro entry hentry
      exact lt_of_lt_of_le
        (selectedRawRow_columns_lt_ambient rowIndex hentry) hambientLe
    have hzero : selectedRawVector rowIndex column = 0 := by
      exact sparseRowValue_apply_eq_zero_of_columns_lt hcolumns
    exact (Finsupp.mem_support_iff.mp hcolumn) hzero
  exact ⟨⟨column, hcolumnLt⟩, rfl⟩

abbrev AmbientVector := Fin ambientColumnCount →₀ ℚ

def ambientExtend : AmbientVector →ₗ[ℚ] Nat →₀ ℚ :=
  Finsupp.lmapDomain ℚ ℚ
    (fun column : Fin ambientColumnCount => (column : Nat))

def ambientRestrict : (Nat →₀ ℚ) →ₗ[ℚ] AmbientVector :=
  Finsupp.lcomapDomain
    (R := ℚ) (M := ℚ)
    (fun column : Fin ambientColumnCount => (column : Nat))
    Fin.val_injective

def ambientSelectedRawVector (rowIndex : Fin selectedRowCount) : AmbientVector :=
  ambientRestrict (selectedRawVector rowIndex)

theorem ambientExtend_ambientSelectedRawVector
    (rowIndex : Fin selectedRowCount) :
    ambientExtend (ambientSelectedRawVector rowIndex) =
      selectedRawVector rowIndex := by
  change Finsupp.mapDomain
      (fun column : Fin ambientColumnCount => (column : Nat))
      (Finsupp.comapDomain
        (fun column : Fin ambientColumnCount => (column : Nat))
        (selectedRawVector rowIndex) Fin.val_injective.injOn) =
    selectedRawVector rowIndex
  exact Finsupp.mapDomain_comapDomain _ Fin.val_injective _
    (selectedRawVector_support_subset_ambient rowIndex)

theorem ambientSelectedRawVector_linearIndependent :
    LinearIndependent ℚ ambientSelectedRawVector := by
  apply LinearIndependent.of_comp ambientExtend
  have hfamily :
      (ambientExtend : AmbientVector → Nat →₀ ℚ) ∘
          ambientSelectedRawVector = selectedRawVector := by
    funext rowIndex
    exact ambientExtend_ambientSelectedRawVector rowIndex
  rw [hfamily]
  exact selectedRawVector_linearIndependent

def ambientSelectedRawSpan : Submodule ℚ AmbientVector :=
  Submodule.span ℚ (Set.range ambientSelectedRawVector)

theorem ambientSelectedRawSpan_finrank :
    Module.finrank ℚ ambientSelectedRawSpan = 11556 := by
  change Module.finrank ℚ
      (Submodule.span ℚ (Set.range ambientSelectedRawVector)) = 11556
  rw [finrank_span_eq_card ambientSelectedRawVector_linearIndependent]
  norm_num [selectedRowCount]

theorem ambientVector_finrank : Module.finrank ℚ AmbientVector = 11654 := by
  simp [AmbientVector, ambientColumnCount]

theorem ambientTraceQuotient_finrank :
    Module.finrank ℚ (AmbientVector ⧸ ambientSelectedRawSpan) = 98 := by
  rw [Submodule.finrank_quotient]
  rw [ambientVector_finrank, ambientSelectedRawSpan_finrank]

theorem normalizedBasisRow_columns_lt_ambient
    (rowIndex : Fin selectedRowCount) {entry : Nat × ExactFraction}
    (hentry : entry ∈ normalizedBasisRow rowIndex) :
    entry.1 < ambientColumnCount := by
  rcases exactSparseRowWellFormed_sound
      (normalizedBasisRow_wellFormed rowIndex) with ⟨_, hstrict, _⟩
  exact lt_of_le_of_lt
    (sparseColumn_le_maxSupport hstrict
      (normalizedBasisRow_maxSupport rowIndex) hentry)
    (rowEvidence rowIndex).pivot_lt

theorem normalizedBasisVector_support_subset_ambient
    (rowIndex : Fin selectedRowCount) :
    ↑(normalizedBasisVector rowIndex).support ⊆
      Set.range (fun column : Fin ambientColumnCount => (column : Nat)) := by
  intro column hcolumn
  have hcolumnLt : column < ambientColumnCount := by
    by_contra hnotLt
    have hambientLe : ambientColumnCount ≤ column := Nat.le_of_not_gt hnotLt
    have hcolumns : ∀ entry ∈ normalizedBasisRow rowIndex,
        entry.1 < column := by
      intro entry hentry
      exact lt_of_lt_of_le
        (normalizedBasisRow_columns_lt_ambient rowIndex hentry) hambientLe
    have hzero : normalizedBasisVector rowIndex column = 0 := by
      exact sparseRowValue_apply_eq_zero_of_columns_lt hcolumns
    exact (Finsupp.mem_support_iff.mp hcolumn) hzero
  exact ⟨⟨column, hcolumnLt⟩, rfl⟩

def ambientNormalizedBasisVector
    (rowIndex : Fin selectedRowCount) : AmbientVector :=
  ambientRestrict (normalizedBasisVector rowIndex)

theorem ambientExtend_ambientNormalizedBasisVector
    (rowIndex : Fin selectedRowCount) :
    ambientExtend (ambientNormalizedBasisVector rowIndex) =
      normalizedBasisVector rowIndex := by
  change Finsupp.mapDomain
      (fun column : Fin ambientColumnCount => (column : Nat))
      (Finsupp.comapDomain
        (fun column : Fin ambientColumnCount => (column : Nat))
        (normalizedBasisVector rowIndex) Fin.val_injective.injOn) =
    normalizedBasisVector rowIndex
  exact Finsupp.mapDomain_comapDomain _ Fin.val_injective _
    (normalizedBasisVector_support_subset_ambient rowIndex)

theorem ambientNormalizedBasisVector_linearIndependent :
    LinearIndependent ℚ ambientNormalizedBasisVector := by
  apply LinearIndependent.of_comp ambientExtend
  have hfamily :
      (ambientExtend : AmbientVector → Nat →₀ ℚ) ∘
          ambientNormalizedBasisVector = normalizedBasisVector := by
    funext rowIndex
    exact ambientExtend_ambientNormalizedBasisVector rowIndex
  rw [hfamily]
  exact normalizedBasisVector_linearIndependent

def ambientNormalizedBasisSpan : Submodule ℚ AmbientVector :=
  Submodule.span ℚ (Set.range ambientNormalizedBasisVector)

theorem ambientNormalizedBasisSpan_finrank :
    Module.finrank ℚ ambientNormalizedBasisSpan = 11556 := by
  change Module.finrank ℚ
      (Submodule.span ℚ (Set.range ambientNormalizedBasisVector)) = 11556
  rw [finrank_span_eq_card ambientNormalizedBasisVector_linearIndependent]
  norm_num [selectedRowCount]

theorem ambientRestrict_selectedRawSpan :
    selectedRawSpan.map ambientRestrict = ambientSelectedRawSpan := by
  rw [selectedRawSpan, Submodule.map_span]
  apply congrArg (Submodule.span ℚ)
  ext vector
  constructor
  · rintro ⟨rawVector, ⟨rowIndex, rfl⟩, rfl⟩
    exact ⟨rowIndex, rfl⟩
  · rintro ⟨rowIndex, rfl⟩
    exact ⟨selectedRawVector rowIndex, ⟨rowIndex, rfl⟩, rfl⟩

theorem ambientNormalizedBasisVector_mem_selectedRawSpan
    (rowIndex : Fin selectedRowCount) :
    ambientNormalizedBasisVector rowIndex ∈ ambientSelectedRawSpan := by
  have hsource : normalizedBasisVector rowIndex ∈ selectedRawSpan :=
    normalizedBasisVector_mem_selectedRawSpan rowIndex
  have hmapped :
      ambientRestrict (normalizedBasisVector rowIndex) ∈
        selectedRawSpan.map ambientRestrict :=
    ⟨normalizedBasisVector rowIndex, hsource, rfl⟩
  rw [ambientRestrict_selectedRawSpan] at hmapped
  exact hmapped

theorem ambientNormalizedBasisSpan_le_selectedRawSpan :
    ambientNormalizedBasisSpan ≤ ambientSelectedRawSpan := by
  apply Submodule.span_le.mpr
  rintro vector ⟨rowIndex, rfl⟩
  exact ambientNormalizedBasisVector_mem_selectedRawSpan rowIndex

theorem ambientNormalizedBasisSpan_eq_selectedRawSpan :
    ambientNormalizedBasisSpan = ambientSelectedRawSpan := by
  apply Submodule.eq_of_le_of_finrank_eq
    ambientNormalizedBasisSpan_le_selectedRawSpan
  rw [ambientNormalizedBasisSpan_finrank,
    ambientSelectedRawSpan_finrank]

theorem freeColumnsCheck_certificate : freeColumnsCheck = true := by
  have hshape := certificateShapeCheck_certificate
  simp only [certificateShapeCheck, Bool.and_eq_true] at hshape
  exact hshape.2

theorem freeColumnCheck_certificate {freeIndex : Nat}
    (hfreeIndex : freeIndex < 98) :
    freeColumnCheck freeIndex = true := by
  apply List.all_eq_true.mp freeColumnsCheck_certificate
  exact List.mem_range.mpr hfreeIndex

structure FreeColumnEvidence (freeIndex : Nat) where
  column : Nat
  lookup : freeColumn? freeIndex = some column
  column_lt : column < ambientColumnCount
  owner : columnOwner? column = some (selectedRowCount + freeIndex)

theorem freeColumnCheck_evidence {freeIndex : Nat}
    (hcheck : freeColumnCheck freeIndex = true) :
    Nonempty (FreeColumnEvidence freeIndex) := by
  unfold freeColumnCheck at hcheck
  generalize hlookup : freeColumn? freeIndex = columnOption at hcheck
  cases columnOption with
  | none => simp at hcheck
  | some column =>
      have hparts : column < ambientColumnCount ∧
          columnOwner? column = some (selectedRowCount + freeIndex) := by
        simpa using hcheck
      exact ⟨⟨column, hlookup, hparts.1, hparts.2⟩⟩

def freeColumnEvidence (freeIndex : Fin 98) :
    FreeColumnEvidence (freeIndex : Nat) :=
  Classical.choice <| freeColumnCheck_evidence <|
    freeColumnCheck_certificate freeIndex.isLt

def certifiedFreeColumn (freeIndex : Fin 98) : Fin ambientColumnCount :=
  ⟨(freeColumnEvidence freeIndex).column,
    (freeColumnEvidence freeIndex).column_lt⟩

theorem certifiedFreeColumn_owner (freeIndex : Fin 98) :
    columnOwner? (certifiedFreeColumn freeIndex : Nat) =
      some (selectedRowCount + (freeIndex : Nat)) :=
  (freeColumnEvidence freeIndex).owner

theorem certifiedFreeColumn_injective :
    Function.Injective certifiedFreeColumn := by
  intro left right hequal
  apply Fin.ext
  have hcolumns :
      (certifiedFreeColumn left : Nat) =
        (certifiedFreeColumn right : Nat) :=
    congrArg Fin.val hequal
  have howners :
      some (selectedRowCount + (left : Nat)) =
        some (selectedRowCount + (right : Nat)) := by
    rw [← certifiedFreeColumn_owner left, hcolumns,
      certifiedFreeColumn_owner right]
  exact Nat.add_left_cancel (Option.some.inj howners)

def ambientCertifiedPivot
    (rowIndex : Fin selectedRowCount) : Fin ambientColumnCount :=
  ⟨certifiedPivot rowIndex, (rowEvidence rowIndex).pivot_lt⟩

theorem ambientCertifiedPivot_injective :
    Function.Injective ambientCertifiedPivot := by
  intro left right hequal
  apply certifiedPivot_injective
  exact congrArg Fin.val hequal

theorem ambientCertifiedPivot_ne_freeColumn
    (rowIndex : Fin selectedRowCount) (freeIndex : Fin 98) :
    ambientCertifiedPivot rowIndex ≠ certifiedFreeColumn freeIndex := by
  intro hequal
  have hcolumns : certifiedPivot rowIndex =
      (certifiedFreeColumn freeIndex : Nat) :=
    congrArg Fin.val hequal
  have hcolumns' : (rowEvidence rowIndex).pivot =
      (certifiedFreeColumn freeIndex : Nat) := by
    simpa [certifiedPivot] using hcolumns
  have howners : some (rowIndex : Nat) =
      some (selectedRowCount + (freeIndex : Nat)) := by
    rw [← (rowEvidence rowIndex).pivotOwner, hcolumns',
      certifiedFreeColumn_owner freeIndex]
  have hindices : (rowIndex : Nat) =
      selectedRowCount + (freeIndex : Nat) := Option.some.inj howners
  omega

theorem ambientNormalizedBasisVector_pivot_ne_zero
    (rowIndex : Fin selectedRowCount) :
    ambientNormalizedBasisVector rowIndex
      (ambientCertifiedPivot rowIndex) ≠ 0 := by
  exact normalizedBasisVector_pivot_ne_zero rowIndex

theorem ambientNormalizedBasisVector_above_pivot
    (rowIndex : Fin selectedRowCount) (column : Fin ambientColumnCount)
    (habove : ambientCertifiedPivot rowIndex < column) :
    ambientNormalizedBasisVector rowIndex column = 0 := by
  change certifiedPivot rowIndex < (column : Nat) at habove
  exact normalizedBasisVector_above_pivot rowIndex column
    habove

def freeCoordinateVector (freeIndex : Fin 98) : AmbientVector :=
  Finsupp.single (certifiedFreeColumn freeIndex) 1

theorem freeCoordinateVector_linearIndependent :
    LinearIndependent ℚ freeCoordinateVector := by
  change LinearIndependent ℚ
    ((fun column : Fin ambientColumnCount =>
      Finsupp.single column (1 : ℚ)) ∘ certifiedFreeColumn)
  exact (Finsupp.linearIndependent_single_one
    (ι := Fin ambientColumnCount) (R := ℚ)).comp
    certifiedFreeColumn certifiedFreeColumn_injective

def completeNatVector :
    Fin selectedRowCount ⊕ Fin 98 → Nat →₀ ℚ
  | Sum.inl rowIndex => normalizedBasisVector rowIndex
  | Sum.inr freeIndex =>
      Finsupp.single (certifiedFreeColumn freeIndex : Nat) 1

def completeNatPivot : Fin selectedRowCount ⊕ Fin 98 → Nat
  | Sum.inl rowIndex => certifiedPivot rowIndex
  | Sum.inr freeIndex => certifiedFreeColumn freeIndex

theorem completeNatPivot_injective : Function.Injective completeNatPivot := by
  intro left right hequal
  cases left with
  | inl leftRow =>
      cases right with
      | inl rightRow =>
          congr 1
          exact certifiedPivot_injective hequal
      | inr rightFree =>
          exfalso
          exact ambientCertifiedPivot_ne_freeColumn leftRow rightFree
            (Fin.ext hequal)
  | inr leftFree =>
      cases right with
      | inl rightRow =>
          exfalso
          exact ambientCertifiedPivot_ne_freeColumn rightRow leftFree
            (Fin.ext hequal.symm)
      | inr rightFree =>
          congr 1
          apply certifiedFreeColumn_injective
          exact Fin.ext hequal

theorem completeNatVector_pivot_ne_zero
    (index : Fin selectedRowCount ⊕ Fin 98) :
    completeNatVector index (completeNatPivot index) ≠ 0 := by
  cases index with
  | inl rowIndex =>
      exact normalizedBasisVector_pivot_ne_zero rowIndex
  | inr freeIndex =>
      simp [completeNatVector, completeNatPivot]

theorem completeNatVector_above_pivot
    (index : Fin selectedRowCount ⊕ Fin 98) (column : Nat)
    (habove : completeNatPivot index < column) :
    completeNatVector index column = 0 := by
  cases index with
  | inl rowIndex =>
      exact normalizedBasisVector_above_pivot rowIndex column habove
  | inr freeIndex =>
      change (certifiedFreeColumn freeIndex : Nat) < column at habove
      simp [completeNatVector, ne_of_lt habove]

theorem completeNatVector_linearIndependent :
    LinearIndependent ℚ completeNatVector :=
  linearIndependent_of_distinct_maxSupport completeNatPivot_injective
    completeNatVector_pivot_ne_zero completeNatVector_above_pivot

def completeEchelonFamily :
    Fin selectedRowCount ⊕ Fin 98 → AmbientVector
  | Sum.inl rowIndex => ambientNormalizedBasisVector rowIndex
  | Sum.inr freeIndex => freeCoordinateVector freeIndex

theorem ambientExtend_completeEchelonFamily
    (index : Fin selectedRowCount ⊕ Fin 98) :
    ambientExtend (completeEchelonFamily index) = completeNatVector index := by
  cases index with
  | inl rowIndex =>
      exact ambientExtend_ambientNormalizedBasisVector rowIndex
  | inr freeIndex =>
      simp [ambientExtend, completeEchelonFamily, completeNatVector,
        freeCoordinateVector, Finsupp.lmapDomain]

theorem completeEchelonFamily_linearIndependent :
    LinearIndependent ℚ completeEchelonFamily := by
  apply LinearIndependent.of_comp ambientExtend
  have hfamily :
      (ambientExtend : AmbientVector → Nat →₀ ℚ) ∘
          completeEchelonFamily = completeNatVector := by
    funext index
    exact ambientExtend_completeEchelonFamily index
  rw [hfamily]
  exact completeNatVector_linearIndependent

def completeEchelonSpan : Submodule ℚ AmbientVector :=
  Submodule.span ℚ (Set.range completeEchelonFamily)

theorem completeEchelonSpan_finrank :
    Module.finrank ℚ completeEchelonSpan = 11654 := by
  change Module.finrank ℚ
      (Submodule.span ℚ (Set.range completeEchelonFamily)) = 11654
  rw [finrank_span_eq_card completeEchelonFamily_linearIndependent]
  norm_num [selectedRowCount]

theorem completeEchelonSpan_eq_top : completeEchelonSpan = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [completeEchelonSpan_finrank, ambientVector_finrank]

noncomputable def completeEchelonBasis :
    Module.Basis (Fin selectedRowCount ⊕ Fin 98) ℚ AmbientVector :=
  Module.Basis.mk completeEchelonFamily_linearIndependent <| by
    simpa [completeEchelonSpan] using completeEchelonSpan_eq_top.symm.le

@[simp] theorem completeEchelonBasis_apply
    (index : Fin selectedRowCount ⊕ Fin 98) :
    completeEchelonBasis index = completeEchelonFamily index := by
  simp [completeEchelonBasis]

theorem ambientNormalizedBasisSpan_disjoint_freeCoordinateSpan :
    Disjoint ambientNormalizedBasisSpan
      (Submodule.span ℚ (Set.range freeCoordinateVector)) := by
  have hparts :=
    linearIndependent_sum.mp completeEchelonFamily_linearIndependent
  simpa [ambientNormalizedBasisSpan, completeEchelonFamily,
    Function.comp_def] using hparts.2.2

theorem ambientSelectedRawSpan_disjoint_freeCoordinateSpan :
    Disjoint ambientSelectedRawSpan
      (Submodule.span ℚ (Set.range freeCoordinateVector)) := by
  rw [← ambientNormalizedBasisSpan_eq_selectedRawSpan]
  exact ambientNormalizedBasisSpan_disjoint_freeCoordinateSpan

abbrev TraceQuotient := AmbientVector ⧸ ambientSelectedRawSpan

def quotientFreeVector (freeIndex : Fin 98) : TraceQuotient :=
  ambientSelectedRawSpan.mkQ (freeCoordinateVector freeIndex)

theorem quotientFreeVector_linearIndependent :
    LinearIndependent ℚ quotientFreeVector := by
  change LinearIndependent ℚ
    (ambientSelectedRawSpan.mkQ ∘ freeCoordinateVector)
  apply freeCoordinateVector_linearIndependent.map
  rw [Submodule.ker_mkQ]
  exact ambientSelectedRawSpan_disjoint_freeCoordinateSpan.symm

def quotientFreeSpan : Submodule ℚ TraceQuotient :=
  Submodule.span ℚ (Set.range quotientFreeVector)

theorem quotientFreeSpan_finrank :
    Module.finrank ℚ quotientFreeSpan = 98 := by
  change Module.finrank ℚ
      (Submodule.span ℚ (Set.range quotientFreeVector)) = 98
  rw [finrank_span_eq_card quotientFreeVector_linearIndependent]
  norm_num

theorem quotientFreeSpan_eq_top : quotientFreeSpan = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [quotientFreeSpan_finrank, ambientTraceQuotient_finrank]

noncomputable def quotientFreeBasis :
    Module.Basis (Fin 98) ℚ TraceQuotient :=
  Module.Basis.mk quotientFreeVector_linearIndependent <| by
    simpa [quotientFreeSpan] using quotientFreeSpan_eq_top.symm.le

@[simp] theorem quotientFreeBasis_apply (freeIndex : Fin 98) :
    quotientFreeBasis freeIndex = quotientFreeVector freeIndex := by
  simp [quotientFreeBasis]

theorem quotientFree_conditioning_identity
    (row column : Fin 98) :
    quotientFreeBasis.repr (quotientFreeVector column) row =
      if row = column then 1 else 0 := by
  calc
    quotientFreeBasis.repr (quotientFreeVector column) row =
        quotientFreeBasis.repr (quotientFreeBasis column) row := by
          rw [quotientFreeBasis_apply]
    _ = if column = row then 1 else 0 :=
      quotientFreeBasis.repr_self_apply column row
    _ = if row = column then 1 else 0 := by
      by_cases hequal : row = column
      · subst column
        rfl
      · simp [hequal, Ne.symm hequal]

end HypercubicDimension16TraceFiniteQuotient
end YangMills
end QuantumTheory
end Mettapedia
