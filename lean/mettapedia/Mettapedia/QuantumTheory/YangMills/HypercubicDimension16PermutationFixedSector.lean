import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16OrbitCharacter
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PermutationDecorationTransport
import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Fixed labeled sectors for one field permutation

The trace-layout fixed equation and the local-decoration fixed equation are
separated exactly.  The former is identified with the ordinary permutation
centralizer; the latter is the indexed decoration character.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PermutationFixedSector

open V14HypercubicFDCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16OrbitCharacter
open HypercubicDimension16CycleBlockDecoration

abbrev IsTraceFixed
    {Label : Type*} (rename trace : Equiv.Perm Label) : Prop :=
  rename.symm.trans (trace.trans rename) = trace

theorem isTraceFixed_iff_mem_centralizer
    {Label : Type*} (rename trace : Equiv.Perm Label) :
    IsTraceFixed rename trace ↔
      trace ∈ Subgroup.centralizer ({rename} : Set (Equiv.Perm Label)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  change rename * trace * rename⁻¹ = trace ↔ trace * rename = rename * trace
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm

def fixedTraceEquivCentralizer
    {Label : Type*} (rename : Equiv.Perm Label) :
    { trace : Equiv.Perm Label // IsTraceFixed rename trace } ≃
      Subgroup.centralizer ({rename} : Set (Equiv.Perm Label)) where
  toFun trace :=
    ⟨trace.1, (isTraceFixed_iff_mem_centralizer rename trace.1).mp trace.2⟩
  invFun trace :=
    ⟨trace.1, (isTraceFixed_iff_mem_centralizer rename trace.1).mpr trace.2⟩
  left_inv trace := by
    cases trace
    rfl
  right_inv trace := by
    cases trace
    rfl

def traceFixedWeight
    {Label : Type*} (rename trace : Equiv.Perm Label) : ℚ := by
  classical
  exact if IsTraceFixed rename trace then 1 else 0

theorem traceFixedIndicatorSum_eq_natCardCentralizer
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (rename : Equiv.Perm Label) :
    (∑ trace : Equiv.Perm Label, traceFixedWeight rename trace) =
      Nat.card (Subgroup.centralizer
        ({rename} : Set (Equiv.Perm Label))) := by
  classical
  calc
    (∑ trace : Equiv.Perm Label, traceFixedWeight rename trace) =
      ∑ trace ∈ (Finset.univ.filter (IsTraceFixed rename)), (1 : ℚ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro trace _
        by_cases fixed : IsTraceFixed rename trace
        · simp [traceFixedWeight, fixed]
        · simp [traceFixedWeight, fixed]
    _ = ∑ trace : { trace : Equiv.Perm Label //
          IsTraceFixed rename trace }, (1 : ℚ) := by
        exact Finset.sum_subtype _ (by simp) _
    _ = Fintype.card { trace : Equiv.Perm Label //
          IsTraceFixed rename trace } := by simp
    _ = Fintype.card (Subgroup.centralizer
          ({rename} : Set (Equiv.Perm Label))) := by
        exact_mod_cast Fintype.card_congr (fixedTraceEquivCentralizer rename)
    _ = Nat.card (Subgroup.centralizer
          ({rename} : Set (Equiv.Perm Label))) := by
        rw [Nat.card_eq_fintype_card]

def labeledLocalWordSectorEquiv
    (fieldCount derivativeCount : ℕ) :
    LabeledLocalWordSector fieldCount derivativeCount ≃
      Equiv.Perm (Fin fieldCount) ×
        LocalWordDecoration fieldCount derivativeCount where
  toFun sector := (sector.trace, sector.decoration)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv sector := by cases sector; rfl
  right_inv pair := by cases pair; rfl

theorem labeledSectorFixed_iff
    (h : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    rename • sector.hypercubicAct h = sector ↔
      IsTraceFixed rename sector.trace ∧
        IsTwistedIndexedDecoration h rename derivativeCount derivativeCount
          sector.decoration.1 := by
  constructor
  · intro fixed
    change (sector.hypercubicAct h).relabel rename = sector at fixed
    have traceFixed := congrArg LabeledLocalWordSector.trace fixed
    have decorationFixed := congrArg LabeledLocalWordSector.decoration fixed
    refine ⟨traceFixed, sector.decoration.2, ?_⟩
    intro field
    have pointwise := congrArg
      (fun decoration : LocalWordDecoration fieldCount derivativeCount =>
        decoration.1 (rename field)) decorationFixed
    dsimp [LabeledLocalWordSector.relabel,
      LabeledLocalWordSector.hypercubicAct,
      LocalWordDecoration.relabel,
      LocalWordDecoration.hypercubicAct] at pointwise
    simpa using pointwise.symm
  · rintro ⟨traceFixed, _degreeFixed, decorationFixed⟩
    change (sector.hypercubicAct h).relabel rename = sector
    apply LabeledLocalWordSector.ext
    · exact traceFixed
    · apply Subtype.ext
      funext field
      have pointwise := decorationFixed (rename.symm field)
      change
        (sector.decoration.1 (rename.symm field)).hypercubicAct h =
          sector.decoration.1 field
      simpa using pointwise.symm

/-! ## Exact factorization of one permutation summand -/

def labeledFixedSectorWeight
    (h : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (sector : LabeledLocalWordSector fieldCount derivativeCount) : ℚ := by
  classical
  exact if rename • sector.hypercubicAct h = sector then
    sector.tensorSign h
  else 0

def labeledFixedSectorCharacter
    (h : Hypercubic4) (fieldCount derivativeCount : ℕ)
    (rename : Equiv.Perm (Fin fieldCount)) : ℚ :=
  ∑ sector : LabeledLocalWordSector fieldCount derivativeCount,
    labeledFixedSectorWeight h rename sector

theorem labeledFixedSectorWeight_eq_trace_mul_decoration
    (h : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    labeledFixedSectorWeight h rename sector =
      traceFixedWeight rename sector.trace *
        indexedDecorationWeight h rename derivativeCount derivativeCount
          sector.decoration.1 := by
  classical
  unfold labeledFixedSectorWeight traceFixedWeight indexedDecorationWeight
  by_cases fixed : rename • sector.hypercubicAct h = sector
  · have separated := (labeledSectorFixed_iff h rename sector).mp fixed
    rw [if_pos fixed, if_pos separated.1, if_pos separated.2, one_mul]
    rfl
  · by_cases traceFixed : IsTraceFixed rename sector.trace
    · have decorationNotFixed :
          ¬IsTwistedIndexedDecoration h rename derivativeCount
            derivativeCount sector.decoration.1 :=
        fun decorationFixed =>
          fixed ((labeledSectorFixed_iff h rename sector).mpr
            ⟨traceFixed, decorationFixed⟩)
      rw [if_neg fixed, if_pos traceFixed, if_neg decorationNotFixed]
      simp
    · rw [if_neg fixed, if_neg traceFixed]
      simp

theorem indexedDecorationCharacter_eq_localWordDecorationSum
    (h : Hypercubic4) (fieldCount derivativeCount : ℕ)
    (rename : Equiv.Perm (Fin fieldCount)) :
    indexedDecorationCharacter h rename derivativeCount derivativeCount =
      ∑ decoration : LocalWordDecoration fieldCount derivativeCount,
        indexedDecorationWeight h rename derivativeCount derivativeCount
          decoration.1 := by
  classical
  unfold indexedDecorationCharacter
  let exactDegree :=
    fun letters : Fin fieldCount → LocalFieldLetter derivativeCount =>
      (∑ field, (letters field).derivativeCount.1) = derivativeCount
  calc
    (∑ letters : Fin fieldCount → LocalFieldLetter derivativeCount,
        indexedDecorationWeight h rename derivativeCount derivativeCount
          letters) =
      ∑ letters ∈ (Finset.univ.filter exactDegree),
        indexedDecorationWeight h rename derivativeCount derivativeCount
          letters := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro letters _
      by_cases degree : exactDegree letters
      · rw [if_pos degree]
      · rw [if_neg degree]
        unfold indexedDecorationWeight
        rw [if_neg]
        exact fun twisted => degree twisted.1
    _ = ∑ decoration : LocalWordDecoration fieldCount derivativeCount,
          indexedDecorationWeight h rename derivativeCount derivativeCount
            decoration.1 := by
      exact Finset.sum_subtype _ (by simp [exactDegree]) _

theorem labeledFixedSectorCharacter_eq_centralizer_mul_decoration
    (h : Hypercubic4) (fieldCount derivativeCount : ℕ)
    (rename : Equiv.Perm (Fin fieldCount)) :
    labeledFixedSectorCharacter h fieldCount derivativeCount rename =
      Nat.card (Subgroup.centralizer
          ({rename} : Set (Equiv.Perm (Fin fieldCount)))) *
        indexedDecorationCharacter h rename derivativeCount derivativeCount := by
  classical
  unfold labeledFixedSectorCharacter
  calc
    (∑ sector : LabeledLocalWordSector fieldCount derivativeCount,
        labeledFixedSectorWeight h rename sector) =
      ∑ pair : Equiv.Perm (Fin fieldCount) ×
          LocalWordDecoration fieldCount derivativeCount,
        traceFixedWeight rename pair.1 *
          indexedDecorationWeight h rename derivativeCount derivativeCount
            pair.2.1 := by
      apply Fintype.sum_equiv
        (labeledLocalWordSectorEquiv fieldCount derivativeCount)
      intro sector
      exact labeledFixedSectorWeight_eq_trace_mul_decoration h rename sector
    _ = ∑ trace : Equiv.Perm (Fin fieldCount),
        ∑ decoration : LocalWordDecoration fieldCount derivativeCount,
          traceFixedWeight rename trace *
            indexedDecorationWeight h rename derivativeCount derivativeCount
              decoration.1 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ trace : Equiv.Perm (Fin fieldCount),
        traceFixedWeight rename trace *
          (∑ decoration : LocalWordDecoration fieldCount derivativeCount,
            indexedDecorationWeight h rename derivativeCount derivativeCount
              decoration.1) := by
      apply Finset.sum_congr rfl
      intro trace _
      rw [Finset.mul_sum]
    _ = (∑ trace : Equiv.Perm (Fin fieldCount),
          traceFixedWeight rename trace) *
        (∑ decoration : LocalWordDecoration fieldCount derivativeCount,
          indexedDecorationWeight h rename derivativeCount derivativeCount
            decoration.1) := by
      rw [Finset.sum_mul]
    _ = Nat.card (Subgroup.centralizer
          ({rename} : Set (Equiv.Perm (Fin fieldCount)))) *
        indexedDecorationCharacter h rename derivativeCount derivativeCount := by
      rw [traceFixedIndicatorSum_eq_natCardCentralizer,
        indexedDecorationCharacter_eq_localWordDecorationSum]

theorem labeledBurnsideNumerator_eq_sum_labeledFixedSectorCharacter
    (h : Hypercubic4) (fieldCount derivativeCount : ℕ) :
    labeledBurnsideNumerator h fieldCount derivativeCount =
      ∑ rename : Equiv.Perm (Fin fieldCount),
        labeledFixedSectorCharacter h fieldCount derivativeCount rename := by
  classical
  unfold labeledBurnsideNumerator labeledFixedSectorCharacter
  apply Finset.sum_congr rfl
  intro rename _
  apply Finset.sum_congr rfl
  intro sector _
  unfold labeledFixedSectorWeight
  by_cases fixed : rename • sector.hypercubicAct h = sector
  · rfl
  · rfl

/-- The honest labeled Burnside numerator after separating trace layouts from
local decorations. -/
theorem labeledBurnsideNumerator_eq_sum_centralizer_mul_decoration
    (h : Hypercubic4) (fieldCount derivativeCount : ℕ) :
    labeledBurnsideNumerator h fieldCount derivativeCount =
      ∑ rename : Equiv.Perm (Fin fieldCount),
        Nat.card (Subgroup.centralizer
            ({rename} : Set (Equiv.Perm (Fin fieldCount)))) *
          indexedDecorationCharacter h rename derivativeCount
            derivativeCount := by
  rw [labeledBurnsideNumerator_eq_sum_labeledFixedSectorCharacter]
  apply Finset.sum_congr rfl
  intro rename _
  exact labeledFixedSectorCharacter_eq_centralizer_mul_decoration
    h fieldCount derivativeCount rename

end HypercubicDimension16PermutationFixedSector
end YangMills
end QuantumTheory
end Mettapedia
