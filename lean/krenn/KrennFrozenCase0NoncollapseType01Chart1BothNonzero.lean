import KrennFrozenCase0NoncollapseType01Chart1X24Zero

/-!
Kernel reductions for the last open part of physical non-collapse type 01,
pivot chart 1, where both `w_24_11` and `w_25_11` are nonzero.

These lemmas connect the next frozen reductions directly to canonical source
rows; no solver verdict is used.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart1BothNonzero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart1X24Zero
open Krenn.SparseCertificate

def reductionSourceIndex : Fin 3 → Fin 747 := ![720, 378, 390]

/-- The balanced amplitude row that detects the remaining equal-secondary
chart once both pivot coefficients are nonzero. -/
def equalSecondarySourceIndex : Fin 747 := 733

/-- Two canonical rows that force the colour-one diagonal sum on edges
`02` and `03` to vanish. -/
def diagonalSumSourceIndex : Fin 2 → Fin 747 := ![646, 648]

/-- Four mixed rows and the colour-two monochromatic row used when the
remaining `w_02_11` pivot is nonzero. -/
def diagonalNonzeroSourceIndex : Fin 5 → Fin 747 := ![700, 698, 354, 349, 746]

theorem reduction_source_not_determinant
    (index : Fin 3) (slot : Fin 18) :
    determinantSourceIndex slot ≠ reductionSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, reductionSourceIndex]

theorem equalSecondary_source_not_determinant (slot : Fin 18) :
    determinantSourceIndex slot ≠ equalSecondarySourceIndex := by
  fin_cases slot <;>
    simp [determinantSourceIndex, equalSecondarySourceIndex]

theorem diagonal_sum_source_not_determinant
    (index : Fin 2) (slot : Fin 18) :
    determinantSourceIndex slot ≠ diagonalSumSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, diagonalSumSourceIndex]

theorem diagonal_nonzero_source_not_determinant
    (index : Fin 5) (slot : Fin 18) :
    determinantSourceIndex slot ≠ diagonalNonzeroSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, diagonalNonzeroSourceIndex]

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- In chart 1, nonzero `w_24_11` and `w_25_11` force `w_01_00 = 0`. -/
theorem w01_zero_of_both_pivots_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0) :
    values 0 = 0 := by
  have reductions := chart1_common_reductions values base hdet chart
  rcases reductions with
    ⟨_h13, h35, h34, _h34_10, _h25_10, _h25_12, _h34_12⟩
  rcases chart with ⟨h23, _h12⟩
  have source : sourceValue values (reductionSourceIndex 0) = 0 :=
    base (reductionSourceIndex 0)
      (fun slot => reduction_source_not_determinant 0 slot)
  have product :
      values 0 * ((-2 : R) * values 51 * values 56) = 0 := by
    calc
      values 0 * ((-2 : R) * values 51 * values 56) =
          sourceValue values (reductionSourceIndex 0) := by
            simp [sourceValue, reductionSourceIndex,
              Krenn.FrozenCase0System.equations,
              SparsePoly.toPoly, SparseTerm.toPoly,
              h23, h34, h35]
            ring
      _ = 0 := source
  have nonzeroFactor : (-2 : R) * values 51 * values 56 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) h24) h25
  exact (mul_eq_zero.mp product).resolve_right nonzeroFactor

/-- On the opposite-pivot chart, two canonical amplitude rows become the
literal linear equations `w_34_21 = 0` and `w_25_21 = 0`. -/
theorem sum_zero_linear_reductions
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0) :
    values 67 = 0 ∧ values 59 = 0 := by
  have reductions := chart1_common_reductions values base hdet chart
  rcases reductions with
    ⟨_h13, h35, h34, _h34_10, _h25_10, _h25_12, _h34_12⟩
  have h01 := w01_zero_of_both_pivots_nonzero
    values base hdet chart h24 h25
  have source0 : sourceValue values (reductionSourceIndex 1) = 0 :=
    base (reductionSourceIndex 1)
      (fun slot => reduction_source_not_determinant 1 slot)
  have source1 : sourceValue values (reductionSourceIndex 2) = 0 :=
    base (reductionSourceIndex 2)
      (fun slot => reduction_source_not_determinant 2 slot)
  have h34_21 : values 67 = 0 := by
    have identity :
        sourceValue values (reductionSourceIndex 1) =
          values 34 * (values 51 + values 56) + values 67 := by
      simp [sourceValue, reductionSourceIndex,
        Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h01]
      ring
    rw [identity, hsum] at source0
    simpa using source0
  have h25_21 : values 59 = 0 := by
    have identity :
        sourceValue values (reductionSourceIndex 2) =
          -(values 26 * (values 51 + values 56)) + values 59 := by
      simp [sourceValue, reductionSourceIndex,
        Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h01, h34, h35]
      ring
    rw [identity, hsum] at source1
    simpa using source1
  exact ⟨h34_21, h25_21⟩

/-- If the two secondary coefficients agree on the both-pivots-nonzero
chart, the canonical balanced amplitude at source row 733 forces the final
diagonal entry of edge 01 to vanish. -/
theorem w01_22_zero_of_equal_secondary
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (heq : values 31 = values 39) :
    values 2 = 0 := by
  have reductions := chart1_common_reductions values base hdet chart
  rcases reductions with
    ⟨_h13, h35, h34, _h34_10, _h25_10, _h25_12, _h34_12⟩
  rcases chart with ⟨h23, h12⟩
  have source : sourceValue values equalSecondarySourceIndex = 0 :=
    base equalSecondarySourceIndex equalSecondary_source_not_determinant
  simp [sourceValue, equalSecondarySourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h35, h34, heq] at source
  ring_nf at source
  have product : values 2 * ((-2 : R) * values 51 * values 56) = 0 := by
    linear_combination source
  exact (mul_eq_zero.mp product).resolve_right
    (mul_ne_zero (mul_ne_zero (by norm_num) h24) h25)

/-- Once both cycle pivots are nonzero, the diagonal coefficients on edges
`02` and `03` must sum to zero.  If their sum were nonzero, source row 646
would kill `w_45_11`; source row 648 would then kill the already-proved
nonzero factor `w_12_00 + w_13_00`. -/
theorem diagonal_sum_zero_of_both_pivots_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0) :
    values 4 + values 7 = 0 := by
  have reductions := chart1_common_reductions values base hdet chart
  rcases reductions with
    ⟨_h13, h35, h34, _h34_10, _h25_10, _h25_12, _h34_12⟩
  have h01 := w01_zero_of_both_pivots_nonzero
    values base hdet chart h24 h25
  obtain ⟨hL, _hGb, _hGa⟩ := noncollapse_factor_geometry values base hdet
  have source0 : sourceValue values (diagonalSumSourceIndex 0) = 0 :=
    base (diagonalSumSourceIndex 0)
      (fun slot => diagonal_sum_source_not_determinant 0 slot)
  have source1 : sourceValue values (diagonalSumSourceIndex 1) = 0 :=
    base (diagonalSumSourceIndex 1)
      (fun slot => diagonal_sum_source_not_determinant 1 slot)
  have product : values 73 * (values 4 + values 7) = 0 := by
    simp [sourceValue, diagonalSumSourceIndex,
      Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h34, h35] at source0
    linear_combination source0
  by_contra hsum
  have h45 : values 73 = 0 :=
    (mul_eq_zero.mp product).resolve_right hsum
  have hLzero : factorL values = 0 := by
    simp [sourceValue, diagonalSumSourceIndex,
      Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h01, h45,
      factorL] at source1 ⊢
    exact source1
  exact hL hLzero

/-- In the equal-secondary chart, the remaining nonzero `w_02_11` branch
is impossible.  Four mixed rows kill `w_14_22` and `w_15_22`; two further
rows then partition the colour-two monochromatic sum, giving `0 = 1`.

This is the kernel form of the three-row strict exact certificate on the
corresponding frozen chart. -/
theorem refutes_equal_secondary_w02_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (heq : values 31 = values 39)
    (h02 : values 4 ≠ 0) : False := by
  have reductions := chart1_common_reductions values base hdet chart
  rcases reductions with
    ⟨_h13, h35, h34, _h34_10, _h25_10, h25_12, h34_12⟩
  have h01_22 := w01_22_zero_of_equal_secondary
    values base hdet chart h24 h25 heq
  have hsum := diagonal_sum_zero_of_both_pivots_nonzero
    values base hdet chart h24 h25
  rcases chart with ⟨h23, _h12⟩
  have h03 : values 7 = -values 4 :=
    eq_neg_of_add_eq_zero_right hsum
  have sourceZero (index : Fin 5) :
      sourceValue values (diagonalNonzeroSourceIndex index) = 0 :=
    base (diagonalNonzeroSourceIndex index)
      (fun slot => diagonal_nonzero_source_not_determinant index slot)
  have source0 := sourceZero 0
  have source1 := sourceZero 1
  have source2 := sourceZero 2
  have source3 := sourceZero 3
  have source4 := sourceZero 4
  have h15_22 : values 46 = 0 := by
    have product : values 46 * ((-2 : R) * values 4 * values 51) = 0 := by
      calc
        values 46 * ((-2 : R) * values 4 * values 51) =
            sourceValue values (diagonalNonzeroSourceIndex 0) := by
          simp [sourceValue, diagonalNonzeroSourceIndex,
            Krenn.FrozenCase0System.equations,
            SparsePoly.toPoly, SparseTerm.toPoly,
            h23, h25_12, h34, h03, heq]
          ring
        _ = 0 := source0
    exact (mul_eq_zero.mp product).resolve_right
      (mul_ne_zero (mul_ne_zero (by norm_num) h02) h24)
  have h14_22 : values 43 = 0 := by
    have product : values 43 * ((-2 : R) * values 4 * values 56) = 0 := by
      calc
        values 43 * ((-2 : R) * values 4 * values 56) =
            sourceValue values (diagonalNonzeroSourceIndex 1) := by
          simp [sourceValue, diagonalNonzeroSourceIndex,
            Krenn.FrozenCase0System.equations,
            SparsePoly.toPoly, SparseTerm.toPoly,
            h23, h34_12, h35, h03, heq]
          ring
        _ = 0 := source1
    exact (mul_eq_zero.mp product).resolve_right
      (mul_ne_zero (mul_ne_zero (by norm_num) h02) h25)
  simp [sourceValue, diagonalNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly, h25_12] at source2
  simp [sourceValue, diagonalNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly, h34_12] at source3
  simp [sourceValue, diagonalNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h01_22, h14_22, h15_22] at source4
  have hzeroone : (0 : R) = 1 := by
    linear_combination source4 - values 32 * source2 - values 40 * source3
  exact zero_ne_one hzeroone

#print axioms w01_zero_of_both_pivots_nonzero
#print axioms sum_zero_linear_reductions
#print axioms w01_22_zero_of_equal_secondary
#print axioms diagonal_sum_zero_of_both_pivots_nonzero
#print axioms refutes_equal_secondary_w02_nonzero

end Krenn.FrozenCase0NoncollapseType01Chart1BothNonzero
