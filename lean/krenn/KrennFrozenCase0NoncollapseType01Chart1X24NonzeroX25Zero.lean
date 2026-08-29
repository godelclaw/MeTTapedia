import KrennFrozenCase0NoncollapseType01Chart1X24Zero
import KrennFrozenCase0NoncollapseType01Chart1X24NonzeroX25ZeroCertificate

/-!
Kernel connector for the strictly certified `w_24_11 != 0`, `w_25_11 = 0`
part of physical non-collapse type-01 pivot chart 1.

The semantic reductions are inherited from the common chart-1 proof.  Lean
then instantiates the 72-variable strict certificate from canonical case-0
values and proves that all 21 selected frozen equations vanish.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart1X24NonzeroX25Zero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart1X24Zero
open Krenn.FrozenCase0NoncollapseType01Chart1X24NonzeroX25ZeroCertificate
open Krenn.SparseCertificate
open MvPolynomial

def selectedSourceIndex : Fin 18 → Fin 747 := ![
  321, 187, 189, 653, 180, 601, 556, 280, 234,
  222, 646, 346, 745, 304, 354, 349, 343, 746
]

theorem selected_source_not_determinant
    (index : Fin 18) (slot : Fin 18) :
    determinantSourceIndex slot ≠ selectedSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, selectedSourceIndex]

noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 → R) : Fin 72 → R := ![
  slotDeterminant values 1,
  (factorGb values)⁻¹,
  (factorL values)⁻¹,
  (values 28)⁻¹,
  (slotDeterminant values 1)⁻¹,
  values 0, values 1, values 2,
  values 3, values 4, values 5,
  values 6, values 7, values 8,
  values 9, values 10, values 11, values 12, values 13,
  values 14, values 15, values 16,
  values 17, values 18, values 19, values 20, values 21,
  values 22, (values 23)⁻¹, values 24,
  values 25, values 26, values 27, values 28, values 29,
  values 30, values 31, values 32,
  values 33, values 34, values 35, values 37, values 38,
  values 39, values 40,
  values 41, values 42, values 43,
  values 44, values 45, values 46,
  values 47, values 49,
  values 50, values 51, (values 51)⁻¹, values 52,
  values 53, values 54,
  values 58, values 59, values 60,
  values 61, values 62, values 66, values 67, values 68,
  values 69, values 71,
  values 72, values 73, values 74
]

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The `w_24_11 != 0`, `w_25_11 = 0` part of type-01 pivot chart 1 is
impossible. -/
theorem refutes_slot1_chart1_w24_nonzero_w25_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25zero : values 56 = 0) : False := by
  have reductions := chart1_common_reductions values base hdet chart
  rcases reductions with
    ⟨h13, h35, h34, h34_10, h25_10, h25_12, h34_12⟩
  rcases chart with ⟨h23, h12⟩
  obtain ⟨hL, hGb, _hGa⟩ := noncollapse_factor_geometry values base hdet
  have hL' : values 25 + values 33 ≠ 0 := by
    simpa [factorL] using hL
  have hLInverse :
      (values 25 + values 33) * (values 25 + values 33)⁻¹ - 1 = 0 := by
    simp [hL']
  have sourceZero (index : Fin 18) :
      sourceValue values (selectedSourceIndex index) = 0 :=
    base (selectedSourceIndex index)
      (fun slot => selected_source_not_determinant index slot)
  have source0 := sourceZero 0
  have source1 := sourceZero 1
  have source2 := sourceZero 2
  have source3 := sourceZero 3
  have source4 := sourceZero 4
  have source5 := sourceZero 5
  have source6 := sourceZero 6
  have source7 := sourceZero 7
  have source8 := sourceZero 8
  have source9 := sourceZero 9
  have source10 := sourceZero 10
  have source11 := sourceZero 11
  have source12 := sourceZero 12
  have source13 := sourceZero 13
  have source14 := sourceZero 14
  have source15 := sourceZero 15
  have source16 := sourceZero 16
  have source17 := sourceZero 17
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source0
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source1
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source2
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source3
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source4
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source5
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source6
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source7
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source8
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source9
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source10
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source11
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source12
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source13
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source14
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source15
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source16
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h25zero, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source17
  apply selectedHasNoCommonZero (leafValues values)
  intro index
  fin_cases index
  all_goals
    simp [selectedEquations, selectedIndices,
      parentEquations, leafValues,
      sourceValue, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      slotDeterminant, slotA1, slotB1, slotA2, slotB2,
      factorL, factorGb,
      h23, h13, h25zero, h35, h34,
      h34_10, h25_10, h25_12, h34_12,
      hdet, hGb, hL, h12, h24]
  all_goals try assumption
  all_goals ring_nf at source0 source1 source2 source3 source4 source5 source6 source7 source8 source9 source10 source11 source12 source13 source14 source15 source16 source17 hLInverse ⊢
  all_goals assumption

#print axioms refutes_slot1_chart1_w24_nonzero_w25_zero

end Krenn.FrozenCase0NoncollapseType01Chart1X24NonzeroX25Zero
