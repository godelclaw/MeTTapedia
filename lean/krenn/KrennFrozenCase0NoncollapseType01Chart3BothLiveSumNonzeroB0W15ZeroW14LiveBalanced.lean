import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LivePropagation

/-!
The eight-row balanced syzygy closing the last `w_15_11 = 0`,
`w_14_11 ≠ 0` B0 subface.

This is the canonical-source form of the strict eight-row external leaf.  It
first derives the two `w_35` zeroes that the external monomial closure found,
then replays the same eight-row identity directly over canonical amplitudes.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LiveBalanced

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 500000
set_option maxHeartbeats 20000000

def sourceIndex : Fin 10 -> Fin 747 := ![729, 730, 175, 31, 25, 349, 333, 679, 336, 746]

theorem source_not_determinant
    (index : Fin 10) (slot : Fin 18) :
    determinantSourceIndex slot ≠ sourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, sourceIndex]

/-- Two monochromatic rows force the two `w_35` coordinates used by the
balanced leaf to vanish. -/
theorem w35_00_w35_22_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h02_11 : values 4 ≠ 0) (h14 : values 42 ≠ 0) :
    values 69 = 0 ∧ values 71 = 0 := by
  obtain ⟨h12_10, h13_12, h12_12, h01⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_reductions
      values base hdet chart h24 h25 hsum
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart h24 h25
  rcases chart with ⟨_, h12, _⟩
  have source729 : sourceValue values (sourceIndex 0) = 0 :=
    base (sourceIndex 0) (source_not_determinant 0)
  have h35_00 : values 69 = 0 := by
    have identity : sourceValue values (sourceIndex 0) = values 4 * values 42 * values 69 := by
      simp [sourceValue, sourceIndex, Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h01, h12, h13_10]
    rw [identity] at source729
    by_contra h35_00
    have product_zero : values 4 * values 42 = 0 :=
      (mul_eq_zero.mp source729).resolve_right h35_00
    exact h14 ((mul_eq_zero.mp product_zero).resolve_left h02_11)
  have source730 : sourceValue values (sourceIndex 1) = 0 :=
    base (sourceIndex 1) (source_not_determinant 1)
  have h35_22 : values 71 = 0 := by
    have identity : sourceValue values (sourceIndex 1) = values 4 * values 42 * values 71 := by
      simp [sourceValue, sourceIndex, Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h01, h12, h13_12]
    rw [identity] at source730
    by_contra h35_22
    have product_zero : values 4 * values 42 = 0 :=
      (mul_eq_zero.mp source730).resolve_right h35_22
    exact h14 ((mul_eq_zero.mp product_zero).resolve_left h02_11)
  exact ⟨h35_00, h35_22⟩

/-- The B0 face with `w_15_11 = 0`, `w_14_11 ≠ 0`, and live `w_02_11`
is impossible.  The proof is an exact eight-source-row identity. -/
theorem refutes_w15_zero_w14_live_w02_11_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h15 : values 45 = 0) (h14 : values 42 ≠ 0)
    (h02_11 : values 4 ≠ 0) : False := by
  obtain ⟨h12_10, h13_12, h12_12, h01⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_reductions
      values base hdet chart h24 h25 hsum
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart h24 h25
  obtain ⟨h03_00, h23_22, h03_11, h03_22, h23_00⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LivePropagation.forced_zeros
      values base hdet chart h24 h25 hsum h15 h14
  obtain ⟨_, h35_22⟩ :=
    w35_00_w35_22_zero values base hdet chart h24 h25 hsum h02_11 h14
  rcases chart with ⟨h23, h12, h13⟩
  have h175 : sourceValue values (sourceIndex 2) = 0 :=
    base (sourceIndex 2) (source_not_determinant 2)
  have h31 : sourceValue values (sourceIndex 3) = 0 :=
    base (sourceIndex 3) (source_not_determinant 3)
  have h25row : sourceValue values (sourceIndex 4) = 0 :=
    base (sourceIndex 4) (source_not_determinant 4)
  have h349 : sourceValue values (sourceIndex 5) = 0 :=
    base (sourceIndex 5) (source_not_determinant 5)
  have h333 : sourceValue values (sourceIndex 6) = 0 :=
    base (sourceIndex 6) (source_not_determinant 6)
  have h679 : sourceValue values (sourceIndex 7) = 0 :=
    base (sourceIndex 7) (source_not_determinant 7)
  have h336 : sourceValue values (sourceIndex 8) = 0 :=
    base (sourceIndex 8) (source_not_determinant 8)
  have h746 : sourceValue values (sourceIndex 9) = 0 :=
    base (sourceIndex 9) (source_not_determinant 9)
  let combo :=
      values 26 * values 38 * values 68 * sourceValue values (sourceIndex 2)
    - values 26 * values 40 * sourceValue values (sourceIndex 3)
    - values 38 * values 68 * sourceValue values (sourceIndex 4)
    + values 40 * sourceValue values (sourceIndex 5)
    - values 26 * values 68 * sourceValue values (sourceIndex 6)
    + values 26 * sourceValue values (sourceIndex 7)
    + values 68 * sourceValue values (sourceIndex 8)
    - sourceValue values (sourceIndex 9)
  have combo_zero : combo = 0 := by
    simp [combo, h175, h31, h25row, h349, h333, h679, h336, h746]
  have combo_one : combo = 1 := by
    dsimp [combo]
    simp [sourceValue, sourceIndex, Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h23_22, h03_22, h35_22]
    ring
  have one_zero : (1 : R) = 0 := combo_one.symm.trans combo_zero
  norm_num at one_zero

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LiveBalanced.w35_00_w35_22_zero
#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LiveBalanced.refutes_w15_zero_w14_live_w02_11_live

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15ZeroW14LiveBalanced
