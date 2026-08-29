import KrennFrozenCase0NoncollapseType01Chart3BothLive

/-!
A structural closure for the remaining chart-3 branches with live
`w_01_11` and zero `w_15_11`.

The earlier chart-3 reduction forces `w_12_10 = 0`.  After that, the only
apparent distinction is whether `w_12_12` vanishes.  Each side has a short
canonical zero-propagation chain ending in amplitude row 644, which becomes
`w_01_11 * w_25_11 = 0`.  Both factors are live in the surviving geometry.

This closes both sides without using a terminal CAS certificate or the
pivot-sum equality.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3W01LiveW15Zero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def zeroW12SourceIndex : Fin 11 -> Fin 747 :=
  ![160, 161, 162, 163, 325, 326, 327, 328, 329, 410, 644]

def liveW12SourceIndex : Fin 10 -> Fin 747 :=
  ![46, 125, 162, 163, 250, 325, 327, 328, 488, 644]

theorem zero_w12_source_not_determinant
    (index : Fin 11) (slot : Fin 18) :
    determinantSourceIndex slot ≠ zeroW12SourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, zeroW12SourceIndex]

theorem live_w12_source_not_determinant
    (index : Fin 10) (slot : Fin 18) :
    determinantSourceIndex slot ≠ liveW12SourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, liveW12SourceIndex]

/-- With `w_12_12 = 0`, the displayed ten source rows reduce to a direct
contradiction in row 644. -/
theorem refutes_zero_w12
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (h13_12 : values 37 = 0)
    (h01 : values 1 ≠ 0) (h15 : values 45 = 0)
    (h12_12 : values 29 = 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have chart' : PivotChart3 values := ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart' h24 h25
  have h12_10 : values 27 = 0 :=
    Krenn.FrozenCase0NoncollapseType01Chart3W12_10Live.w12_10_zero_of_chart3
      values base hdet chart'
  have source0 : sourceValue values (zeroW12SourceIndex 0) = 0 :=
    base (zeroW12SourceIndex 0) (zero_w12_source_not_determinant 0)
  have h25_21 : values 59 = 0 := by
    have identity : sourceValue values (zeroW12SourceIndex 0) = values 1 * values 59 := by
      simp [sourceValue, zeroW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h12_12, h13_12, h15]
    rw [identity] at source0
    exact (mul_eq_zero.mp source0).resolve_left h01
  have source1 : sourceValue values (zeroW12SourceIndex 1) = 0 :=
    base (zeroW12SourceIndex 1) (zero_w12_source_not_determinant 1)
  have h25_22 : values 60 = 0 := by
    have identity : sourceValue values (zeroW12SourceIndex 1) = values 1 * values 60 := by
      simp [sourceValue, zeroW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h12_12, h13_12, h15]
    rw [identity] at source1
    exact (mul_eq_zero.mp source1).resolve_left h01
  have source2 : sourceValue values (zeroW12SourceIndex 2) = 0 :=
    base (zeroW12SourceIndex 2) (zero_w12_source_not_determinant 2)
  have h34_21 : values 67 = 0 := by
    have identity : sourceValue values (zeroW12SourceIndex 2) = values 1 * values 67 := by
      simp [sourceValue, zeroW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h12_12, h13_12, h15]
    rw [identity] at source2
    exact (mul_eq_zero.mp source2).resolve_left h01
  have source3 : sourceValue values (zeroW12SourceIndex 3) = 0 :=
    base (zeroW12SourceIndex 3) (zero_w12_source_not_determinant 3)
  have h34_22 : values 68 = 0 := by
    have identity : sourceValue values (zeroW12SourceIndex 3) = values 1 * values 68 := by
      simp [sourceValue, zeroW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h12_12, h13_12, h15]
    rw [identity] at source3
    exact (mul_eq_zero.mp source3).resolve_left h01
  have source4 : sourceValue values (zeroW12SourceIndex 4) = 0 :=
    base (zeroW12SourceIndex 4) (zero_w12_source_not_determinant 4)
  have h25_12 : values 57 = 0 := by
    have identity : sourceValue values (zeroW12SourceIndex 4) = values 1 * values 57 := by
      simp [sourceValue, zeroW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h12_12, h13_12, h15]
    rw [identity] at source4
    exact (mul_eq_zero.mp source4).resolve_left h01
  have source5 : sourceValue values (zeroW12SourceIndex 5) = 0 :=
    base (zeroW12SourceIndex 5) (zero_w12_source_not_determinant 5)
  have h25_20 : values 58 = 0 := by
    have identity : sourceValue values (zeroW12SourceIndex 5) = values 1 * values 58 := by
      simp [sourceValue, zeroW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h12_12, h13_12, h15]
    rw [identity] at source5
    exact (mul_eq_zero.mp source5).resolve_left h01
  have source6 : sourceValue values (zeroW12SourceIndex 6) = 0 :=
    base (zeroW12SourceIndex 6) (zero_w12_source_not_determinant 6)
  have h34_02 : values 62 = 0 := by
    have identity : sourceValue values (zeroW12SourceIndex 6) = values 1 * values 62 := by
      simp [sourceValue, zeroW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h12_12, h13_12, h15]
    rw [identity] at source6
    exact (mul_eq_zero.mp source6).resolve_left h01
  have source7 : sourceValue values (zeroW12SourceIndex 7) = 0 :=
    base (zeroW12SourceIndex 7) (zero_w12_source_not_determinant 7)
  have h34_12 : values 65 = 0 := by
    have identity : sourceValue values (zeroW12SourceIndex 7) = values 1 * values 65 := by
      simp [sourceValue, zeroW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h12_12, h13_12, h15]
    rw [identity] at source7
    exact (mul_eq_zero.mp source7).resolve_left h01
  have source8 : sourceValue values (zeroW12SourceIndex 8) = 0 :=
    base (zeroW12SourceIndex 8) (zero_w12_source_not_determinant 8)
  have h34_20 : values 66 = 0 := by
    have identity : sourceValue values (zeroW12SourceIndex 8) = values 1 * values 66 := by
      simp [sourceValue, zeroW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h12_12, h13_12, h15]
    rw [identity] at source8
    exact (mul_eq_zero.mp source8).resolve_left h01
  have source9 : sourceValue values (zeroW12SourceIndex 9) = 0 :=
    base (zeroW12SourceIndex 9) (zero_w12_source_not_determinant 9)
  have h34_00 : values 61 = 0 := by
    have identity : sourceValue values (zeroW12SourceIndex 9) =
        values 1 * values 56 * values 61 := by
      simp [sourceValue, zeroW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h12_12, h13_12, h15,
        h25_21, h25_22, h34_21, h34_22, h25_12, h25_20,
        h34_02, h34_12, h34_20]
    rw [identity] at source9
    exact (mul_eq_zero.mp source9).resolve_left (mul_ne_zero h01 h25)
  have source10 : sourceValue values (zeroW12SourceIndex 10) = 0 :=
    base (zeroW12SourceIndex 10) (zero_w12_source_not_determinant 10)
  have identity : sourceValue values (zeroW12SourceIndex 10) = values 1 * values 56 := by
    simp [sourceValue, zeroW12SourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h23, h12, h13, h13_10, h12_10, h12_12, h13_12, h15,
      h25_21, h25_22, h34_21, h34_22, h25_12, h25_20,
      h34_02, h34_12, h34_20, h34_00]
  rw [identity] at source10
  exact (mul_eq_zero.mp source10).elim h01 h25

/-- With `w_12_12` live, a different nine-row canonical propagation chain
again reduces row 644 to the product of two live pivots. -/
theorem refutes_live_w12
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (h13_12 : values 37 = 0)
    (h01 : values 1 ≠ 0) (h15 : values 45 = 0)
    (h12_12 : values 29 ≠ 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have chart' : PivotChart3 values := ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart' h24 h25
  have h12_10 : values 27 = 0 :=
    Krenn.FrozenCase0NoncollapseType01Chart3W12_10Live.w12_10_zero_of_chart3
      values base hdet chart'
  have source0 : sourceValue values (liveW12SourceIndex 0) = 0 :=
    base (liveW12SourceIndex 0) (live_w12_source_not_determinant 0)
  have h34_00 : values 61 = 0 := by
    have identity : sourceValue values (liveW12SourceIndex 0) = values 29 * values 61 := by
      simp [sourceValue, liveW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h13_12, h15]
    rw [identity] at source0
    exact (mul_eq_zero.mp source0).resolve_left h12_12
  have source1 : sourceValue values (liveW12SourceIndex 1) = 0 :=
    base (liveW12SourceIndex 1) (live_w12_source_not_determinant 1)
  have h05_22 : values 24 = 0 := by
    have identity : sourceValue values (liveW12SourceIndex 1) = values 24 * values 29 := by
      simp [sourceValue, liveW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h13_12, h15]
    rw [identity] at source1
    exact (mul_eq_zero.mp source1).resolve_right h12_12
  have source2 : sourceValue values (liveW12SourceIndex 2) = 0 :=
    base (liveW12SourceIndex 2) (live_w12_source_not_determinant 2)
  have h34_21 : values 67 = 0 := by
    have identity : sourceValue values (liveW12SourceIndex 2) = values 1 * values 67 := by
      simp [sourceValue, liveW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h13_12, h15]
    rw [identity] at source2
    exact (mul_eq_zero.mp source2).resolve_left h01
  have source3 : sourceValue values (liveW12SourceIndex 3) = 0 :=
    base (liveW12SourceIndex 3) (live_w12_source_not_determinant 3)
  have h34_22 : values 68 = 0 := by
    have identity : sourceValue values (liveW12SourceIndex 3) = values 1 * values 68 := by
      simp [sourceValue, liveW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h13_12, h15]
    rw [identity] at source3
    exact (mul_eq_zero.mp source3).resolve_left h01
  have source4 : sourceValue values (liveW12SourceIndex 4) = 0 :=
    base (liveW12SourceIndex 4) (live_w12_source_not_determinant 4)
  have h34_20 : values 66 = 0 := by
    have identity : sourceValue values (liveW12SourceIndex 4) = values 29 * values 66 := by
      simp [sourceValue, liveW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h13_12, h15]
    rw [identity] at source4
    exact (mul_eq_zero.mp source4).resolve_left h12_12
  have source5 : sourceValue values (liveW12SourceIndex 5) = 0 :=
    base (liveW12SourceIndex 5) (live_w12_source_not_determinant 5)
  have h25_12 : values 57 = 0 := by
    have identity : sourceValue values (liveW12SourceIndex 5) = values 1 * values 57 := by
      simp [sourceValue, liveW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h13_12, h15]
    rw [identity] at source5
    exact (mul_eq_zero.mp source5).resolve_left h01
  have source6 : sourceValue values (liveW12SourceIndex 6) = 0 :=
    base (liveW12SourceIndex 6) (live_w12_source_not_determinant 6)
  have h34_02 : values 62 = 0 := by
    have identity : sourceValue values (liveW12SourceIndex 6) = values 1 * values 62 := by
      simp [sourceValue, liveW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h13_12, h15]
    rw [identity] at source6
    exact (mul_eq_zero.mp source6).resolve_left h01
  have source7 : sourceValue values (liveW12SourceIndex 7) = 0 :=
    base (liveW12SourceIndex 7) (live_w12_source_not_determinant 7)
  have h34_12 : values 65 = 0 := by
    have identity : sourceValue values (liveW12SourceIndex 7) = values 1 * values 65 := by
      simp [sourceValue, liveW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h13_12, h15]
    rw [identity] at source7
    exact (mul_eq_zero.mp source7).resolve_left h01
  have source8 : sourceValue values (liveW12SourceIndex 8) = 0 :=
    base (liveW12SourceIndex 8) (live_w12_source_not_determinant 8)
  have h05_21 : values 23 = 0 := by
    have identity : sourceValue values (liveW12SourceIndex 8) = values 23 * values 29 := by
      simp [sourceValue, liveW12SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h13_12, h15]
    rw [identity] at source8
    exact (mul_eq_zero.mp source8).resolve_right h12_12
  have source9 : sourceValue values (liveW12SourceIndex 9) = 0 :=
    base (liveW12SourceIndex 9) (live_w12_source_not_determinant 9)
  have identity : sourceValue values (liveW12SourceIndex 9) = values 1 * values 56 := by
    simp [sourceValue, liveW12SourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h23, h12, h13, h13_10, h12_10, h13_12, h15,
      h34_00, h05_22, h34_21, h34_22, h34_20, h25_12,
      h34_02, h34_12, h05_21]
  rw [identity] at source9
  exact (mul_eq_zero.mp source9).elim h01 h25

/-- The two `w_12_12` cases exhaust this branch, so no certificate leaf
survives when `w_01_11` is live, `w_15_11` is zero, and `w_13_12` is zero. -/
theorem refutes_chart3_w01_live_w15_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (h13_12 : values 37 = 0)
    (h01 : values 1 ≠ 0) (h15 : values 45 = 0) : False := by
  by_cases h12_12 : values 29 = 0
  · exact refutes_zero_w12 values base hdet chart h24 h25 h13_12 h01 h15 h12_12
  · exact refutes_live_w12 values base hdet chart h24 h25 h13_12 h01 h15 h12_12

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3W01LiveW15Zero.refutes_zero_w12
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3W01LiveW15Zero.refutes_live_w12
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3W01LiveW15Zero.refutes_chart3_w01_live_w15_zero

end Krenn.FrozenCase0NoncollapseType01Chart3W01LiveW15Zero
