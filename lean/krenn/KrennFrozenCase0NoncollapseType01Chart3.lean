import KrennFrozenCase0NoncollapseType01Pivot

/-!
The structural first split for pivot chart 3 of physical non-collapse type
01.  On this chart the three middle-colour pivot entries vanish.  The two
opposite pivots `w_24_11` and `w_25_11` cannot both vanish, because their
vanishing would force the already-proved non-collapse factor `Gb` to vanish.

The remaining three zero/nonzero leaves are deliberately left explicit;
they require separate exact certificates or further structural splits.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The numeric coordinates used by the opposite-pivot split are tied to
the variable inventory exported from the same byte-hashed frozen system as
the canonical equations. -/
theorem opposite_pivot_coordinate_names :
    Krenn.FrozenCase0System.variableNames 51 = "w_24_11" ∧
      Krenn.FrozenCase0System.variableNames 56 = "w_25_11" := by
  decide

theorem source180_not_determinant (slot : Fin 18) :
    determinantSourceIndex slot ≠ (180 : Fin 747) := by
  fin_cases slot <;> simp [determinantSourceIndex]

theorem source502_not_determinant (slot : Fin 18) :
    determinantSourceIndex slot ≠ (502 : Fin 747) := by
  fin_cases slot <;> simp [determinantSourceIndex]

/-- Canonical row 302 is an amplitude row, not one of the eighteen
all-collapse determinants omitted from `BaseCommonZero`. -/
theorem source302_not_determinant (slot : Fin 18) :
    determinantSourceIndex slot ≠ (302 : Fin 747) := by
  fin_cases slot <;> simp [determinantSourceIndex]

def nonzeroW13SourceIndex : Fin 5 → Fin 747 := ![44, 66, 115, 302, 137]

def nonzeroW14SourceIndex : Fin 2 → Fin 747 := ![709, 714]

def w14ZeroSourceIndex : Fin 2 → Fin 747 := ![644, 745]

def nonzeroW23_22SourceIndex : Fin 4 → Fin 747 := ![315, 602, 540, 362]

def nonzeroW01_11SourceIndex : Fin 4 → Fin 747 := ![325, 326, 160, 161]

def nonzeroW03_11SourceIndex : Fin 5 → Fin 747 := ![666, 670, 418, 671, 426]

def nonzeroW02_11SourceIndex : Fin 3 → Fin 747 := ![729, 644, 730]

/-- The three canonical amplitude rows that, after the chart-3 and
both-live reductions, are respectively `w_01_11 * w_25_12`,
`w_01_11 * w_25_21`, and `w_01_11 * w_25_22`. -/
def w25TailSourceIndex : Fin 3 → Fin 747 := ![325, 160, 161]

theorem nonzero_w13_source_not_determinant
    (index : Fin 5) (slot : Fin 18) :
    determinantSourceIndex slot ≠ nonzeroW13SourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, nonzeroW13SourceIndex]

theorem nonzero_w14_source_not_determinant
    (index : Fin 2) (slot : Fin 18) :
    determinantSourceIndex slot ≠ nonzeroW14SourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, nonzeroW14SourceIndex]

theorem w14_zero_source_not_determinant
    (index : Fin 2) (slot : Fin 18) :
    determinantSourceIndex slot ≠ w14ZeroSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, w14ZeroSourceIndex]

theorem nonzero_w23_22_source_not_determinant
    (index : Fin 4) (slot : Fin 18) :
    determinantSourceIndex slot ≠ nonzeroW23_22SourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, nonzeroW23_22SourceIndex]

theorem nonzero_w01_11_source_not_determinant
    (index : Fin 4) (slot : Fin 18) :
    determinantSourceIndex slot ≠ nonzeroW01_11SourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, nonzeroW01_11SourceIndex]

theorem nonzero_w03_11_source_not_determinant
    (index : Fin 5) (slot : Fin 18) :
    determinantSourceIndex slot ≠ nonzeroW03_11SourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, nonzeroW03_11SourceIndex]

theorem nonzero_w02_11_source_not_determinant
    (index : Fin 3) (slot : Fin 18) :
    determinantSourceIndex slot ≠ nonzeroW02_11SourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, nonzeroW02_11SourceIndex]

theorem w25_tail_source_not_determinant
    (index : Fin 3) (slot : Fin 18) :
    determinantSourceIndex slot ≠ w25TailSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, w25TailSourceIndex]

/-- In pivot chart 3, `w_24_11` and `w_25_11` cannot both vanish. -/
theorem opposite_pivots_not_both_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (_chart : PivotChart3 values)
    (h24 : values 51 = 0) (h25 : values 56 = 0) : False := by
  obtain ⟨_hL, hGb, _hGa⟩ := noncollapse_factor_geometry values base hdet
  apply hGb
  simp [factorGb, h24, h25]

/-- The exhaustive surviving geometry after removing the impossible
both-zero leaf. -/
theorem opposite_pivot_cover
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values) :
    (values 51 = 0 ∧ values 56 ≠ 0) ∨
      (values 51 ≠ 0 ∧ values 56 = 0) ∨
      (values 51 ≠ 0 ∧ values 56 ≠ 0) := by
  by_cases h24 : values 51 = 0
  · by_cases h25 : values 56 = 0
    · exact (opposite_pivots_not_both_zero values base hdet chart h24 h25).elim
    · exact Or.inl ⟨h24, h25⟩
  · by_cases h25 : values 56 = 0
    · exact Or.inr (Or.inl ⟨h24, h25⟩)
    · exact Or.inr (Or.inr ⟨h24, h25⟩)

/-- In the both-pivots-live chart, row 302 is exactly
`w_13_10 * Gb`.  Since non-collapse makes `Gb` nonzero, this proves the
previously external reduction `w_13_10 = 0` directly from the canonical
base system. -/
theorem w13_10_zero_of_both_opposite_pivots_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (_h24 : values 51 ≠ 0) (_h25 : values 56 ≠ 0) : values 35 = 0 := by
  obtain ⟨_hL, hGb, _hGa⟩ := noncollapse_factor_geometry values base hdet
  have source : sourceValue values 302 = 0 :=
    base 302 source302_not_determinant
  rcases chart with ⟨_h23, h12, _h13⟩
  have identity : sourceValue values 302 = values 35 * factorGb values := by
    simp [sourceValue, Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      factorGb, h12]
    ring
  rw [identity] at source
  exact (mul_eq_zero.mp source).resolve_right hGb

/-- The previously external `tailzeros` reduction is a direct canonical
consequence.  In the both-pivots-live branch, once `w_12_12` vanishes, the
nonzero `w_01_11` pivot forces
the three named tail coordinates of edge 25 to vanish. -/
theorem w25_tail_zero_of_both_opposite_pivots_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (h12_12 : values 29 = 0)
    (h01_11 : values 1 ≠ 0) :
    values 57 = 0 ∧ values 59 = 0 ∧ values 60 = 0 := by
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live
      values base hdet chart h24 h25
  rcases chart with ⟨_h23, h12_11, _h13_11⟩
  have source0 : sourceValue values (w25TailSourceIndex 0) = 0 :=
    base (w25TailSourceIndex 0) (w25_tail_source_not_determinant 0)
  have source1 : sourceValue values (w25TailSourceIndex 1) = 0 :=
    base (w25TailSourceIndex 1) (w25_tail_source_not_determinant 1)
  have source2 : sourceValue values (w25TailSourceIndex 2) = 0 :=
    base (w25TailSourceIndex 2) (w25_tail_source_not_determinant 2)
  have h25_12 : values 57 = 0 := by
    have identity : sourceValue values (w25TailSourceIndex 0) =
        values 1 * values 57 := by
      simp [sourceValue, w25TailSourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h12_11, h13_10]
    rw [identity] at source0
    exact (mul_eq_zero.mp source0).resolve_left h01_11
  have h25_21 : values 59 = 0 := by
    have identity : sourceValue values (w25TailSourceIndex 1) =
        values 1 * values 59 := by
      simp [sourceValue, w25TailSourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h13_10, h12_12]
    rw [identity] at source1
    exact (mul_eq_zero.mp source1).resolve_left h01_11
  have h25_22 : values 60 = 0 := by
    have identity : sourceValue values (w25TailSourceIndex 2) =
        values 1 * values 60 := by
      simp [sourceValue, w25TailSourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h13_10, h12_12]
    rw [identity] at source2
    exact (mul_eq_zero.mp source2).resolve_left h01_11
  exact ⟨h25_12, h25_21, h25_22⟩

/-- If only `w_25_11` survives, canonical amplitude row 180 forces
`w_13_12 = 0`. -/
theorem w13_12_zero_of_w24_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (_hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 = 0) (h25 : values 56 ≠ 0) : values 37 = 0 := by
  rcases chart with ⟨_h23, h12, _h13⟩
  have source : sourceValue values 180 = 0 :=
    base 180 source180_not_determinant
  simp (config := { maxSteps := 3000000 }) [sourceValue,
    Krenn.FrozenCase0System.equations,
    Krenn.SparseCertificate.SparsePoly.toPoly,
    Krenn.SparseCertificate.SparseTerm.toPoly,
    h12, h24] at source
  exact source.resolve_right h25

/-- If only `w_24_11` survives, the same canonical amplitude row forces
`w_13_12 = 0`. -/
theorem w13_12_zero_of_w25_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (_hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 = 0) : values 37 = 0 := by
  rcases chart with ⟨_h23, h12, _h13⟩
  have source : sourceValue values 180 = 0 :=
    base 180 source180_not_determinant
  simp (config := { maxSteps := 3000000 }) [sourceValue,
    Krenn.FrozenCase0System.equations,
    Krenn.SparseCertificate.SparsePoly.toPoly,
    Krenn.SparseCertificate.SparseTerm.toPoly,
    h12, h25] at source
  exact source.resolve_right h24

/-- On the `w_24_11 = 0`, `w_25_11 ≠ 0` leaf, a nonzero
`w_13_10` forces the entire even-colour column of edge 04 to vanish.
These are five direct canonical amplitude consequences. -/
theorem w04_even_column_zero_of_w13_10_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (_hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 = 0) (h25 : values 56 ≠ 0)
    (h13_10 : values 35 ≠ 0) :
    values 9 = 0 ∧ values 10 = 0 ∧ values 14 = 0 ∧
      values 15 = 0 ∧ values 16 = 0 := by
  rcases chart with ⟨_h23, h12, _h13⟩
  have source0 : sourceValue values (nonzeroW13SourceIndex 0) = 0 :=
    base (nonzeroW13SourceIndex 0)
      (nonzero_w13_source_not_determinant 0)
  have source1 : sourceValue values (nonzeroW13SourceIndex 1) = 0 :=
    base (nonzeroW13SourceIndex 1)
      (nonzero_w13_source_not_determinant 1)
  have source2 : sourceValue values (nonzeroW13SourceIndex 2) = 0 :=
    base (nonzeroW13SourceIndex 2)
      (nonzero_w13_source_not_determinant 2)
  have source3 : sourceValue values (nonzeroW13SourceIndex 3) = 0 :=
    base (nonzeroW13SourceIndex 3)
      (nonzero_w13_source_not_determinant 3)
  have source4 : sourceValue values (nonzeroW13SourceIndex 4) = 0 :=
    base (nonzeroW13SourceIndex 4)
      (nonzero_w13_source_not_determinant 4)
  have nonzeroFactor : values 35 * values 56 ≠ 0 :=
    mul_ne_zero h13_10 h25
  have h0 : values 9 = 0 := by
    have identity :
        sourceValue values (nonzeroW13SourceIndex 0) =
          values 9 * (values 35 * values 56) := by
      simp [sourceValue, nonzeroW13SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h12]
      ring
    rw [identity] at source0
    exact (mul_eq_zero.mp source0).resolve_right nonzeroFactor
  have h1 : values 10 = 0 := by
    have identity :
        sourceValue values (nonzeroW13SourceIndex 1) =
          values 10 * (values 35 * values 56) := by
      simp [sourceValue, nonzeroW13SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h12]
      ring
    rw [identity] at source1
    exact (mul_eq_zero.mp source1).resolve_right nonzeroFactor
  have h2 : values 14 = 0 := by
    have identity :
        sourceValue values (nonzeroW13SourceIndex 2) =
          values 14 * (values 35 * values 56) := by
      simp [sourceValue, nonzeroW13SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h12]
      ring
    rw [identity] at source2
    exact (mul_eq_zero.mp source2).resolve_right nonzeroFactor
  have h3 : values 15 = 0 := by
    have identity :
        sourceValue values (nonzeroW13SourceIndex 3) =
          values 15 * (values 35 * values 56) := by
      simp [sourceValue, nonzeroW13SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h12, h24]
      ring
    rw [identity] at source3
    exact (mul_eq_zero.mp source3).resolve_right nonzeroFactor
  have h4 : values 16 = 0 := by
    have identity :
        sourceValue values (nonzeroW13SourceIndex 4) =
          values 16 * (values 35 * values 56) := by
      simp [sourceValue, nonzeroW13SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h12]
      ring
    rw [identity] at source4
    exact (mul_eq_zero.mp source4).resolve_right nonzeroFactor
  exact ⟨h0, h1, h2, h3, h4⟩

/-- The nonzero `w_13_10` half of the exactly-one-pivot leaf is impossible.
The forced `w_04_21 = 0`, together with `w_24_11 = 0`, makes `Gb` vanish. -/
theorem refutes_w24_zero_w13_10_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 = 0) (h25 : values 56 ≠ 0)
    (h13_10 : values 35 ≠ 0) : False := by
  obtain ⟨_h0, _h1, _h2, h04_21, _h4⟩ :=
    w04_even_column_zero_of_w13_10_nonzero
      values base hdet chart h24 h25 h13_10
  obtain ⟨_hL, hGb, _hGa⟩ := noncollapse_factor_geometry values base hdet
  apply hGb
  simp [factorGb, h24, h04_21]

/-- Consequently the exactly-one-pivot leaf reduces structurally to
`w_13_10 = 0`. -/
theorem w13_10_zero_of_w24_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 = 0) (h25 : values 56 ≠ 0) : values 35 = 0 := by
  by_contra h13_10
  exact refutes_w24_zero_w13_10_nonzero
    values base hdet chart h24 h25 h13_10

/-- After the two `w_13` reductions on the exactly-one-pivot leaf, a
nonzero `w_14_11` forces both diagonal ends of edge 03 to vanish. -/
theorem w03_ends_zero_of_w14_11_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (_hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 = 0) (h25 : values 56 ≠ 0)
    (h13_12 : values 37 = 0) (h13_10 : values 35 = 0)
    (h14_11 : values 42 ≠ 0) : values 6 = 0 ∧ values 8 = 0 := by
  rcases chart with ⟨_h23, h12, _h13⟩
  have source0 : sourceValue values (nonzeroW14SourceIndex 0) = 0 :=
    base (nonzeroW14SourceIndex 0)
      (nonzero_w14_source_not_determinant 0)
  have source1 : sourceValue values (nonzeroW14SourceIndex 1) = 0 :=
    base (nonzeroW14SourceIndex 1)
      (nonzero_w14_source_not_determinant 1)
  have nonzeroFactor : values 42 * values 56 ≠ 0 :=
    mul_ne_zero h14_11 h25
  have h03_00 : values 6 = 0 := by
    have identity :
        sourceValue values (nonzeroW14SourceIndex 0) =
          values 6 * (values 42 * values 56) := by
      simp [sourceValue, nonzeroW14SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h12, h24, h13_10]
      ring
    rw [identity] at source0
    exact (mul_eq_zero.mp source0).resolve_right nonzeroFactor
  have h03_22 : values 8 = 0 := by
    have identity :
        sourceValue values (nonzeroW14SourceIndex 1) =
          values 8 * (values 42 * values 56) := by
      simp [sourceValue, nonzeroW14SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h12, h24, h13_12]
      ring
    rw [identity] at source1
    exact (mul_eq_zero.mp source1).resolve_right nonzeroFactor
  exact ⟨h03_00, h03_22⟩

/-- If `w_14_11` also vanishes, canonical rows 644 and 745 become
`E = 0` and `w_34_11 * E - 1 = 0`, an immediate contradiction. -/
theorem refutes_w24_zero_w13_10_zero_w14_11_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (_hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 = 0) (h13_10 : values 35 = 0)
    (h14_11 : values 42 = 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have source0 : sourceValue values (w14ZeroSourceIndex 0) = 0 :=
    base (w14ZeroSourceIndex 0) (w14_zero_source_not_determinant 0)
  have source1 : sourceValue values (w14ZeroSourceIndex 1) = 0 :=
    base (w14ZeroSourceIndex 1) (w14_zero_source_not_determinant 1)
  have identity :
      sourceValue values (w14ZeroSourceIndex 1) =
        values 64 * sourceValue values (w14ZeroSourceIndex 0) - 1 := by
    simp [sourceValue, w14ZeroSourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h23, h12, h13, h24, h13_10, h14_11]
    ring
  rw [identity, source0] at source1
  norm_num at source1

/-- On the surviving nonzero-`w_14_11` leaf, canonical row 502 reduces
literally to `w_12_12`. -/
theorem w12_12_zero_of_w03_00_zero_w13_10_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (_hdet : slotDeterminant values 1 ≠ 0)
    (h03_00 : values 6 = 0) (h13_10 : values 35 = 0) :
    values 29 = 0 := by
  have source : sourceValue values 502 = 0 :=
    base 502 source502_not_determinant
  simpa [sourceValue, Krenn.FrozenCase0System.equations,
    Krenn.SparseCertificate.SparsePoly.toPoly,
    Krenn.SparseCertificate.SparseTerm.toPoly,
    h03_00, h13_10] using source

/-- If `w_23_22` survives on the last exactly-one-pivot subchart, three
edge-05 entries vanish and `w_15_11 = -w_14_11`. -/
theorem reductions_of_w23_22_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (_hdet : slotDeterminant values 1 ≠ 0)
    (h13_12 : values 37 = 0) (h12_12 : values 29 = 0)
    (h03_22 : values 8 = 0)
    (h14_11 : values 42 ≠ 0) (h23_22 : values 49 ≠ 0) :
    values 17 = 0 ∧ values 18 = 0 ∧ values 22 = 0 ∧
      values 45 = -values 42 := by
  have source0 : sourceValue values (nonzeroW23_22SourceIndex 0) = 0 :=
    base (nonzeroW23_22SourceIndex 0)
      (nonzero_w23_22_source_not_determinant 0)
  have source1 : sourceValue values (nonzeroW23_22SourceIndex 1) = 0 :=
    base (nonzeroW23_22SourceIndex 1)
      (nonzero_w23_22_source_not_determinant 1)
  have source2 : sourceValue values (nonzeroW23_22SourceIndex 2) = 0 :=
    base (nonzeroW23_22SourceIndex 2)
      (nonzero_w23_22_source_not_determinant 2)
  have source3 : sourceValue values (nonzeroW23_22SourceIndex 3) = 0 :=
    base (nonzeroW23_22SourceIndex 3)
      (nonzero_w23_22_source_not_determinant 3)
  have nonzeroFactor : values 42 * values 49 ≠ 0 :=
    mul_ne_zero h14_11 h23_22
  have h05_00 : values 17 = 0 := by
    have identity :
        sourceValue values (nonzeroW23_22SourceIndex 0) =
          values 17 * (values 42 * values 49) := by
      simp [sourceValue, nonzeroW23_22SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h13_12, h12_12]
      ring
    rw [identity] at source0
    exact (mul_eq_zero.mp source0).resolve_right nonzeroFactor
  have h05_02 : values 18 = 0 := by
    have identity :
        sourceValue values (nonzeroW23_22SourceIndex 1) =
          values 18 * (values 42 * values 49) := by
      simp [sourceValue, nonzeroW23_22SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h13_12, h12_12]
      ring
    rw [identity] at source1
    exact (mul_eq_zero.mp source1).resolve_right nonzeroFactor
  have h05_20 : values 22 = 0 := by
    have identity :
        sourceValue values (nonzeroW23_22SourceIndex 2) =
          values 22 * (values 42 * values 49) := by
      simp [sourceValue, nonzeroW23_22SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h13_12, h12_12, h03_22]
      ring
    rw [identity] at source2
    exact (mul_eq_zero.mp source2).resolve_right nonzeroFactor
  have h15_11 : values 45 = -values 42 := by
    have identity :
        sourceValue values (nonzeroW23_22SourceIndex 3) =
          (values 42 + values 45) * values 49 := by
      simp [sourceValue, nonzeroW23_22SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h13_12, h12_12]
      ring
    rw [identity] at source3
    have sumZero := (mul_eq_zero.mp source3).resolve_right h23_22
    exact eq_neg_of_add_eq_zero_right sumZero
  exact ⟨h05_00, h05_02, h05_20, h15_11⟩

/-- On the `w_23_22 = 0` survivor, nonzero `w_01_11` forces four
off-diagonal entries of edge 25 to vanish. -/
theorem w25_tail_zero_of_w01_11_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (_hdet : slotDeterminant values 1 ≠ 0)
    (h12 : values 28 = 0) (h12_12 : values 29 = 0)
    (h13_10 : values 35 = 0) (h01_11 : values 1 ≠ 0) :
    values 57 = 0 ∧ values 58 = 0 ∧ values 59 = 0 ∧ values 60 = 0 := by
  have source0 : sourceValue values (nonzeroW01_11SourceIndex 0) = 0 :=
    base (nonzeroW01_11SourceIndex 0)
      (nonzero_w01_11_source_not_determinant 0)
  have source1 : sourceValue values (nonzeroW01_11SourceIndex 1) = 0 :=
    base (nonzeroW01_11SourceIndex 1)
      (nonzero_w01_11_source_not_determinant 1)
  have source2 : sourceValue values (nonzeroW01_11SourceIndex 2) = 0 :=
    base (nonzeroW01_11SourceIndex 2)
      (nonzero_w01_11_source_not_determinant 2)
  have source3 : sourceValue values (nonzeroW01_11SourceIndex 3) = 0 :=
    base (nonzeroW01_11SourceIndex 3)
      (nonzero_w01_11_source_not_determinant 3)
  simp [sourceValue, nonzeroW01_11SourceIndex,
    Krenn.FrozenCase0System.equations,
    Krenn.SparseCertificate.SparsePoly.toPoly,
    Krenn.SparseCertificate.SparseTerm.toPoly,
    h12, h12_12, h13_10] at source0 source1 source2 source3
  exact ⟨source0.resolve_left h01_11, source1.resolve_left h01_11,
    source2.resolve_left h01_11, source3.resolve_left h01_11⟩

/-- On the `w_01_11 = 0` survivor, nonzero `w_03_11` and the already
forced nonzero `w_14_11` kill every off-diagonal entry of edge 25 except
the live pivot `w_25_11`.  These are five direct canonical amplitude
consequences. -/
theorem w25_offdiagonal_zero_of_w03_11_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (_hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h12_12 : values 29 = 0) (h01_11 : values 1 = 0)
    (h14_11 : values 42 ≠ 0) (h03_11 : values 7 ≠ 0) :
    values 55 = 0 ∧ values 57 = 0 ∧ values 58 = 0 ∧
      values 59 = 0 ∧ values 60 = 0 := by
  rcases chart with ⟨h23, h12, h13⟩
  have source0 : sourceValue values (nonzeroW03_11SourceIndex 0) = 0 :=
    base (nonzeroW03_11SourceIndex 0)
      (nonzero_w03_11_source_not_determinant 0)
  have source1 : sourceValue values (nonzeroW03_11SourceIndex 1) = 0 :=
    base (nonzeroW03_11SourceIndex 1)
      (nonzero_w03_11_source_not_determinant 1)
  have source2 : sourceValue values (nonzeroW03_11SourceIndex 2) = 0 :=
    base (nonzeroW03_11SourceIndex 2)
      (nonzero_w03_11_source_not_determinant 2)
  have source3 : sourceValue values (nonzeroW03_11SourceIndex 3) = 0 :=
    base (nonzeroW03_11SourceIndex 3)
      (nonzero_w03_11_source_not_determinant 3)
  have source4 : sourceValue values (nonzeroW03_11SourceIndex 4) = 0 :=
    base (nonzeroW03_11SourceIndex 4)
      (nonzero_w03_11_source_not_determinant 4)
  have nonzeroFactor : values 7 * values 42 ≠ 0 :=
    mul_ne_zero h03_11 h14_11
  have reduce_source
      (source : R) (entry : R) (identity : source = (values 7 * values 42) * entry)
      (source_zero : source = 0) : entry = 0 := by
    rw [identity] at source_zero
    exact (mul_eq_zero.mp source_zero).resolve_left nonzeroFactor
  have h0 : values 55 = 0 := by
    apply reduce_source (sourceValue values (nonzeroW03_11SourceIndex 0))
      (values 55) _ source0
    simp [sourceValue, nonzeroW03_11SourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h23, h12, h13, h01_11]
  have h1 : values 57 = 0 := by
    apply reduce_source (sourceValue values (nonzeroW03_11SourceIndex 1))
      (values 57) _ source1
    simp [sourceValue, nonzeroW03_11SourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h23, h12, h13, h01_11]
  have h2 : values 58 = 0 := by
    apply reduce_source (sourceValue values (nonzeroW03_11SourceIndex 2))
      (values 58) _ source2
    simp [sourceValue, nonzeroW03_11SourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h12_12, h13, h01_11]
  have h3 : values 59 = 0 := by
    apply reduce_source (sourceValue values (nonzeroW03_11SourceIndex 3))
      (values 59) _ source3
    simp [sourceValue, nonzeroW03_11SourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h12_12, h13, h01_11]
  have h4 : values 60 = 0 := by
    apply reduce_source (sourceValue values (nonzeroW03_11SourceIndex 4))
      (values 60) _ source4
    simp [sourceValue, nonzeroW03_11SourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h12_12, h13, h01_11]
  exact ⟨h0, h1, h2, h3, h4⟩

/-- On the final `w_03_11 = 0` survivor, nonzero `w_02_11` forces
`w_15_11 = w_35_00 = w_35_22 = 0`.  The three equations are canonical
rows 644, 729, and 730; the nonzero factor is `w_02_11*w_14_11`. -/
theorem reductions_of_w02_11_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (_hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 = 0) (h13_12 : values 37 = 0)
    (h13_10 : values 35 = 0) (h01_11 : values 1 = 0)
    (h14_11 : values 42 ≠ 0) (h02_11 : values 4 ≠ 0) :
    values 45 = 0 ∧ values 69 = 0 ∧ values 71 = 0 := by
  rcases chart with ⟨_h23, h12, _h13⟩
  have source0 : sourceValue values (nonzeroW02_11SourceIndex 0) = 0 :=
    base (nonzeroW02_11SourceIndex 0)
      (nonzero_w02_11_source_not_determinant 0)
  have source1 : sourceValue values (nonzeroW02_11SourceIndex 1) = 0 :=
    base (nonzeroW02_11SourceIndex 1)
      (nonzero_w02_11_source_not_determinant 1)
  have source2 : sourceValue values (nonzeroW02_11SourceIndex 2) = 0 :=
    base (nonzeroW02_11SourceIndex 2)
      (nonzero_w02_11_source_not_determinant 2)
  have nonzeroFactor : values 4 * values 42 ≠ 0 :=
    mul_ne_zero h02_11 h14_11
  have h35_00 : values 69 = 0 := by
    have identity :
        sourceValue values (nonzeroW02_11SourceIndex 0) =
          (values 4 * values 42) * values 69 := by
      simp [sourceValue, nonzeroW02_11SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h01_11, h24, h13_10, h12]
    rw [identity] at source0
    exact (mul_eq_zero.mp source0).resolve_left nonzeroFactor
  have h15_11 : values 45 = 0 := by
    have identity :
        sourceValue values (nonzeroW02_11SourceIndex 1) =
          values 4 * values 45 := by
      simp [sourceValue, nonzeroW02_11SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h01_11, h24, h13_10, h12]
    rw [identity] at source1
    exact (mul_eq_zero.mp source1).resolve_left h02_11
  have h35_22 : values 71 = 0 := by
    have identity :
        sourceValue values (nonzeroW02_11SourceIndex 2) =
          (values 4 * values 42) * values 71 := by
      simp [sourceValue, nonzeroW02_11SourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h01_11, h24, h13_12, h12]
    rw [identity] at source2
    exact (mul_eq_zero.mp source2).resolve_left nonzeroFactor
  exact ⟨h15_11, h35_00, h35_22⟩

/-- The `w_02_11 = 0` half of the last survivor is impossible without a
certificate: canonical monochromatic row 745 becomes the constant `-1`. -/
theorem refutes_w02_11_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (_hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h01_11 : values 1 = 0) (h02_11 : values 4 = 0)
    (h03_11 : values 7 = 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have source : sourceValue values 745 = 0 :=
    base 745 (w14_zero_source_not_determinant 1)
  have identity : sourceValue values 745 = -1 := by
    simp [sourceValue, Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h23, h12, h13, h01_11, h02_11, h03_11]
  rw [identity] at source
  norm_num at source

#print axioms opposite_pivots_not_both_zero
#print axioms opposite_pivot_cover
#print axioms w13_12_zero_of_w24_zero
#print axioms w13_12_zero_of_w25_zero
#print axioms w13_10_zero_of_both_opposite_pivots_live
#print axioms w25_tail_zero_of_both_opposite_pivots_live
#print axioms w04_even_column_zero_of_w13_10_nonzero
#print axioms refutes_w24_zero_w13_10_nonzero
#print axioms w13_10_zero_of_w24_zero
#print axioms w03_ends_zero_of_w14_11_nonzero
#print axioms refutes_w24_zero_w13_10_zero_w14_11_zero
#print axioms w12_12_zero_of_w03_00_zero_w13_10_zero
#print axioms reductions_of_w23_22_nonzero
#print axioms w25_tail_zero_of_w01_11_nonzero
#print axioms w25_offdiagonal_zero_of_w03_11_nonzero
#print axioms reductions_of_w02_11_nonzero
#print axioms refutes_w02_11_zero
#print axioms opposite_pivot_coordinate_names

end Krenn.FrozenCase0NoncollapseType01Chart3
