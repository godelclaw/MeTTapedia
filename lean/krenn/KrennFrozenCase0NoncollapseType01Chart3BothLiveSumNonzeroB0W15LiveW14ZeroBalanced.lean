import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroPropagation
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroSource745

/-!
The final balanced strict leaf of the B0 nonzero-sum chart-3 branch.

The external certificate lives after a chain of zero substitutions and affine
coordinate changes.  This file reflects its eleven selected rows through that
chain into the canonical 747-row system before using the exact identity.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroBalanced

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 500000
set_option maxHeartbeats 20000000

/-- The two propagation rows which force the displayed `w_24` diagonal zeroes. -/
def propagationSourceIndex : Fin 2 -> Fin 747 := ![728, 731]

theorem propagation_source_not_determinant
    (index : Fin 2) (slot : Fin 18) :
    determinantSourceIndex slot ≠ propagationSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, propagationSourceIndex]

/-- The final live `w_03_11` subface forces both displayed `w_24` diagonal
coordinates to vanish. -/
theorem w24_00_w24_22_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h15 : values 45 ≠ 0) (h03_11 : values 7 ≠ 0) :
    values 50 = 0 ∧ values 52 = 0 := by
  obtain ⟨h12_10, _, h12_12, h01⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_reductions
      values base hdet chart h24 h25 hsum
  rcases chart with ⟨_, _, h13⟩
  have source728 : sourceValue values (propagationSourceIndex 0) = 0 :=
    base (propagationSourceIndex 0) (propagation_source_not_determinant 0)
  have h24_00 : values 50 = 0 := by
    have identity : sourceValue values (propagationSourceIndex 0) = values 7 * values 45 * values 50 := by
      simp [sourceValue, propagationSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h01, h12_10, h13]
    rw [identity] at source728
    by_contra h24_00
    have product_zero : values 7 * values 45 = 0 :=
      (mul_eq_zero.mp source728).resolve_right h24_00
    exact h15 ((mul_eq_zero.mp product_zero).resolve_left h03_11)
  have source731 : sourceValue values (propagationSourceIndex 1) = 0 :=
    base (propagationSourceIndex 1) (propagation_source_not_determinant 1)
  have h24_22 : values 52 = 0 := by
    have identity : sourceValue values (propagationSourceIndex 1) = values 7 * values 45 * values 52 := by
      simp [sourceValue, propagationSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h01, h12_12, h13]
    rw [identity] at source731
    by_contra h24_22
    have product_zero : values 7 * values 45 = 0 :=
      (mul_eq_zero.mp source731).resolve_right h24_22
    exact h15 ((mul_eq_zero.mp product_zero).resolve_left h03_11)
  exact ⟨h24_00, h24_22⟩

/-- Canonical provenance of the eleven nonzero multipliers in the strict
terminal certificate. -/
def selectedSourceIndex : Fin 11 -> Fin 747
  | 0 => 457
  | 1 => 219
  | 2 => 5
  | 3 => 231
  | 4 => 32
  | 5 => 40
  | 6 => 605
  | 7 => 428
  | 8 => 343
  | 9 => 685
  | 10 => 746

theorem selected_source_not_determinant
    (index : Fin 11) (slot : Fin 18) :
    determinantSourceIndex slot ≠ selectedSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, selectedSourceIndex]

theorem source488_not_determinant (slot : Fin 18) :
    determinantSourceIndex slot ≠ (488 : Fin 747) := by
  fin_cases slot <;> simp [determinantSourceIndex]

def selectedEquations : Fin 11 -> SparsePoly (Fin 66)
  | 0 => [{ coefficient := 1, powers := [(27, 1)] }, { coefficient := 1, powers := [(32, 1)] }]
  | 1 => [{ coefficient := 1, powers := [(27, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1)] }]
  | 2 => [{ coefficient := 1, powers := [(11, 1), (34, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }]
  | 3 => [{ coefficient := 1, powers := [(29, 1)] }, { coefficient := 1, powers := [(32, 1), (47, 1)] }]
  | 4 => [{ coefficient := 1, powers := [(19, 1), (29, 1)] }, { coefficient := 1, powers := [(32, 1), (48, 1)] }]
  | 5 => [{ coefficient := 1, powers := [(29, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (47, 1)] }]
  | 6 => [{ coefficient := 1, powers := [(19, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (59, 1)] }, { coefficient := 1, powers := [(34, 1), (48, 1)] }]
  | 7 => [{ coefficient := 1, powers := [(2, 1), (27, 1)] }, { coefficient := 1, powers := [(8, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1)] }]
  | 8 => [{ coefficient := 1, powers := [(2, 1), (27, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (34, 1)] }]
  | 9 => [{ coefficient := 1, powers := [(8, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (55, 1)] }]
  | 10 => [{ coefficient := 1, powers := [(8, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (56, 1)] }, { coefficient := -1, powers := [] }]

def multipliers : Fin 11 -> SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (11, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (48, 1)] }, { coefficient := -1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (48, 1)] }, { coefficient := -1, powers := [(16, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (16, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (16, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [] }]
]

/-- Exact replay of the selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly * (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly]
  ring

theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 66 -> R) :
    ¬ ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) values (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ) constantIdentity constantNonzero values

/-- The exact value map of the 66-variable terminal leaf.  Entries omitted
by the frozen transforms are supplied by the corresponding canonical zero or
affine relation in `direct_selected_zero` below. -/
noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 -> R) : Fin 66 -> R := ![
  (values 51)⁻¹, (values 56)⁻¹, slotDeterminant values 1,
  (factorGb values)⁻¹, (factorL values)⁻¹, (values 51 + values 56)⁻¹,
  (slotDeterminant values 1)⁻¹,
  values 0, values 2, values 7, values 9, values 10, values 11, values 12,
  values 13, values 14, values 15, values 16, values 17, values 18,
  values 19, values 20, values 21, values 22, values 24, values 25,
  values 26, values 30, values 31, values 32, values 33, values 34,
  values 38, values 39, values 40, values 41, values 43, values 44,
  values 45, values 46, values 51, values 53, values 54, values 55,
  values 56, values 57, values 58, values 59, values 60, values 61,
  values 62, values 63, values 64, values 65, values 66, values 67,
  values 68, values 69, values 70, values 71, values 72, values 73,
  values 74, (values 64)⁻¹, (values 45)⁻¹, (values 7)⁻¹
]

@[simp] theorem leafValues_delta {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 2 = slotDeterminant values 1 := rfl
@[simp] theorem leafValues_w01_22 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 8 = values 2 := rfl
@[simp] theorem leafValues_w04_02 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 11 = values 10 := rfl
@[simp] theorem leafValues_w04_21 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 16 = values 15 := rfl
@[simp] theorem leafValues_w04_22 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 17 = values 16 := rfl
@[simp] theorem leafValues_w05_02 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 19 = values 18 := rfl
@[simp] theorem leafValues_w05_22 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 24 = values 24 := rfl
@[simp] theorem leafValues_w12_20 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 27 = values 30 := rfl
@[simp] theorem leafValues_w12_22 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 29 = values 32 := rfl
@[simp] theorem leafValues_w13_20 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 32 = values 38 := rfl
@[simp] theorem leafValues_w13_22 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 34 = values 40 := rfl
@[simp] theorem leafValues_w25_21 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 47 = values 59 := rfl
@[simp] theorem leafValues_w25_22 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 48 = values 60 := rfl
@[simp] theorem leafValues_w34_21 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 55 = values 67 := rfl
@[simp] theorem leafValues_w34_22 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 56 = values 68 := rfl
@[simp] theorem leafValues_w35_22 {R : Type*} [Field R] (values : Fin 75 -> R) :
    leafValues values 59 = values 71 := rfl

/-- The one B0 zero which is used by the final certificate but had not been
needed by the preceding propagation lemmas. -/
theorem w02_22_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (h15 : values 45 ≠ 0) (h12_12 : values 29 = 0)
    (h13_10 : values 35 = 0) : values 5 = 0 := by
  have source : sourceValue values 488 = 0 := base 488 source488_not_determinant
  have identity : sourceValue values 488 = values 5 * values 45 := by
    simp [sourceValue, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h12_12, h13_10]
  rw [identity] at source
  exact (mul_eq_zero.mp source).resolve_right h15

set_option linter.unusedSimpArgs false in
theorem direct_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h15 : values 45 ≠ 0) (h14 : values 42 = 0)
    (h34 : values 64 ≠ 0) (h03_11 : values 7 ≠ 0) :
    ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) (leafValues values) (selectedEquations index).toPoly = 0 := by
  obtain ⟨h12_10, h13_12, h12_12, h01⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_reductions
      values base hdet chart h24 h25 hsum
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart h24 h25
  have h02_22 : values 5 = 0 := w02_22_zero values base h15 h12_12 h13_10
  obtain ⟨h02_00, h03_00, h23_22, h03_22, h23_00⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroPropagation.forced_zeros
      values base hdet chart h24 h25 hsum h15 h14 h34
  obtain ⟨h24_00, h24_22⟩ :=
    w24_00_w24_22_zero values base hdet chart h24 h25 hsum h15 h03_11
  rcases chart with ⟨h23, h12, h13⟩
  have hDelta : values 23 - values 15 = slotDeterminant values 1 := by
    simp [slotDeterminant, slotA1, slotB1, slotA2, slotB2]
  have h05_21 : values 23 = slotDeterminant values 1 + values 15 := by
    calc
      values 23 = (values 23 - values 15) + values 15 := by ring
      _ = slotDeterminant values 1 + values 15 := by rw [hDelta]
  intro index
  have source : sourceValue values (selectedSourceIndex index) = 0 :=
    base (selectedSourceIndex index) (selected_source_not_determinant index)
  fin_cases index
  · simpa [selectedEquations, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h02_00, h03_00] using source
  · simpa [selectedEquations, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h02_00] using source
  · simpa [selectedEquations, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly] using source
  · simpa [selectedEquations, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h03_00] using source
  · simpa [selectedEquations, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly] using source
  · simpa [selectedEquations, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly] using source
  · simpa [selectedEquations, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h23_22] using source
  · simp [selectedEquations, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h23_00, h05_21] at source ⊢
    ring_nf at source ⊢
    exact source
  · simp [selectedEquations, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h03_22, h05_21] at source ⊢
    ring_nf at source ⊢
    exact source
  · simpa [selectedEquations, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h02_22, h23_22] using source
  · simpa [selectedEquations, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h02_22, h03_22, h23_22, h24_22] using source

/-- The last B0 face is impossible by the reflected eleven-row identity. -/
theorem refutes_w15_live_w14_zero_w03_11_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h15 : values 45 ≠ 0) (h14 : values 42 = 0)
    (h34 : values 64 ≠ 0) (h03_11 : values 7 ≠ 0) : False := by
  apply selectedHasNoCommonZero (leafValues values)
  exact direct_selected_zero values base hdet chart h24 h25 hsum h15 h14 h34 h03_11

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroBalanced.refutes_w15_live_w14_zero_w03_11_live

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W15LiveW14ZeroBalanced
