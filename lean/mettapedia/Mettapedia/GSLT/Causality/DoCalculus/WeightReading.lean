import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mettapedia.GSLT.Causality.DoCalculus.AdjustCounts
import Mettapedia.GSLT.Causality.DoCalculus.Distinctions

/-!
# The front-door weight is the interventional count

`smokeProbJoint` is the smoking cell table as a probability. `frontDoorOf`
reads the front-door formula off that joint. The value is `3 / 5`, and that
is the strength of `frontDoorCounts`, the canonical count of the same ratio.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open scoped BigOperators ENNReal

/-- The smoking cells as a probability, with the confounder bit held false. -/
noncomputable def smokeProbJoint (f : Smoke → Bool) : ℝ≥0∞ :=
  if f .u = false then (smokeCell (f .s) (f .t) (f .c) : ℝ≥0∞) / smokeTotal else 0

lemma add_nat_div (n m : ℕ) (c : ℝ≥0∞) :
    (n : ℝ≥0∞) / c + (m : ℝ≥0∞) / c = ((n + m : ℕ) : ℝ≥0∞) / c := by
  rw [ENNReal.div_add_div_same, ← Nat.cast_add]

lemma add_inv_inv (c : ℝ≥0∞) :
    c⁻¹ + c⁻¹ = ((1 + 1 : ℕ) : ℝ≥0∞) / c := by
  simpa [one_div] using add_nat_div 1 1 c

lemma one_inv_div (c : ℝ≥0∞) : c⁻¹ = ((1 : ℕ) : ℝ≥0∞) / c := by
  rw [← one_div, ← Nat.cast_one]

lemma mass_s (s0 : Bool) :
    smokeMass smokeProbJoint (fun f => f .s = s0) =
      (smokeN s0 : ℝ≥0∞) / smokeTotal := by
  cases s0 <;>
    · unfold smokeMass
      rw [sum_smoke]
      simp only [sum_bool]
      simp [smokeOf, smokeProbJoint, smokeCell]
      repeat rw [add_inv_inv]
      try rw [one_inv_div smokeTotal]
      repeat rw [ENNReal.div_add_div_same]
      refine congrArg (fun x : ℝ≥0∞ => x / smokeTotal) ?_
      norm_cast

lemma mass_st (s0 t0 : Bool) :
    smokeMass smokeProbJoint (fun f => f .s = s0 ∧ f .t = t0) =
      (smokeNT s0 t0 : ℝ≥0∞) / smokeTotal := by
  cases s0 <;> cases t0 <;>
    · unfold smokeMass
      rw [sum_smoke]
      simp only [sum_bool]
      simp [smokeOf, smokeProbJoint, smokeCell]
      repeat rw [add_inv_inv]
      try rw [one_inv_div smokeTotal]
      repeat rw [ENNReal.div_add_div_same]
      refine congrArg (fun x : ℝ≥0∞ => x / smokeTotal) ?_
      norm_cast

lemma mass_cst (s0 t0 : Bool) :
    smokeMass smokeProbJoint (fun f => f .c = true ∧ f .t = t0 ∧ f .s = s0) =
      (smokeNC s0 t0 : ℝ≥0∞) / smokeTotal := by
  cases s0 <;> cases t0 <;>
    · unfold smokeMass
      rw [sum_smoke]
      simp only [sum_bool]
      simp [smokeOf, smokeProbJoint, smokeCell]
      try rw [one_inv_div smokeTotal]
      refine congrArg (fun x : ℝ≥0∞ => x / smokeTotal) ?_
      norm_cast

lemma natDiv (a b : ℕ) (hb : 0 < b) :
    (a : ℝ≥0∞) / b = ENNReal.ofReal ((a : ℝ) / b) := by
  rw [← ENNReal.ofReal_natCast a, ← ENNReal.ofReal_natCast b]
  exact (ENNReal.ofReal_div_of_pos (by exact_mod_cast hb)).symm

lemma ratio24 (a b : ℕ) (hb : 0 < b) :
    ((a : ℝ≥0∞) / ((24 : ℕ) : ℝ≥0∞)) / ((b : ℝ≥0∞) / ((24 : ℕ) : ℝ≥0∞)) =
      ENNReal.ofReal ((a : ℝ) / b) := by
  rw [natDiv a 24 (by decide), natDiv b 24 (by decide)]
  rw [← ENNReal.ofReal_div_of_pos (div_pos (by exact_mod_cast hb) (by norm_num))]
  congr 1
  field_simp

noncomputable def frontEnn : ℝ≥0∞ :=
  ∑ bt, ((smokeNT true bt : ℝ≥0∞) / smokeTotal) / ((smokeN true : ℝ≥0∞) / smokeTotal) *
    (∑ bs, ((smokeNC bs bt : ℝ≥0∞) / smokeTotal) /
        ((smokeNT bs bt : ℝ≥0∞) / smokeTotal) *
      ((smokeN bs : ℝ≥0∞) / smokeTotal))

theorem front_door_of_is_frontEnn :
    frontDoorOf true true smokeProbJoint = frontEnn := by
  unfold frontDoorOf frontEnn
  simp only [mass_s, mass_st, mass_cst]

theorem frontEnn_three_fifths : frontEnn = (3 : ℝ≥0∞) / 5 := by
  unfold frontEnn
  simp only [sum_bool]
  have hT : smokeTotal = 24 := by decide
  have hN0 : smokeN false = 12 := by decide
  have hN1 : smokeN true = 12 := by decide
  have hNT00 : smokeNT false false = 10 := by decide
  have hNT01 : smokeNT false true = 2 := by decide
  have hNT10 : smokeNT true false = 2 := by decide
  have hNT11 : smokeNT true true = 10 := by decide
  have hNC00 : smokeNC false false = 2 := by decide
  have hNC10 : smokeNC true false = 1 := by decide
  have hNC01 : smokeNC false true = 1 := by decide
  have hNC11 : smokeNC true true = 8 := by decide
  rw [hT, hN0, hN1, hNT00, hNT01, hNT10, hNT11, hNC00, hNC10, hNC01, hNC11]
  rw [ratio24 2 12 (by decide), ratio24 2 10 (by decide), ratio24 1 2 (by decide),
    ratio24 10 12 (by decide), ratio24 8 10 (by decide)]
  rw [natDiv 12 24 (by decide)]
  let R (n m : ℕ) : ℝ := (n : ℝ) / m
  have hBC : ENNReal.ofReal (R 2 10) * ENNReal.ofReal (R 12 24) =
      ENNReal.ofReal (R 2 10 * R 12 24) :=
    (ENNReal.ofReal_mul (by norm_num)).symm
  have hDC : ENNReal.ofReal (R 1 2) * ENNReal.ofReal (R 12 24) =
      ENNReal.ofReal (R 1 2 * R 12 24) :=
    (ENNReal.ofReal_mul (by norm_num)).symm
  have hFC : ENNReal.ofReal (R 8 10) * ENNReal.ofReal (R 12 24) =
      ENNReal.ofReal (R 8 10 * R 12 24) :=
    (ENNReal.ofReal_mul (by norm_num)).symm
  rw [hBC, hDC, hFC]
  have hsum0 : ENNReal.ofReal (R 2 10 * R 12 24) + ENNReal.ofReal (R 1 2 * R 12 24) =
      ENNReal.ofReal (R 2 10 * R 12 24 + R 1 2 * R 12 24) :=
    (ENNReal.ofReal_add (by norm_num) (by norm_num)).symm
  have hsum1 : ENNReal.ofReal (R 1 2 * R 12 24) + ENNReal.ofReal (R 8 10 * R 12 24) =
      ENNReal.ofReal (R 1 2 * R 12 24 + R 8 10 * R 12 24) :=
    (ENNReal.ofReal_add (by norm_num) (by norm_num)).symm
  rw [hsum0, hsum1]
  have hA : ENNReal.ofReal (R 2 12) * ENNReal.ofReal (R 2 10 * R 12 24 + R 1 2 * R 12 24) =
      ENNReal.ofReal (R 2 12 * (R 2 10 * R 12 24 + R 1 2 * R 12 24)) :=
    (ENNReal.ofReal_mul (by norm_num)).symm
  have hE : ENNReal.ofReal (R 10 12) * ENNReal.ofReal (R 1 2 * R 12 24 + R 8 10 * R 12 24) =
      ENNReal.ofReal (R 10 12 * (R 1 2 * R 12 24 + R 8 10 * R 12 24)) :=
    (ENNReal.ofReal_mul (by norm_num)).symm
  rw [hA, hE]
  have hfin :
      ENNReal.ofReal (R 2 12 * (R 2 10 * R 12 24 + R 1 2 * R 12 24)) +
        ENNReal.ofReal (R 10 12 * (R 1 2 * R 12 24 + R 8 10 * R 12 24)) =
      ENNReal.ofReal
        (R 2 12 * (R 2 10 * R 12 24 + R 1 2 * R 12 24) +
          R 10 12 * (R 1 2 * R 12 24 + R 8 10 * R 12 24)) :=
    (ENNReal.ofReal_add (by norm_num) (by norm_num)).symm
  rw [hfin]
  change _ =
    ((3 : ℕ) : ℝ≥0∞) / ((5 : ℕ) : ℝ≥0∞)
  rw [natDiv 3 5 (by decide)]
  apply congrArg ENNReal.ofReal
  norm_num

theorem front_door_of_cell_joint :
    frontDoorOf true true smokeProbJoint = (3 : ℝ≥0∞) / 5 :=
  front_door_of_is_frontEnn.trans frontEnn_three_fifths

theorem front_door_weight_reads_count_strength :
    frontDoorOf true true smokeProbJoint =
      ENNReal.ofReal (frontDoorCounts.strength : ℝ) := by
  rw [front_door_of_cell_joint, front_door_count_strength]
  change ((3 : ℕ) : ℝ≥0∞) / ((5 : ℕ) : ℝ≥0∞) = _
  rw [natDiv 3 5 (by decide)]
  apply congrArg ENNReal.ofReal
  norm_num

theorem front_door_weight_count_licence (experiment : Bool) :
    identify smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS (∅ : Finset Smoke) =
        .doFree frontDoorExpr ∧
      frontDoorOf true true smokeProbJoint =
        ENNReal.ofReal (frontDoorCounts.strength : ℝ) ∧
      (poolInterventional frontDoorState experiment).interventional =
        frontDoorCounts.revise experiment ∧
      (poolInterventional frontDoorState experiment).observational =
        smokeObsCounts := by
  refine ⟨front_door_separates_id.2.1, front_door_weight_reads_count_strength, ?_⟩
  exact front_door_pool_is_one_revision experiment

end Mettapedia.GSLT.Causality.DoCalculus
