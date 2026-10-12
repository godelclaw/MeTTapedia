import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.NormNum
import Mettapedia.GSLT.Causality.DoCalculus.BackDoorAny
import Mettapedia.GSLT.Causality.DoCalculus.WeightReading

/-!
# The back-door weight is the interventional count

`doorProbJoint` is the door cell table as a probability. `backDoorFromMargin`
reads the back-door formula off the observed margin of that joint. The value
is `1 / 2`, and that is the strength of `backDoorCounts`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open scoped BigOperators ENNReal

def doorOf (bz bx byy : Bool) : Door → Bool
  | .z => bz
  | .x => bx
  | .y => byy

lemma sum_door (g : (Door → Bool) → ℝ≥0∞) :
    ∑ f, g f = ∑ bz, ∑ bx, ∑ byy, g (doorOf bz bx byy) := by
  let e : (Door → Bool) ≃ Bool × Bool × Bool :=
    { toFun := fun f => (f .z, f .x, f .y)
      invFun := fun p => doorOf p.1 p.2.1 p.2.2
      left_inv := by
        intro f
        ext v
        cases v <;> rfl
      right_inv := by
        rintro ⟨bz, bx, byy⟩
        rfl }
  rw [← Equiv.sum_comp e.symm g]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun bz _ => ?_
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun bx _ => ?_
  refine Finset.sum_congr rfl fun byy _ => ?_
  rfl

noncomputable def doorProbJoint (f : Door → Bool) : ℝ≥0∞ :=
  (doorCell (f .z) (f .x) (f .y) : ℝ≥0∞) / doorTotal

def doorAt (bz : Bool) : Door → Bool
  | .z => bz
  | .x => true
  | .y => true

lemma zEquiv_sum (g : ({v // v ∈ doorZ} → Bool) → ℝ≥0∞) :
    ∑ inn, g inn = g (fun _ => false) + g (fun _ => true) := by
  let e : ({v // v ∈ doorZ} → Bool) ≃ Bool :=
    { toFun := fun f => f ⟨Door.z, by simp [doorZ]⟩
      invFun := fun bz _ => bz
      left_inv := by
        intro f
        ext ⟨v, hv⟩
        simp [doorZ] at hv
        subst hv
        rfl
      right_inv := by
        intro bz
        rfl }
  rw [← Equiv.sum_comp e.symm g, sum_bool]
  rfl

lemma extend_door (bz : Bool) :
    extendAnchor doorZ (fun _ => bz) (doorAt false) = doorAt bz := by
  ext v
  cases v <;> simp [extendAnchor, glue, doorZ, doorAt]

theorem back_door_margin_weight :
    backDoorFromMargin Door.x Door.y doorZ (doorAt false)
      (observedMargin (backDoorLatent Door.x Door.y doorZ) doorProbJoint) =
      ((1 : ℕ) : ℝ≥0∞) / 2 := by
  rw [← backDoorExpr_through_margin]
  unfold backDoorExpr denoteJoint
  rw [zEquiv_sum]
  rw [extend_door false, extend_door true]
  simp only [backDoorAdjustedBody, backDoorOutcomeObs, backDoorCovariateObs, denoteJoint]
  simp [sum_door, doorOf, doorProbJoint, doorCell, doorAt, doorZ, agreesOn, doorTotal]
  rw [← Nat.cast_add]
  have hsum : doorNZ false + doorNZ true = 18 := by decide
  rw [hsum]
  rw [show (8 : ℝ≥0∞) = ((8 : ℕ) : ℝ≥0∞) from Nat.cast_ofNat.symm]
  rw [one_inv_div ((18 : ℕ) : ℝ≥0∞)]
  have hdiv : ((8 : ℕ) : ℝ≥0∞) / ((18 : ℕ) : ℝ≥0∞) ≠ 0 := by
    rw [natDiv 8 18 (by decide)]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)
  have htop : ((8 : ℕ) : ℝ≥0∞) / ((18 : ℕ) : ℝ≥0∞) ≠ ∞ := by
    rw [natDiv 8 18 (by decide)]
    exact ENNReal.ofReal_ne_top
  rw [ENNReal.div_self hdiv htop, one_mul]
  rw [add_nat_div 8 1 ((18 : ℕ) : ℝ≥0∞)]
  rw [add_nat_div 1 8 ((18 : ℕ) : ℝ≥0∞)]
  rw [add_nat_div 9 9 ((18 : ℕ) : ℝ≥0∞)]
  have h18ne : ((18 : ℕ) : ℝ≥0∞) ≠ 0 := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)
  rw [ENNReal.div_self h18ne (ENNReal.natCast_ne_top 18), div_one]
  have hrhs : ((1 : ℕ) : ℝ≥0∞) / ((2 : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ := by
    rw [← one_inv_div, Nat.cast_ofNat]
  rw [natDiv 9 18 (by decide), ← hrhs, natDiv 1 2 (by decide)]
  apply congrArg ENNReal.ofReal
  norm_num

theorem back_door_weight_reads_count_strength :
    backDoorFromMargin Door.x Door.y doorZ (doorAt false)
      (observedMargin (backDoorLatent Door.x Door.y doorZ) doorProbJoint) =
      ENNReal.ofReal (backDoorCounts.strength : ℝ) := by
  rw [back_door_margin_weight, back_door_count_strength]
  change ((1 : ℕ) : ℝ≥0∞) / ((2 : ℕ) : ℝ≥0∞) = _
  rw [natDiv 1 2 (by decide)]
  apply congrArg ENNReal.ofReal
  norm_num

theorem back_door_weight_count_licence (experiment : Bool) :
    identify doorGraph 2 doorEnum (∅ : Finset Door) doorY doorX (∅ : Finset Door) =
        .doFree (backDoorShape doorX doorY doorZ) ∧
      backDoorFromMargin Door.x Door.y doorZ (doorAt false)
        (observedMargin (backDoorLatent Door.x Door.y doorZ) doorProbJoint) =
        ENNReal.ofReal (backDoorCounts.strength : ℝ) ∧
      (poolInterventional backDoorState experiment).interventional =
        backDoorCounts.revise experiment ∧
      (poolInterventional backDoorState experiment).observational =
        doorObsCounts := by
  refine ⟨(back_door_identify_count_licence experiment).1,
    back_door_weight_reads_count_strength, ?_⟩
  exact back_door_pool_is_one_revision experiment

end Mettapedia.GSLT.Causality.DoCalculus
