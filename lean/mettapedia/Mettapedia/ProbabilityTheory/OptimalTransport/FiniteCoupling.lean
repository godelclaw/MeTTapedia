import Mettapedia.ProbabilityTheory.OptimalTransport.Basic
import Mettapedia.Cybernetics.ApproximateAdequacy.MassFunction

/-!
# Finite coupling tables and probability mass functions

The ordered-field coupling interface permits exact finite arithmetic; the
discrete transport interface uses Mathlib's `PMF`.  Over the reals, the two
existing representations agree.  The conversions below retain every joint
weight, both prescribed marginals and support, and are inverse.  No additional
coupling carrier is introduced.

The cost correspondence concerns finite, nonnegative real cost functions,
embedded in `ENNReal`.  It does not identify signed costs with truncated
nonnegative readouts, or require bounded costs or additional nonemptiness
assumptions.  Normalized marginals already exclude empty carriers.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory.OptimalTransport.FiniteCoupling

open Mettapedia.Cybernetics.ApproximateAdequacy
open scoped BigOperators ENNReal

variable {S T : Type*} [Fintype S] [Fintype T]
variable {μ : S → ℝ} {ν : T → ℝ}

/-- A finite joint table has total mass one as soon as its left marginal does. -/
theorem joint_distribution (table : Coupling μ ν) (left : IsDistribution μ) :
    IsDistribution (fun pair : S × T => table.weight pair.1 pair.2) where
  nonneg pair := table.nonneg pair.1 pair.2
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    exact table.total left

/-- Reuse the existing finite-distribution conversion on the joint table. -/
def toPMF (table : Coupling μ ν) (left : IsDistribution μ) : PMF (S × T) :=
  (joint_distribution table left).toPMF

@[simp] theorem toPMF_apply (table : Coupling μ ν) (left : IsDistribution μ)
    (pair : S × T) :
    toPMF table left pair = ENNReal.ofReal (table.weight pair.1 pair.2) := rfl

theorem toPMF_toReal (table : Coupling μ ν) (left : IsDistribution μ) (x : S) (y : T) :
    (toPMF table left (x, y)).toReal = table.weight x y :=
  ENNReal.toReal_ofReal (table.nonneg x y)

theorem support_toPMF (table : Coupling μ ν) (left : IsDistribution μ) :
    (toPMF table left).support = {pair | table.weight pair.1 pair.2 ≠ 0} :=
  (joint_distribution table left).support_toPMF

/-- Finite first-coordinate marginalization is a row sum. -/
theorem map_fst_apply (joint : PMF (S × T)) (x : S) :
    joint.map Prod.fst x = ∑ y, joint (x, y) := by
  classical
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

/-- Finite second-coordinate marginalization is a column sum. -/
theorem map_snd_apply (joint : PMF (S × T)) (y : T) :
    joint.map Prod.snd y = ∑ x, joint (x, y) := by
  classical
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp

theorem toPMF_isCoupling (table : Coupling μ ν)
    (left : IsDistribution μ) (right : IsDistribution ν) :
    IsCoupling (toPMF table left) left.toPMF right.toPMF := by
  constructor
  · ext x
    rw [map_fst_apply]
    simp only [toPMF_apply, IsDistribution.toPMF_apply]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => table.nonneg x y), table.sum_right]
  · ext y
    rw [map_snd_apply]
    simp only [toPMF_apply, IsDistribution.toPMF_apply]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => table.nonneg x y), table.sum_left]

/-- Reading finite PMF point masses as reals gives the existing coupling table. -/
def ofPMF (left : IsDistribution μ) (right : IsDistribution ν)
    (joint : PMF (S × T)) (marginals : IsCoupling joint left.toPMF right.toPMF) :
    Coupling μ ν where
  weight x y := (joint (x, y)).toReal
  nonneg _ _ := ENNReal.toReal_nonneg
  sum_right x := by
    calc
      ∑ y, (joint (x, y)).toReal = (∑ y, joint (x, y)).toReal :=
        (ENNReal.toReal_sum (fun y _ => joint.apply_ne_top (x, y))).symm
      _ = (joint.map Prod.fst x).toReal := congrArg ENNReal.toReal (map_fst_apply joint x).symm
      _ = (left.toPMF x).toReal := congrArg (fun law : PMF S => (law x).toReal) marginals.1
      _ = μ x := left.toReal_toPMF x
  sum_left y := by
    calc
      ∑ x, (joint (x, y)).toReal = (∑ x, joint (x, y)).toReal :=
        (ENNReal.toReal_sum (fun x _ => joint.apply_ne_top (x, y))).symm
      _ = (joint.map Prod.snd y).toReal := congrArg ENNReal.toReal (map_snd_apply joint y).symm
      _ = (right.toPMF y).toReal := congrArg (fun law : PMF T => (law y).toReal) marginals.2
      _ = ν y := right.toReal_toPMF y

/-- Extensionality retains the complete joint weighting, not just its marginals. -/
theorem table_ext {first second : Coupling μ ν}
    (weights : ∀ x y, first.weight x y = second.weight x y) : first = second := by
  cases first with
  | mk first nonneg firstRows firstColumns =>
      cases second with
      | mk second nonneg secondRows secondColumns =>
          have same : first = second := funext fun x => funext fun y => weights x y
          cases same
          rfl

@[simp] theorem ofPMF_toPMF (table : Coupling μ ν)
    (left : IsDistribution μ) (right : IsDistribution ν) :
    ofPMF left right (toPMF table left) (toPMF_isCoupling table left right) = table := by
  apply table_ext
  intro x y
  exact toPMF_toReal table left x y

@[simp] theorem toPMF_ofPMF (left : IsDistribution μ) (right : IsDistribution ν)
    (joint : PMF (S × T)) (marginals : IsCoupling joint left.toPMF right.toPMF) :
    toPMF (ofPMF left right joint marginals) left = joint := by
  ext pair
  exact ENNReal.ofReal_toReal (joint.apply_ne_top pair)

/-- A lossless correspondence between the two already existing coupling forms. -/
def couplingEquiv (left : IsDistribution μ) (right : IsDistribution ν) :
    Coupling μ ν ≃ {joint : PMF (S × T) // IsCoupling joint left.toPMF right.toPMF} where
  toFun table := ⟨toPMF table left, toPMF_isCoupling table left right⟩
  invFun joint := ofPMF left right joint.1 joint.2
  left_inv table := ofPMF_toPMF table left right
  right_inv joint := Subtype.ext (toPMF_ofPMF left right joint.1 joint.2)

/-- Finite nonnegative real costs agree exactly with the discrete PMF cost. -/
theorem couplingCost_toPMF (table : Coupling μ ν) (left : IsDistribution μ)
    (cost : S → T → ℝ) (nonnegative : ∀ x y, 0 ≤ cost x y) :
    couplingCost (toPMF table left) (fun pair => ENNReal.ofReal (cost pair.1 pair.2)) =
      ENNReal.ofReal (table.cost cost) := by
  calc
    couplingCost (toPMF table left) (fun pair => ENNReal.ofReal (cost pair.1 pair.2)) =
        ∑ pair : S × T, ENNReal.ofReal (table.weight pair.1 pair.2 * cost pair.1 pair.2) := by
      rw [couplingCost, tsum_fintype]
      apply Finset.sum_congr rfl
      intro pair _
      rw [toPMF_apply, ENNReal.ofReal_mul (table.nonneg pair.1 pair.2)]
    _ = ENNReal.ofReal (∑ pair : S × T, table.weight pair.1 pair.2 * cost pair.1 pair.2) :=
      (ENNReal.ofReal_sum_of_nonneg (fun pair _ =>
        mul_nonneg (table.nonneg pair.1 pair.2) (nonnegative pair.1 pair.2))).symm
    _ = ENNReal.ofReal (table.cost cost) := by rw [Fintype.sum_prod_type]; rfl

/-- An existing finite-table certificate bounds the existing PMF transport cost. -/
theorem kantorovichCost_le_tableCost (table : Coupling μ ν)
    (left : IsDistribution μ) (right : IsDistribution ν)
    (cost : S → T → ℝ) (nonnegative : ∀ x y, 0 ≤ cost x y) :
    kantorovichCost left.toPMF right.toPMF (fun pair => ENNReal.ofReal (cost pair.1 pair.2)) ≤
      ENNReal.ofReal (table.cost cost) := by
  exact (kantorovichCost_le_of_isCoupling _ _ _ (toPMF table left)
    (toPMF_isCoupling table left right)).trans_eq (couplingCost_toPMF table left cost nonnegative)

/-- Taking the infimum over finite tables gives exactly the existing PMF
transport value.  No optimizer existence or metric hypotheses are assumed. -/
theorem kantorovichCost_eq_iInf_tableCost
    (left : IsDistribution μ) (right : IsDistribution ν)
    (cost : S → T → ℝ) (nonnegative : ∀ x y, 0 ≤ cost x y) :
    kantorovichCost left.toPMF right.toPMF (fun pair => ENNReal.ofReal (cost pair.1 pair.2)) =
      ⨅ table : Coupling μ ν, ENNReal.ofReal (table.cost cost) := by
  apply le_antisymm
  · exact le_iInf fun table => kantorovichCost_le_tableCost table left right cost nonnegative
  · unfold kantorovichCost
    apply le_sInf
    rintro value ⟨joint, rfl⟩
    calc
      (⨅ table : Coupling μ ν, ENNReal.ofReal (table.cost cost)) ≤
          ENNReal.ofReal ((ofPMF left right joint.1 joint.2).cost cost) := iInf_le _ _
      _ = couplingCost joint.1 (fun pair => ENNReal.ofReal (cost pair.1 pair.2)) := by
        rw [← couplingCost_toPMF (ofPMF left right joint.1 joint.2) left cost nonnegative,
          toPMF_ofPMF]

/-! ## A correlated joint law, and a normalized law with a wrong marginal -/

namespace Controls

def fair (_ : Bool) : ℝ := 1 / 2

theorem fair_distribution : IsDistribution fair where
  nonneg _ := by norm_num [fair]
  sum_eq_one := by norm_num [fair, Fintype.univ_bool]

/-- Two nonzero diagonal entries give a correlated coupling of two fair laws. -/
def diagonal : Coupling fair fair where
  weight x y := if x = y then 1 / 2 else 0
  nonneg x y := by split_ifs <;> norm_num
  sum_right x := by cases x <;> norm_num [Fintype.univ_bool, fair]
  sum_left y := by cases y <;> norm_num [Fintype.univ_bool, fair]

def mismatch (x y : Bool) : ℝ := if x = y then 0 else 1

theorem diagonal_joint_marginals_and_entries :
    IsCoupling (toPMF diagonal fair_distribution)
        fair_distribution.toPMF fair_distribution.toPMF ∧
      toPMF diagonal fair_distribution (true, true) = 1 / 2 ∧
      toPMF diagonal fair_distribution (false, false) = 1 / 2 ∧
      toPMF diagonal fair_distribution (true, false) = 0 := by
  refine ⟨toPMF_isCoupling diagonal fair_distribution fair_distribution, ?_, ?_, ?_⟩ <;>
    norm_num [diagonal, ENNReal.ofReal_div_of_pos]

/-- The finite table and its PMF have the same zero mismatch cost. -/
theorem diagonal_cost_agrees :
    diagonal.cost mismatch = 0 ∧
      couplingCost (toPMF diagonal fair_distribution)
        (fun pair => ENNReal.ofReal (mismatch pair.1 pair.2)) = 0 := by
  have costZero : diagonal.cost mismatch = 0 := by
    norm_num [Coupling.cost, diagonal, mismatch, Fintype.univ_bool]
  refine ⟨costZero, ?_⟩
  rw [couplingCost_toPMF diagonal fair_distribution mismatch
    (fun x y => by unfold mismatch; split_ifs <;> norm_num), costZero, ENNReal.ofReal_zero]

/-- Prescribed marginals do not determine the joint weighting or its cost:
the independent and diagonal couplings have distinct mismatch costs. -/
theorem correct_marginals_do_not_determine_cost :
    diagonal.cost mismatch = 0 ∧
      (Coupling.independent fair_distribution fair_distribution).cost mismatch = 1 / 2 := by
  refine ⟨diagonal_cost_agrees.1, ?_⟩
  norm_num [Coupling.cost, Coupling.independent, mismatch, fair, Fintype.univ_bool]

/-- This is a normalized PMF whose first marginal is fair and whose second
marginal is a point mass.  Normalization alone does not fix both marginals. -/
def wrongRight : PMF (Bool × Bool) :=
  independentCoupling fair_distribution.toPMF (PMF.pure true)

theorem one_correct_marginal_is_insufficient :
    wrongRight.map Prod.fst = fair_distribution.toPMF ∧
      ¬ IsCoupling wrongRight fair_distribution.toPMF fair_distribution.toPMF := by
  have actualMarginals := isCoupling_independentCoupling
    fair_distribution.toPMF (PMF.pure true)
  refine ⟨actualMarginals.1, ?_⟩
  intro claimedMarginals
  have falseEquality : PMF.pure true = fair_distribution.toPMF :=
    actualMarginals.2.symm.trans claimedMarginals.2
  have atTrue := congrArg (fun law : PMF Bool => (law true).toReal) falseEquality
  norm_num [IsDistribution.toReal_toPMF, fair] at atTrue

end Controls

end Mettapedia.ProbabilityTheory.OptimalTransport.FiniteCoupling
