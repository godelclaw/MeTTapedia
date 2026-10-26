import Mettapedia.PLN.Core.CompletePLN
import Mettapedia.PLN.Comparisons.DeductionReadout
import Mettapedia.PLN.Comparisons.BalancedScreeningInformationError
import Mettapedia.PLN.Comparisons.ErrorCharacterization

/-!
# Finite PLN observations and information certificates

Joint tables retain their exact world weights under `probabilityEquiv`.
Their named four-input readouts, Boolean conditionals and CMI observations
instantiate the shared recovery certificate. The balanced bound implies the
ordinary bound. A query can be exact despite positive dependence information.
-/

open scoped BigOperators
open Mettapedia.InformationTheory Mettapedia.InformationTheory.FiniteRV
open Mettapedia.PLN.Core.CompletePLN Mettapedia.PLN.Comparisons.DeductionStability
open Mettapedia.ProbabilityTheory.FiniteEventMass Mettapedia.ProbabilityTheory.FiniteConditionalStability
open Mettapedia.PLN.Comparisons.ScreeningInformationError

namespace Mettapedia.PLN.Bridges.ProbabilityTheory

namespace FiniteJointDistribution

/-- All four exact readouts from one finite joint distribution, with unit-interval proofs. -/
noncomputable def deductionPremises {n : ℕ} (joint : JointDistribution n) (a b c : Fin n) : PremiseValues where
  ab := ⟨condProb joint b a, cond_prob_mem_unit joint b a⟩
  bc := ⟨condProb joint c b, cond_prob_mem_unit joint c b⟩
  b := ⟨marginalProb joint b, marginal_prob_bounds joint b⟩
  c := ⟨marginalProb joint c, marginal_prob_bounds joint c⟩

/-- Dependence of the three selected Boolean observations, in nats. -/
noncomputable def deductionInformation {n : ℕ} (joint : JointDistribution n) (a b c : Fin n) : ℝ :=
  FiniteRV.condMutualInfo joint.prob (worldToAssignment n · a)
    (worldToAssignment n · b) (worldToAssignment n · c)

/-- Balanced query radius; positive antecedent mass is required by its certificate. -/
noncomputable def deductionRadius {n : ℕ} (joint : JointDistribution n) (a b c : Fin n) : ℝ :=
  balancedRadius (marginalProb joint a) (deductionInformation joint a b c)

variable {n : ℕ}

def probabilityEquiv : JointDistribution n ≃ Prob (Fin (2 ^ n)) where
  toFun source := ⟨source.prob, source.prob_nonneg, source.prob_sum_one⟩
  invFun source := ⟨source.1, source.2.1, source.2.2⟩
  left_inv source := by cases source; rfl
  right_inv source := by cases source; rfl

theorem mass_marginal (source : JointDistribution n) (i : Fin n) :
    mass (probabilityEquiv source).1 (worldToAssignment n · i) = marginalProb source i := rfl

theorem mass_joint (source : JointDistribution n) (i j : Fin n) :
    mass (probabilityEquiv source).1
      (fun world => worldToAssignment n world i && worldToAssignment n world j) =
      jointProb2 source i j := by
  simp only [mass, probabilityEquiv, Equiv.coe_fn_mk, jointProb2, Bool.and_eq_true]

/-- The guarded API and division agree even at zero antecedent mass. -/
theorem joint_ratio_readout (source : JointDistribution n) (i j : Fin n) :
    jointProb2 source i j / marginalProb source j = condProb source i j := by
  by_cases zero : marginalProb source j = 0 <;> simp [condProb, zero]

theorem conditional_readout (source : JointDistribution n) (i j : Fin n) :
    conditional (probabilityEquiv source).1 (worldToAssignment n · i) (worldToAssignment n · j) =
      condProb source i j := by
  unfold conditional
  rw [mass_joint, mass_marginal, joint_ratio_readout]

end FiniteJointDistribution

open FiniteJointDistribution

variable {n : ℕ}

namespace FiniteJointInformation

theorem pushforward_true (source : JointDistribution n) (i : Fin n) :
    pushforward source.prob (worldToAssignment n · i) true = marginalProb source i := by
  simp only [pushforward_eq_sum_ite, marginalProb]

theorem law2_true_true (source : JointDistribution n) (i j : Fin n) :
    law2 source.prob (worldToAssignment n · i) (worldToAssignment n · j) (true, true) =
      jointProb2 source i j := by
  simp only [law2, pushforward_eq_sum_ite, Prod.mk.injEq, jointProb2]

theorem information_query_readout (source : JointDistribution n) (i j : Fin n) :
    law2 source.prob (worldToAssignment n · j) (worldToAssignment n · i) (true, true) /
        pushforward source.prob (worldToAssignment n · j) true = condProb source i j := by
  rw [law2_true_true, pushforward_true, jointProb2_comm source j i, joint_ratio_readout]

end FiniteJointInformation

open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInformation

namespace FiniteJointBalancedInformation

/-- The transported recovery certificate retains the complementary antecedent mass. -/
theorem query_error_sq_le_balanced_cmi (source : JointDistribution n) (a b c : Fin n)
    (possible : 0 < marginalProb source a) :
    2 * marginalProb source a *
      (completeDeduction source a b c - estimate (deductionPremises source a b c)) ^ 2 ≤
      (1 - marginalProb source a) * deductionInformation source a b c := by
  have bound := Mettapedia.PLN.Comparisons.BalancedScreeningInformationError.pln_query_error_sq_le_balanced_cmi
    (probabilityEquiv source) (worldToAssignment n · a) (worldToAssignment n · b)
    (worldToAssignment n · c) (by simpa only [probabilityEquiv, Equiv.coe_fn_mk,
      pushforward_true] using possible)
  simp only [probabilityEquiv, Equiv.coe_fn_mk, screenedValue, queryValue] at bound
  rw [information_query_readout source c a, information_query_readout source b a,
    information_query_readout source c b, pushforward_true, pushforward_true, pushforward_true] at bound
  exact bound

/-- The finite query may have empty intermediate branches. -/
theorem query_error_le_sqrt_balanced_cmi (source : JointDistribution n) (a b c : Fin n)
    (possible : 0 < marginalProb source a) :
    |completeDeduction source a b c - estimate (deductionPremises source a b c)| ≤
      deductionRadius source a b c := by
  apply Real.abs_le_sqrt
  exact (le_div_iff₀ (by positivity : 0 < 2 * marginalProb source a)).mpr
    (by simpa only [mul_comm (2 * marginalProb source a)] using
      query_error_sq_le_balanced_cmi source a b c possible)

end FiniteJointBalancedInformation

namespace FiniteJointInformation

/-- The ordinary bound follows by discarding the complementary-mass improvement. -/
theorem query_error_sq_le_cmi (source : JointDistribution n) (a b c : Fin n)
    (possible : 0 < marginalProb source a) :
    2 * marginalProb source a *
      (completeDeduction source a b c - estimate (deductionPremises source a b c)) ^ 2 ≤
      deductionInformation source a b c := by
  have bound := FiniteJointBalancedInformation.query_error_sq_le_balanced_cmi source a b c possible
  have info : 0 ≤ deductionInformation source a b c :=
    condMutualInfo_nonneg source.prob source.prob_nonneg _ _ _
  nlinarith [ (marginal_prob_bounds source a).1 ]

theorem query_error_le_sqrt_cmi (source : JointDistribution n) (a b c : Fin n)
    (possible : 0 < marginalProb source a) :
    |completeDeduction source a b c - estimate (deductionPremises source a b c)| ≤
      informationRadius (marginalProb source a) (deductionInformation source a b c) := by
  apply Real.abs_le_sqrt
  exact (le_div_iff₀ (by positivity : 0 < 2 * marginalProb source a)).mpr
    (by simpa only [mul_comm (2 * marginalProb source a)] using
      query_error_sq_le_cmi source a b c possible)

theorem zero_cmi_implies_query_exact (source : JointDistribution n) (a b c : Fin n)
    (possible : 0 < marginalProb source a) (zero : deductionInformation source a b c = 0) :
    completeDeduction source a b c = estimate (deductionPremises source a b c) := by
  have bound := query_error_le_sqrt_cmi source a b c possible
  simpa only [informationRadius, zero, zero_div, Real.sqrt_zero, abs_nonpos_iff,
    sub_eq_zero] using bound

namespace Controls

open Mettapedia.PLN.Comparisons.ErrorCharacterization
open Mettapedia.PLN.Comparisons.ErrorCharacterization.Controls

/-- The parity example is genuinely dependent even though its selected
conditional query is predicted exactly. CMI is not that query's error. -/
theorem cancelling_query_has_positive_cmi :
    completeDeduction cancellingDistribution 0 1 2 =
        screeningDeduction cancellingDistribution 0 1 2 ∧
      0 < condMutualInfo cancellingDistribution.prob (worldToAssignment 3 · 0)
        (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) := by
  refine ⟨exact_query_need_not_have_branch_screening.1, ?_⟩
  apply lt_of_le_of_ne (condMutualInfo_nonneg _ cancellingDistribution.prob_nonneg _ _ _)
  intro zero
  have atom := (condMutualInfo_eq_zero_iff _ cancellingDistribution.prob_nonneg
    (worldToAssignment 3 · 0) (worldToAssignment 3 · 1) (worldToAssignment 3 · 2)).mp zero.symm
      (true, true, true)
  norm_num [CondIndep, law3, law2, pushforward_eq_sum_ite, cancellingDistribution,
    ← Fin.sum_ofFn, List.ofFn, Fin.foldr, Fin.foldr.loop, worldToAssignment] at atom

end Controls

end FiniteJointInformation

end Mettapedia.PLN.Bridges.ProbabilityTheory
