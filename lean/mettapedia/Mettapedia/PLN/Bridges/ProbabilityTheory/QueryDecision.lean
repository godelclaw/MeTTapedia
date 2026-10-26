import Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.InputStability
import Mettapedia.Cybernetics.ApproximateAdequacy.DecisionBounds

/-!
# Conditional query certificates and goal selection

Candidates are Boolean goals, scored by their conditional probabilities. An
approximately best screened score need not choose the best actual goal. Its
regret is bounded by the two candidates' query radii plus optimization error.
These are observational choices, not causal interventions or arbitrary rewards.
Native ensembles retain their aggregation gap; no pooled joint law is assumed.
-/

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.QueryDecision

open Mettapedia.PLN.Core.CompletePLN Mettapedia.PLN.Comparisons.DeductionStability
open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointDistribution
open Mettapedia.Cybernetics.ApproximateAdequacy.DecisionBounds

variable {Candidate : Type*}

/-- Every admissible approximately best score has the certified pairwise regret. -/
def RegretBound (actual screened radius : Candidate → ℝ) (admissible : Candidate → Prop) : Prop :=
  ∀ selected η, admissible selected →
    (∀ c, admissible c → screened c ≤ screened selected + η) →
    ∀ alternative, admissible alternative →
      actual alternative - actual selected ≤ radius alternative + radius selected + η

/-- Query certificates imply the decision contract; only two radii are charged. -/
theorem regret_le (actual screened radius : Candidate → ℝ) (admissible : Candidate → Prop)
    (error : ∀ c, admissible c → |actual c - screened c| ≤ radius c) :
    RegretBound actual screened radius admissible := by
  intro selected η allowed best alternative available
  have first := abs_le.mp (error alternative available)
  have second := abs_le.mp (error selected allowed)
  linarith [best alternative available]

/-- Goals share one antecedent and mediator in the same finite joint model. -/
theorem finite_query_regret {n : ℕ} (joint : JointDistribution n) (a b : Fin n)
    (goal : Candidate → Fin n) (admissible : Candidate → Prop)
    (possible : 0 < marginalProb joint a) :
    RegretBound (completeDeduction joint a b ∘ goal)
      (fun c => estimate (deductionPremises joint a b (goal c)))
      (deductionRadius joint a b ∘ goal) admissible :=
  regret_le _ _ _ admissible (fun c _ =>
    FiniteJointBalancedInformation.query_error_le_sqrt_balanced_cmi joint a b (goal c) possible)

/-- A common information budget gives a uniform `2δ + η` decision bound. -/
theorem uniform_information_regret {n : ℕ} (joint : JointDistribution n) (a b : Fin n)
    (goal : Candidate → Fin n) (admissible : Candidate → Prop) (selected : Candidate) (η I : ℝ)
    (possible : 0 < marginalProb joint a)
    (information : ∀ c, admissible c → deductionInformation joint a b (goal c) ≤ I)
    (allowed : admissible selected)
    (best : ∀ c, admissible c → estimate (deductionPremises joint a b (goal c)) ≤
      estimate (deductionPremises joint a b (goal selected)) + η)
    (alternative : Candidate) (available : admissible alternative) :
    completeDeduction joint a b (goal alternative) - completeDeduction joint a b (goal selected) ≤
      2 * balancedRadius (marginalProb joint a) I + η := by
  apply regret_le_of_score_error _ _ admissible selected _ η _ allowed best alternative available
  intro c hc
  apply (FiniteJointBalancedInformation.query_error_le_sqrt_balanced_cmi joint a b (goal c) possible).trans
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (information c hc) (sub_nonneg.mpr (marginal_prob_bounds joint a).2))
    (by positivity))

/-- Finite nonempty admissible families admit a certified screened optimum.
This existence theorem makes no claim about efficiently comparing real scores. -/
theorem finite_optimal_query [Fintype Candidate] {n : ℕ} (joint : JointDistribution n)
    (a b : Fin n) (goal : Candidate → Fin n) (admissible : Candidate → Prop)
    (nonempty : ∃ c, admissible c) (possible : 0 < marginalProb joint a) :
    ∃ selected, admissible selected ∧
      (∀ c, admissible c → estimate (deductionPremises joint a b (goal c)) ≤
        estimate (deductionPremises joint a b (goal selected))) ∧
      ∀ c, admissible c → completeDeduction joint a b (goal c) -
        completeDeduction joint a b (goal selected) ≤
          deductionRadius joint a b (goal c) + deductionRadius joint a b (goal selected) := by
  obtain ⟨selected, allowed, best⟩ := finite_optimal_exists admissible
    (fun c => estimate (deductionPremises joint a b (goal c))) nonempty
  refine ⟨selected, allowed, best, fun c hc => ?_⟩
  simpa using finite_query_regret joint a b goal admissible possible selected 0 allowed
    (fun c hc => by simpa [Mettapedia.Enactive.Razor.Criterion.ofBenefit] using best c hc) c hc

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.FiniteEventMass Mettapedia.PLN.WorldModel
open Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet
open ScreeningError EnsembleInformationError PLNBNCompilation

variable {V : Type*} [Fintype V] [DecidableEq V] {bn : BayesianNetwork V}
  [∀ v, Fintype (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]

/-- CPT goals use actual conditional mass, without assuming screening. -/
theorem cpt_query_regret (cpt : bn.DiscreteCPT) (obs : Candidate → Fin 3 → bn.JointSpace → Bool)
    (admissible : Candidate → Prop)
    (possible : ∀ c, admissible c → 0 < mass (realWeight cpt) (obs c 0)) :
    RegretBound (fun c => mass (realWeight cpt) (fun w => obs c 2 w && obs c 0 w) /
      mass (realWeight cpt) (obs c 0))
      (fun c => estimate (deductionPremises (observedJoint cpt (obs c)) 0 1 2))
      (fun c => observedInformationRadius cpt (obs c)) admissible :=
  regret_le _ _ _ admissible (fun c hc =>
    BalancedInformationError.cpt_query_error_le_sqrt_balanced_cmi cpt (obs c) (possible c hc))

variable [∀ v, DecidableEq (bn.stateSpace v)]
  [∀ v, MeasurableSingletonClass (bn.stateSpace v)] [DecidableRel bn.graph.edges]

/-- Native pooling charges component dependence and aggregation. Fixed-context
goals instantiate the first two atoms identically for every candidate. -/
theorem ensemble_query_regret (models : BNWorldModel.State (bn := bn))
    (atoms : Candidate → Fin 3 → Σ v, bn.stateSpace v) (admissible : Candidate → Prop)
    (nonempty : 0 < models.card)
    (possible : ∀ c, admissible c → ∀ model ∈ models,
      0 < mass (realWeight model) (atomObservations (atoms c) 0)) :
    RegretBound (fun c => (queryReadout models (AtomQuery.link (atoms c 0) (atoms c 2)) : ℝ))
      (fun c => pooledEstimate models (atoms c)) (fun c => ensembleRadius models (atoms c)) admissible :=
  regret_le _ _ _ admissible (fun c hc => wm_ensemble_error_le models (atoms c) nonempty (possible c hc))

namespace Controls

/-- A rare antecedent and its complement, with an always-false mediator. -/
noncomputable def rareRanking : JointDistribution 3 where
  prob w := if w.val = 1 then 1/4 else if w.val = 4 then 3/4 else 0
  prob_nonneg w := by split_ifs <;> norm_num
  prob_sum_one := by change (∑ w : Fin 8, _) = 1; norm_num [Fin.sum_univ_succ]

/-- Screening reverses the ordering of two goals in this same coherent law. -/
theorem ranking_readouts :
    completeDeduction rareRanking 0 1 0 = 1 ∧ completeDeduction rareRanking 0 1 2 = 0 ∧
    estimate (deductionPremises rareRanking 0 1 0) = 1/4 ∧
    estimate (deductionPremises rareRanking 0 1 2) = 3/4 := by
  norm_num [completeDeduction, estimate, deductionPremises,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation.plnDeductionStrength,
    condProb, jointProb2, marginalProb, rareRanking, worldToAssignment,
    ← Fin.sum_ofFn, List.ofFn, Fin.foldr, Fin.foldr.loop]

/-- The wrong screened choice incurs one unit of actual regret, within its certificate. -/
theorem wrong_ranking_regret :
    completeDeduction rareRanking 0 1 0 - completeDeduction rareRanking 0 1 2 = 1 ∧
    1 ≤ deductionRadius rareRanking 0 1 0 + deductionRadius rareRanking 0 1 2 := by
  rcases ranking_readouts with ⟨actual₀, actual₂, screened₀, screened₂⟩
  refine ⟨by rw [actual₀, actual₂]; norm_num, ?_⟩
  have bound := finite_query_regret rareRanking 0 1 (fun c : Bool => if c then 2 else 0)
    (fun _ => True)
    (by norm_num [marginalProb, rareRanking, worldToAssignment,
      ← Fin.sum_ofFn, List.ofFn, Fin.foldr, Fin.foldr.loop]) true 0 trivial
    (by intro c _; cases c <;> norm_num [screened₀, screened₂]) false trivial
  simpa only [Function.comp_apply, Bool.false_eq_true, ↓reduceIte, actual₀, actual₂, sub_zero, add_zero] using bound

end Controls

end Mettapedia.PLN.Bridges.ProbabilityTheory.QueryDecision
