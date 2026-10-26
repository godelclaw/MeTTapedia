import Mettapedia.InformationTheory.FiniteRecovery
import Mettapedia.ProbabilityTheory.BayesianInference.Coarsening
import Mettapedia.Cybernetics.ApproximateAdequacy.DecisionBounds

/-!
# Bayesian updates and decisions after finite recovery

Recovery commutes with a likelihood carried by the retained observation.
Discarded KL bounds reconstructed expectations and approximate decision regret.
After conditioning, the applicable budget is the new posterior's KL loss;
no uniform conditioning guarantee is inferred from the old budget.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy.RecoveryDecision

open Finset Real
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.InformationTheory.FiniteRecovery
open Mettapedia.ProbabilityTheory.BayesianInference

variable {Ω C Candidate : Type*} [Fintype Ω] [Fintype C] [DecidableEq C]

/-- Supported reconstruction retains the likelihood's evidence exactly. -/
theorem evidence_recover (q : Prob Ω) (view : Ω → C) (r : Prob C)
    (support : ∀ c, 0 < r.1 c → 0 < pushforward q.1 view c) (likelihood : C → ℝ) :
    evidence (recover q view r) (likelihood ∘ view) = evidence r likelihood := by
  rw [← evidence_coarsen, coarsen_recover q view r support]

/-- A retained likelihood updates the recovered law and the coarse law compatibly. -/
theorem recover_posterior (q : Prob Ω) (view : Ω → C) (r : Prob C)
    (support : ∀ c, 0 < r.1 c → 0 < pushforward q.1 view c)
    (likelihood : C → ℝ) (nonneg : ∀ c, 0 ≤ likelihood c)
    (possible : 0 < evidence r likelihood) :
    recover q view (posterior r likelihood nonneg possible) =
      posterior (recover q view r) (likelihood ∘ view) (fun x => nonneg (view x))
        (by rw [evidence_recover q view r support]; exact possible) := by
  apply Subtype.ext
  funext x
  rw [recover_apply q view _ (fun c positive =>
      support c ((posterior_pos_iff r likelihood nonneg possible c).mp positive).1),
    posterior_apply, posterior_apply, recover_apply q view r support,
    evidence_recover q view r support]
  change q.1 x * (r.1 (view x) * likelihood (view x) / evidence r likelihood) /
      pushforward q.1 view (view x) =
    (q.1 x * r.1 (view x) / pushforward q.1 view (view x)) * likelihood (view x) /
      evidence r likelihood
  ring

/-- Exact recovery before observation implies exact recovery of the fine posterior. -/
theorem recover_posterior_exact (p q : Prob Ω) (view : Ω → C)
    (support : ∀ x, 0 < p.1 x → 0 < q.1 x)
    (exactRecovery : recover q view (Prob.coarsen p view) = p)
    (likelihood : C → ℝ) (nonneg : ∀ c, 0 ≤ likelihood c)
    (possible : 0 < evidence p (likelihood ∘ view)) :
    recover q view (posterior (Prob.coarsen p view) likelihood nonneg
      (by rw [evidence_coarsen]; exact possible)) =
      posterior p (likelihood ∘ view) (fun x => nonneg (view x)) possible := by
  simpa only [exactRecovery] using recover_posterior q view (Prob.coarsen p view)
    (coarsen_support p q view support) likelihood nonneg
    (by rw [evidence_coarsen]; exact possible)

/-- Conditioning uses its own information-loss budget, with no unchanged-prior shortcut. -/
theorem posterior_recovery_l1_sq_le (p q : Prob Ω) (view : Ω → C)
    (support : ∀ x, 0 < p.1 x → 0 < q.1 x)
    (likelihood : C → ℝ) (nonneg : ∀ c, 0 ≤ likelihood c)
    (possible : 0 < evidence p (likelihood ∘ view)) :
    let fine := posterior p (likelihood ∘ view) (fun x => nonneg (view x)) possible
    let coarse := posterior (Prob.coarsen p view) likelihood nonneg
      (by rw [evidence_coarsen]; exact possible)
    (∑ x, |fine.1 x - (recover q view coarse).1 x|)^2 ≤ 2 * klLoss fine q view := by
  dsimp only
  have bound := recovery_l1_sq_le
    (posterior p (likelihood ∘ view) (fun x => nonneg (view x)) possible) q view
    (fun x positive => support x
      ((posterior_pos_iff p _ (fun x => nonneg (view x)) possible x).mp positive).1)
  rwa [coarsen_posterior] at bound

/-- A bounded readout pays its range times the reconstruction total variation. -/
theorem expectation_error (p q : Prob Ω) (view : Ω → C)
    (support : ∀ x, 0 < p.1 x → 0 < q.1 x) (score : Ω → ℝ)
    {lo hi : ℝ} (ordered : lo ≤ hi)
    (lower : ∀ x, lo ≤ score x) (upper : ∀ x, score x ≤ hi) :
    |(∑ x, p.1 x * score x) -
      ∑ x, (recover q view (Prob.coarsen p view)).1 x * score x| ≤
      ((hi - lo) / 2) * sqrt (2 * klLoss p q view) := by
  exact (abs_expectation_sub_le_of_bounds p _ score lower upper).trans
    (mul_le_mul_of_nonneg_left (recovery_l1_le p q view support) (by linarith))

/-- Approximate optimization under the reconstructed law inherits a task-value guarantee. -/
theorem regret_le (p q : Prob Ω) (view : Ω → C)
    (support : ∀ x, 0 < p.1 x → 0 < q.1 x)
    (score : Candidate → Ω → ℝ) (admissible : Candidate → Prop)
    {lo hi : ℝ} (ordered : lo ≤ hi)
    (lower : ∀ c, admissible c → ∀ x, lo ≤ score c x)
    (upper : ∀ c, admissible c → ∀ x, score c x ≤ hi)
    (selected : Candidate) (selected_admissible : admissible selected) (η : ℝ)
    (best : ∀ c, admissible c →
      (∑ x, (recover q view (Prob.coarsen p view)).1 x * score c x) ≤
        (∑ x, (recover q view (Prob.coarsen p view)).1 x * score selected x) + η)
    (alternative : Candidate) (alternative_admissible : admissible alternative) :
    (∑ x, p.1 x * score alternative x) - (∑ x, p.1 x * score selected x) ≤
      (hi - lo) * sqrt (2 * klLoss p q view) + η := by
  have bound := DecisionBounds.regret_le_of_score_error
    (fun c => ∑ x, p.1 x * score c x)
    (fun c => ∑ x, (recover q view (Prob.coarsen p view)).1 x * score c x)
    admissible selected (((hi - lo) / 2) * sqrt (2 * klLoss p q view)) η
    (fun c eligible => expectation_error p q view support (score c) ordered
      (lower c eligible) (upper c eligible)) selected_admissible best alternative alternative_admissible
  linarith

/-- Finite nonempty admissible decision families have an actual reconstructed-score maximizer. -/
theorem optimal_exists [Fintype Candidate] (q : Prob Ω) (view : Ω → C) (r : Prob C)
    (score : Candidate → Ω → ℝ) (admissible : Candidate → Prop)
    (nonempty : ∃ c, admissible c) :
    ∃ selected, admissible selected ∧ ∀ c, admissible c →
      (∑ x, (recover q view r).1 x * score c x) ≤
        ∑ x, (recover q view r).1 x * score selected x := by
  exact DecisionBounds.finite_optimal_exists admissible
    (fun c => ∑ x, (recover q view r).1 x * score c x) nonempty

namespace Controls

noncomputable def actual : Prob (Fin 2) := binaryDist (3/4) (by norm_num) (by norm_num)
noncomputable def reference : Prob (Fin 2) := binaryDist (1/4) (by norm_num) (by norm_num)
def score (choice : Bool) (x : Fin 2) : ℝ :=
  if choice then (if x = 0 then 1 else 0) else (if x = 1 then 1 else 0)

private theorem reference_positive (x : Fin 2) : 0 < reference.1 x := by
  fin_cases x <;> norm_num [reference, binaryDist]

private theorem score_nonneg (choice : Bool) (x : Fin 2) : 0 ≤ score choice x := by
  cases choice <;> simp only [score, Bool.false_eq_true, ↓reduceIte]
  all_goals split_ifs <;> norm_num

private theorem score_le_one (choice : Bool) (x : Fin 2) : score choice x ≤ 1 := by
  cases choice <;> simp only [score, Bool.false_eq_true, ↓reduceIte]
  all_goals split_ifs <;> norm_num

/-- The reconstructed law selects an action with strictly worse actual value. -/
theorem concrete_regret :
    (∑ x, actual.1 x * score true x) - (∑ x, actual.1 x * score false x) = 1/2 := by
  norm_num [actual, binaryDist, score, Fin.sum_univ_two]

/-- The independently computed half-unit regret obeys the recovery-information bound. -/
theorem concrete_regret_bound :
    1/2 ≤ sqrt (2 * klLoss actual reference (fun _ => ())) := by
  have best (choice : Bool) (_ : choice ∈ (Finset.univ : Finset Bool)) :
      (∑ x, (recover reference (fun _ => ()) (Prob.coarsen actual (fun _ => ()))).1 x * score choice x) ≤
        (∑ x, (recover reference (fun _ => ()) (Prob.coarsen actual (fun _ => ()))).1 x * score false x) + 0 := by
    rw [FiniteRecovery.Controls.constant_recover]
    cases choice <;> norm_num [reference, binaryDist, score, Fin.sum_univ_two]
  have bound := regret_le actual reference (fun _ => ()) (fun x _ => reference_positive x)
    score (fun choice => choice ∈ (Finset.univ : Finset Bool)) (lo := 0) (hi := 1) (by norm_num)
    (fun choice _ => score_nonneg choice) (fun choice _ => score_le_one choice)
    false (by simp) 0 best true (by simp)
  simpa only [concrete_regret, sub_zero, one_mul, add_zero] using bound

def retainedLikelihood (c : Bool) : ℝ := if c then 2 else 1

private theorem likelihood_nonneg (c : Bool) : 0 ≤ retainedLikelihood c := by
  cases c <;> norm_num [retainedLikelihood]

private theorem observation_possible :
    0 < evidence FiniteRecovery.Controls.source
      (retainedLikelihood ∘ FiniteRecovery.Controls.mergedView) := by
  norm_num [evidence, FiniteRecovery.Controls.source, FiniteRecovery.Controls.mergedView,
    retainedLikelihood, Function.comp_def, Fin.sum_univ_succ]

/-- A genuinely merged pair is still recovered after a nonconstant retained observation. -/
theorem exact_after_observation :
    recover FiniteRecovery.Controls.reference FiniteRecovery.Controls.mergedView
      (posterior (Prob.coarsen FiniteRecovery.Controls.source FiniteRecovery.Controls.mergedView)
        retainedLikelihood likelihood_nonneg
        (by rw [evidence_coarsen]; exact observation_possible)) =
      posterior FiniteRecovery.Controls.source
        (retainedLikelihood ∘ FiniteRecovery.Controls.mergedView)
        (fun x => likelihood_nonneg (FiniteRecovery.Controls.mergedView x)) observation_possible :=
  recover_posterior_exact _ _ _
    (by intro x _; fin_cases x <;> norm_num [FiniteRecovery.Controls.reference])
    FiniteRecovery.Controls.noninjective_exact.2.2 _ likelihood_nonneg observation_possible

/-- An impossible observation supplies no positive-evidence posterior premise. -/
theorem impossible_observation : ¬ 0 < evidence reference (fun _ => 0) := by
  simp [evidence]

/-- A fine likelihood can reveal information that a constant retained observation cannot carry. -/
theorem unretained_likelihood_changes_recovery :
    let likelihood : Fin 2 → ℝ := fun x => if x = 0 then 1 else 0
    let fine := posterior reference likelihood (by intro x; dsimp [likelihood]; split_ifs <;> norm_num)
      (by norm_num [likelihood, evidence, reference, binaryDist, Fin.sum_univ_two])
    recover reference (fun _ => ()) (Prob.coarsen fine (fun _ => ())) ≠ fine := by
  dsimp only
  rw [FiniteRecovery.Controls.constant_recover]
  intro equal
  have first := congrArg (fun law : Prob (Fin 2) => law.1 0) equal
  norm_num [posterior_apply, evidence, reference, binaryDist, Fin.sum_univ_two] at first

end Controls

end Mettapedia.Cybernetics.ApproximateAdequacy.RecoveryDecision
