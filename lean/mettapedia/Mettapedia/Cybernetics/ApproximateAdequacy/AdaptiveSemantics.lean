import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptivePolicy
import Mettapedia.Cybernetics.ApproximateAdequacy.DecisionBounds

/-!
# Finite policy semantics and sufficient representations

Joint state/observation compatibility transports the terminal distribution.
Policy values are its expected rewards. Latent-state marginal agreement alone
does not preserve the observations that select later actions.
-/

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob

variable {S C O A : Type*} [Fintype S] [Fintype C] [Fintype O]

noncomputable instance observationPolicyFintype (O A : Type*) [Fintype O] [Fintype A] (n : ℕ) :
    Fintype (ObservationPolicy O A n) := by
  classical
  exact match n with
    | 0 => inferInstanceAs (Fintype PUnit)
    | n + 1 =>
        letI := observationPolicyFintype O A n
        inferInstanceAs (Fintype (A × (O → ObservationPolicy O A n)))

/-- The induced terminal-state distribution, retaining the observation-contingent branches. -/
noncomputable def terminalLaw [DecidableEq S] (kernel : A → S → Prob (S × O)) :
    {n : ℕ} → ObservationPolicy O A n → S → Prob S
  | 0, _, s => Prob.dirac s
  | n + 1, policy, s =>
      Prob.bind (kernel policy.1 s)
        (fun next => terminalLaw kernel (n := n) (policy.2 next.2) next.1)

/-- The value recurrence is the expectation of the independently constructed terminal law. -/
theorem terminalLaw_value [DecidableEq S] (kernel : A → S → Prob (S × O))
    (reward : S → ℝ) {n : ℕ} (policy : ObservationPolicy O A n) (s : S) :
    (∑ t, (terminalLaw kernel policy s).1 t * reward t) =
      adaptiveValue kernel reward policy s := by
  induction n generalizing s with
  | zero =>
      change (∑ t, (Prob.dirac s).1 t * reward t) = reward s
      exact expectation_dirac s reward
  | succ n ih =>
      rw [terminalLaw, expectation_bind]
      simp only [ih, adaptiveValue, expect]

section Coarsening

variable [DecidableEq C] [DecidableEq O]
variable (view : S → C) (source : A → S → Prob (S × O)) (target : A → C → Prob (C × O))
variable (compatible : ∀ a s,
  coarsen (source a s) (fun next => (view next.1, next.2)) = target a (view s))
include compatible

/-- Compatible joint steps preserve the independently defined terminal law.
The branch-selecting observation is retained along with the state view. -/
theorem terminalLaw_coarsen [DecidableEq S]
    {n : ℕ} (policy : ObservationPolicy O A n) (s : S) :
    coarsen (terminalLaw source policy s) view = terminalLaw target policy (view s) := by
  induction n generalizing s with
  | zero => exact coarsen_dirac s view
  | succ n ih =>
      change coarsen (bind (source policy.1 s)
        (fun next => terminalLaw source (policy.2 next.2) next.1)) view = _
      rw [coarsen_bind]
      simp_rw [ih]
      exact (bind_of_coarsen (source policy.1 s) (fun next => (view next.1, next.2))
        (fun next => terminalLaw target (policy.2 next.2) next.1)).trans
          (congrArg (fun law => bind law (fun next => terminalLaw target (policy.2 next.2) next.1))
            (compatible policy.1 s))

/-- Exact state aggregation preserves every adaptive policy value when it
retains both next abstract state and the branch-selecting observation. -/
theorem adaptiveValue_coarsen
    (reward : C → ℝ) {n : ℕ} (policy : ObservationPolicy O A n) (s : S) :
    adaptiveValue source (reward ∘ view) policy s =
      adaptiveValue target reward policy (view s) := by
  classical
  rw [← terminalLaw_value source (reward ∘ view), ← terminalLaw_value target reward]
  simp only [Function.comp_apply]
  rw [← coarsen_expectation (terminalLaw source policy s) view reward,
    terminalLaw_coarsen view source target compatible]

/-- A factored reward has the same prior-averaged policy value in the compressed model. -/
theorem expected_adaptiveValue_coarsen
    (prior : Prob S) (reward : C → ℝ) {n : ℕ} (policy : ObservationPolicy O A n) :
    expect prior.1 (adaptiveValue source (reward ∘ view) policy) =
      expect (coarsen prior view).1 (adaptiveValue target reward policy) := by
  rw [show adaptiveValue source (reward ∘ view) policy =
    adaptiveValue target reward policy ∘ view from
      funext (adaptiveValue_coarsen view source target compatible reward policy)]
  exact (coarsen_expectation prior view _).symm

end Coarsening

/-- Nonempty admissible finite-horizon policies have an optimum. -/
theorem finite_policy_optimal_exists [Fintype A] {n : ℕ}
    (admissible : ObservationPolicy O A n → Prop) (score : ObservationPolicy O A n → ℝ)
    (nonempty : ∃ p, admissible p) :
    ∃ p, (Mettapedia.Enactive.Razor.Criterion.ofBenefit admissible score).IsOptimal p :=
  DecisionBounds.finite_optimal_exists admissible score nonempty

end Mettapedia.Cybernetics.ApproximateAdequacy
