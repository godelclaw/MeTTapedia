import Mettapedia.ProbabilityTheory.BayesianInference.Basic
import Mettapedia.ProbabilityTheory.FiniteConditionalStability

/-!
# Event conditioning and conditional divergence

Event conditioning is the existing Bayesian posterior with an indicator
likelihood. When two models give the conditioning event the same positive
mass, the conditional divergence consumes at most that event's share of the
full divergence. Pinsker then gives a conditional-query error bound with a
square-root dependence on the inverse carrier mass.
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference.EventConditioning

open scoped BigOperators
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.FiniteEventMass
open Mettapedia.ProbabilityTheory.FiniteConditionalStability

variable {Ω : Type*} [Fintype Ω]

def indicator (event : Ω → Bool) : Ω → ℝ := fun world => if event world then 1 else 0

theorem evidence_indicator (prior : Prob Ω) (event : Ω → Bool) :
    evidence prior (indicator event) = mass prior.1 event := by
  simp only [evidence, indicator, mass, mul_ite, mul_one, mul_zero]

/-- Event conditioning through the Bayesian posterior. Positive event mass
is required. -/
noncomputable def condition (prior : Prob Ω) (event : Ω → Bool)
    (possible : 0 < mass prior.1 event) : Prob Ω :=
  posterior prior (indicator event) (by intro world; unfold indicator; split_ifs <;> norm_num)
    (by simpa only [evidence_indicator] using possible)

theorem condition_apply (prior : Prob Ω) (event : Ω → Bool)
    (possible : 0 < mass prior.1 event) (world : Ω) :
    (condition prior event possible).1 world =
      (if event world then prior.1 world else 0) / mass prior.1 event := by
  simp only [condition, posterior_apply, evidence_indicator, indicator, mul_ite, mul_one, mul_zero]

theorem conditioned_event_mass (prior : Prob Ω) (event query : Ω → Bool)
    (possible : 0 < mass prior.1 event) :
    mass (condition prior event possible).1 query = conditional prior.1 query event := by
  unfold conditional mass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro world _
  rw [condition_apply]
  cases he : event world <;> cases hq : query world <;> simp [he, hq, mass]

theorem condition_supported (p q : Prob Ω) (event : Ω → Bool)
    (pPossible : 0 < mass p.1 event) (qPossible : 0 < mass q.1 event)
    (supported : ∀ world, 0 < p.1 world → 0 < q.1 world) :
    ∀ world, 0 < (condition p event pPossible).1 world →
      0 < (condition q event qPossible).1 world := by
  intro world positive
  rw [condition_apply] at positive ⊢
  by_cases present : event world = true
  · simp only [present, if_true] at positive ⊢
    exact div_pos (supported world ((div_pos_iff_of_pos_right pPossible).mp positive)) qPossible
  · simp [present] at positive

theorem condition_kl_scale (p q : Prob Ω) (event : Ω → Bool)
    (pPossible : 0 < mass p.1 event) (qPossible : 0 < mass q.1 event)
    (same : mass p.1 event = mass q.1 event) :
    mass p.1 event * klSum (condition p event pPossible).1 (condition q event qPossible).1 =
      klSumOn (Finset.univ.filter (fun world => event world = true)) p.1 q.1 := by
  classical
  rw [klSum_eq_sum, Finset.mul_sum]
  unfold klSumOn
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro world _
  simp only [condition_apply, ← same]
  by_cases present : event world = true
  · simp only [present, if_true, div_div_div_cancel_right₀ pPossible.ne']
    field_simp
  · simp [present]

private theorem sum_filter_not_event (weight : Ω → ℝ) (event : Ω → Bool) :
    (∑ world ∈ Finset.univ.filter (fun world => ¬ event world = true), weight world) =
      mass weight (fun world => !event world) := by
  rw [Finset.sum_filter]
  unfold mass
  apply Finset.sum_congr rfl
  intro world _
  cases h : event world <;> simp [h]

/-- Equal event masses make the complementary divergence nonnegative. The
support premise is required by the real-valued KL convention at zero. -/
theorem scaled_condition_kl_le (p q : Prob Ω) (event : Ω → Bool)
    (pPossible : 0 < mass p.1 event) (qPossible : 0 < mass q.1 event)
    (same : mass p.1 event = mass q.1 event)
    (supported : ∀ world, 0 < p.1 world → 0 < q.1 world) :
    mass p.1 event * klSum (condition p event pPossible).1 (condition q event qPossible).1 ≤
      klSum p.1 q.1 := by
  classical
  rw [condition_kl_scale p q event pPossible qPossible same]
  have outsideNonneg :
      0 ≤ klSumOn (Finset.univ.filter (fun world => ¬ event world = true)) p.1 q.1 := by
    apply klSumOn_nonneg _ _ _ (fun world _ => p.2.1 world) (fun world _ => q.2.1 world)
      (fun world _ => supported world)
    apply le_of_eq
    rw [sum_filter_not_event, sum_filter_not_event, complement, complement, p.2.2, q.2.2, same]
  have split := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun world => event world = true) (fun world => p.1 world * Real.log (p.1 world / q.1 world))
  simpa only [klSum, klSumOn] using (le_add_of_nonneg_right outsideNonneg |>.trans_eq split)

/-- Conditional event error has a stronger denominator dependence when the
conditioning mass is shared: `2 m error² ≤ KL(p‖q)`. -/
theorem conditional_error_sq_le_kl (p q : Prob Ω) (event query : Ω → Bool)
    (pPossible : 0 < mass p.1 event) (qPossible : 0 < mass q.1 event)
    (same : mass p.1 event = mass q.1 event)
    (supported : ∀ world, 0 < p.1 world → 0 < q.1 world) :
    2 * mass p.1 event * (conditional p.1 query event - conditional q.1 query event) ^ 2 ≤
      klSum p.1 q.1 := by
  let posteriorP := condition p event pPossible
  let posteriorQ := condition q event qPossible
  have posteriorSupport := condition_supported p q event pPossible qPossible supported
  have squared := l1_sq_le_two_klSum posteriorP posteriorQ posteriorSupport
  have eventBound := event_error_le_half_l1 posteriorP posteriorQ query
  have l1Nonneg : 0 ≤ ∑ world, |posteriorP.1 world - posteriorQ.1 world| :=
    Finset.sum_nonneg fun world _ => abs_nonneg _
  have posteriorError :
      2 * (mass posteriorP.1 query - mass posteriorQ.1 query) ^ 2 ≤
        klSum posteriorP.1 posteriorQ.1 := by
    have squaredBound := mul_self_le_mul_self (abs_nonneg _) eventBound
    nlinarith [sq_abs (mass posteriorP.1 query - mass posteriorQ.1 query)]
  have weighted := mul_le_mul_of_nonneg_left posteriorError pPossible.le
  have jointBound := scaled_condition_kl_le p q event pPossible qPossible same supported
  have result := weighted.trans jointBound
  simpa only [posteriorP, posteriorQ, conditioned_event_mass, mul_comm, mul_left_comm, mul_assoc] using result

theorem conditional_error_le_sqrt_kl (p q : Prob Ω) (event query : Ω → Bool)
    (pPossible : 0 < mass p.1 event) (qPossible : 0 < mass q.1 event)
    (same : mass p.1 event = mass q.1 event)
    (supported : ∀ world, 0 < p.1 world → 0 < q.1 world) :
    |conditional p.1 query event - conditional q.1 query event| ≤
      Real.sqrt (klSum p.1 q.1 / (2 * mass p.1 event)) := by
  have squared := conditional_error_sq_le_kl p q event query pPossible qPossible same supported
  have denominator : 0 < 2 * mass p.1 event := mul_pos (by norm_num) pPossible
  have divided : (conditional p.1 query event - conditional q.1 query event) ^ 2 ≤
      klSum p.1 q.1 / (2 * mass p.1 event) := by
    apply (le_div_iff₀ denominator).mpr
    nlinarith
  rw [← Real.sqrt_sq (abs_nonneg (conditional p.1 query event - conditional q.1 query event))]
  apply Real.sqrt_le_sqrt
  simpa only [sq_abs] using divided

end Mettapedia.ProbabilityTheory.BayesianInference.EventConditioning
