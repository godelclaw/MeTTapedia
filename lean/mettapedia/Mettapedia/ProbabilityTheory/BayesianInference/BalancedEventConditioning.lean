import Mettapedia.ProbabilityTheory.BayesianInference.EventConditioning

/-!
# Conditional error with both marginals retained

When two probability models agree on the conditioning-event mass and the query
mass, conditional errors inside the event and its complement must balance.
Accounting for both conditional divergences strengthens Pinsker's bound to
`2 m error² ≤ (1 - m) KL`. The statement includes a full-mass conditioning
event and uses no conditioning operation on a zero-mass branch.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianInference.BalancedEventConditioning

open scoped BigOperators
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.FiniteEventMass
open Mettapedia.ProbabilityTheory.FiniteConditionalStability
open Mettapedia.ProbabilityTheory.BayesianInference.EventConditioning

variable {Ω : Type*} [Fintype Ω]

private theorem mass_true (prior : Prob Ω) : mass prior.1 (fun _ => true) = 1 := by
  simpa only [mass, if_true] using prior.2.2

/-- Pinsker specialized to a finite event. -/
theorem event_error_sq_le_kl (p q : Prob Ω) (query : Ω → Bool)
    (supported : ∀ world, 0 < p.1 world → 0 < q.1 world) :
    2 * (mass p.1 query - mass q.1 query) ^ 2 ≤ klSum p.1 q.1 := by
  have result := conditional_error_sq_le_kl p q (fun _ => true) query
    (by rw [mass_true]; exact zero_lt_one) (by rw [mass_true]; exact zero_lt_one)
    (by rw [mass_true, mass_true]) supported
  simpa only [conditional, Bool.and_true, mass_true, div_one, mul_one] using result

/-- The weighted conditional error is bounded by the divergence on its own
branch, rather than by the whole divergence separately for every branch. -/
theorem branch_error_sq_le_kl (p q : Prob Ω) (event query : Ω → Bool)
    (pPossible : 0 < mass p.1 event) (qPossible : 0 < mass q.1 event)
    (same : mass p.1 event = mass q.1 event)
    (supported : ∀ world, 0 < p.1 world → 0 < q.1 world) :
    2 * mass p.1 event * (conditional p.1 query event - conditional q.1 query event) ^ 2 ≤
      klSumOn (Finset.univ.filter (fun world => event world = true)) p.1 q.1 := by
  have bound := event_error_sq_le_kl (condition p event pPossible) (condition q event qPossible)
    query (condition_supported p q event pPossible qPossible supported)
  have weighted := mul_le_mul_of_nonneg_left bound pPossible.le
  rw [condition_kl_scale p q event pPossible qPossible same] at weighted
  simpa only [conditioned_event_mass, mul_comm, mul_left_comm, mul_assoc] using weighted

/-- The weighted identity remains valid on empty branches; no numerical
zero-denominator value is interpreted as an available conditional there. -/
theorem weighted_conditional (weight : Ω → ℝ) (positive : ∀ world, 0 ≤ weight world)
    (event query : Ω → Bool) :
    mass weight event * conditional weight query event =
      mass weight (fun world => query world && event world) := by
  unfold conditional
  by_cases empty : mass weight event = 0
  · have bounded := mono weight positive (first := fun world => query world && event world)
      (second := event) (fun world yes => by
        simp only [Bool.and_eq_true] at yes
        exact yes.2)
    have zero : mass weight (fun world => query world && event world) = 0 :=
      le_antisymm (bounded.trans_eq empty) (nonneg weight positive _)
    simp [empty, zero]
  · field_simp

/-- Equal query marginals force the two branch errors to cancel. -/
theorem conditional_error_balance (p q : Prob Ω) (event query : Ω → Bool)
    (sameEvent : mass p.1 event = mass q.1 event) (sameQuery : mass p.1 query = mass q.1 query) :
    mass p.1 event * (conditional p.1 query event - conditional q.1 query event) +
      (1 - mass p.1 event) *
        (conditional p.1 query (fun world => !event world) -
          conditional q.1 query (fun world => !event world)) = 0 := by
  have pPartition := partition p.1 query event
  have qPartition := partition q.1 query event
  have pInside := weighted_conditional p.1 p.2.1 event query
  have qInside := weighted_conditional q.1 q.2.1 event query
  have pOutside := weighted_conditional p.1 p.2.1 (fun world => !event world) query
  have qOutside := weighted_conditional q.1 q.2.1 (fun world => !event world) query
  rw [complement, p.2.2] at pOutside
  rw [complement, q.2.2, ← sameEvent] at qOutside
  rw [← sameEvent] at qInside
  linarith

private theorem kl_branch_partition (p q : Prob Ω) (event : Ω → Bool) :
    klSumOn (Finset.univ.filter (fun world => event world = true)) p.1 q.1 +
      klSumOn (Finset.univ.filter (fun world => (!event world) = true)) p.1 q.1 = klSum p.1 q.1 := by
  classical
  have filters : Finset.univ.filter (fun world => (!event world) = true) =
      Finset.univ.filter (fun world => ¬ event world = true) := by
    apply Finset.filter_congr
    intro world _
    cases event world <;> simp
  rw [filters]
  exact Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun world => event world = true) (fun world => p.1 world * Real.log (p.1 world / q.1 world))

/-- Both branch divergences yield the complementary-mass improvement. -/
theorem conditional_error_sq_le_balanced_kl (p q : Prob Ω) (event query : Ω → Bool)
    (possible : 0 < mass p.1 event) (sameEvent : mass p.1 event = mass q.1 event)
    (sameQuery : mass p.1 query = mass q.1 query)
    (supported : ∀ world, 0 < p.1 world → 0 < q.1 world) :
    2 * mass p.1 event * (conditional p.1 query event - conditional q.1 query event) ^ 2 ≤
      (1 - mass p.1 event) * klSum p.1 q.1 := by
  have balance := conditional_error_balance p q event query sameEvent sameQuery
  have outsideNonneg : 0 ≤ 1 - mass p.1 event := by
    simpa only [complement, p.2.2] using nonneg p.1 p.2.1 (fun world => !event world)
  by_cases full : 1 - mass p.1 event = 0
  · have insideOne : mass p.1 event = 1 := by linarith
    have sameConditional : conditional p.1 query event - conditional q.1 query event = 0 := by
      simpa only [insideOne, sub_self, one_mul, zero_mul, add_zero] using balance
    simp [full, sameConditional]
  · have outsidePositive := lt_of_le_of_ne outsideNonneg (Ne.symm full)
    have pOutside : 0 < mass p.1 (fun world => !event world) := by
      simpa only [complement, p.2.2] using outsidePositive
    have qOutside : 0 < mass q.1 (fun world => !event world) := by
      simpa only [complement, q.2.2, ← sameEvent] using outsidePositive
    have sameOutside : mass p.1 (fun world => !event world) =
        mass q.1 (fun world => !event world) := by
      rw [complement, complement, p.2.2, q.2.2, sameEvent]
    have inside := branch_error_sq_le_kl p q event query possible
      (by rwa [← sameEvent]) sameEvent supported
    have outside := branch_error_sq_le_kl p q (fun world => !event world) query
      pOutside qOutside sameOutside supported
    have combined := add_le_add inside outside
    rw [kl_branch_partition p q event, complement, p.2.2] at combined
    have weighted := mul_le_mul_of_nonneg_left combined outsideNonneg
    have relation : (1 - mass p.1 event) *
        (conditional p.1 query (fun world => !event world) -
          conditional q.1 query (fun world => !event world)) =
        -(mass p.1 event * (conditional p.1 query event - conditional q.1 query event)) := by
      linarith
    have squaredRelation := congrArg (fun value : ℝ => value ^ 2) relation
    nlinarith

theorem conditional_error_le_sqrt_balanced_kl (p q : Prob Ω) (event query : Ω → Bool)
    (possible : 0 < mass p.1 event) (sameEvent : mass p.1 event = mass q.1 event)
    (sameQuery : mass p.1 query = mass q.1 query)
    (supported : ∀ world, 0 < p.1 world → 0 < q.1 world) :
    |conditional p.1 query event - conditional q.1 query event| ≤
      Real.sqrt (((1 - mass p.1 event) * klSum p.1 q.1) / (2 * mass p.1 event)) := by
  have squared := conditional_error_sq_le_balanced_kl p q event query possible sameEvent sameQuery supported
  have positive : 0 < 2 * mass p.1 event := mul_pos (by norm_num) possible
  have divided : (conditional p.1 query event - conditional q.1 query event) ^ 2 ≤
      ((1 - mass p.1 event) * klSum p.1 q.1) / (2 * mass p.1 event) := by
    apply (le_div_iff₀ positive).mpr
    nlinarith
  rw [← Real.sqrt_sq (abs_nonneg _)]
  exact Real.sqrt_le_sqrt (by simpa only [sq_abs] using divided)

end Mettapedia.ProbabilityTheory.BayesianInference.BalancedEventConditioning
