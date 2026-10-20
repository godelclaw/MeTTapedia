import Mettapedia.ProbabilityTheory.BayesianInference.BalancedEventConditioning
import Mettapedia.ProbabilityTheory.BooleanPairMass

/-!
# Balanced conditional-error controls

A positively supported correlated table gives a nonzero query-error example.
Two separating tables show why the preserved query marginal and the support
premise are substantive. The real-valued logarithm convention at zero cannot
replace support by an unchecked numerical KL expression.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianInference.BalancedConditioningControls

open scoped BigOperators
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.FiniteEventMass
open Mettapedia.ProbabilityTheory.FiniteConditionalStability
open Mettapedia.ProbabilityTheory.BooleanPairMass
open Mettapedia.ProbabilityTheory.BayesianInference.BalancedEventConditioning

noncomputable def correlated : Prob (Bool × Bool) :=
  ⟨fun world => if world.1 = world.2 then 3/8 else 1/8, by
    constructor
    · intro world
      dsimp only
      split_ifs <;> norm_num
    · norm_num [Fintype.sum_prod_type, Fintype.sum_bool]⟩

noncomputable def uniform : Prob (Bool × Bool) :=
  ⟨fun _ => 1/4, by constructor <;> norm_num [Fintype.sum_prod_type, Fintype.sum_bool]⟩

/-- Error `1/4` at source mass `1/2` forces KL at least `1/8` by the
balanced certificate. Both models have strictly positive cells. -/
theorem nonzero_supported_error :
    conditional correlated.1 Prod.snd Prod.fst - conditional uniform.1 Prod.snd Prod.fst = 1/4 ∧
      (1/8 : ℝ) ≤ klSum correlated.1 uniform.1 := by
  have possible : 0 < mass correlated.1 Prod.fst := by
    norm_num [mass_fst, correlated, Fintype.sum_bool]
  have sameSource : mass correlated.1 Prod.fst = mass uniform.1 Prod.fst := by
    norm_num [mass_fst, correlated, uniform, Fintype.sum_bool]
  have sameQuery : mass correlated.1 Prod.snd = mass uniform.1 Prod.snd := by
    norm_num [mass_snd, correlated, uniform, Fintype.sum_bool]
  have support : ∀ world, 0 < correlated.1 world → 0 < uniform.1 world := by
    intro world _
    norm_num [uniform]
  have bound := conditional_error_sq_le_balanced_kl correlated uniform Prod.fst Prod.snd
    possible sameSource sameQuery support
  have error : conditional correlated.1 Prod.snd Prod.fst -
      conditional uniform.1 Prod.snd Prod.fst = 1/4 := by
    norm_num [conditional_snd_fst, correlated, uniform, Fintype.sum_bool]
  refine ⟨error, ?_⟩
  rw [error] at bound
  have carrier : mass correlated.1 Prod.fst = 1/2 := by
    norm_num [mass_fst, correlated, Fintype.sum_bool]
  rw [carrier] at bound
  nlinarith

private noncomputable def first : Prob Bool :=
  ⟨fun world => if world then 3/4 else 1/4, by
    constructor
    · intro world; cases world <;> norm_num
    · norm_num [Fintype.sum_bool]⟩

private noncomputable def second : Prob Bool :=
  ⟨fun world => if world then 1/4 else 3/4, by
    constructor
    · intro world; cases world <;> norm_num
    · norm_num [Fintype.sum_bool]⟩

/-- Full support and equal conditioning mass are insufficient when the
query marginals differ. A full-mass carrier makes the omitted premise visible. -/
theorem query_marginal_agreement_is_essential :
    (∀ world, 0 < first.1 world → 0 < second.1 world) ∧
      mass first.1 (fun _ => true) = mass second.1 (fun _ => true) ∧
      ¬ (2 * mass first.1 (fun _ => true) *
        (conditional first.1 id (fun _ => true) - conditional second.1 id (fun _ => true)) ^ 2 ≤
          (1 - mass first.1 (fun _ => true)) * klSum first.1 second.1) := by
  constructor
  · intro world _
    cases world <;> norm_num [second]
  · norm_num [mass, conditional, first, second, Fintype.sum_bool]

noncomputable def diagonal : Prob (Bool × Bool) :=
  ⟨fun world => if world.1 = world.2 then 1/2 else 0, by
    constructor
    · intro world; dsimp only; split_ifs <;> norm_num
    · norm_num [Fintype.sum_prod_type, Fintype.sum_bool]⟩

noncomputable def antidiagonal : Prob (Bool × Bool) :=
  ⟨fun world => if world.1 = world.2 then 0 else 1/2, by
    constructor
    · intro world; dsimp only; split_ifs <;> norm_num
    · norm_num [Fintype.sum_prod_type, Fintype.sum_bool]⟩

/-- Equal endpoint marginals do not make the real-log KL convention a
supported divergence. These disjoint-support tables have error one. -/
theorem support_is_essential :
    mass diagonal.1 Prod.fst = mass antidiagonal.1 Prod.fst ∧
      mass diagonal.1 Prod.snd = mass antidiagonal.1 Prod.snd ∧
      klSum diagonal.1 antidiagonal.1 = 0 ∧
      ¬ (2 * mass diagonal.1 Prod.fst *
        (conditional diagonal.1 Prod.snd Prod.fst - conditional antidiagonal.1 Prod.snd Prod.fst) ^ 2 ≤
          (1 - mass diagonal.1 Prod.fst) * klSum diagonal.1 antidiagonal.1) := by
  norm_num [mass_fst, mass_snd, conditional_snd_fst, diagonal, antidiagonal,
    klSum, klSumOn, Fintype.sum_prod_type, Fintype.sum_bool]

end Mettapedia.ProbabilityTheory.BayesianInference.BalancedConditioningControls
