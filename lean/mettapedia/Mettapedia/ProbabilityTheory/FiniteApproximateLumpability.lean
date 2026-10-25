import Mettapedia.ProbabilityTheory.FiniteLumpability
import Mettapedia.Cybernetics.ApproximateAdequacy.SquareIteration
import Mettapedia.Cybernetics.ApproximateAdequacy.Coupling

/-!
# Approximate observation squares for finite stochastic kernels

Exact lumpability identifies the observed row of every fine state with one
coarse row. This file weakens that equality to a uniform finite ℓ¹ budget.
Mixtures do not enlarge the row budget, deterministic observations and
stochastic kernels are nonexpansive, and the existing approximate-square
iteration laws therefore apply without an independence assumption.

The bound concerns predicted distributions and bounded observers. It neither
identifies supports nor turns an approximate square into an exact quotient.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.FiniteApproximateLumpability

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob
open Mettapedia.GSLT.Scope
open Mettapedia.Cybernetics.ApproximateAdequacy
open scoped BigOperators

variable {S T C D : Type*}
  [Fintype S] [Fintype T] [Fintype C] [Fintype D]
  [DecidableEq C] [DecidableEq D]

/-- Every fine row, after observation, is within `δ` of the supplied coarse
row selected by the source observation. -/
def ApproxRows (sourceView : S → C) (targetView : T → D)
    (fine : S → Prob T) (coarse : C → Prob D) (δ : ℝ) : Prop :=
  ∀ state, l1Distance (coarsen (fine state) targetView) (coarse (sourceView state)) ≤ δ

/-- Uniform row error controls the prediction error for every prior. -/
theorem prediction_le (sourceView : S → C) (targetView : T → D)
    (fine : S → Prob T) (coarse : C → Prob D) (δ : ℝ)
    (rows : ApproxRows sourceView targetView fine coarse δ) (prior : Prob S) :
    l1Distance (coarsen (bind prior fine) targetView)
      (bind (coarsen prior sourceView) coarse) ≤ δ := by
  rw [coarsen_bind, ← bind_of_coarsen prior sourceView coarse]
  exact l1Distance_bind_rows_le prior _ _ δ rows

/-- The prediction law is precisely an approximate commuting square on
probability simplices. -/
theorem approxSquare (sourceView : S → C) (targetView : T → D)
    (fine : S → Prob T) (coarse : C → Prob D) (δ : ℝ)
    (rows : ApproxRows sourceView targetView fine coarse δ) :
    ApproxSquare l1Distance (fun prior => coarsen prior sourceView)
      (fun law => coarsen law targetView) (fun prior => bind prior fine)
      (fun prior => bind prior coarse) δ :=
  fun prior => prediction_le sourceView targetView fine coarse δ rows prior

omit [Fintype S] [Fintype C] [DecidableEq C] in
/-- Exact row compatibility is the zero-error special case. -/
theorem approxRows_zero_of_exact (sourceView : S → C) (targetView : T → D)
    (fine : S → Prob T) (coarse : C → Prob D)
    (rows : ∀ state, coarsen (fine state) targetView = coarse (sourceView state)) :
    ApproxRows sourceView targetView fine coarse 0 := by
  intro state
  rw [rows state, l1Distance_self]

omit [DecidableEq C] [DecidableEq D] in
/-- Applying the same stochastic kernel to two priors is nonexpansive. -/
theorem kernel_nonexpansive (kernel : C → Prob D) (first second : Prob C) :
    l1Distance (bind first kernel) (bind second kernel) ≤ l1Distance first second :=
  l1Distance_bind_le first second kernel

section Iteration

/-- A homogeneous approximate observation square accumulates at most `n δ`
under repeated nonexpansive coarse prediction. -/
theorem iterate (view : S → C) (fine : S → Prob S) (coarse : C → Prob C)
    (δ : ℝ) (rows : ApproxRows view view fine coarse δ) (n : ℕ) :
    ApproxSquare l1Distance (fun prior => coarsen prior view)
      (fun prior => coarsen prior view) (fun prior => bind prior fine)^[n]
      (fun prior => bind prior coarse)^[n] (n • δ) :=
  ApproxSquare.iterate l1Distance_self l1Distance_triangle
    (kernel_nonexpansive coarse) (approxSquare view view fine coarse δ rows) n

/-- If the supplied coarse update is `κ`-Lipschitz, the existing geometric
iteration theorem gives the sharper `δ Σ κ^k` budget. -/
theorem iterate_lipschitz (view : S → C) (fine : S → Prob S) (coarse : C → Prob C)
    (δ κ : ℝ) (κ_nonneg : 0 ≤ κ)
    (lipschitz : ∀ first second,
      l1Distance (bind first coarse) (bind second coarse) ≤ κ * l1Distance first second)
    (rows : ApproxRows view view fine coarse δ) (n : ℕ) :
    ApproxSquare l1Distance (fun prior => coarsen prior view)
      (fun prior => coarsen prior view) (fun prior => bind prior fine)^[n]
      (fun prior => bind prior coarse)^[n]
      (δ * ∑ k ∈ Finset.range n, κ ^ k) :=
  ApproxSquare.iterate_lipschitz l1Distance_self l1Distance_triangle κ_nonneg
    lipschitz (approxSquare view view fine coarse δ rows) n

end Iteration

/-- The same distribution budget controls every bounded observer of the
coarse prediction. The exact source-to-observation leg is `coarsen_expectation`
(equivalently, the canonical observation coupling). -/
theorem observer_error_le (sourceView : S → C) (targetView : T → D)
    (fine : S → Prob T) (coarse : C → Prob D) (δ bound : ℝ)
    (rows : ApproxRows sourceView targetView fine coarse δ)
    (observer : D → ℝ) (bound_nonneg : 0 ≤ bound)
    (bounded : ∀ outcome, |observer outcome| ≤ bound) (prior : Prob S) :
    |(∑ target, (bind prior fine).1 target * observer (targetView target)) -
        ∑ outcome, (bind (coarsen prior sourceView) coarse).1 outcome * observer outcome| ≤
      bound * δ := by
  rw [← coarsen_expectation]
  exact (abs_expectation_sub_le_l1 _ _ observer bound bounded).trans
    (mul_le_mul_of_nonneg_left
      (prediction_le sourceView targetView fine coarse δ rows prior) bound_nonneg)

/-! ## Coupling-certified row errors -/

/-- A stronger, geometry-aware row certificate supplies a coupling whose
declared transport cost is bounded. -/
def CoupledRows (sourceView : S → C) (targetView : T → D)
    (fine : S → Prob T) (coarse : C → Prob D)
    (cost : D → D → ℝ) (δ : ℝ) : Prop :=
  ∀ state, ∃ coupling : Mettapedia.Cybernetics.ApproximateAdequacy.Coupling
      (coarsen (fine state) targetView).1 (coarse (sourceView state)).1,
    coupling.cost cost ≤ δ

/-- Coupling costs mix under the prior: a pointwise Lipschitz observer has
one-step prediction error at most the uniform row transport budget. -/
theorem coupled_observer_error_le (sourceView : S → C) (targetView : T → D)
    (fine : S → Prob T) (coarse : C → Prob D) (cost : D → D → ℝ) (δ : ℝ)
    (rows : CoupledRows sourceView targetView fine coarse cost δ)
    (observer : D → ℝ)
    (observerBound : ∀ first second,
      |observer first - observer second| ≤ cost first second)
    (prior : Prob S) :
    |(∑ target, (bind prior fine).1 target * observer (targetView target)) -
        ∑ outcome, (bind (coarsen prior sourceView) coarse).1 outcome * observer outcome| ≤ δ := by
  rw [← coarsen_expectation, coarsen_bind, ← bind_of_coarsen prior sourceView coarse,
    expectation_bind, expectation_bind]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ state, (prior.1 state *
        (∑ outcome, (coarsen (fine state) targetView).1 outcome * observer outcome) -
      prior.1 state *
        (∑ outcome, (coarse (sourceView state)).1 outcome * observer outcome))| ≤
        ∑ state, |prior.1 state *
          (∑ outcome, (coarsen (fine state) targetView).1 outcome * observer outcome) -
          prior.1 state *
          (∑ outcome, (coarse (sourceView state)).1 outcome * observer outcome)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ state, prior.1 state *
        |(∑ outcome, (coarsen (fine state) targetView).1 outcome * observer outcome) -
         (∑ outcome, (coarse (sourceView state)).1 outcome * observer outcome)| := by
      apply Finset.sum_congr rfl
      intro state _
      rw [← mul_sub, abs_mul, abs_of_nonneg (prior.2.1 state)]
    _ ≤ ∑ state, prior.1 state * δ := by
      apply Finset.sum_le_sum
      intro state _
      obtain ⟨coupling, costBound⟩ := rows state
      exact mul_le_mul_of_nonneg_left
        ((coupling.abs_expect_sub_le observerBound).trans costBound) (prior.2.1 state)
    _ = δ := by rw [← Finset.sum_mul, prior.2.2, one_mul]

namespace Controls

/-- One-state agreement says nothing about a row never charged by that prior. -/
theorem one_prior_does_not_bound_all_rows :
    l1Distance
      (bind (dirac false) (dirac (S := Bool)))
      (bind (dirac false) (fun _ => dirac false)) = 0 ∧
    l1Distance
      (bind (dirac true) (dirac (S := Bool)))
      (bind (dirac true) (fun _ => dirac false)) = 2 := by
  constructor
  · simp
  · norm_num [l1Distance, bind_apply, dirac_apply, Fintype.sum_bool]

/-- The additive two-step bound can be attained. -/
theorem additive_error_is_real :
    Mettapedia.GSLT.Scope.natDist
      ((Mettapedia.GSLT.Scope.Succ.step)^[2] 0) ((id : Nat → Nat)^[2] 0) = 2 := by
  exact Mettapedia.GSLT.Scope.Succ.error_iterate 2 0

end Controls

end Mettapedia.ProbabilityTheory.FiniteApproximateLumpability
