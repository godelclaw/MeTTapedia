import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Orthogonal-gradient retention across a task sequence

Bennani, Doan, and Sugiyama, *Generalisation Guarantees for Continual
Learning with Orthogonal Gradient Descent* (2020), Theorem 2, prove
no-forgetting on stored examples in the neural-tangent linearization when all
later updates are orthogonal to the stored Jacobian.

This file isolates and strengthens that algebraic core. Linear observations
commute with finite additive accumulation. It proves exact retention for an
arbitrary finite update sequence in a real inner-product space, an approximate
bound in terms of Jacobian drift and net displacement, hence total path length,
and a nonlinear counterexample showing why first-order orthogonality alone
does not imply finite functional retention outside the fixed-Jacobian model.

The result complements `MinimumChangeUpdate`, which constructs and
characterizes orthogonal projections, and `RetentionSafeUpdate`, which gives
finite nonlinear trust-region conditions.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

open scoped InnerProductSpace

/-- Sum of a finite sequence of parameter updates, in execution order. -/
def totalUpdate {Parameter : Type*} [AddMonoid Parameter] (updates : List Parameter) : Parameter :=
  updates.sum

/-- Parameter reached after applying a finite additive update sequence. -/
def accumulatedParameter {Parameter : Type*} [AddMonoid Parameter]
    (initial : Parameter) (updates : List Parameter) : Parameter :=
  initial + totalUpdate updates

/-- Additive observations commute with update accumulation, preserving every
input occurrence in the observed sum. -/
theorem observe_accumulatedParameter {Parameter Observation : Type*}
    [AddMonoid Parameter] [AddMonoid Observation] (observe : Parameter →+ Observation)
    (initial : Parameter) (updates : List Parameter) :
    observe (accumulatedParameter initial updates) =
      observe initial + (updates.map observe).sum := by
  simp [accumulatedParameter, totalUpdate, map_list_sum]

variable {Parameter : Type*} [NormedAddCommGroup Parameter]
  [InnerProductSpace ℝ Parameter]

/-- Change of a fixed-Jacobian scalar prediction along a finite update
sequence. -/
noncomputable def linearizedRetentionChange
    (jacobian : Parameter) (updates : List Parameter) : ℝ :=
  (updates.map (fun update => ⟪jacobian, update⟫_ℝ)).sum

/-- Total parameter-space path length of the update sequence. -/
noncomputable def updatePathLength (updates : List Parameter) : ℝ :=
  (updates.map norm).sum

/-- A scalar readout in the fixed-Jacobian, neural-tangent linearization
anchored at `initial`. -/
noncomputable def linearizedReadout
    (base : ℝ) (jacobian initial parameter : Parameter) : ℝ :=
  base + ⟪jacobian, parameter - initial⟫_ℝ

/-- The fixed-Jacobian readout change is exactly the sum of the per-update
directional derivatives. -/
theorem inner_totalUpdate_eq_linearizedRetentionChange
    (jacobian : Parameter) :
    ∀ updates : List Parameter,
      ⟪jacobian, totalUpdate updates⟫_ℝ =
        linearizedRetentionChange jacobian updates := by
  intro updates
  simpa [totalUpdate, linearizedRetentionChange] using map_list_sum (innerSL ℝ jacobian) updates

/-- Source correspondence: the prediction after the finite sequence is its
initial value plus the recursively accumulated routed derivative. -/
theorem linearizedReadout_accumulated
    (base : ℝ) (jacobian initial : Parameter)
    (updates : List Parameter) :
    linearizedReadout base jacobian initial
        (accumulatedParameter initial updates) =
      base + linearizedRetentionChange jacobian updates := by
  simp [linearizedReadout, accumulatedParameter, inner_totalUpdate_eq_linearizedRetentionChange]

/-- Exact no-forgetting theorem: if every later update is orthogonal to the
stored Jacobian, the stored linearized prediction is unchanged. -/
theorem linearizedReadout_no_forgetting
    (base : ℝ) (jacobian initial : Parameter)
    (updates : List Parameter)
    (orthogonal : ∀ update ∈ updates, ⟪jacobian, update⟫_ℝ = 0) :
    linearizedReadout base jacobian initial
        (accumulatedParameter initial updates) = base := by
  rw [linearizedReadout_accumulated]
  have hchange : linearizedRetentionChange jacobian updates = 0 :=
    List.sum_eq_zero (by simpa using orthogonal)
  rw [hchange, add_zero]

/-- The sharper cumulative bound uses net displacement; cancelling updates
need not pay the entire path length. -/
theorem linearizedRetentionChange_abs_le_norm_mul_totalUpdate
    (jacobian : Parameter) (updates : List Parameter) :
    |linearizedRetentionChange jacobian updates| ≤ ‖jacobian‖ * ‖totalUpdate updates‖ := by
  rw [← inner_totalUpdate_eq_linearizedRetentionChange]
  exact abs_real_inner_le_norm _ _

/-- Cauchy--Schwarz turns a fixed Jacobian and update path into a cumulative
linearized-retention bound. -/
theorem linearizedRetentionChange_abs_le_norm_mul_pathLength
    (jacobian : Parameter) :
    ∀ updates : List Parameter,
      |linearizedRetentionChange jacobian updates| ≤
        ‖jacobian‖ * updatePathLength updates := by
  intro updates
  apply (linearizedRetentionChange_abs_le_norm_mul_totalUpdate jacobian updates).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa [totalUpdate, updatePathLength] using norm_multiset_sum_le (updates : Multiset Parameter)

/-- If every update is orthogonal to the stored Jacobian, evaluating with a
drifted actual Jacobian is equivalent to evaluating only the Jacobian drift. -/
theorem linearizedRetentionChange_eq_jacobianDrift
    (stored actual : Parameter) :
    ∀ updates : List Parameter,
      (∀ update ∈ updates, ⟪stored, update⟫_ℝ = 0) →
      linearizedRetentionChange actual updates =
        linearizedRetentionChange (actual - stored) updates := by
  intro updates orthogonal
  have hzero : linearizedRetentionChange stored updates = 0 :=
    List.sum_eq_zero (by simpa using orthogonal)
  simp only [← inner_totalUpdate_eq_linearizedRetentionChange, inner_sub_left] at hzero ⊢
  rw [hzero, sub_zero]

/-- Jacobian drift times net displacement bounds the final readout change. -/
theorem linearizedReadout_forgetting_le_jacobianDrift_mul_totalUpdate
    (base : ℝ) (stored actual initial : Parameter) (updates : List Parameter)
    (orthogonal : ∀ update ∈ updates, ⟪stored, update⟫_ℝ = 0) :
    |linearizedReadout base actual initial (accumulatedParameter initial updates) - base| ≤
      ‖actual - stored‖ * ‖totalUpdate updates‖ := by
  rw [linearizedReadout_accumulated, add_sub_cancel_left,
    linearizedRetentionChange_eq_jacobianDrift stored actual updates orthogonal]
  exact linearizedRetentionChange_abs_le_norm_mul_totalUpdate _ _

/-- Approximate no-forgetting under Jacobian drift.  The error is controlled
by the drift norm times the total update path length, rather than being
silently treated as zero. -/
theorem linearizedReadout_forgetting_le_jacobianDrift_mul_pathLength
    (base : ℝ) (stored actual initial : Parameter)
    (updates : List Parameter)
    (orthogonal : ∀ update ∈ updates, ⟪stored, update⟫_ℝ = 0) :
    |linearizedReadout base actual initial
          (accumulatedParameter initial updates) - base| ≤
      ‖actual - stored‖ * updatePathLength updates := by
  rw [linearizedReadout_accumulated]
  simp only [add_sub_cancel_left]
  rw [linearizedRetentionChange_eq_jacobianDrift stored actual updates orthogonal]
  exact linearizedRetentionChange_abs_le_norm_mul_pathLength
    (actual - stored) updates

/-! ## Positive and negative fixtures -/

omit [InnerProductSpace ℝ Parameter] in
/-- Opposite updates cancel at the endpoint while their path length can be positive. -/
theorem cancelling_updates_endpoint_and_pathLength (initial update : Parameter) :
    accumulatedParameter initial [update, -update] = initial ∧
      updatePathLength [update, -update] = 2 * ‖update‖ := by
  simp [accumulatedParameter, totalUpdate, updatePathLength, two_mul]

/-- A two-coordinate stored feature and a sequence confined to its orthogonal
coordinate satisfy exact no-forgetting. -/
theorem twoCoordinate_orthogonal_sequence_preserves_readout :
    linearizedReadout (7 : ℝ) (1 : ℂ) 0
        (accumulatedParameter 0
          [(2 : ℝ) • Complex.I, (-3 : ℝ) • Complex.I]) = 7 := by
  apply linearizedReadout_no_forgetting
  intro update updateMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at updateMem
  rcases updateMem with rfl | rfl <;> norm_num

/-- A first-order stationary point does not make an arbitrary finite update
safe for a nonlinear readout. -/
def nonlinearQuadraticReadout (parameter : ℝ) : ℝ :=
  parameter ^ 2

theorem nonlinear_stationary_gradient_does_not_imply_no_forgetting :
    HasDerivAt nonlinearQuadraticReadout 0 0 ∧
      nonlinearQuadraticReadout (0 + 1) ≠
        nonlinearQuadraticReadout 0 := by
  constructor
  · unfold nonlinearQuadraticReadout
    simpa using (hasDerivAt_pow 2 (0 : ℝ))
  · norm_num [nonlinearQuadraticReadout]


end Mettapedia.MachineLearning.ContinualLearning
