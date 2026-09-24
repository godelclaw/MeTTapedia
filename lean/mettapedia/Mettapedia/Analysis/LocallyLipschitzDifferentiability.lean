import Mathlib.Analysis.Calculus.Rademacher

/-! # Rademacher differentiability for locally Lipschitz maps

Compact-ball exhaustion removes the global Lipschitz constant from the
finite-dimensional theorem. The measure is any additive Haar measure.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace LocallyLipschitz

theorem ae_differentiableAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] {f : E → F} (hf : LocallyLipschitz f)
    (mu : Measure E) [Measure.IsAddHaarMeasure mu] :
    ∀ᵐ x ∂mu, DifferentiableAt ℝ f x := by
  have hball : ∀ n : ℕ, ∀ᵐ x ∂mu, x ∈ Metric.ball (0 : E) (n + 1 : ℝ) →
      DifferentiableAt ℝ f x := by
    intro n
    obtain ⟨C, hC⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall (0 : E) (n + 1 : ℝ))
    filter_upwards [hC.ae_differentiableWithinAt_of_mem (μ := mu)] with x hx hxb
    exact (hx (Metric.ball_subset_closedBall hxb)).differentiableAt
      (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hxb) Metric.ball_subset_closedBall)
  filter_upwards [ae_all_iff.mpr hball] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  apply hx n
  simpa only [Metric.mem_ball, dist_zero_right] using hn.trans (by norm_num : (n : ℝ) < n + 1)

end LocallyLipschitz

/-- Derivatives of a jointly continuous family are strongly measurable
when evaluated at a fixed real parameter. -/
theorem Continuous.stronglyMeasurable_deriv_const
    {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopologyEither X E] {f : X → ℝ → E}
    (hf : Continuous f.uncurry) (t : ℝ) :
    StronglyMeasurable (fun x ↦ deriv (f x) t) := by
  exact (stronglyMeasurable_deriv_with_param hf).comp_measurable
    (show Measurable (fun x : X ↦ (x, t)) from measurable_id.prodMk measurable_const)
