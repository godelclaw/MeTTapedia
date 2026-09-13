import Mettapedia.Analysis.ContinuousFieldMinkowski

/-! # Spatial Cauchy--Schwarz for continuous Hilbert-space-valued fields -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.ContinuousFieldInnerProduct

open scoped RealInnerProductSpace
open MeasureTheory

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (μ : Measure X) [IsFiniteMeasure μ]

theorem inner_toLp (f g : C(X, E)) :
    ⟪f.toLp 2 μ ℝ, g.toLp 2 μ ℝ⟫ = ∫ x, ⟪f x, g x⟫ ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp (p := 2) (𝕜 := ℝ) μ, g.coeFn_toLp (p := 2) (𝕜 := ℝ) μ] with x hf hg
  rw [hf, hg]

theorem abs_integral_inner_le (f g : X → E) (hf : Continuous f) (hg : Continuous g) :
    |∫ x, ⟪f x, g x⟫ ∂μ| ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have h := abs_real_inner_le_norm (ContinuousMap.toLp 2 μ ℝ ⟨f, hf⟩)
    (ContinuousMap.toLp 2 μ ℝ ⟨g, hg⟩)
  simpa only [inner_toLp, ContinuousFieldMinkowski.norm_toL2, ContinuousMap.coe_mk] using h

end Mettapedia.Analysis.ContinuousFieldInnerProduct
