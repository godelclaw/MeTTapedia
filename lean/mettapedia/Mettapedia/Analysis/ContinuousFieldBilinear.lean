import Mettapedia.Analysis.ContinuousFieldInnerProduct
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Bilinear calculus in the uniform norm on continuous fields -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.ContinuousFieldBilinear

open scoped RealInnerProductSpace
open MeasureTheory
variable {X E F G : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def pointwise (B : E →L[ℝ] F →L[ℝ] G) (f : C(X, E)) (g : C(X, F)) : C(X, G) :=
  ⟨fun x ↦ B (f x) (g x), (B.continuous.comp f.continuous).clm_apply g.continuous⟩

def pointwiseLinear (B : E →L[ℝ] F →L[ℝ] G) : C(X, E) →ₗ[ℝ] C(X, F) →ₗ[ℝ] C(X, G) :=
  LinearMap.mk₂ ℝ (pointwise B)
    (fun f h g ↦ by ext x; simp [pointwise, map_add])
    (fun c f g ↦ by ext x; simp [pointwise, map_smul])
    (fun f g h ↦ by ext x; simp [pointwise, map_add])
    (fun c f g ↦ by ext x; simp [pointwise, map_smul])

theorem norm_pointwise_le (B : E →L[ℝ] F →L[ℝ] G) (f : C(X, E)) (g : C(X, F)) :
    ‖pointwise B f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
  apply ((pointwise B f g).norm_le (by positivity)).mpr
  intro x
  exact (B.le_opNorm₂ (f x) (g x)).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg B))
      (g.norm_coe_le_norm x) (norm_nonneg _) (by positivity))

set_option maxHeartbeats 800000 in
def pointwiseCLM (B : E →L[ℝ] F →L[ℝ] G) : C(X, E) →L[ℝ] C(X, F) →L[ℝ] C(X, G) :=
  (pointwiseLinear B).mkContinuous₂ ‖B‖ (by
    intro f g
    change ‖pointwise B f g‖ ≤ _
    exact norm_pointwise_le B f g)

theorem hasDerivAt_pointwise (B : E →L[ℝ] F →L[ℝ] G)
    {f : ℝ → C(X, E)} {g : ℝ → C(X, F)} {df : C(X, E)} {dg : C(X, F)} {t : ℝ}
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t) :
    HasDerivAt (fun τ ↦ pointwise B (f τ) (g τ))
      (pointwise B (f t) dg + pointwise B df (g t)) t :=
  (pointwiseCLM B).hasDerivAt_of_bilinear (fun _ ↦ hf) (fun _ ↦ hg)

section Energy
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

theorem hasDerivAt_integral_norm_sq {f : ℝ → C(X, V)} {df : C(X, V)} {t : ℝ}
    (hf : HasDerivAt f df t) :
    HasDerivAt (fun τ ↦ ∫ x, ‖f τ x‖ ^ 2 ∂μ) (2 * ∫ x, ⟪f t x, df x⟫ ∂μ) t := by
  have h := ((ContinuousMap.toLp 2 μ ℝ).hasFDerivAt.comp_hasDerivAt t hf).norm_sq
  simpa only [Function.comp_def, ContinuousFieldMinkowski.norm_toL2_sq,
    ContinuousFieldInnerProduct.inner_toLp] using h

end Energy
end Mettapedia.Analysis.ContinuousFieldBilinear
