import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeConeKernelScaling
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Operator-valued cone kernels

The Leray projector and the strain symbol are matrix-valued, so the scalar
kernel bound is not yet the correct target type.  This file lifts the
anisotropic aperture calculation to kernels taking values in bounded linear
operators.

For an operator kernel `K`, define

`K_delta(x_perp,z) = delta^3 K(delta x_perp,z)`.

The operator-norm `L¹` mass again scales by exactly `delta`, and convolution
against `K_delta` maps a uniformly bounded receiver `f` to a field bounded by
`delta * ‖K‖_L¹ * ‖f‖_∞`.  When `K` is Schwartz, every integrability and
continuity premise is discharged by construction.

This is the analytic target shape needed by the coherent Leray/strain
multiplier.  Identifying that concrete frequency symbol with a uniformly
bounded family of these kernels remains a subsequent theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeConeOperatorKernel

open MeasureTheory
open PancakeConeKernelScaling
open scoped RealInnerProductSpace SchwartzMap

/-- Two-transverse-direction rescaling of an operator-valued kernel. -/
def rescaledOperatorKernel {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (delta : ℝ) (K : AnisotropicSpace → (E →L[ℝ] F))
    (p : AnisotropicSpace) : E →L[ℝ] F :=
  delta ^ 3 • K (delta • p.1, p.2)

/-- Iterated `L¹` mass of the operator norm. -/
def iteratedOperatorKernelL1 {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : AnisotropicSpace → (E →L[ℝ] F)) : ℝ :=
  iteratedKernelL1 (fun p => ‖K p‖)

/-- Exact aperture scaling of the operator-norm kernel mass. -/
theorem iteratedOperatorKernelL1_rescaled {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : AnisotropicSpace → (E →L[ℝ] F))
    {delta : ℝ} (hdelta : 0 < delta) :
    iteratedOperatorKernelL1 (rescaledOperatorKernel delta K) =
      delta * iteratedOperatorKernelL1 K := by
  calc
    iteratedOperatorKernelL1 (rescaledOperatorKernel delta K) =
        iteratedKernelL1
          (rescaledConeKernel delta (fun p : AnisotropicSpace => ‖K p‖)) := by
      unfold iteratedOperatorKernelL1
      apply congrArg iteratedKernelL1
      funext p
      simp only [rescaledOperatorKernel, rescaledConeKernel, norm_smul,
        Real.norm_eq_abs, abs_of_pos (pow_pos hdelta 3)]
    _ = delta * iteratedKernelL1 (fun p : AnisotropicSpace => ‖K p‖) :=
      iteratedKernelL1_rescaled _ hdelta
    _ = delta * iteratedOperatorKernelL1 K := rfl

/-- Operator-kernel rescaling preserves Schwartz class. -/
def rescaledSchwartzOperatorKernel {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (delta : ℝ) (hdelta : delta ≠ 0)
    (K : 𝓢(AnisotropicSpace, E →L[ℝ] F)) :
    𝓢(AnisotropicSpace, E →L[ℝ] F) :=
  delta ^ 3 • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (transverseDilationContinuousLinearEquiv delta hdelta) K

@[simp]
theorem rescaledSchwartzOperatorKernel_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (delta : ℝ) (hdelta : delta ≠ 0)
    (K : 𝓢(AnisotropicSpace, E →L[ℝ] F)) (p : AnisotropicSpace) :
    rescaledSchwartzOperatorKernel delta hdelta K p =
      rescaledOperatorKernel delta K p := by
  rfl

/-- A rescaled Schwartz operator kernel is automatically integrable in
operator norm. -/
theorem rescaledOperatorKernel_integrable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (delta : ℝ) (hdelta : delta ≠ 0)
    (K : 𝓢(AnisotropicSpace, E →L[ℝ] F)) :
    Integrable (rescaledOperatorKernel delta K) anisotropicVolume := by
  refine ((rescaledSchwartzOperatorKernel delta hdelta K).integrable
    (μ := anisotropicVolume)).congr ?_
  filter_upwards with p
  exact rescaledSchwartzOperatorKernel_apply delta hdelta K p

/-- Convolution action of an operator-valued kernel. -/
def operatorKernelAction {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : AnisotropicSpace → (E →L[ℝ] F)) (f : AnisotropicSpace → E)
    (x : AnisotropicSpace) : F :=
  ∫ y, K y (f (x - y)) ∂anisotropicVolume

/-- Endpoint Young estimate for an operator-valued kernel. -/
theorem norm_operatorKernelAction_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : AnisotropicSpace → (E →L[ℝ] F)) (f : AnisotropicSpace → E)
    (x : AnisotropicSpace) (M : ℝ)
    (hK : Integrable K anisotropicVolume) (hKc : Continuous K)
    (hf : Continuous f) (hfb : ∀ y, ‖f y‖ ≤ M) :
    ‖operatorKernelAction K f x‖ ≤
      (∫ y, ‖K y‖ ∂anisotropicVolume) * M := by
  have hcont : Continuous
      (fun y : AnisotropicSpace => K y (f (x - y))) := by
    fun_prop
  have hdom : Integrable
      (fun y : AnisotropicSpace => ‖K y‖ * M) anisotropicVolume :=
    hK.norm.mul_const M
  have hint : Integrable
      (fun y : AnisotropicSpace => K y (f (x - y))) anisotropicVolume := by
    apply hdom.mono' hcont.aestronglyMeasurable
    filter_upwards with y
    exact (K y).le_opNorm_of_le (hfb _)
  unfold operatorKernelAction
  calc
    ‖∫ y : AnisotropicSpace, K y (f (x - y)) ∂anisotropicVolume‖
      ≤ ∫ y : AnisotropicSpace, ‖K y (f (x - y))‖ ∂anisotropicVolume :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y : AnisotropicSpace, ‖K y‖ * M ∂anisotropicVolume := by
      apply integral_mono hint.norm hdom
      intro y
      exact (K y).le_opNorm_of_le (hfb _)
    _ = (∫ y : AnisotropicSpace, ‖K y‖ ∂anisotropicVolume) * M :=
      integral_mul_const M _

/-- Product-space operator-kernel mass equals its iterated form. -/
theorem integral_norm_eq_iteratedOperatorKernelL1 {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : AnisotropicSpace → (E →L[ℝ] F))
    (hK : Integrable K anisotropicVolume) :
    (∫ p : AnisotropicSpace, ‖K p‖ ∂anisotropicVolume) =
      iteratedOperatorKernelL1 K := by
  have hKnorm : Integrable
      (fun p : AnisotropicSpace => ‖K p‖) anisotropicVolume := hK.norm
  unfold anisotropicVolume at hKnorm ⊢
  unfold iteratedOperatorKernelL1 iteratedKernelL1
  simpa only [abs_norm] using
    (integral_prod (fun p : AnisotropicSpace => ‖K p‖) hKnorm)

/-- **Schwartz operator-kernel aperture gain.**  This is the matrix-valued
`L∞ → L∞` form needed for the coherent Leray/strain multiplier. -/
theorem norm_rescaledSchwartzOperatorKernelAction_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : 𝓢(AnisotropicSpace, E →L[ℝ] F))
    (f : AnisotropicSpace → E) (x : AnisotropicSpace) (M : ℝ)
    {delta : ℝ} (hdelta : 0 < delta)
    (hf : Continuous f) (hfb : ∀ y, ‖f y‖ ≤ M) :
    ‖operatorKernelAction (rescaledOperatorKernel delta K) f x‖ ≤
      delta * (∫ y, ‖K y‖ ∂anisotropicVolume) * M := by
  have hK : Integrable K anisotropicVolume :=
    K.integrable (μ := anisotropicVolume)
  have hKdelta : Integrable
      (rescaledOperatorKernel delta K) anisotropicVolume :=
    rescaledOperatorKernel_integrable delta hdelta.ne' K
  have hKdeltaCont : Continuous (rescaledOperatorKernel delta K) := by
    unfold rescaledOperatorKernel
    fun_prop
  have hYoung := norm_operatorKernelAction_le
    (rescaledOperatorKernel delta K) f x M hKdelta hKdeltaCont hf hfb
  rw [integral_norm_eq_iteratedOperatorKernelL1 _ hKdelta,
    iteratedOperatorKernelL1_rescaled K hdelta,
    ← integral_norm_eq_iteratedOperatorKernelL1 K hK] at hYoung
  exact hYoung

end PancakeConeOperatorKernel
end NavierStokes
end FluidDynamics
end Mettapedia
