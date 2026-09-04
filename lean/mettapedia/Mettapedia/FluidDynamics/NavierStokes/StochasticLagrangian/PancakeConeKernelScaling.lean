import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeConeLatticeCount
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Anisotropic cone-kernel scaling and the `L∞` receiver norm

The amplitude/lattice theorems reduce the coherent source to the correct
improved Bernstein scale.  To feed `D_Q`, however, the high-frequency receiver
must remain in `L∞`; replacing it by Fourier `ℓ¹` would lose the desired norm.
This file establishes the physical-space mechanism that avoids that loss.

For the two transverse directions and one axial direction, a cone multiplier
with amplitude gain `delta` has the rescaled inverse-kernel template

`K_delta(x_perp,z) = delta^3 K(delta x_perp,z)`.

The factor `delta^3` consists of the symbol gain `delta` and the two-dimensional
Jacobian `delta^2`.  The checked change of variables proves exactly

`‖K_delta‖_L1 = delta ‖K‖_L1`.

The second theorem is the endpoint Young estimate

`‖K * f (x)‖ ≤ ‖K‖_L1 M` whenever `‖f(y)‖ ≤ M`.

Together they retain the receiver's uniform norm with the aperture gain.  The
remaining harmonic-analysis obligation is to identify the smooth localized
coherent Leray/strain symbols with a uniformly integrable base-kernel family;
that identification is not assumed or claimed here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeConeKernelScaling

open MeasureTheory
open scoped RealInnerProductSpace SchwartzMap

/-- The two transverse physical coordinates. -/
abbrev TransversePlane := EuclideanSpace ℝ (Fin 2)

/-- Transverse/axial product coordinates used for anisotropic scaling. -/
abbrev AnisotropicSpace := TransversePlane × ℝ

/-- The explicit Borel product of transverse and axial Lebesgue measure.  It is
kept explicit to make the Fubini and Schwartz-space interfaces definitionally
agree. -/
abbrev anisotropicVolume : Measure AnisotropicSpace :=
  (volume : Measure TransversePlane).prod (volume : Measure ℝ)

/-- Kernel template with two-dimensional transverse dilation. -/
def rescaledConeKernel (delta : ℝ) (K : AnisotropicSpace → ℝ)
    (p : AnisotropicSpace) : ℝ :=
  delta ^ 3 * K (delta • p.1, p.2)

/-- Iterated `L¹` integral in transverse/axial coordinates. -/
def iteratedKernelL1 (K : AnisotropicSpace → ℝ) : ℝ :=
  ∫ x : TransversePlane, ∫ z : ℝ, |K (x, z)|

/-- The invertible dilation of the two transverse coordinates, leaving the
axial coordinate fixed. -/
def transverseDilationLinearEquiv (delta : ℝ) (hdelta : delta ≠ 0) :
    AnisotropicSpace ≃ₗ[ℝ] AnisotropicSpace where
  toFun p := (delta • p.1, p.2)
  invFun p := (delta⁻¹ • p.1, p.2)
  left_inv p := by
    ext <;> simp [hdelta]
  right_inv p := by
    ext <;> simp [hdelta]
  map_add' p q := by
    ext <;> simp [smul_add]
  map_smul' c p := by
    ext <;> simp [smul_smul, mul_comm]

/-- The transverse dilation as a continuous linear equivalence.  Finite
dimensionality supplies continuity automatically. -/
def transverseDilationContinuousLinearEquiv (delta : ℝ) (hdelta : delta ≠ 0) :
    AnisotropicSpace ≃L[ℝ] AnisotropicSpace :=
  (transverseDilationLinearEquiv delta hdelta).toContinuousLinearEquiv

/-- The rescaled kernel stays in Schwartz space. -/
def rescaledSchwartzKernel (delta : ℝ) (hdelta : delta ≠ 0)
    (K : 𝓢(AnisotropicSpace, ℝ)) : 𝓢(AnisotropicSpace, ℝ) :=
  delta ^ 3 • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (transverseDilationContinuousLinearEquiv delta hdelta) K

@[simp]
theorem rescaledSchwartzKernel_apply (delta : ℝ) (hdelta : delta ≠ 0)
    (K : 𝓢(AnisotropicSpace, ℝ)) (p : AnisotropicSpace) :
    rescaledSchwartzKernel delta hdelta K p = rescaledConeKernel delta K p := by
  rfl

/-- Unlike an arbitrary rescaled function, the rescaling of a Schwartz kernel
is automatically integrable. -/
theorem rescaledConeKernel_integrable (delta : ℝ) (hdelta : delta ≠ 0)
    (K : 𝓢(AnisotropicSpace, ℝ)) :
    Integrable (rescaledConeKernel delta K) anisotropicVolume := by
  refine ((rescaledSchwartzKernel delta hdelta K).integrable
    (μ := anisotropicVolume)).congr ?_
  filter_upwards with p
  exact rescaledSchwartzKernel_apply delta hdelta K p

/-- **Exact anisotropic aperture scaling.**  The rescaled cone kernel has
`L¹` mass `delta` times that of its unit-aperture template.  The identity is
valid under Lean's integral conventions; integrability is added below when the
identity is used as an operator bound. -/
theorem iteratedKernelL1_rescaled (K : AnisotropicSpace → ℝ)
    {delta : ℝ} (hdelta : 0 < delta) :
    iteratedKernelL1 (rescaledConeKernel delta K) =
      delta * iteratedKernelL1 K := by
  let F : TransversePlane → ℝ := fun x => ∫ z : ℝ, |K (x, z)|
  have hscale : (∫ x : TransversePlane, F (delta • x)) =
      (delta ^ 2)⁻¹ * ∫ x : TransversePlane, F x := by
    have h := Measure.integral_comp_smul (volume : Measure TransversePlane) F delta
    simpa [finrank_euclideanSpace,
      abs_of_pos (inv_pos.mpr (pow_pos hdelta 2))] using h
  unfold iteratedKernelL1 rescaledConeKernel
  simp_rw [abs_mul, abs_of_pos (pow_pos hdelta 3), integral_const_mul]
  change delta ^ 3 * (∫ x : TransversePlane, F (delta • x)) =
    delta * ∫ x : TransversePlane, F x
  rw [hscale]
  field_simp

/-- Physical-space action of a scalar convolution kernel on a vector-valued
receiver. -/
def kernelAction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : AnisotropicSpace → ℝ) (f : AnisotropicSpace → E)
    (x : AnisotropicSpace) : E :=
  ∫ y, K y • f (x - y) ∂anisotropicVolume

/-- **Endpoint Young bound.**  An integrable kernel acts on a continuous,
uniformly bounded receiver without changing the receiver norm. -/
theorem norm_kernelAction_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : AnisotropicSpace → ℝ)
    (f : AnisotropicSpace → E) (x : AnisotropicSpace) (M : ℝ)
    (hK : Integrable K anisotropicVolume) (hf : Continuous f)
    (hfb : ∀ y, ‖f y‖ ≤ M) :
    ‖kernelAction K f x‖ ≤ (∫ y, |K y| ∂anisotropicVolume) * M := by
  have hmeas : AEStronglyMeasurable
      (fun y : AnisotropicSpace => K y • f (x - y)) anisotropicVolume :=
    hK.aestronglyMeasurable.smul
      (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hdom : Integrable
      (fun y : AnisotropicSpace => |K y| * M) anisotropicVolume := by
    simpa [Real.norm_eq_abs] using hK.norm.mul_const M
  have hint : Integrable
      (fun y : AnisotropicSpace => K y • f (x - y)) anisotropicVolume := by
    apply hdom.mono' hmeas
    filter_upwards with y
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hfb _) (abs_nonneg _)
  unfold kernelAction
  calc
    ‖∫ y : AnisotropicSpace, K y • f (x - y) ∂anisotropicVolume‖
      ≤ ∫ y : AnisotropicSpace, ‖K y • f (x - y)‖ ∂anisotropicVolume :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y : AnisotropicSpace, |K y| * M ∂anisotropicVolume := by
      apply integral_mono hint.norm hdom
      intro y
      dsimp only
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hfb _) (abs_nonneg _)
    _ = (∫ y : AnisotropicSpace, |K y| ∂anisotropicVolume) * M :=
      integral_mul_const M _

/-- Product-space `L¹` mass agrees with the iterated kernel integral. -/
theorem integral_abs_eq_iteratedKernelL1 (K : AnisotropicSpace → ℝ)
    (hK : Integrable K anisotropicVolume) :
    (∫ p : AnisotropicSpace, |K p| ∂anisotropicVolume) = iteratedKernelL1 K := by
  have hKnorm : Integrable (fun p : AnisotropicSpace => |K p|) anisotropicVolume := by
    simpa [Real.norm_eq_abs] using hK.norm
  unfold anisotropicVolume at hKnorm ⊢
  exact integral_prod (fun p : AnisotropicSpace => |K p|) hKnorm

/-- **Aperture-gain `L∞` multiplier bound.**  Once a localized coherent
multiplier has the anisotropically rescaled kernel form, its action retains the
receiver's uniform norm and gains one full factor of `delta`. -/
theorem norm_rescaledConeKernelAction_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : AnisotropicSpace → ℝ)
    (f : AnisotropicSpace → E) (x : AnisotropicSpace) (M : ℝ)
    {delta : ℝ} (hdelta : 0 < delta)
    (hK : Integrable K anisotropicVolume)
    (hKdelta : Integrable (rescaledConeKernel delta K) anisotropicVolume)
    (hf : Continuous f) (hfb : ∀ y, ‖f y‖ ≤ M) :
    ‖kernelAction (rescaledConeKernel delta K) f x‖ ≤
      delta * (∫ y, |K y| ∂anisotropicVolume) * M := by
  have hYoung := norm_kernelAction_le (rescaledConeKernel delta K) f x M
    hKdelta hf hfb
  rw [integral_abs_eq_iteratedKernelL1 _ hKdelta,
    iteratedKernelL1_rescaled K hdelta,
    ← integral_abs_eq_iteratedKernelL1 K hK] at hYoung
  exact hYoung

/-- **Schwartz-kernel form of the aperture-gain estimate.**  Both kernel
integrability premises of `norm_rescaledConeKernelAction_le` are discharged by
construction. -/
theorem norm_rescaledSchwartzKernelAction_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : 𝓢(AnisotropicSpace, ℝ))
    (f : AnisotropicSpace → E) (x : AnisotropicSpace) (M : ℝ)
    {delta : ℝ} (hdelta : 0 < delta)
    (hf : Continuous f) (hfb : ∀ y, ‖f y‖ ≤ M) :
    ‖kernelAction (rescaledConeKernel delta K) f x‖ ≤
      delta * (∫ y, |K y| ∂anisotropicVolume) * M := by
  exact norm_rescaledConeKernelAction_le K f x M hdelta
    (K.integrable (μ := anisotropicVolume))
    (rescaledConeKernel_integrable delta hdelta.ne' K) hf hfb

end PancakeConeKernelScaling
end NavierStokes
end FluidDynamics
end Mettapedia
