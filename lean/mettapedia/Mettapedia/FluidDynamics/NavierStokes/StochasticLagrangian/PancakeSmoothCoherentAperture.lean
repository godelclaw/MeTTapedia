import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSmoothCoherentSymbol
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeConeKernelScaling

/-!
# Attenuated aperture scaling of the smooth coherent operator kernel

The localized coherent projection constructed in
`PancakeSmoothCoherentSymbol` has an actual operator-valued Schwartz kernel in
Euclidean three-space.  This module transports that kernel to transverse/axial
coordinates and performs the two-dimensional transverse rescaling.

For the deliberately attenuated rescaled kernel

`K_delta(x_perp,z) = delta^3 K(delta x_perp,z)`,

the operator-norm `L¹` mass is exactly `delta` times the unit-aperture mass.
Combining this identity with the endpoint Young estimate gives an
`L∞ → L∞` bound with one full factor.  In two transverse dimensions an
unattenuated cone multiplier instead has the physical rescaling
`delta^2 K(delta x_perp,z)` and no such `L¹` gain.  Thus the extra power here
also attenuates the Fourier symbol by `delta`; it does **not** prove that the
coherent projection itself has aperture-small operator norm.  The periodic
lower bound in `PancakePeriodicOperatorKernel` proves that any exact
projection fixing a unit Fourier mode has kernel mass at least one.  The
route must obtain its aperture gain from the bilinear Biot--Savart stretching
symbol before applying this endpoint mechanism.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeSmoothCoherentAperture

open MeasureTheory
open PancakeConeKernelScaling
open PancakeSmoothCoherentSymbol
open scoped SchwartzMap

/-- Transverse/axial coordinates identified with Euclidean three-space. -/
def anisotropicToEuclideanLinearEquiv :
    AnisotropicSpace ≃ₗ[ℝ] EuclideanFrequency where
  toFun p := !₂[p.1 0, p.1 1, p.2]
  invFun ξ := (!₂[ξ 0, ξ 1], ξ 2)
  left_inv p := by
    apply Prod.ext
    · ext i
      fin_cases i <;> simp
    · simp
  right_inv ξ := by
    ext i
    fin_cases i <;> simp
  map_add' p q := by
    ext i
    fin_cases i <;> simp
  map_smul' c p := by
    ext i
    fin_cases i <;> simp

/-- The coordinate identification as a linear homeomorphism. -/
def anisotropicToEuclideanEquiv :
    AnisotropicSpace ≃L[ℝ] EuclideanFrequency :=
  anisotropicToEuclideanLinearEquiv.toContinuousLinearEquiv

/-- The constructed coherent operator kernel in transverse/axial
coordinates. -/
def anisotropicLocalizedProjectionKernel (D : BufferedCoherentCutoff) :
    𝓢(AnisotropicSpace, ComplexVec3 →L[ℂ] ComplexVec3) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ anisotropicToEuclideanEquiv
    (localizedProjectionOperatorKernel D)

@[simp]
theorem anisotropicLocalizedProjectionKernel_apply
    (D : BufferedCoherentCutoff) (p : AnisotropicSpace) :
    anisotropicLocalizedProjectionKernel D p =
      localizedProjectionOperatorKernel D
        (anisotropicToEuclideanEquiv p) := rfl

/-- Transverse rescaling with one additional amplitude factor.  The natural
two-dimensional geometric rescaling has power `delta^2`; the third power
here is an explicit attenuation. -/
def rescaledComplexOperatorKernel (delta : ℝ)
    (K : AnisotropicSpace → (ComplexVec3 →L[ℂ] ComplexVec3))
    (p : AnisotropicSpace) : ComplexVec3 →L[ℂ] ComplexVec3 :=
  ((delta ^ 3 : ℝ) : ℂ) • K (delta • p.1, p.2)

/-- Iterated `L¹` mass of the complex-operator norm. -/
def iteratedComplexOperatorKernelL1
    (K : AnisotropicSpace → (ComplexVec3 →L[ℂ] ComplexVec3)) : ℝ :=
  iteratedKernelL1 (fun p ↦ ‖K p‖)

/-- Exact mass scaling of the attenuated complex-operator kernel. -/
theorem iteratedComplexOperatorKernelL1_rescaled
    (K : AnisotropicSpace → (ComplexVec3 →L[ℂ] ComplexVec3))
    {delta : ℝ} (hdelta : 0 < delta) :
    iteratedComplexOperatorKernelL1
        (rescaledComplexOperatorKernel delta K) =
      delta * iteratedComplexOperatorKernelL1 K := by
  calc
    iteratedComplexOperatorKernelL1
        (rescaledComplexOperatorKernel delta K) =
        iteratedKernelL1
          (rescaledConeKernel delta (fun p : AnisotropicSpace ↦ ‖K p‖)) := by
      unfold iteratedComplexOperatorKernelL1
      apply congrArg iteratedKernelL1
      funext p
      simp [rescaledComplexOperatorKernel, rescaledConeKernel,
        norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hdelta]
    _ = delta * iteratedKernelL1
        (fun p : AnisotropicSpace ↦ ‖K p‖) :=
      iteratedKernelL1_rescaled _ hdelta
    _ = delta * iteratedComplexOperatorKernelL1 K := rfl

/-- The aperture-rescaled kernel remains Schwartz. -/
def rescaledSchwartzComplexOperatorKernel
    (delta : ℝ) (hdelta : delta ≠ 0)
    (K : 𝓢(AnisotropicSpace, ComplexVec3 →L[ℂ] ComplexVec3)) :
    𝓢(AnisotropicSpace, ComplexVec3 →L[ℂ] ComplexVec3) :=
  ((delta ^ 3 : ℝ) : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (transverseDilationContinuousLinearEquiv delta hdelta) K

@[simp]
theorem rescaledSchwartzComplexOperatorKernel_apply
    (delta : ℝ) (hdelta : delta ≠ 0)
    (K : 𝓢(AnisotropicSpace, ComplexVec3 →L[ℂ] ComplexVec3))
    (p : AnisotropicSpace) :
    rescaledSchwartzComplexOperatorKernel delta hdelta K p =
      rescaledComplexOperatorKernel delta K p := rfl

theorem rescaledComplexOperatorKernel_integrable
    (delta : ℝ) (hdelta : delta ≠ 0)
    (K : 𝓢(AnisotropicSpace, ComplexVec3 →L[ℂ] ComplexVec3)) :
    Integrable (rescaledComplexOperatorKernel delta K) anisotropicVolume := by
  refine ((rescaledSchwartzComplexOperatorKernel delta hdelta K).integrable
    (μ := anisotropicVolume)).congr ?_
  filter_upwards with p
  exact rescaledSchwartzComplexOperatorKernel_apply delta hdelta K p

/-- Convolution action of a complex-linear operator kernel. -/
def complexOperatorKernelAction
    (K : AnisotropicSpace → (ComplexVec3 →L[ℂ] ComplexVec3))
    (f : AnisotropicSpace → ComplexVec3) (x : AnisotropicSpace) :
    ComplexVec3 :=
  ∫ y, K y (f (x - y)) ∂anisotropicVolume

/-- Endpoint Young inequality for a complex-linear operator kernel. -/
theorem norm_complexOperatorKernelAction_le
    (K : AnisotropicSpace → (ComplexVec3 →L[ℂ] ComplexVec3))
    (f : AnisotropicSpace → ComplexVec3) (x : AnisotropicSpace) (M : ℝ)
    (hK : Integrable K anisotropicVolume) (hKc : Continuous K)
    (hf : Continuous f) (hfb : ∀ y, ‖f y‖ ≤ M) :
    ‖complexOperatorKernelAction K f x‖ ≤
      (∫ y, ‖K y‖ ∂anisotropicVolume) * M := by
  have hcont : Continuous
      (fun y : AnisotropicSpace ↦ K y (f (x - y))) := by
    fun_prop
  have hdom : Integrable
      (fun y : AnisotropicSpace ↦ ‖K y‖ * M) anisotropicVolume :=
    hK.norm.mul_const M
  have hint : Integrable
      (fun y : AnisotropicSpace ↦ K y (f (x - y))) anisotropicVolume := by
    apply hdom.mono' hcont.aestronglyMeasurable
    filter_upwards with y
    exact (K y).le_opNorm_of_le (hfb _)
  unfold complexOperatorKernelAction
  calc
    ‖∫ y : AnisotropicSpace, K y (f (x - y)) ∂anisotropicVolume‖ ≤
        ∫ y : AnisotropicSpace, ‖K y (f (x - y))‖ ∂anisotropicVolume :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : AnisotropicSpace, ‖K y‖ * M ∂anisotropicVolume := by
      apply integral_mono hint.norm hdom
      intro y
      exact (K y).le_opNorm_of_le (hfb _)
    _ = (∫ y : AnisotropicSpace, ‖K y‖ ∂anisotropicVolume) * M :=
      integral_mul_const M _

/-- Product-space mass agrees with the iterated operator-kernel mass. -/
theorem integral_norm_eq_iteratedComplexOperatorKernelL1
    (K : AnisotropicSpace → (ComplexVec3 →L[ℂ] ComplexVec3))
    (hK : Integrable K anisotropicVolume) :
    (∫ p : AnisotropicSpace, ‖K p‖ ∂anisotropicVolume) =
      iteratedComplexOperatorKernelL1 K := by
  have hKnorm : Integrable
      (fun p : AnisotropicSpace ↦ ‖K p‖) anisotropicVolume := hK.norm
  unfold anisotropicVolume at hKnorm ⊢
  unfold iteratedComplexOperatorKernelL1 iteratedKernelL1
  simpa only [abs_norm] using
    (integral_prod (fun p : AnisotropicSpace ↦ ‖K p‖) hKnorm)

/-- Endpoint estimate for the explicitly attenuated Schwartz kernel. -/
theorem norm_rescaledSchwartzComplexOperatorKernelAction_le
    (K : 𝓢(AnisotropicSpace, ComplexVec3 →L[ℂ] ComplexVec3))
    (f : AnisotropicSpace → ComplexVec3) (x : AnisotropicSpace) (M : ℝ)
    {delta : ℝ} (hdelta : 0 < delta)
    (hf : Continuous f) (hfb : ∀ y, ‖f y‖ ≤ M) :
    ‖complexOperatorKernelAction
        (rescaledComplexOperatorKernel delta K) f x‖ ≤
      delta * (∫ y, ‖K y‖ ∂anisotropicVolume) * M := by
  have hK : Integrable K anisotropicVolume :=
    K.integrable (μ := anisotropicVolume)
  have hKdelta : Integrable
      (rescaledComplexOperatorKernel delta K) anisotropicVolume :=
    rescaledComplexOperatorKernel_integrable delta hdelta.ne' K
  have hKdeltaCont : Continuous
      (rescaledComplexOperatorKernel delta K) := by
    unfold rescaledComplexOperatorKernel
    fun_prop
  have hYoung := norm_complexOperatorKernelAction_le
    (rescaledComplexOperatorKernel delta K) f x M
      hKdelta hKdeltaCont hf hfb
  rw [integral_norm_eq_iteratedComplexOperatorKernelL1 _ hKdelta,
    iteratedComplexOperatorKernelL1_rescaled K hdelta,
    ← integral_norm_eq_iteratedComplexOperatorKernelL1 K hK] at hYoung
  exact hYoung

/-- The final specialization uses the explicitly constructed nonzero coherent
kernel, attenuated by the extra `delta` amplitude.  This is not an exact
realization of the unattenuated coherent projection family. -/
theorem norm_rescaledExplicitCoherentKernelAction_le
    (f : AnisotropicSpace → ComplexVec3) (x : AnisotropicSpace) (M : ℝ)
    {delta : ℝ} (hdelta : 0 < delta)
    (hf : Continuous f) (hfb : ∀ y, ‖f y‖ ≤ M) :
    ‖complexOperatorKernelAction
        (rescaledComplexOperatorKernel delta
          (anisotropicLocalizedProjectionKernel explicitBufferedCutoff))
        f x‖ ≤
      delta *
        (∫ y, ‖anisotropicLocalizedProjectionKernel
          explicitBufferedCutoff y‖ ∂anisotropicVolume) * M := by
  exact norm_rescaledSchwartzComplexOperatorKernelAction_le
    (anisotropicLocalizedProjectionKernel explicitBufferedCutoff)
      f x M hdelta hf hfb

end PancakeSmoothCoherentAperture
end NavierStokes
end FluidDynamics
end Mettapedia
