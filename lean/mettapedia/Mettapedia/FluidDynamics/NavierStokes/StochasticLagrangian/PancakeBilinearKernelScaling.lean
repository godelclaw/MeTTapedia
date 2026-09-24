import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeConeKernelScaling
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSmoothCoherentSymbol
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Bilinear anisotropic kernel scaling for coherent stretching

The coherent pancake gain belongs to the bilinear Biot--Savart stretching
symbol, not to the coherent projection by itself.  This module supplies the
correct endpoint template for that bilinear symbol.

There are four transverse integration variables (two for the source and two
for the receiver) and two axial variables.  Once the symbol algebra factors
one genuine aperture power `delta`, its inverse kernel has the form

`K_delta(y_perp,z_perp;y_ax,z_ax) = delta^5
  K(delta y_perp, delta z_perp; y_ax,z_ax)`.

The four-dimensional Jacobian consumes four powers and leaves exactly
`delta` in `L¹`.  The bilinear Young estimate then keeps both inputs in
`L∞`.  This file proves that analytic mechanism; identifying the explicit
localized coherent stretching symbol with the rescaled kernel is the next
symbol-specific theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeBilinearKernelScaling

open MeasureTheory
open PancakeConeKernelScaling
open PancakeSmoothCoherentSymbol
open scoped SchwartzMap

/-- Four transverse physical coordinates: two for each bilinear input. -/
abbrev BilinearTransverseSpace := EuclideanSpace ℝ (Fin 4)

/-- Two axial physical coordinates: one for each bilinear input. -/
abbrev BilinearAxialSpace := EuclideanSpace ℝ (Fin 2)

/-- Product coordinates for a translation-invariant bilinear kernel. -/
abbrev BilinearKernelSpace := BilinearTransverseSpace × BilinearAxialSpace

/-- Explicit product Lebesgue measure used by the Fubini calculation. -/
abbrev bilinearKernelVolume : Measure BilinearKernelSpace :=
  (volume : Measure BilinearTransverseSpace).prod
    (volume : Measure BilinearAxialSpace)

/-- Coefficients of a complex-bilinear operator on Fourier three-vectors.
This finite tensor representation has a transparent continuous norm and is
equivalent to a bilinear map in the fixed three-dimensional target. -/
abbrev CoherentBilinearOperator :=
  Fin 3 → Fin 3 → Fin 3 → ℂ

/-- Apply a bilinear coefficient tensor to two complex three-vectors. -/
def applyCoherentBilinearOperator (A : CoherentBilinearOperator)
    (u v : ComplexVec3) : ComplexVec3 :=
  fun i ↦ ∑ j : Fin 3, ∑ l : Fin 3, A i j l * u j * v l

/-- The tensor sup norm controls the associated bilinear map, with the
finite dimensional constant `3 * 3 = 9`. -/
theorem norm_applyCoherentBilinearOperator_le
    (A : CoherentBilinearOperator) (u v : ComplexVec3) :
    ‖applyCoherentBilinearOperator A u v‖ ≤
      9 * ‖A‖ * ‖u‖ * ‖v‖ := by
  have hnonneg : 0 ≤ 9 * ‖A‖ * ‖u‖ * ‖v‖ := by positivity
  rw [pi_norm_le_iff_of_nonneg hnonneg]
  intro i
  unfold applyCoherentBilinearOperator
  calc
    ‖∑ j : Fin 3, ∑ l : Fin 3, A i j l * u j * v l‖ ≤
        ∑ j : Fin 3, ∑ l : Fin 3, ‖A i j l * u j * v l‖ := by
      exact (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun j _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _j : Fin 3, ∑ _l : Fin 3, ‖A‖ * ‖u‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      rw [norm_mul, norm_mul]
      gcongr
      · exact (norm_le_pi_norm (A i j) l).trans
          ((norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i))
      · exact norm_le_pi_norm u j
      · exact norm_le_pi_norm v l
    _ = 9 * ‖A‖ * ‖u‖ * ‖v‖ := by
      simp
      ring

/-- The first anisotropic displacement encoded by the six kernel
coordinates. -/
def firstDisplacement (p : BilinearKernelSpace) : AnisotropicSpace :=
  (!₂[p.1 0, p.1 1], p.2 0)

/-- The second anisotropic displacement encoded by the six kernel
coordinates. -/
def secondDisplacement (p : BilinearKernelSpace) : AnisotropicSpace :=
  (!₂[p.1 2, p.1 3], p.2 1)

@[fun_prop]
theorem continuous_firstDisplacement : Continuous firstDisplacement := by
  unfold firstDisplacement
  fun_prop

@[fun_prop]
theorem continuous_secondDisplacement : Continuous secondDisplacement := by
  unfold secondDisplacement
  fun_prop

/-- Four-dimensional transverse dilation, leaving both axial coordinates
fixed. -/
def bilinearTransverseDilationLinearEquiv (delta : ℝ) (hdelta : delta ≠ 0) :
    BilinearKernelSpace ≃ₗ[ℝ] BilinearKernelSpace where
  toFun p := (delta • p.1, p.2)
  invFun p := (delta⁻¹ • p.1, p.2)
  left_inv p := by ext <;> simp [hdelta]
  right_inv p := by ext <;> simp [hdelta]
  map_add' p q := by ext <;> simp [smul_add]
  map_smul' c p := by ext <;> simp [smul_smul, mul_comm]

set_option synthInstance.maxHeartbeats 100000 in
/-- The bilinear transverse dilation as a linear homeomorphism. -/
def bilinearTransverseDilationContinuousLinearEquiv
    (delta : ℝ) (hdelta : delta ≠ 0) :
    BilinearKernelSpace ≃L[ℝ] BilinearKernelSpace :=
  (bilinearTransverseDilationLinearEquiv delta hdelta).toContinuousLinearEquiv

/-- The correct four-Jacobian rescaling after one aperture factor has
already been extracted from the bilinear symbol. -/
def rescaledBilinearKernel
    (delta : ℝ) (K : BilinearKernelSpace → CoherentBilinearOperator)
    (p : BilinearKernelSpace) : CoherentBilinearOperator :=
  ((delta ^ 5 : ℝ) : ℂ) • K (delta • p.1, p.2)

/-- Iterated operator-norm mass. -/
def iteratedBilinearKernelL1
    (K : BilinearKernelSpace → CoherentBilinearOperator) : ℝ :=
  ∫ y : BilinearTransverseSpace,
    ∫ z : BilinearAxialSpace, ‖K (y, z)‖

/-- Exact `L¹` scaling: four transverse Jacobian powers cancel four of
the five kernel powers, leaving the genuine aperture factor. -/
theorem iteratedBilinearKernelL1_rescaled
    (K : BilinearKernelSpace → CoherentBilinearOperator)
    {delta : ℝ} (hdelta : 0 < delta) :
    iteratedBilinearKernelL1 (rescaledBilinearKernel delta K) =
      delta * iteratedBilinearKernelL1 K := by
  let G : BilinearTransverseSpace → ℝ := fun y ↦
    ∫ z : BilinearAxialSpace, ‖K (y, z)‖
  have hscale : (∫ y : BilinearTransverseSpace, G (delta • y)) =
      (delta ^ 4)⁻¹ * ∫ y : BilinearTransverseSpace, G y := by
    have h := Measure.integral_comp_smul
      (volume : Measure BilinearTransverseSpace) G delta
    simpa [finrank_euclideanSpace,
      abs_of_pos (inv_pos.mpr (pow_pos hdelta 4))] using h
  unfold iteratedBilinearKernelL1 rescaledBilinearKernel
  simp_rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos hdelta 5), integral_const_mul]
  change delta ^ 5 * (∫ y : BilinearTransverseSpace, G (delta • y)) =
    delta * ∫ y : BilinearTransverseSpace, G y
  rw [hscale]
  field_simp

/-- Translation-invariant bilinear kernel action. -/
def bilinearKernelAction
    (K : BilinearKernelSpace → CoherentBilinearOperator)
    (f g : AnisotropicSpace → ComplexVec3)
    (x : AnisotropicSpace) : ComplexVec3 :=
  ∫ p, applyCoherentBilinearOperator (K p)
      (f (x - firstDisplacement p))
      (g (x - secondDisplacement p)) ∂bilinearKernelVolume

/-- Bilinear endpoint Young inequality, retaining both input `L∞` norms. -/
theorem norm_bilinearKernelAction_le
    (K : BilinearKernelSpace → CoherentBilinearOperator)
    (f g : AnisotropicSpace → ComplexVec3)
    (x : AnisotropicSpace) (M N : ℝ)
    (hK : Integrable K bilinearKernelVolume) (hKc : Continuous K)
    (hf : Continuous f) (hg : Continuous g)
    (hfb : ∀ y, ‖f y‖ ≤ M) (hgb : ∀ y, ‖g y‖ ≤ N) :
    ‖bilinearKernelAction K f g x‖ ≤
      9 * (∫ p, ‖K p‖ ∂bilinearKernelVolume) * M * N := by
  have hM : 0 ≤ M := (norm_nonneg (f x)).trans (hfb x)
  have hN : 0 ≤ N := (norm_nonneg (g x)).trans (hgb x)
  have hcont : Continuous (fun p : BilinearKernelSpace ↦
      applyCoherentBilinearOperator (K p)
        (f (x - firstDisplacement p))
        (g (x - secondDisplacement p))) := by
    unfold applyCoherentBilinearOperator
    fun_prop
  have hdom : Integrable
      (fun p : BilinearKernelSpace ↦ 9 * ‖K p‖ * M * N)
      bilinearKernelVolume :=
    (hK.norm.const_mul 9).mul_const M |>.mul_const N
  have hpoint : ∀ p : BilinearKernelSpace,
      ‖applyCoherentBilinearOperator (K p)
          (f (x - firstDisplacement p))
          (g (x - secondDisplacement p))‖ ≤ 9 * ‖K p‖ * M * N := by
    intro p
    refine (norm_applyCoherentBilinearOperator_le (K p) _ _).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hfb _)
        (mul_nonneg (by norm_num) (norm_nonneg (K p))))
      (hgb _) (norm_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg (K p))) hM)
  have hint : Integrable (fun p : BilinearKernelSpace ↦
      applyCoherentBilinearOperator (K p)
        (f (x - firstDisplacement p))
        (g (x - secondDisplacement p))) bilinearKernelVolume := by
    exact hdom.mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
  unfold bilinearKernelAction
  calc
    ‖∫ p : BilinearKernelSpace,
        applyCoherentBilinearOperator (K p)
          (f (x - firstDisplacement p))
          (g (x - secondDisplacement p)) ∂bilinearKernelVolume‖ ≤
        ∫ p : BilinearKernelSpace,
          ‖applyCoherentBilinearOperator (K p)
            (f (x - firstDisplacement p))
            (g (x - secondDisplacement p))‖ ∂bilinearKernelVolume :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ p : BilinearKernelSpace, 9 * ‖K p‖ * M * N
          ∂bilinearKernelVolume :=
      integral_mono hint.norm hdom hpoint
    _ = 9 * (∫ p : BilinearKernelSpace,
          ‖K p‖ ∂bilinearKernelVolume) * M * N := by
      rw [integral_mul_const, integral_mul_const, integral_const_mul]

/-- Product-space mass equals the iterated mass. -/
theorem integral_norm_eq_iteratedBilinearKernelL1
    (K : BilinearKernelSpace → CoherentBilinearOperator)
    (hK : Integrable K bilinearKernelVolume) :
    (∫ p, ‖K p‖ ∂bilinearKernelVolume) =
      iteratedBilinearKernelL1 K := by
  have hKnorm : Integrable (fun p : BilinearKernelSpace ↦ ‖K p‖)
      bilinearKernelVolume := hK.norm
  unfold bilinearKernelVolume at hKnorm ⊢
  unfold iteratedBilinearKernelL1
  simpa only [abs_norm] using
    (integral_prod (fun p : BilinearKernelSpace ↦ ‖K p‖) hKnorm)

/-- Bilinear `L∞ × L∞ → L∞` aperture gain after the coherent stretching
symbol has supplied one genuine `delta` factor.  The symbol-specific layer
must prove the two displayed kernel integrability hypotheses. -/
theorem norm_rescaledBilinearKernelAction_le
    (K : BilinearKernelSpace → CoherentBilinearOperator)
    (f g : AnisotropicSpace → ComplexVec3)
    (x : AnisotropicSpace) (M N : ℝ)
    {delta : ℝ} (hdelta : 0 < delta)
    (hK : Integrable K bilinearKernelVolume)
    (hKdelta : Integrable (rescaledBilinearKernel delta K)
      bilinearKernelVolume)
    (hKc : Continuous K)
    (hf : Continuous f) (hg : Continuous g)
    (hfb : ∀ y, ‖f y‖ ≤ M) (hgb : ∀ y, ‖g y‖ ≤ N) :
    ‖bilinearKernelAction (rescaledBilinearKernel delta K) f g x‖ ≤
      9 * delta * (∫ p, ‖K p‖ ∂bilinearKernelVolume) * M * N := by
  have hKdeltaCont : Continuous (rescaledBilinearKernel delta K) := by
    unfold rescaledBilinearKernel
    fun_prop
  have hYoung := norm_bilinearKernelAction_le
    (rescaledBilinearKernel delta K) f g x M N
      hKdelta hKdeltaCont hf hg hfb hgb
  rw [integral_norm_eq_iteratedBilinearKernelL1 _ hKdelta,
    iteratedBilinearKernelL1_rescaled K hdelta,
    ← integral_norm_eq_iteratedBilinearKernelL1 K hK] at hYoung
  convert hYoung using 1 <;> ring

end PancakeBilinearKernelScaling
end NavierStokes
end FluidDynamics
end Mettapedia
