import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeRealCoherentPairEstimate
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Smooth localized coherent projection symbol

The normalized coherent projection is singular where its coherent direction
vanishes.  A Littlewood--Paley/cone cutoff stays away from that set, but a
global Fourier symbol still needs a smooth definition through the complement.
This module implements the standard two-cutoff repair.

An inner compact cutoff carries the multiplier.  An outer cutoff is identically
one wherever the inner cutoff is nonzero.  Adding the squared buffer
`(1 - outer)^2` to the coherent denominator removes the global singularity,
while the buffer vanishes on the inner support, so the regularized matrix is
exactly the intended coherent projection there.  Every matrix entry is then a
Schwartz function by construction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeSmoothCoherentSymbol

open PancakeRealCoherentPairEstimate
open MeasureTheory
open scoped ContDiff FourierTransform RealInnerProductSpace SchwartzMap

def coordinate (v : RealVec3) : Fin 3 → ℝ :=
  fun i ↦ if i = 0 then v.1 else if i = 1 then v.2.1 else v.2.2

@[simp] theorem coordinate_zero (v : RealVec3) : coordinate v 0 = v.1 := by
  simp [coordinate]
@[simp] theorem coordinate_one (v : RealVec3) : coordinate v 1 = v.2.1 := by
  simp [coordinate]
@[simp] theorem coordinate_two (v : RealVec3) : coordinate v 2 = v.2.2 := by
  simp [coordinate]

/-- Smooth nested cutoffs and the nonvanishing certificate for the buffered
coherent denominator. -/
structure BufferedCoherentCutoff where
  inner : RealVec3 → ℝ
  outer : RealVec3 → ℝ
  inner_contDiff : ContDiff ℝ ∞ inner
  outer_contDiff : ContDiff ℝ ∞ outer
  inner_compact : HasCompactSupport inner
  outer_eq_one_on_inner : ∀ k, inner k ≠ 0 → outer k = 1
  denominator_ne : ∀ k,
    normSq (coherentW k) + (1 - outer k) ^ 2 ≠ 0

def bufferedDenominator (D : BufferedCoherentCutoff) (k : RealVec3) : ℝ :=
  normSq (coherentW k) + (1 - D.outer k) ^ 2

/-- One entry of the compactly localized, globally regularized coherent
projection matrix. -/
def localizedProjectionEntry (D : BufferedCoherentCutoff)
    (i j : Fin 3) (k : RealVec3) : ℝ :=
  D.inner k *
    (coordinate (coherentW k) i * coordinate (coherentW k) j /
      bufferedDenominator D k)

theorem contDiff_coordinate_coherentW (i : Fin 3) :
    ContDiff ℝ ∞
      (fun k : RealVec3 ↦ coordinate (coherentW k) i) := by
  fin_cases i <;>
    simp [coordinate, coherentW, normSq, dot, add, smul, ex] <;>
    fun_prop

theorem contDiff_bufferedDenominator (D : BufferedCoherentCutoff) :
    ContDiff ℝ ∞ (bufferedDenominator D) := by
  have h0 := contDiff_coordinate_coherentW (0 : Fin 3)
  have h1 := contDiff_coordinate_coherentW (1 : Fin 3)
  have h2 := contDiff_coordinate_coherentW (2 : Fin 3)
  change ContDiff ℝ ∞ (fun k : RealVec3 ↦
    coordinate (coherentW k) 0 * coordinate (coherentW k) 0 +
      coordinate (coherentW k) 1 * coordinate (coherentW k) 1 +
      coordinate (coherentW k) 2 * coordinate (coherentW k) 2 +
      (1 - D.outer k) ^ 2)
  exact (((h0.mul h0).add (h1.mul h1)).add (h2.mul h2)).add
    ((contDiff_const.sub D.outer_contDiff).pow 2)

theorem contDiff_localizedProjectionEntry (D : BufferedCoherentCutoff)
    (i j : Fin 3) :
    ContDiff ℝ ∞ (localizedProjectionEntry D i j) := by
  unfold localizedProjectionEntry
  exact D.inner_contDiff.mul
    ((contDiff_coordinate_coherentW i).mul
      (contDiff_coordinate_coherentW j) |>.div
        (contDiff_bufferedDenominator D) D.denominator_ne)

theorem hasCompactSupport_localizedProjectionEntry
    (D : BufferedCoherentCutoff) (i j : Fin 3) :
    HasCompactSupport (localizedProjectionEntry D i j) := by
  unfold localizedProjectionEntry
  exact D.inner_compact.mul_right

/-- Every regularized matrix entry is a genuine Schwartz symbol. -/
def localizedProjectionEntrySchwartz (D : BufferedCoherentCutoff)
    (i j : Fin 3) : 𝓢(RealVec3, ℝ) :=
  (hasCompactSupport_localizedProjectionEntry D i j).toSchwartzMap
    (contDiff_localizedProjectionEntry D i j)

@[simp]
theorem localizedProjectionEntrySchwartz_apply
    (D : BufferedCoherentCutoff) (i j : Fin 3) (k : RealVec3) :
    localizedProjectionEntrySchwartz D i j k =
      localizedProjectionEntry D i j k := rfl

/-- On every retained point, the regularized entry is exactly the inner cutoff
times the true normalized coherent projector entry. -/
theorem localizedProjectionEntry_eq_on_inner
    (D : BufferedCoherentCutoff) (i j : Fin 3) (k : RealVec3)
    (hinner : D.inner k ≠ 0) :
    localizedProjectionEntry D i j k =
      D.inner k *
        (coordinate (coherentW k) i * coordinate (coherentW k) j /
          normSq (coherentW k)) := by
  unfold localizedProjectionEntry bufferedDenominator
  rw [D.outer_eq_one_on_inner k hinner]
  ring_nf

/-- The inner cutoff is not forced to be vacuous: any buffered datum with a
nonzero value produces a nonzero localized diagonal entry whenever the
corresponding coherent coordinate is nonzero. -/
theorem localizedProjectionEntry_ne_zero
    (D : BufferedCoherentCutoff) (i : Fin 3) (k : RealVec3)
    (hinner : D.inner k ≠ 0)
    (hcoord : coordinate (coherentW k) i ≠ 0) :
    localizedProjectionEntry D i i k ≠ 0 := by
  rw [localizedProjectionEntry_eq_on_inner D i i k hinner]
  have hden : normSq (coherentW k) ≠ 0 := by
    intro hzero
    have hx : (coherentW k).1 = 0 := by
      simp only [normSq, dot] at hzero
      nlinarith [sq_nonneg (coherentW k).1, sq_nonneg (coherentW k).2.1,
        sq_nonneg (coherentW k).2.2]
    have hy : (coherentW k).2.1 = 0 := by
      simp only [normSq, dot] at hzero
      nlinarith [sq_nonneg (coherentW k).1, sq_nonneg (coherentW k).2.1,
        sq_nonneg (coherentW k).2.2]
    have hz : (coherentW k).2.2 = 0 := by
      simp only [normSq, dot] at hzero
      nlinarith [sq_nonneg (coherentW k).1, sq_nonneg (coherentW k).2.1,
        sq_nonneg (coherentW k).2.2]
    fin_cases i <;> simp [coordinate, hx, hy, hz] at hcoord
  exact mul_ne_zero hinner (div_ne_zero (mul_ne_zero hcoord hcoord) hden)

/-! ## A concrete nonvacuous buffered cutoff -/

/-- A transverse frequency used as the center of the explicit cutoff. -/
def transverseCenter : RealVec3 := (0, 0, 1)

/-- The retained cutoff: it is supported in the radius `1/4` ball about
`transverseCenter`. -/
def retainedBump : ContDiffBump transverseCenter :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The buffer cutoff: it equals one on the radius `1/2` ball and is supported
in the radius `3/4` ball about `transverseCenter`. -/
def bufferBump : ContDiffBump transverseCenter :=
  ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩

theorem bufferBump_eq_one_of_retainedBump_ne_zero (k : RealVec3)
    (hk : retainedBump k ≠ 0) :
    bufferBump k = 1 := by
  apply bufferBump.one_of_mem_closedBall
  have hmem : k ∈ Function.support retainedBump := hk
  rw [retainedBump.support_eq] at hmem
  change dist k transverseCenter < retainedBump.rOut at hmem
  change dist k transverseCenter ≤ bufferBump.rIn
  exact hmem.le.trans (by norm_num [retainedBump, bufferBump])

theorem coherentW_normSq_pos_of_bufferBump_ne_zero (k : RealVec3)
    (hk : bufferBump k ≠ 0) :
    0 < normSq (coherentW k) := by
  have hmem : k ∈ Function.support bufferBump := hk
  rw [bufferBump.support_eq] at hmem
  have hdist : dist k transverseCenter < 3 / 4 := by
    simpa [bufferBump] using hmem
  rw [Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff] at hdist
  have hzabs : |k.2.2 - 1| < 3 / 4 := by
    simpa [transverseCenter, Real.dist_eq] using hdist.2.2
  have hzpos : 0 < k.2.2 := by
    have := (abs_lt.mp hzabs).1
    linarith
  have hwfirst : 0 < (coherentW k).1 := by
    simp only [coherentW, normSq, dot, add, smul, ex]
    nlinarith [sq_pos_of_pos hzpos, sq_nonneg k.2.1]
  simp only [normSq, dot]
  nlinarith [sq_pos_of_pos hwfirst, sq_nonneg (coherentW k).2.1,
    sq_nonneg (coherentW k).2.2]

theorem explicit_buffered_denominator_ne (k : RealVec3) :
    normSq (coherentW k) + (1 - bufferBump k) ^ 2 ≠ 0 := by
  by_cases hk : bufferBump k = 0
  · have hnonneg := normSq_nonneg (coherentW k)
    rw [hk]
    norm_num
    linarith
  · have hpos := coherentW_normSq_pos_of_bufferBump_ne_zero k hk
    nlinarith [sq_nonneg (1 - bufferBump k)]

/-- A concrete globally smooth buffered datum.  This closes the logical
nonvacuity gap in the abstract construction above. -/
def explicitBufferedCutoff : BufferedCoherentCutoff where
  inner := retainedBump
  outer := bufferBump
  inner_contDiff := retainedBump.contDiff
  outer_contDiff := bufferBump.contDiff
  inner_compact := retainedBump.hasCompactSupport
  outer_eq_one_on_inner := bufferBump_eq_one_of_retainedBump_ne_zero
  denominator_ne := explicit_buffered_denominator_ne

theorem retainedBump_center : retainedBump transverseCenter = 1 := by
  apply retainedBump.one_of_mem_closedBall
  simp [retainedBump]

theorem coherentW_center_first :
    coordinate (coherentW transverseCenter) 0 = 1 := by
  norm_num [transverseCenter, coordinate, coherentW, normSq, dot, add, smul, ex]

/-- The explicit localized symbol is genuinely nonzero. -/
theorem explicit_localizedProjectionEntry_ne_zero :
    localizedProjectionEntry explicitBufferedCutoff 0 0 transverseCenter ≠ 0 := by
  apply localizedProjectionEntry_ne_zero
  · change retainedBump transverseCenter ≠ 0
    rw [retainedBump_center]
    norm_num
  · rw [coherentW_center_first]
    norm_num

/-! ## Fourier kernels of the localized entries -/

/-- The Euclidean realization of the three frequency coordinates.  The
earlier algebra uses nested products for transparent coordinate proofs, while
Fourier inversion uses the canonical Euclidean inner product. -/
abbrev EuclideanFrequency := EuclideanSpace ℝ (Fin 3)

/-- Coordinate identification between Euclidean frequency space and the
nested-product algebraic model. -/
def euclideanToRealVec3LinearEquiv : EuclideanFrequency ≃ₗ[ℝ] RealVec3 where
  toFun ξ := (ξ 0, ξ 1, ξ 2)
  invFun k := !₂[k.1, k.2.1, k.2.2]
  left_inv ξ := by
    ext i
    fin_cases i <;> simp
  right_inv k := by
    ext <;> simp
  map_add' ξ η := by
    ext <;> simp
  map_smul' c ξ := by
    ext <;> simp

/-- The same coordinate identification as a linear homeomorphism. -/
def euclideanToRealVec3Equiv : EuclideanFrequency ≃L[ℝ] RealVec3 :=
  euclideanToRealVec3LinearEquiv.toContinuousLinearEquiv

/-- Transport of a localized entry from the algebraic coordinate model to
Euclidean frequency space. -/
def euclideanLocalizedProjectionEntrySchwartz (D : BufferedCoherentCutoff)
    (i j : Fin 3) : 𝓢(EuclideanFrequency, ℝ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ euclideanToRealVec3Equiv
    (localizedProjectionEntrySchwartz D i j)

/-- Complexification of a Euclidean localized entry, in the codomain required
by the Fourier transform. -/
def complexLocalizedProjectionEntrySchwartz (D : BufferedCoherentCutoff)
    (i j : Fin 3) : 𝓢(EuclideanFrequency, ℂ) :=
  (euclideanLocalizedProjectionEntrySchwartz D i j).postcompCLM
    Complex.ofRealCLM

@[simp]
theorem complexLocalizedProjectionEntrySchwartz_apply
    (D : BufferedCoherentCutoff) (i j : Fin 3) (ξ : EuclideanFrequency) :
    complexLocalizedProjectionEntrySchwartz D i j ξ =
      localizedProjectionEntry D i j (euclideanToRealVec3Equiv ξ) := rfl

/-- The Euclidean convolution kernel attached to one localized coherent
projector entry. -/
def localizedProjectionKernelEntry (D : BufferedCoherentCutoff)
    (i j : Fin 3) : 𝓢(EuclideanFrequency, ℂ) :=
  𝓕⁻ (complexLocalizedProjectionEntrySchwartz D i j)

theorem localizedProjectionKernelEntry_integrable
    (D : BufferedCoherentCutoff) (i j : Fin 3) :
    Integrable (localizedProjectionKernelEntry D i j) :=
  (localizedProjectionKernelEntry D i j).integrable

/-- Fourier transformation of the constructed kernel recovers the exact
localized multiplier entry. -/
theorem fourier_localizedProjectionKernelEntry
    (D : BufferedCoherentCutoff) (i j : Fin 3) :
    𝓕 (localizedProjectionKernelEntry D i j) =
      complexLocalizedProjectionEntrySchwartz D i j := by
  exact FourierTransform.fourier_fourierInv_eq _

/-- The transverse center in Euclidean coordinates. -/
def euclideanTransverseCenter : EuclideanFrequency := !₂[0, 0, 1]

@[simp]
theorem euclideanToRealVec3Equiv_transverseCenter :
    euclideanToRealVec3Equiv euclideanTransverseCenter = transverseCenter := by
  ext <;> simp [euclideanToRealVec3Equiv, euclideanToRealVec3LinearEquiv,
    euclideanTransverseCenter, transverseCenter]

theorem explicit_complexLocalizedProjectionEntrySchwartz_ne_zero :
    complexLocalizedProjectionEntrySchwartz explicitBufferedCutoff 0 0 ≠ 0 := by
  intro hzero
  have hvalue := congrArg
    (fun f : 𝓢(EuclideanFrequency, ℂ) ↦ f euclideanTransverseCenter) hzero
  simp only [complexLocalizedProjectionEntrySchwartz_apply,
    euclideanToRealVec3Equiv_transverseCenter, zero_apply] at hvalue
  exact explicit_localizedProjectionEntry_ne_zero (Complex.ofReal_injective hvalue)

/-- The explicit convolution kernel itself is nonzero. -/
theorem explicit_localizedProjectionKernelEntry_ne_zero :
    localizedProjectionKernelEntry explicitBufferedCutoff 0 0 ≠ 0 := by
  intro hzero
  have hfourier := congrArg
    (fun f : 𝓢(EuclideanFrequency, ℂ) ↦ 𝓕 f) hzero
  rw [fourier_localizedProjectionKernelEntry] at hfourier
  have hfourierZero :
      𝓕 (0 : 𝓢(EuclideanFrequency, ℂ)) =
        (0 : 𝓢(EuclideanFrequency, ℂ)) :=
    FourierTransform.fourier_zero
  exact explicit_complexLocalizedProjectionEntrySchwartz_ne_zero
    (hfourier.trans hfourierZero)

/-! ## Assembly into an operator-valued kernel -/

/-- Complex three-vectors used by the Fourier-side operator. -/
abbrev ComplexVec3 := Fin 3 → ℂ

/-- The elementary operator sending the `j`-th input coordinate to the
`i`-th output coordinate. -/
def elementaryOperator (i j : Fin 3) : ComplexVec3 →L[ℂ] ComplexVec3 :=
  (ContinuousLinearMap.proj j : ComplexVec3 →L[ℂ] ℂ).smulRight
    (Pi.single i 1)

@[simp]
theorem elementaryOperator_apply (i j : Fin 3) (v : ComplexVec3) :
    elementaryOperator i j v = v j • Pi.single i 1 := rfl

/-- Scalar multiplication of a fixed operator, as a continuous linear map. -/
def scalarMultipleOperatorCLM (A : ComplexVec3 →L[ℂ] ComplexVec3) :
    ℂ →L[ℂ] (ComplexVec3 →L[ℂ] ComplexVec3) :=
  (ContinuousLinearMap.lsmul ℂ ℂ).flip A

@[simp]
theorem scalarMultipleOperatorCLM_apply
    (A : ComplexVec3 →L[ℂ] ComplexVec3) (c : ℂ) :
    scalarMultipleOperatorCLM A c = c • A := rfl

/-- Fourier transformation commutes with bounded complex-linear
postcomposition on Schwartz functions. -/
theorem fourier_postcompCLM
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : 𝓢(EuclideanFrequency, ℂ)) (L : ℂ →L[ℂ] F) :
    𝓕 (f.postcompCLM L) = (𝓕 f).postcompCLM L := by
  ext ξ
  change 𝓕 (fun x : EuclideanFrequency ↦ L (f x)) ξ =
    L (𝓕 (fun x : EuclideanFrequency ↦ f x) ξ)
  rw [Real.fourier_eq, Real.fourier_eq]
  have hint : Integrable (fun x : EuclideanFrequency ↦
      𝐞 (-(inner ℝ x ξ)) • f x) :=
    (Real.fourierIntegral_convergent_iff ξ).2 f.integrable
  rw [← L.integral_comp_comm hint]
  congr 1
  funext x
  exact (L.map_smul_of_tower (𝐞 (-(inner ℝ x ξ))) (f x)).symm

/-- Assembly of the nine inverse-Fourier entries into one genuine
operator-valued Schwartz kernel. -/
def localizedProjectionOperatorKernel (D : BufferedCoherentCutoff) :
    𝓢(EuclideanFrequency, ComplexVec3 →L[ℂ] ComplexVec3) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (localizedProjectionKernelEntry D i j).postcompCLM
      (scalarMultipleOperatorCLM (elementaryOperator i j))

/-- The operator-valued coherent projection symbol assembled from its nine
regularized entries. -/
def localizedProjectionOperatorSymbol (D : BufferedCoherentCutoff) :
    𝓢(EuclideanFrequency, ComplexVec3 →L[ℂ] ComplexVec3) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (complexLocalizedProjectionEntrySchwartz D i j).postcompCLM
      (scalarMultipleOperatorCLM (elementaryOperator i j))

@[simp]
theorem localizedProjectionOperatorKernel_apply
    (D : BufferedCoherentCutoff) (x : EuclideanFrequency) :
    localizedProjectionOperatorKernel D x =
      ∑ i : Fin 3, ∑ j : Fin 3,
        localizedProjectionKernelEntry D i j x • elementaryOperator i j := by
  simp [localizedProjectionOperatorKernel]

@[simp]
theorem localizedProjectionOperatorSymbol_apply
    (D : BufferedCoherentCutoff) (ξ : EuclideanFrequency) :
    localizedProjectionOperatorSymbol D ξ =
      ∑ i : Fin 3, ∑ j : Fin 3,
        complexLocalizedProjectionEntrySchwartz D i j ξ •
          elementaryOperator i j := by
  simp [localizedProjectionOperatorSymbol]

/-- Exact recovery of the complete operator symbol from the assembled
convolution kernel. -/
theorem fourier_localizedProjectionOperatorKernel
    (D : BufferedCoherentCutoff) :
    𝓕 (localizedProjectionOperatorKernel D) =
      localizedProjectionOperatorSymbol D := by
  simp [localizedProjectionOperatorKernel, localizedProjectionOperatorSymbol,
    fourier_postcompCLM, fourier_localizedProjectionKernelEntry]

theorem localizedProjectionOperatorKernel_integrable
    (D : BufferedCoherentCutoff) :
    Integrable (localizedProjectionOperatorKernel D) :=
  (localizedProjectionOperatorKernel D).integrable

theorem localizedProjectionOperatorKernel_continuous
    (D : BufferedCoherentCutoff) :
    Continuous (localizedProjectionOperatorKernel D) :=
  (localizedProjectionOperatorKernel D).continuous

/-- Euclidean convolution action of the assembled operator kernel. -/
def localizedProjectionKernelAction (D : BufferedCoherentCutoff)
    (f : EuclideanFrequency → ComplexVec3) (x : EuclideanFrequency) :
    ComplexVec3 :=
  ∫ y, localizedProjectionOperatorKernel D y (f (x - y))

/-- Endpoint Young inequality for the actual assembled coherent-projection
kernel.  The remaining scale-uniform task is to estimate the displayed finite
kernel mass after cone rescaling. -/
theorem norm_localizedProjectionKernelAction_le
    (D : BufferedCoherentCutoff)
    (f : EuclideanFrequency → ComplexVec3) (x : EuclideanFrequency) (M : ℝ)
    (hf : Continuous f) (hfb : ∀ y, ‖f y‖ ≤ M) :
    ‖localizedProjectionKernelAction D f x‖ ≤
      (∫ y, ‖localizedProjectionOperatorKernel D y‖) * M := by
  have hK := localizedProjectionOperatorKernel_integrable D
  have hKc := localizedProjectionOperatorKernel_continuous D
  have hcont : Continuous (fun y : EuclideanFrequency ↦
      localizedProjectionOperatorKernel D y (f (x - y))) := by
    fun_prop
  have hdom : Integrable (fun y : EuclideanFrequency ↦
      ‖localizedProjectionOperatorKernel D y‖ * M) :=
    hK.norm.mul_const M
  have hint : Integrable (fun y : EuclideanFrequency ↦
      localizedProjectionOperatorKernel D y (f (x - y))) := by
    apply hdom.mono' hcont.aestronglyMeasurable
    filter_upwards with y
    exact (localizedProjectionOperatorKernel D y).le_opNorm_of_le (hfb _)
  unfold localizedProjectionKernelAction
  calc
    ‖∫ y : EuclideanFrequency,
        localizedProjectionOperatorKernel D y (f (x - y))‖ ≤
        ∫ y : EuclideanFrequency,
          ‖localizedProjectionOperatorKernel D y (f (x - y))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : EuclideanFrequency,
        ‖localizedProjectionOperatorKernel D y‖ * M := by
      apply integral_mono hint.norm hdom
      intro y
      exact (localizedProjectionOperatorKernel D y).le_opNorm_of_le (hfb _)
    _ = (∫ y : EuclideanFrequency,
        ‖localizedProjectionOperatorKernel D y‖) * M :=
      integral_mul_const M _

end PancakeSmoothCoherentSymbol
end NavierStokes
end FluidDynamics
end Mettapedia
