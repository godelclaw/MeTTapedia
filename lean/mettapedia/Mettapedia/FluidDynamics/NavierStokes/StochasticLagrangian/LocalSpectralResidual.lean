import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpectralDefectSources

/-!
# The material equation for the gap-weighted residual

For `z = λω - Sω`, the strain-square and stretching terms cancel to
`z' = -λz + (<e,Re>ω - Rω) + (λI-S)f`.
The coefficient `-λ` is dissipative for the largest eigenvalue of an
incompressible strain. The remaining source is explicit, not bounded here.
The actual equation holds almost everywhere across eigenvalue collisions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpectralResidual

open scoped RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories PancakeLocalSpatialVelocity
open PancakeFourierMaterialPaths PancakeLocalStrainReality PancakeLocalStrainEquation
open PancakeLocalGradientEquation PancakeHigherDerivativeMoments
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeStrainSpectralFrame PancakeTopEigenvalueDerivative PancakeSpectralDefectEvolution
open PancakeSpectralDefectBudget PancakeSpectralClusterDichotomy
open LocalMaterialStrain LocalMaterialVorticity LocalSpectralDefect

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The exact residual derivative, before choosing a top eigenvalue. -/
theorem hasDerivAt_spectralResidual
    (S : ℝ → H →L[ℝ] H) (lambda : ℝ → ℝ) (w : ℝ → H)
    (R : H →L[ℝ] H) (e f : H) (t : ℝ)
    (hS : HasDerivAt S (-S t * S t + R) t)
    (hlambda : HasDerivAt lambda (-lambda t ^ 2 + ⟪e, R e⟫) t)
    (hw : HasDerivAt w (S t (w t) + f) t) :
    HasDerivAt (fun τ ↦ spectralResidual (S τ) (lambda τ) (w τ))
      (-lambda t • spectralResidual (S t) (lambda t) (w t) +
        (⟪e, R e⟫ • w t - R (w t)) + spectralResidual (S t) (lambda t) f) t := by
  have h := (hlambda.smul hw).sub (hS.clm_apply hw)
  apply h.congr_deriv
  simp only [spectralResidual, add_apply, neg_apply, mul_apply_eq_comp, map_add]
  module

/-- No sign is assigned to the source, but a nonnegative top eigenvalue
cannot amplify the residual through its scalar linear coefficient. -/
theorem residual_inner_rate_le (lambda : ℝ) (z source : H) (hlambda : 0 ≤ lambda) :
    ⟪z, -lambda • z + source⟫ ≤ ‖z‖ * ‖source‖ := by
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hd : -lambda * ‖z‖ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlambda)
    (sq_nonneg _)
  linarith [real_inner_le_norm z source]

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- Each diagonal entry is a Rayleigh quotient on a coordinate unit vector. -/
theorem realMatrix_diagonal_le_topEigenvalue
    (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : A.transpose = A) (i : Fin 3) :
    (A i i).re ≤ topEigenvalue ⟨realMatrixOperator A, realMatrixOperator_symmetric A hA⟩ := by
  let S : SymmetricStrain := ⟨realMatrixOperator A, realMatrixOperator_symmetric A hA⟩
  let e := (EuclideanSpace.basisFun (Fin 3) ℝ) i
  have h := rayleigh_le_topEigenvalue_mul_norm_sq S.1 S.2 e
  have hn : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one i
  rw [hn, one_pow, mul_one] at h
  change ⟪e, realMatrixOperator A e⟫ ≤ topEigenvalue S at h
  change (A i i).re ≤ topEigenvalue S
  simpa [realMatrixOperator, Matrix.inner_toEuclideanCLM, e,
    EuclideanSpace.basisFun_apply, realMatrix, Matrix.mulVec, dotProduct] using h

variable {nu T B : ℝ} {u₀ : FourierVelocity}

theorem topEigenvalue_symmetricStrainAlong_nonneg
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3) (t : ℝ)
    (hm : Summable (fourierMoment 2 (s.coefficients t))) :
    0 ≤ topEigenvalue (symmetricStrainAlong s X t) := by
  have hd (i : Fin 3) := realMatrix_diagonal_le_topEigenvalue
    (PancakeLocalStrainEquation.spatialStrain (spatialField s t) (torusPoint (X t)))
    (spatialStrain_symmetric _ _) i
  have htr := congrArg Complex.re
    (spatialStrain_trace_zero _ hm (s.transverse t) (torusPoint (X t)))
  simp only [Matrix.trace, Fin.sum_univ_three, Matrix.diag_apply, Complex.add_re, Complex.zero_re] at htr
  change 0 ≤ topEigenvalue
    ⟨realMatrixOperator (PancakeLocalStrainEquation.spatialStrain (spatialField s t) (torusPoint (X t))),
      realMatrixOperator_symmetric _ (spatialStrain_symmetric _ _)⟩
  dsimp [spatialField] at hd ⊢
  linarith [hd 0, hd 1, hd 2]

/-- The actual source in the residual equation: strain-remainder anisotropy
acting on vorticity, plus the spectral gap operator acting on viscosity. -/
def sourceAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) : R3 :=
  let S := symmetricStrainAlong s X t
  let e := (orderedEigenframe S.1 S.2).eigenbasis 0
  ⟪e, strainRemainderAlong s X t e⟫ • vorticityAlong s X t -
    strainRemainderAlong s X t (vorticityAlong s X t) +
      spectralResidual S.1 (topEigenvalue S) (diffusionAlong s X t)

/-- The residual has an almost-everywhere material equation without any
lower bound on an eigenvalue gap. -/
theorem ae_hasDerivAt_residualAlong
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    {a b : ℝ} (hI : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ∀ᵐ t, t ∈ Set.uIcc a b → HasDerivAt (residualAlong s X)
      (-topEigenvalue (symmetricStrainAlong s X t) • residualAlong s X t + sourceAlong s X t) t := by
  let S := symmetricStrainAlong s X
  have hS := (contDiffOn_strainAlong s g hg hSum hu hB X hX).mono hI
  filter_upwards [(absolutelyContinuousOnInterval_topEigenvalue S a b hS).ae_differentiableAt]
    with t ht hmem
  have hdS : HasDerivAt (fun τ ↦ (S τ).1)
      (-(S t).1 * (S t).1 + strainRemainderAlong s X t) t :=
    hasDerivAt_strainAlong s g hg hSum hu X hX t (hI hmem)
  have hdw := hasDerivAt_vorticityAlong s g hg hSum hu X hX t (hI hmem)
  have hl := hasDerivAt_topEigenvalue_of_differentiableAt S _ t hdS (ht hmem)
  rw [eigenvalueRate_strainSquare (S t).1 (strainRemainderAlong s X t) _ _
    ((orderedEigenframe (S t).1 (S t).2).eigenbasis.norm_eq_one 0)
    ((orderedEigenframe (S t).1 (S t).2).apply_eigenbasis 0)] at hl
  have h := hasDerivAt_spectralResidual (fun τ ↦ (S τ).1) (fun τ ↦ topEigenvalue (S τ))
    (vorticityAlong s X) (strainRemainderAlong s X t) _ (diffusionAlong s X t) t hdS hl hdw
  simp only [add_assoc] at h
  convert! h using 1

end Mettapedia.FluidDynamics.NavierStokes.LocalSpectralResidual
