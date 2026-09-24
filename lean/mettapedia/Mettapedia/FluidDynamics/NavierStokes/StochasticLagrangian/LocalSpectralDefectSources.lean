import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpectralDefect

/-!
# Signed physical sources in the material spectral defect

The spin of the actual velocity annihilates its actual vorticity. Its
contribution to the spectral-defect balance is therefore nonnegative.
Pressure and viscosity retain their full anisotropic contributions.

The final algebraic identity records how an added strain-rate source and
vorticity-rate source enter the balance. It does not identify two different
PDE solutions or assert that their pressure Hessians agree.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpectralDefectSources

open scoped RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeFourierMaterialPaths PancakeLocalGradientEquation
open PancakeLocalStrainEquation PancakeLocalStrainReality PancakeCurlOutputTail
open PancakeInfiniteSpatialPressure PancakeInfinitePressureHessian
open PancakeInfiniteSpatialCurl PancakeMatrixCurlAlgebra
open PancakePhysicalNonlinearReconstruction PancakeDyadicDirectionEvolution
open PancakeSpectralDefectEvolution PancakeSpectralDefectBudget PancakeStrainSpectralFrame
open LocalMaterialVorticity LocalMaterialStrain LocalSpectralDefect

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "M3" => Matrix (Fin 3) (Fin 3) ℂ

theorem realMatrixOperator_skew (A : M3) (hA : A.transpose = -A) :
    ∀ x y : R3, ⟪realMatrixOperator A x, y⟫ = -⟪x, realMatrixOperator A y⟫ := by
  have ht : (realMatrix A).transpose = -realMatrix A := by
    ext i j
    have h := congrArg Complex.re (congrFun (congrFun hA i) j)
    simpa only [realMatrix, Matrix.transpose_apply, Matrix.neg_apply, Complex.neg_re] using h
  intro x y
  rw [real_inner_comm, realMatrixOperator, Matrix.inner_toEuclideanCLM,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ht, Matrix.neg_mulVec, neg_dotProduct]
  rw [dotProduct_comm, ← Matrix.inner_toEuclideanCLM]

variable {nu T B : ℝ} {u₀ : FourierVelocity}

def spinAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) : R3 →L[ℝ] R3 :=
  realMatrixOperator (PancakeLocalStrainEquation.spatialSpin (spatialField s t) (torusPoint (X t)))

def pressureDiffusionAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) : R3 →L[ℝ] R3 :=
  realMatrixOperator (-spatialHessian (spatialPressure (s.coefficients t)) (torusPoint (X t)) +
    (nu : ℂ) • matrixLaplacian
      (PancakeLocalStrainEquation.spatialStrain (spatialField s t)) (torusPoint (X t)))

theorem spinAlong_skew (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) :
    ∀ x y : R3, ⟪spinAlong s X t x, y⟫ = -⟪x, spinAlong s X t y⟫ :=
  realMatrixOperator_skew _ (spatialSpin_skew _ _)

private theorem spatialSpin_im_eq_zero (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) (hm : Summable (fourierMoment 1 (s.coefficients t))) (i j : Fin 3) :
    (PancakeLocalStrainEquation.spatialSpin (spatialField s t) (torusPoint (X t)) i j).im = 0 := by
  have h := congrArg Complex.im (spatialSpin_reality _ hm (s.reality t) (torusPoint (X t)) i j)
  simp only [Complex.conj_im] at h
  dsimp [spatialField]
  linarith

/-- Spin annihilates the vorticity built from this same velocity gradient. -/
theorem spinAlong_vorticityAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) (hm : Summable (fourierMoment 1 (s.coefficients t))) :
    spinAlong s X t (vorticityAlong s X t) = 0 := by
  have h := congrArg complexRealPartEuclideanCLM
    (spin_mulVec_matrixCurl (spatialVelocityGradient (spatialField s t) (torusPoint (X t))))
  rw [matrixCurl_velocityGradient] at h
  change complexRealPartEuclideanCLM
    ((PancakeLocalStrainEquation.spatialSpin (spatialField s t) (torusPoint (X t))).mulVec
      (spatialCurl (spatialField s t) (torusPoint (X t)))) = complexRealPartEuclideanCLM 0 at h
  rw [complexRealPart_mulVec _ _ (spatialSpin_im_eq_zero s X t hm), map_zero] at h
  exact h

theorem strainRemainderAlong_eq (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) (hm : Summable (fourierMoment 1 (s.coefficients t))) :
    strainRemainderAlong s X t =
      -spinAlong s X t * spinAlong s X t + pressureDiffusionAlong s X t := by
  simp only [strainRemainderAlong, spinAlong, pressureDiffusionAlong, Matrix.neg_mul,
    realMatrixOperator_add, realMatrixOperator_sub, realMatrixOperator_neg,
    realMatrixOperator_mul _ _ (spatialSpin_im_eq_zero s X t hm)]
  ext v
  simp only [add_apply, sub_apply, neg_apply, mul_apply_eq_comp]
  abel_nf

/-- Actual spin contributes a positive square, not an additional damping
term. The remaining pressure/viscosity contribution is not signed. -/
theorem anisotropyAlong_eq (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) (hm : Summable (fourierMoment 1 (s.coefficients t))) :
    let S := symmetricStrainAlong s X t
    let e := (orderedEigenframe S.1 S.2).eigenbasis 0
    anisotropyAlong s X t =
      ‖spinAlong s X t e‖ ^ 2 * ‖vorticityAlong s X t‖ ^ 2 +
        remainderAnisotropy (pressureDiffusionAlong s X t) e (vorticityAlong s X t) := by
  dsimp only [anisotropyAlong, topRemainderAnisotropy]
  rw [strainRemainderAlong_eq s X t hm]
  exact remainderAnisotropy_spin_and_forcing _ _ _ _
    (spinAlong_skew s X t) (spinAlong_vorticityAlong s X t hm)

/-- At fixed state, added strain-rate and vorticity-rate sources contribute
exactly these two channels. For a body force they are `sym ∇F` and `curl F`,
with any pressure change also retained in the strain-rate source. Smoothness
alone gives neither channel a favorable sign. -/
theorem spectralDefect_source_increment {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (R Q : H →L[ℝ] H) (e w z f h : H) :
    (remainderAnisotropy (R + Q) e w + 2 * ⟪z, f + h⟫) -
      (remainderAnisotropy R e w + 2 * ⟪z, f⟫) =
        remainderAnisotropy Q e w + 2 * ⟪z, h⟫ := by
  rw [remainderAnisotropy_add, inner_add_right]
  ring

end Mettapedia.FluidDynamics.NavierStokes.LocalSpectralDefectSources
