import Mettapedia.Analysis.ScalarTripleProductEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityTangency
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalMeanAlignmentBalance

/-!
# Vorticity and separation in the actual material flow

The common velocity gradient cancels from the signed scalar triple product
of the two endpoint vorticities and their lifted separation. The remaining
terms are the gradient difference, the first-order velocity remainder and
both viscous endpoint terms. All objects come from the same full Fourier
velocity; no common-gradient approximation is made in the identity.

Separation is a difference of real lifts, not a globally smooth choice of
shortest torus displacement. The result is a local material identity, not
a bound on its time integral or on a weighted stretching source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalVorticitySeparation

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths
open PancakeLocalMaterialTrajectories PancakeLocalSpatialVelocity PancakeLocalGradientEquation
open PancakeLocalStrainEquation PancakeMatrixCurlAlgebra PancakeFilteredStrainDynamics
open PancakeLocalProjectedEquation PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open PancakePeriodicComplexStretch PancakeInfiniteFourierDerivative
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentForcing
open Mettapedia.Analysis.EuclideanCrossProduct
open LocalMeanAlignmentBalance (velocity)
open scoped RealInnerProductSpace

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

def gradientMatrix (u : FourierVelocity) (x : T3) : Matrix (Fin 3) (Fin 3) ℝ :=
  realMatrix (spatialVelocityGradient (fullFourierField id u) x)

def gradient (u : FourierVelocity) (x : T3) : R3 →L[ℝ] R3 :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (gradientMatrix u x)

theorem trace_gradientMatrix (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hd : ∀ k, modeDot k (u k) = 0) (x : T3) : (gradientMatrix u x).trace = 0 := by
  have h := congrArg Complex.re (spatialDivergence_fullFourierField u hu hd x)
  simpa only [gradientMatrix, realMatrix, spatialVelocityGradient, spatialDivergence,
    Matrix.trace, Fin.sum_univ_three, Matrix.diag_apply, Complex.add_re, Complex.zero_re] using h

theorem realMatrixOperator_symmetrize_axial (A : Matrix (Fin 3) (Fin 3) ℂ) :
    realMatrixOperator (symmetrize A) (complexRealPartEuclideanCLM (matrixCurl A)) =
      realMatrixOperator A (complexRealPartEuclideanCLM (matrixCurl A)) := by
  ext i
  fin_cases i <;>
    simp [realMatrixOperator_apply, complexRealPartEuclideanCLM_apply,
      complexRealPartEuclidean, matrixCurl, symmetrize, Fin.sum_univ_three] <;> ring

/-- Spin annihilates the axial vector of this same gradient. -/
theorem gradient_vorticity (u : FourierVelocity) (x : T3) :
    gradient u x (fullVorticity u x) = fullStrainOperator u x (fullVorticity u x) := by
  exact (realMatrixOperator_symmetrize_axial
    (spatialVelocityGradient (fullFourierField id u) x)).symm

def separation (x y : X3) : R3 := WithLp.toLp 2 (x - y)

def velocityRemainder (u : FourierVelocity) (x y : X3) : R3 :=
  velocity u (torusPoint x) - velocity u (torusPoint y) -
    gradient u (torusPoint x) (separation x y)

def gradientRemainder (u : FourierVelocity) (x y : T3) : R3 :=
  (gradient u y - gradient u x) (fullVorticity u y)

def signedSeparation (u : FourierVelocity) (x y : X3) : ℝ :=
  tripleProduct (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (separation x y)

def nonviscousRate (u : FourierVelocity) (x y : X3) : ℝ :=
  tripleRate (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (separation x y)
    0 (gradientRemainder u (torusPoint x) (torusPoint y)) (velocityRemainder u x y)

def viscousRate (u : FourierVelocity) (x y : X3) : ℝ :=
  tripleRate (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (separation x y)
    (fullVorticityLaplacian u (torusPoint x)) (fullVorticityLaplacian u (torusPoint y)) 0

theorem materialRate_eq (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ k, modeDot k (u k) = 0) (x y : X3) :
    tripleRate (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (separation x y)
      (fullStrainOperator u (torusPoint x) (fullVorticity u (torusPoint x)) +
        nu • fullVorticityLaplacian u (torusPoint x))
      (fullStrainOperator u (torusPoint y) (fullVorticity u (torusPoint y)) +
        nu • fullVorticityLaplacian u (torusPoint y))
      (velocity u (torusPoint x) - velocity u (torusPoint y)) =
        nonviscousRate u x y + nu * viscousRate u x y := by
  rw [← gradient_vorticity, ← gradient_vorticity]
  have h := tripleRate_cancel_common (gradientMatrix u (torusPoint x))
    (trace_gradientMatrix u hu hd _) (fullVorticity u (torusPoint x))
    (fullVorticity u (torusPoint y)) (separation x y)
    (nu • fullVorticityLaplacian u (torusPoint x))
    (gradientRemainder u (torusPoint x) (torusPoint y) + nu • fullVorticityLaplacian u (torusPoint y))
    (velocityRemainder u x y)
  change tripleRate _ _ _ (gradient u _ _ + _) (gradient u _ _ + _) (gradient u _ _ + _) = _ at h
  simp only [gradientRemainder, velocityRemainder, sub_apply] at h
  have hy : gradient u (torusPoint x) (fullVorticity u (torusPoint y)) +
      ((gradient u (torusPoint y) (fullVorticity u (torusPoint y)) -
        gradient u (torusPoint x) (fullVorticity u (torusPoint y))) +
          nu • fullVorticityLaplacian u (torusPoint y)) =
      gradient u (torusPoint y) (fullVorticity u (torusPoint y)) +
        nu • fullVorticityLaplacian u (torusPoint y) := by abel
  rw [hy, add_sub_cancel] at h
  rw [h]
  simp only [nonviscousRate, viscousRate, tripleRate, gradientRemainder, velocityRemainder,
    sub_apply, cross_add_right, cross_smul_left, cross_smul_right, zero_cross, zero_add,
    inner_add_left, real_inner_smul_left, inner_zero_right]
  ring

/-- Only the first-order remainders are estimated; no uniform bound for
the velocity gradient or its spatial variation is assumed. -/
theorem abs_nonviscousRate_le (u : FourierVelocity) (x y : X3) :
    |nonviscousRate u x y| ≤ ‖fullVorticity u (torusPoint x)‖ * ‖fullVorticity u (torusPoint y)‖ *
      (‖gradient u (torusPoint y) - gradient u (torusPoint x)‖ * ‖separation x y‖ +
        ‖velocityRemainder u x y‖) := by
  have h := abs_tripleRate_le (fullVorticity u (torusPoint x))
    (fullVorticity u (torusPoint y)) (separation x y) 0
    (gradientRemainder u (torusPoint x) (torusPoint y)) (velocityRemainder u x y)
  simp only [norm_zero, zero_mul, zero_add] at h
  apply h.trans
  have hg := (gradient u (torusPoint y) - gradient u (torusPoint x)).le_opNorm
    (fullVorticity u (torusPoint y))
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hg (norm_nonneg (fullVorticity u (torusPoint x))))
    (norm_nonneg (separation x y))
  dsimp only [gradientRemainder] at h ⊢
  nlinarith only [hm]

theorem hasDerivAt_signedSeparation_path {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X Y : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
    (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t) :
    HasDerivAt (fun τ ↦ signedSeparation (s.coefficients τ) (X τ) (Y τ))
      (nonviscousRate (s.coefficients t) (X t) (Y t) +
        nu * viscousRate (s.coefficients t) (X t) (Y t)) t := by
  have hx := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  have hy := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI Y t ht hY
  let L := (WithLp.linearEquiv 2 ℝ X3).symm.toContinuousLinearEquiv
  have hh : HasDerivAt (fun τ ↦ separation (X τ) (Y τ))
      (velocity (s.coefficients t) (torusPoint (X t)) -
        velocity (s.coefficients t) (torusPoint (Y t))) t :=
    L.hasFDerivAt.comp_hasDerivAt t (hX.sub hY)
  have h := hasDerivAt_tripleProduct hx hy hh
  have hm := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3)
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
      (hu t (Set.Ioo_subset_Icc_self (hI (Set.Ioo_subset_Icc_self ht)))))
  rw [materialRate_eq _ nu hm (s.transverse t)] at h
  exact h

end Mettapedia.FluidDynamics.NavierStokes.LocalVorticitySeparation
