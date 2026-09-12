import Mettapedia.Analysis.CrossProductStrain
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityTangency
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedPayment
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TraceFreeStrainAngle
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredStrainTrace
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalInitialSpectral

/-!
# Two-point angle dynamics for the actual unforced vorticity

Both points move with the actual local velocity. Common strain cancels to
minus strain acting on their cross product. The strain difference and both
viscous terms remain explicit. The normalized equation requires nonzero
endpoint vorticities, as is appropriate on the high-amplitude pair region.
No monotonicity, coherence modulus, or time-integrated source bound is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPairAngle

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths
open PancakeLocalMaterialTrajectories PancakeLocalSpatialVelocity PancakeLocalStrainEquation
open PancakeLocalStrainReality LocalLowDiffusionBudget LocalJointDiffusionBudget
open LocalAlignmentForcing PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative
open LocalInitialSpectral PancakeSpectralDefectEvolution
open Mettapedia.Analysis.EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

theorem cross_fullStrain_apply_add (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hd : ∀ k, modeDot k (u k) = 0) (x : T3) (a b : R3) :
    cross (fullStrainOperator u x a) b + cross a (fullStrainOperator u x b) =
      -fullStrainOperator u x (cross a b) := by
  let A := spatialStrain (fullFourierField id u) x
  have hA : (realMatrix A).transpose = realMatrix A := by
    ext i j
    exact congrArg Complex.re (congrFun (congrFun (spatialStrain_symmetric _ _) i) j)
  have htr : (realMatrix A).trace = 0 := by
    have h := congrArg Complex.re (spatialStrain_trace_zero u hu hd x)
    simpa only [realMatrix, Matrix.trace, Fin.sum_univ_three, Matrix.diag_apply,
      Complex.add_re, Complex.zero_re, A] using h
  exact cross_mulVec_add_mulVec_cross_of_symmetric_trace_zero (realMatrix A) hA htr a b

def pairSource (u : FourierVelocity) (nu : ℝ) (x y : T3) : R3 :=
  pairForcing (fullStrainOperator u x) (fullStrainOperator u y)
    (fullVorticity u x) (fullVorticity u y)
    (nu • fullVorticityLaplacian u x) (nu • fullVorticityLaplacian u y)

def pairAngleRate (u : FourierVelocity) (nu : ℝ) (x y : T3) : ℝ :=
  angleRate (fullStrainOperator u x) (fullStrainOperator u y)
    (fullVorticity u x) (fullVorticity u y)
    (nu • fullVorticityLaplacian u x) (nu • fullVorticityLaplacian u y)

def pairAnglePerturbation (u : FourierVelocity) (nu : ℝ) (x y : T3) : ℝ :=
  anglePerturbation (fullStrainOperator u x) (fullStrainOperator u y)
    (fullVorticity u x) (fullVorticity u y)
    (nu • fullVorticityLaplacian u x) (nu • fullVorticityLaplacian u y)

theorem trace_fullStrainOperator_eq_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ k, modeDot k (u k) = 0) (x : T3) :
    LinearMap.trace ℝ R3 (fullStrainOperator u x).toLinearMap = 0 := by
  rw [fullStrainOperator, FilteredStrainTrace.trace_realMatrixOperator,
    spatialStrain_trace_zero u hu hd x, Complex.zero_re]

/-- Both defects are measured relative to the strain at the first endpoint.
The other strain and both Laplacians remain in the signed perturbation. -/
theorem pairAngleRate_le_topSpectralDefects (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ k, modeDot k (u k) = 0)
    (x y : T3) (hx : fullVorticity u x ≠ 0) (hy : fullVorticity u y ≠ 0) :
    pairAngleRate u nu x y ≤
      2 * (topSpectralDefect (fullSymmetricStrain u x) (fullVorticity u x) /
          ‖fullVorticity u x‖ ^ 2 +
        topSpectralDefect (fullSymmetricStrain u x) (fullVorticity u y) /
          ‖fullVorticity u y‖ ^ 2) * angleEnergy (fullVorticity u x) (fullVorticity u y) +
        pairAnglePerturbation u nu x y := by
  exact TraceFreeStrainAngle.angleRate_le_defects_add_perturbation
    (fullSymmetricStrain u x) (trace_fullStrainOperator_eq_zero u hu hd x)
    _ _ _ _ _ hx hy

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
  (X Y : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
  (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
  (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t)

include hg hSum hu hab hI ht hX hY

theorem hasDerivAt_pairCross_path :
    HasDerivAt (fun τ ↦ cross
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ))))
      (-fullStrainOperator (s.coefficients t) (torusPoint (X t))
        (cross (fullVorticity (s.coefficients t) (torusPoint (X t)))
          (fullVorticity (s.coefficients t) (torusPoint (Y t)))) +
        pairSource (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t))) t := by
  have hwX := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  have hwY := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI Y t ht hY
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
    (hu t (Set.Ioo_subset_Icc_self (hI (Set.Ioo_subset_Icc_self ht))))
  exact hasDerivAt_cross_of_strainEquations _ _ _ _ hwX hwY
    (cross_fullStrain_apply_add _ (summable_fourierMoment_of_le _ (by norm_num : 2 ≤ 3) hm)
      (s.transverse t) _ _ _)

theorem hasDerivAt_pairAngle_path
    (hx : fullVorticity (s.coefficients t) (torusPoint (X t)) ≠ 0)
    (hy : fullVorticity (s.coefficients t) (torusPoint (Y t)) ≠ 0) :
    HasDerivAt (fun τ ↦ angleEnergy
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ))))
      (pairAngleRate (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t))) t := by
  have hwX := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  have hwY := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI Y t ht hY
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
    (hu t (Set.Ioo_subset_Icc_self (hI (Set.Ioo_subset_Icc_self ht))))
  exact hasDerivAt_angleEnergy_of_strainEquations _ _ _ _ hwX hwY hx hy
    (cross_fullStrain_apply_add _ (summable_fourierMoment_of_le _ (by norm_num : 2 ≤ 3) hm)
      (s.transverse t) _ _ _)

theorem deriv_pairAngle_path_le_topSpectralDefects
    (hx : fullVorticity (s.coefficients t) (torusPoint (X t)) ≠ 0)
    (hy : fullVorticity (s.coefficients t) (torusPoint (Y t)) ≠ 0) :
    deriv (fun τ ↦ angleEnergy
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ)))) t ≤
      2 * (topSpectralDefect (fullSymmetricStrain (s.coefficients t) (torusPoint (X t)))
          (fullVorticity (s.coefficients t) (torusPoint (X t))) /
            ‖fullVorticity (s.coefficients t) (torusPoint (X t))‖ ^ 2 +
        topSpectralDefect (fullSymmetricStrain (s.coefficients t) (torusPoint (X t)))
          (fullVorticity (s.coefficients t) (torusPoint (Y t))) /
            ‖fullVorticity (s.coefficients t) (torusPoint (Y t))‖ ^ 2) *
        angleEnergy (fullVorticity (s.coefficients t) (torusPoint (X t)))
          (fullVorticity (s.coefficients t) (torusPoint (Y t))) +
        pairAnglePerturbation (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t)) := by
  rw [(hasDerivAt_pairAngle_path s g hg hSum hu a b hab hI X Y t ht hX hY hx hy).deriv]
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
    (hu t (Set.Ioo_subset_Icc_self (hI (Set.Ioo_subset_Icc_self ht))))
  exact pairAngleRate_le_topSpectralDefects _ nu
    (summable_fourierMoment_of_le _ (by norm_num : 2 ≤ 3) hm) (s.transverse t) _ _ hx hy

end Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPairAngle
