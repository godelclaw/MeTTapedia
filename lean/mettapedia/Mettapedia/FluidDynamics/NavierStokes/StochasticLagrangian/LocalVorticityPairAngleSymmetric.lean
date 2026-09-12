import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityPairAngle

/-!
# Symmetric material angle bound with endpoint-local spectral defects

Each normalized defect is evaluated using its own endpoint's actual strain.
The signed remainder retains the strain difference and viscosity. This is
an actual local differential inequality, not a time-integrated budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPairAngle

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths
open PancakeLocalMaterialTrajectories LocalLowDiffusionBudget LocalJointDiffusionBudget
open LocalAlignmentForcing LocalInitialSpectral PancakeSpectralDefectEvolution
open PancakeSpectralProjectorRegularity.SymmetricStrain
open Mettapedia.Analysis.EuclideanCrossProduct
local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

def endpointDefectCoefficient (u : FourierVelocity) (x y : T3) : ℝ :=
  2 * (topSpectralDefect (fullSymmetricStrain u x) (fullVorticity u x) /
      ‖fullVorticity u x‖ ^ 2 +
    topSpectralDefect (fullSymmetricStrain u y) (fullVorticity u y) /
      ‖fullVorticity u y‖ ^ 2)

def endpointGapSum (u : FourierVelocity) (x y : T3) : ℝ :=
  topGap (fullSymmetricStrain u x) + topGap (fullSymmetricStrain u y)

def symmetricPairAnglePerturbation (u : FourierVelocity) (nu : ℝ) (x y : T3) : ℝ :=
  symmetricAnglePerturbation (fullStrainOperator u x) (fullStrainOperator u y)
    (fullVorticity u x) (fullVorticity u y)
    (nu • fullVorticityLaplacian u x) (nu • fullVorticityLaplacian u y)

theorem endpointDefectCoefficient_nonneg (u : FourierVelocity) (x y : T3) :
    0 ≤ endpointDefectCoefficient u x y := by
  unfold endpointDefectCoefficient
  exact mul_nonneg (by norm_num) (add_nonneg
    (div_nonneg (topSpectralDefect_nonneg _ _) (sq_nonneg _))
    (div_nonneg (topSpectralDefect_nonneg _ _) (sq_nonneg _)))

theorem pairAngleRate_le_endpointDefects (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ k, modeDot k (u k) = 0)
    (x y : T3) (hx : fullVorticity u x ≠ 0) (hy : fullVorticity u y ≠ 0) :
    pairAngleRate u nu x y ≤
      endpointDefectCoefficient u x y * angleEnergy (fullVorticity u x) (fullVorticity u y) +
        symmetricPairAnglePerturbation u nu x y := by
  unfold pairAngleRate
  rw [angleRate_eq_symmetric _ _ _ _ _ _
    (cross_fullStrain_apply_add u hu hd x _ _) (cross_fullStrain_apply_add u hu hd y _ _)]
  exact TraceFreeStrainAngle.symmetricAngleRate_le_endpointDefects
    (fullSymmetricStrain u x) (fullSymmetricStrain u y)
    (trace_fullStrainOperator_eq_zero u hu hd x) (trace_fullStrainOperator_eq_zero u hu hd y)
    _ _ _ _ hx hy

theorem pairAngleRate_le_gap_damping (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ k, modeDot k (u k) = 0)
    (x y : T3) (hx : fullVorticity u x ≠ 0) (hy : fullVorticity u y ≠ 0) :
    pairAngleRate u nu x y ≤
      (endpointDefectCoefficient u x y - endpointGapSum u x y) *
        angleEnergy (fullVorticity u x) (fullVorticity u y) +
        symmetricPairAnglePerturbation u nu x y := by
  unfold pairAngleRate
  rw [angleRate_eq_symmetric _ _ _ _ _ _
    (cross_fullStrain_apply_add u hu hd x _ _) (cross_fullStrain_apply_add u hu hd y _ _)]
  exact TraceFreeStrainAngle.symmetricAngleRate_le_gap_damping
    (fullSymmetricStrain u x) (fullSymmetricStrain u y)
    (trace_fullStrainOperator_eq_zero u hu hd x) (trace_fullStrainOperator_eq_zero u hu hd y)
    _ _ _ _ hx hy

theorem deriv_pairAngle_path_le_gap_damping {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X Y : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
    (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t)
    (hx : fullVorticity (s.coefficients t) (torusPoint (X t)) ≠ 0)
    (hy : fullVorticity (s.coefficients t) (torusPoint (Y t)) ≠ 0) :
    deriv (fun τ ↦ angleEnergy
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ)))) t ≤
      (endpointDefectCoefficient (s.coefficients t) (torusPoint (X t)) (torusPoint (Y t)) -
        endpointGapSum (s.coefficients t) (torusPoint (X t)) (torusPoint (Y t))) *
        angleEnergy (fullVorticity (s.coefficients t) (torusPoint (X t)))
          (fullVorticity (s.coefficients t) (torusPoint (Y t))) +
        symmetricPairAnglePerturbation (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t)) := by
  rw [(hasDerivAt_pairAngle_path s g hg hSum hu a b hab hI X Y t ht hX hY hx hy).deriv]
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
    (hu t (Set.Ioo_subset_Icc_self (hI (Set.Ioo_subset_Icc_self ht))))
  exact pairAngleRate_le_gap_damping _ nu
    (summable_fourierMoment_of_le _ (by norm_num : 2 ≤ 3) hm) (s.transverse t) _ _ hx hy

end Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPairAngle
