import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltResidualRate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltLocalSolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalInitialSpectral
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralResidualDepletion
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Alignment loss along an actual local Navier–Stokes evolution

At the initial origin the vorticity lies in the simple top strain
eigenline. For every nonzero perturbation and every positive viscosity,
the full spectral residual has a nonzero initial right derivative and
is nonzero for all sufficiently small positive times at that point.

This is a local alignment obstruction, not a singularity construction
or a failure of global regularity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTiltEvolution

open scoped Topology RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeCurlOutputTail PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralFiniteDifference
open PancakeTransverseEnergyFreezing PancakeSpectralDefectEvolution PancakeSpectralResidualDepletion
open LocalLowDiffusionBudget LocalAlignmentForcing LocalInitialSpectral SpectralEigenvalueWithin
open PressureTiltDatum PressureTiltOrigin PressureTiltAlignment PressureTiltResidualRate

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def residualAtOrigin (u : FourierVelocity) : R3 :=
  spectralResidual (fullStrainOperator u 0) (topEigenvalue (fullSymmetricStrain u 0))
    (fullVorticity u 0)

def defectAtOrigin (u : FourierVelocity) : ℝ :=
  topSpectralDefect (fullSymmetricStrain u 0) (fullVorticity u 0)

theorem fullSymmetricStrain_origin (epsilon : ℝ) :
    fullSymmetricStrain (velocity epsilon) 0 = originStrain epsilon :=
  Subtype.ext (fullStrainOperator_origin epsilon)

theorem residualAtOrigin_initial (epsilon : ℝ) : residualAtOrigin (velocity epsilon) = 0 := by
  unfold residualAtOrigin
  rw [fullStrainOperator_origin, fullSymmetricStrain_origin]
  exact spectralResidual_origin epsilon

theorem defectAtOrigin_initial (epsilon : ℝ) : defectAtOrigin (velocity epsilon) = 0 := by
  unfold defectAtOrigin
  rw [fullSymmetricStrain_origin]
  exact topSpectralDefect_origin epsilon

variable {epsilon nu T B : ℝ}
  (s : LocalInfiniteVelocitySolution nu (velocity epsilon) T B)
  (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
  (hu : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 3 (s.coefficients t) k ≤ g k)

include hg hSum hu

theorem residual_hasDerivWithinAt_initial (hT : 0 < T) (hB : 0 ≤ B) :
    HasDerivWithinAt (fun t ↦ residualAtOrigin (s.coefficients t))
      (residualRate epsilon nu) (Set.Ici (0 : ℝ)) 0 := by
  let S : ℝ → SymmetricStrain := fun t ↦ fullSymmetricStrain (s.coefficients t) 0
  have hS := fullStrainOperator_hasDerivWithinAt_initial s g hg hSum hu hT hB 0
  have hw := fullVorticity_hasDerivWithinAt_initial s g hg hSum hu hT hB 0
  have hS0 : S 0 = originStrain epsilon := by
    dsimp only [S]
    rw [s.initial, fullSymmetricStrain_origin]
  have hg0 : 0 < topGap (S 0) := by rw [hS0, topGap_origin]; positivity
  have hl := hasDerivWithinAt_topEigenvalue S (strainRate epsilon nu) (Set.Ici 0) 0 hS hg0
  change HasDerivWithinAt (fun t ↦ topEigenvalue (S t))
    ⟪topVector (S 0), strainRate epsilon nu (topVector (S 0))⟫ (Set.Ici 0) 0 at hl
  rw [hS0] at hl
  change HasDerivWithinAt (fun t ↦ topEigenvalue (S t))
    (eigenvalueRate epsilon nu) (Set.Ici 0) 0 at hl
  have hz := (hl.smul hw).sub (hS.clm_apply hw)
  apply hz.congr_deriv
  simp only [s.initial, fullStrainOperator_origin, hS0, residualRate, strainRate, vorticityRate]
  module

theorem eventually_residual_ne_zero (hT : 0 < T) (hB : 0 ≤ B) (he : epsilon ≠ 0) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), residualAtOrigin (s.coefficients t) ≠ 0 := by
  have h := (residual_hasDerivWithinAt_initial s g hg hSum hu hT hB).eventually_ne
    (c := (0 : R3)) (residualRate_ne_zero epsilon nu he)
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by ext t; simp
  simpa only [hset] using h

theorem eventually_defect_pos (hT : 0 < T) (hB : 0 ≤ B) (he : epsilon ≠ 0) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < defectAtOrigin (s.coefficients t) := by
  filter_upwards [eventually_residual_ne_zero s g hg hSum hu hT hB he] with t ht
  apply lt_of_le_of_ne (topSpectralDefect_nonneg _ _)
  intro hz
  exact ht ((topSpectralDefect_eq_zero_iff _ _).mp hz.symm)

omit hg hSum hu in
/-- An actual local solution starts aligned and immediately leaves the zero-residual set. -/
theorem exists_local_alignment_loss (epsilon nu : ℝ) (hnu : 0 < nu) (he : epsilon ≠ 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (velocity epsilon) T B,
        residualAtOrigin (s.coefficients 0) = 0 ∧
        HasDerivWithinAt (fun t ↦ residualAtOrigin (s.coefficients t))
          (residualRate epsilon nu) (Set.Ici (0 : ℝ)) 0 ∧
        (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), residualAtOrigin (s.coefficients t) ≠ 0) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    PressureTiltLocalSolution.exists_localMomentEnvelope epsilon nu hnu 3
  refine ⟨T, hT, B, hB, s, ?_,
    residual_hasDerivWithinAt_initial s g hg hSum hu hT hB,
    eventually_residual_ne_zero s g hg hSum hu hT hB he⟩
  rw [s.initial, residualAtOrigin_initial]

omit hg hSum hu in
/-- Scalar alignment defect is zero initially and positive immediately afterwards. -/
theorem exists_local_defect_growth (epsilon nu : ℝ) (hnu : 0 < nu) (he : epsilon ≠ 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (velocity epsilon) T B,
        defectAtOrigin (s.coefficients 0) = 0 ∧
        (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < defectAtOrigin (s.coefficients t)) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    PressureTiltLocalSolution.exists_localMomentEnvelope epsilon nu hnu 3
  refine ⟨T, hT, B, hB, s, ?_, eventually_defect_pos s g hg hSum hu hT hB he⟩
  rw [s.initial, defectAtOrigin_initial]

end Mettapedia.FluidDynamics.NavierStokes.PressureTiltEvolution
