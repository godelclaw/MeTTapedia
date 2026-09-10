import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MaterialInitialGradient
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltEvolution

/-!
# Alignment loss on a constructed Navier–Stokes material trajectory

The initial residual response persists when evaluated on the actual
fluid particle starting at the origin. The trajectory is constructed
on the same local interval as the unforced velocity solution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTiltMaterialEvolution

open scoped Topology RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeCurlOutputTail PancakeHigherDerivativeMoments PancakeLocalGradientEquation
open PancakeDyadicDirectionEvolution PancakeFilteredStrainDynamics
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralDefectEvolution PancakeSpectralResidualDepletion
open MaterialInitialGradient LocalInitialSpectral LocalMaterialStrain LocalMaterialVorticity
open LocalLowDiffusionBudget LocalAlignmentForcing
open PressureTiltDatum PressureTiltOrigin PressureTiltAlignment PressureTiltTangent PressureTiltResidualRate

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

variable {epsilon nu T B : ℝ}

def residualAlong (s : LocalInfiniteVelocitySolution nu (velocity epsilon) T B)
    (X : ℝ → X3) (t : ℝ) : R3 :=
  spectralResidual (strainAlong s X t) (topEigenvalue (symmetricStrainAlong s X t))
    (vorticityAlong s X t)

def defectAlong (s : LocalInfiniteVelocitySolution nu (velocity epsilon) T B)
    (X : ℝ → X3) (t : ℝ) : ℝ :=
  topSpectralDefect (symmetricStrainAlong s X t) (vorticityAlong s X t)

theorem torusPoint_initial (X : ℝ → X3) (hX0 : X 0 = 0) : torusPoint (X 0) = 0 := by
  rw [hX0]
  ext i
  simp [torusPoint]

variable (s : LocalInfiniteVelocitySolution nu (velocity epsilon) T B)
  (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
  (hu : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 3 (s.coefficients t) k ≤ g k)
  (X : ℝ → X3) (hX0 : X 0 = 0)

include hX0

theorem strain_initial : symmetricStrainAlong s X 0 = originStrain epsilon := by
  apply Subtype.ext
  change fullStrainOperator (s.coefficients 0) (torusPoint (X 0)) = _
  rw [s.initial, torusPoint_initial X hX0, fullStrainOperator_origin]

theorem vorticity_initial : vorticityAlong s X 0 = fullVorticity (velocity epsilon) 0 := by
  change fullVorticity (s.coefficients 0) (torusPoint (X 0)) = _
  rw [s.initial, torusPoint_initial X hX0]

theorem residual_initial : residualAlong s X 0 = 0 := by
  change spectralResidual (symmetricStrainAlong s X 0).1
    (topEigenvalue (symmetricStrainAlong s X 0)) (vorticityAlong s X 0) = 0
  rw [strain_initial s X hX0, vorticity_initial s X hX0]
  exact spectralResidual_origin epsilon

theorem defect_initial : defectAlong s X 0 = 0 := by
  rw [defectAlong, strain_initial s X hX0, vorticity_initial s X hX0]
  exact topSpectralDefect_origin epsilon

include hg hSum hu

theorem gradient_hasDerivWithinAt_initial (hT : 0 < T) (hB : 0 ≤ B)
    (hXc : ContinuousOn X (Set.Icc (0 : ℝ) T))
    (hX : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s t (X t)) t) :
    HasDerivWithinAt (fun t ↦ spatialVelocityGradient (spatialField s t) (torusPoint (X t)))
      (gradientRate epsilon nu) (Set.Ici (0 : ℝ)) 0 := by
  have hd := MaterialInitialGradient.velocityGradient_hasDerivWithinAt_initial
    s g hg hSum hu hT hB X hXc hX
  rw [torusPoint_initial X hX0,
    materialGradientRate_eq_velocityRHS_of_stagnation nu (velocity epsilon)
      (velocity_moments epsilon 3) (velocity_transverse epsilon) 0 (velocity_origin epsilon)] at hd
  exact hd

theorem residual_hasDerivWithinAt_initial (hT : 0 < T) (hB : 0 ≤ B)
    (hXc : ContinuousOn X (Set.Icc (0 : ℝ) T))
    (hX : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s t (X t)) t) :
    HasDerivWithinAt (residualAlong s X) (residualRate epsilon nu) (Set.Ici (0 : ℝ)) 0 := by
  have hd := gradient_hasDerivWithinAt_initial s g hg hSum hu X hX0 hT hB hXc hX
  have hS : HasDerivWithinAt (fun t ↦ (symmetricStrainAlong s X t).1)
      (strainRate epsilon nu) (Set.Ici (0 : ℝ)) 0 :=
    realMatrixOperatorCLM.hasFDerivAt.comp_hasDerivWithinAt 0
      (hasDerivWithinAt_symmetrize _ _ _ 0 hd)
  have hw : HasDerivWithinAt (vorticityAlong s X)
      (vorticityRate epsilon nu) (Set.Ici (0 : ℝ)) 0 :=
    complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivWithinAt 0
      (hasDerivWithinAt_matrixCurl _ _ _ 0 hd)
  exact hasDerivWithinAt_residual_of_rates epsilon nu 0 (Set.Ici 0)
    (symmetricStrainAlong s X) (vorticityAlong s X) hS hw
    (strain_initial s X hX0) (vorticity_initial s X hX0)

theorem eventually_defect_pos (hT : 0 < T) (hB : 0 ≤ B) (he : epsilon ≠ 0)
    (hXc : ContinuousOn X (Set.Icc (0 : ℝ) T))
    (hX : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s t (X t)) t) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < defectAlong s X t := by
  have hz := (residual_hasDerivWithinAt_initial s g hg hSum hu X hX0 hT hB hXc hX).eventually_ne
    (c := (0 : R3)) (residualRate_ne_zero epsilon nu he)
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by ext t; simp
  rw [hset] at hz
  filter_upwards [hz] with t ht
  apply lt_of_le_of_ne (topSpectralDefect_nonneg _ _)
  intro h
  exact ht ((topSpectralDefect_eq_zero_iff _ _).mp h.symm)

omit hg hSum hu hX0 in
/-- Both the velocity solution and its particle path are constructed. -/
theorem exists_material_alignment_loss (epsilon nu : ℝ) (hnu : 0 < nu) (he : epsilon ≠ 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (velocity epsilon) T B,
      ∃ X : ℝ → X3, X 0 = 0 ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          HasDerivWithinAt X (liftedVelocity s t (X t)) (Set.Icc (0 : ℝ) T) t) ∧
        defectAlong s X 0 = 0 ∧
        HasDerivWithinAt (residualAlong s X) (residualRate epsilon nu) (Set.Ici (0 : ℝ)) 0 ∧
        (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < defectAlong s X t) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    PressureTiltLocalSolution.exists_localMomentEnvelope epsilon nu hnu 3
  have hu1 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 1 (s.coefficients t) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 1 ≤ 3) q).trans (hu t ht q)
  obtain ⟨X, hX0, hX⟩ := exists_materialTrajectory s g hg hSum hu1 hT.le 0
  have hXc := HasDerivWithinAt.continuousOn hX
  have hXi (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :=
    (hX t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  exact ⟨T, hT, B, hB, s, X, hX0, hX, defect_initial s X hX0,
    residual_hasDerivWithinAt_initial s g hg hSum hu X hX0 hT hB hXc hXi,
    eventually_defect_pos s g hg hSum hu X hX0 hT hB he hXc hXi⟩

end Mettapedia.FluidDynamics.NavierStokes.PressureTiltMaterialEvolution
