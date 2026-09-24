import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltMaterialEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralDefectAsymptotics

/-!
# Exact quadratic alignment-defect generation on the physical particle

The first residual rate determines the leading scalar defect coefficient.
The result is a right-hand asymptotic of an actual unforced local solution,
not an assumption of second time differentiability.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTiltQuadraticGrowth

open scoped Topology RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeCurlOutputTail PancakeHigherDerivativeMoments PancakeStrainSpectralFrame
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference
open PancakeSpectralResidualDepletion LocalInitialSpectral LocalMaterialStrain LocalMaterialVorticity
open PressureTiltDatum PressureTiltOrigin PressureTiltAlignment PressureTiltResidualRate
open PressureTiltMaterialEvolution SpectralDefectAsymptotics

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem thirdEigenvalue_origin (epsilon : ℝ) :
    thirdEigenvalue (originStrain epsilon) = -2 * Real.pi := by
  let F := orderedEigenframe (originStrain epsilon).1 (originStrain epsilon).2
  have ho : ⟪topVector (originStrain epsilon), F.eigenbasis 2⟫ = 0 :=
    F.eigenbasis.inner_eq_zero (by decide)
  have hc := congrArg (fun v : R3 ↦ ⟪v, F.eigenbasis 2⟫) (topVector_diagonalDirection epsilon)
  simp only [real_inner_smul_left, ho, mul_zero] at hc
  have hd : ⟪diagonalDirection, F.eigenbasis 2⟫ = 0 :=
    (mul_eq_zero.mp hc).resolve_left (inner_diagonalDirection_topVector_ne_zero epsilon)
  have hh := F.apply_eigenbasis 2
  rw [strain_apply, hd, zero_smul, zero_sub, smul_neg] at hh
  have hi := congrArg (fun v : R3 ↦ ⟪F.eigenbasis 2, v⟫) hh
  simp only [inner_neg_right, real_inner_smul_right, F.eigenbasis.inner_eq_one, mul_one] at hi
  change F.eigenvalue 2 = -2 * Real.pi
  linarith

theorem spectralWidth_origin (epsilon : ℝ) :
    spectralWidth (originStrain epsilon) = 6 * Real.pi := by
  change topEigenvalue (originStrain epsilon) - thirdEigenvalue (originStrain epsilon) = _
  rw [topEigenvalue_origin, thirdEigenvalue_origin]
  ring

def quadraticCoefficient (epsilon nu : ℝ) : ℝ :=
  (4096 / 25 : ℝ) * Real.pi ^ 5 * epsilon ^ 2 * (25 * Real.pi ^ 2 * nu ^ 2 + 3)

theorem quadraticCoefficient_eq_rate_quotient (epsilon nu : ℝ) :
    quadraticCoefficient epsilon nu = ‖residualRate epsilon nu‖ ^ 2 / topGap (originStrain epsilon) := by
  rw [norm_residualRate_sq, topGap_origin]
  unfold quadraticCoefficient
  field_simp
  ring

theorem quadraticCoefficient_pos (epsilon nu : ℝ) (he : epsilon ≠ 0) :
    0 < quadraticCoefficient epsilon nu := by
  have he2 : 0 < epsilon ^ 2 := sq_pos_of_ne_zero he
  unfold quadraticCoefficient
  positivity

variable {epsilon nu T B : ℝ}
  (s : LocalInfiniteVelocitySolution nu (velocity epsilon) T B)
  (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
  (hu : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 3 (s.coefficients t) k ≤ g k)
  (X : ℝ → X3) (hX0 : X 0 = 0)

include hg hSum hu hX0

theorem tendsto_material_defect_div_sq (hT : 0 < T) (hB : 0 ≤ B)
    (hXc : ContinuousOn X (Set.Icc (0 : ℝ) T))
    (hX : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s t (X t)) t) :
    Filter.Tendsto (fun t ↦ defectAlong s X t / t ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (quadraticCoefficient epsilon nu)) := by
  have hG := gradient_hasDerivWithinAt_initial s g hg hSum hu X hX0 hT hB hXc hX
  have hS : HasDerivWithinAt (fun t ↦ (symmetricStrainAlong s X t).1)
      (strainRate epsilon nu) (Set.Ici (0 : ℝ)) 0 :=
    realMatrixOperatorCLM.hasFDerivAt.comp_hasDerivWithinAt 0
      (hasDerivWithinAt_symmetrize _ _ _ 0 hG)
  have hSc : ContinuousWithinAt (symmetricStrainAlong s X) (Set.Ici (0 : ℝ)) 0 :=
    tendsto_subtype_rng.mpr hS.continuousWithinAt
  have hlim := tendsto_defect_div_sq (symmetricStrainAlong s X) (vorticityAlong s X)
    (residualRate epsilon nu) hSc
    (residual_hasDerivWithinAt_initial s g hg hSum hu X hX0 hT hB hXc hX)
    (residual_initial s X hX0)
    (by rw [strain_initial s X hX0, topGap_origin]; positivity)
    (by rw [strain_initial s X hX0, spectralWidth_origin, topGap_origin])
  rw [quadraticCoefficient_eq_rate_quotient, ← strain_initial s X hX0]
  exact hlim

omit hg hSum hu hX0 in
/-- A constructed solution and particle exhibit the exact positive quadratic coefficient. -/
theorem exists_material_quadratic_growth (epsilon nu : ℝ) (hnu : 0 < nu) (he : epsilon ≠ 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (velocity epsilon) T B,
      ∃ X : ℝ → X3, X 0 = 0 ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          HasDerivWithinAt X (liftedVelocity s t (X t)) (Set.Icc (0 : ℝ) T) t) ∧
        defectAlong s X 0 = 0 ∧ 0 < quadraticCoefficient epsilon nu ∧
        Filter.Tendsto (fun t ↦ defectAlong s X t / t ^ 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (quadraticCoefficient epsilon nu)) := by
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
    quadraticCoefficient_pos epsilon nu he,
    tendsto_material_defect_div_sq s g hg hSum hu X hX0 hT hB hXc hXi⟩

end Mettapedia.FluidDynamics.NavierStokes.PressureTiltQuadraticGrowth
