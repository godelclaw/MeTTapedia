import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpaceTimeExtension
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalInteriorTrajectory
import Mettapedia.Analysis.TangentCurveDerivative

/-!
# Full vorticity along curves tangent to the material velocity

A curve need only have the material velocity at the time in question.
Construct a genuine material trajectory through the same point, then
use space-time Lipschitz regularity to transfer its derivative. This
justifies frozen straight paths without treating them as flow lines.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalVorticityTangency

open scoped Topology
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeLocalInfiniteVelocity PancakeHigherDerivativeMoments PancakeFourierMaterialPaths
open PancakeLocalMaterialTrajectories PancakeLocalSpatialVelocity
open LocalSpaceTimeExtension LocalInteriorTrajectory LocalMaterialVorticity
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentForcing

local notation "X3" => Fin 3 → ℝ
local notation "ST" => ℝ × X3

/-- Pointwise tangency suffices for the full vorticity equation. -/
theorem hasDerivAt_fullVorticity_path {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t) :
    HasDerivAt (fun τ ↦ fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullStrainOperator (s.coefficients t) (torusPoint (X t))
        (fullVorticity (s.coefficients t) (torusPoint (X t))) +
        nu • fullVorticityLaplacian (s.coefficients t) (torusPoint (X t))) t := by
  have htT := hI (Set.Ioo_subset_Icc_self ht)
  have hu1 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 1 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 1 ≤ 3) q).trans (hu τ hτ q)
  obtain ⟨Y, hYt, _, hY⟩ := exists_materialTrajectory_through s g hg hSum hu1
    t (Set.Ioo_subset_Icc_self htT) (X t)
  have hDY : HasDerivAt (fun τ ↦ fullVorticity (s.coefficients τ) (torusPoint (Y τ)))
      (fullStrainOperator (s.coefficients t) (torusPoint (X t))
        (fullVorticity (s.coefficients t) (torusPoint (X t))) +
        nu • fullVorticityLaplacian (s.coefficients t) (torusPoint (X t))) t := by
    have h := hasDerivAt_vorticityAlong s g hg hSum hu Y hY t htT
    unfold vorticityAlong strainAlong diffusionAlong at h
    simpa only [spatialField, fullVorticity, fullStrainOperator, fullVorticityLaplacian, hYt] using h
  let F := fun z : ST ↦ fullVorticity (coefficients s a b hab z.1) (torusPoint z.2)
  have hF : LocallyLipschitz F := locallyLipschitz_fullVorticity s a b hab hI g hg hSum hu
  have hDY' : HasDerivAt (fun τ ↦ F (τ, Y τ))
      (fullStrainOperator (s.coefficients t) (torusPoint (X t))
        (fullVorticity (s.coefficients t) (torusPoint (X t))) +
        nu • fullVorticityLaplacian (s.coefficients t) (torusPoint (X t))) t := by
    apply hDY.congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    simp only [F, coefficients_eq s a b hab τ hτ]
  have hDYpath : HasDerivAt (fun τ ↦ (τ, Y τ)) (1, liftedVelocity s t (X t)) t :=
    (hasDerivAt_id t).prodMk (by simpa only [hYt] using hY t htT)
  have hDXpath : HasDerivAt (fun τ ↦ (τ, X τ)) (1, liftedVelocity s t (X t)) t :=
    (hasDerivAt_id t).prodMk hX
  have h := hF.hasDerivAt_comp_of_tangent hDYpath hDXpath (by simp only [hYt]) hDY'
  apply h.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
  simp only [F, coefficients_eq s a b hab τ hτ]

end Mettapedia.FluidDynamics.NavierStokes.LocalVorticityTangency
