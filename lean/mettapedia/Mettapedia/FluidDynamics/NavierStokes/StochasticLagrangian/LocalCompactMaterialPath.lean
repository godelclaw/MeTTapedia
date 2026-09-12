import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalInteriorTrajectory
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalFilteredSpectralDefect

/-!
# Globally Lipschitz representatives of compact interior material paths

The ODE constructs the path. Its restriction to a compact interior interval
is Lipschitz and is extended constantly outside that interval. The material
equation is asserted only in the interval's interior.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalCompactMaterialPath

open PeriodicFourierTriad PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open PancakeCurlOutputTail PancakeLocalMaterialTrajectories
open scoped Topology
local notation "X3" => Fin 3 → ℝ

theorem exists_locallyLipschitz_materialPath_through
    {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 1 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (x : X3) :
    ∃ X : ℝ → X3, X t = x ∧ LocallyLipschitz X ∧
      ∀ τ ∈ Set.Ioo a b, HasDerivAt X (liftedVelocity s τ (X τ)) τ := by
  obtain ⟨Y, hYt, _, hY⟩ := LocalInteriorTrajectory.exists_materialTrajectory_through
    s g hg hSum hu t (Set.Ioo_subset_Icc_self (hI ht)) x
  have hc := LocalFilteredSpectralDefect.contDiffOn_materialPath s Y hY (a := a) (b := b)
    (by simpa only [Set.uIcc_of_le hab] using hI)
  obtain ⟨K, hK⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc (min a b) (max a b)) isCompact_Icc
  have hK' : LipschitzOnWith K Y (Set.Icc a b) := by
    simpa only [Set.uIcc_of_le hab] using hK
  let X : ℝ → X3 := fun τ ↦ Y (Set.projIcc a b hab τ)
  have he (τ : ℝ) (hτ : τ ∈ Set.Icc a b) : X τ = Y τ := by
    simp only [X, Set.projIcc_of_mem hab hτ]
  refine ⟨X, (he t ht).trans hYt, ?_, ?_⟩
  · exact (hK'.to_restrict.comp (LipschitzWith.projIcc hab)).locallyLipschitz
  · intro τ hτ
    rw [he τ (Set.Ioo_subset_Icc_self hτ)]
    apply (hY τ (hI (Set.Ioo_subset_Icc_self hτ))).congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds hτ.1 hτ.2] with r hr
    exact he r hr

end Mettapedia.FluidDynamics.NavierStokes.LocalCompactMaterialPath
