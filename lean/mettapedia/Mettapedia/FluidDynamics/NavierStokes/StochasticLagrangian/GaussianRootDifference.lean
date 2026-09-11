import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootDifferentiation

/-!
# Root-patch differences with the actual vorticity retained

This is the two-point factor required in a physical localization error.
It does not divide by the vorticity magnitude or require the scalar root
patch to have a square-integrable derivative. Integration against the
pressure kernel and scale-uniform control remain separate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootDifference

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open LocalLowDiffusionBudget GaussianRootVorticity

local notation "T3" => UnitAddTorus (Fin 3)

theorem rootPatch_eq_factor (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x : T3) :
    rootPatch gamma chi modes u centers tau i x =
      rootFieldFactor gamma chi modes u centers tau i x * Real.sqrt ‖fullVorticity u x‖ := by
  unfold rootPatch rootFieldFactor
  ring

theorem abs_rootPatch_sub_mul_vorticity_norm_le
    (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x y : T3) :
    |rootPatch gamma chi modes u centers tau i x - rootPatch gamma chi modes u centers tau i y| *
        ‖fullVorticity u y‖ ≤
      |rootFieldFactor gamma chi modes u centers tau i x - rootFieldFactor gamma chi modes u centers tau i y| *
        Real.sqrt ‖fullVorticity u y‖ * ‖fullVorticity u y‖ +
      |rootFieldFactor gamma chi modes u centers tau i x| * Real.sqrt ‖fullVorticity u y‖ *
        ‖fullVorticity u x - fullVorticity u y‖ := by
  simp only [rootPatch_eq_factor]
  exact Mettapedia.Analysis.RadialSquareRoot.abs_mul_sqrt_norm_sub_mul_norm_le _ _ _ _

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootDifference
