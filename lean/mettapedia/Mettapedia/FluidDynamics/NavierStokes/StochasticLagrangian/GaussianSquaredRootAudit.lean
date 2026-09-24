import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianSquaredRootLocalization

/-! Squared-root-patch regressions at coincident points and zero vorticity. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootAudit

open GaussianSquaredRootLocalization GaussianRootVorticity
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail LocalLowDiffusionBudget

local notation "T3" => UnitAddTorus (Fin 3)

example (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (x : T3) :
    squaredPatchDifference gamma chi modes u centers tau x x = 0 := by
  simp [squaredPatchDifference]

/-- At a vorticity zero the difference retains the other endpoint's fourth-power weight. -/
example (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (x y : T3)
    (hx : fullVorticity u x = 0) :
    squaredPatchDifference gamma chi modes u centers tau x y =
      ∑ i : ↑centers, rootPatch gamma chi modes u centers tau i y ^ 4 := by
  have hz (i : ↑centers) : rootPatch gamma chi modes u centers tau i x = 0 := by
    simp [rootPatch, hx]
  unfold squaredPatchDifference
  apply Finset.sum_congr rfl
  intro i _
  rw [hz i]
  ring

example (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (x y : T3)
    (hx : fullVorticity u x = 0) (hy : fullVorticity u y = 0) :
    squaredPatchDifference gamma chi modes u centers tau x y = 0 := by
  simp [squaredPatchDifference, rootPatch, hx, hy]

end Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootLocalization.rootPatch_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootLocalization.locallyLipschitz_rootPatch_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootLocalization.ae_coordinate_differentiable_rootPatch_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootLocalization.sum_norm_rootLocalization_integrand_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootLocalization.ae_coordinate_rootPatch_sq_derivative_bound
