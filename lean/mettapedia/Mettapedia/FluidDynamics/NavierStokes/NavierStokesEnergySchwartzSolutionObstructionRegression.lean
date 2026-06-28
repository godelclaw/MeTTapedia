import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolutionObstruction

/-!
# Regression checks for the line-invariant slice-Schwartz obstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

namespace Regression

theorem lineInvariant_velocitySlice_zero_regression
    {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν)
    {t : NSTime} {v : NSSpace} (hv : v ≠ 0)
    (hinv : TranslationInvariantAlong v (fun x : NSSpace => S.velocitySlice t x)) :
    ∀ x, S.velocity t x = 0 := by
  exact S.velocity_eq_zero_of_velocitySlice_translationInvariantAlong hv hinv

theorem nonzero_schwartz_solution_not_all_lineInvariant_regression
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {v : NSSpace} (hv : v ≠ 0) :
    ¬ ∀ t : NSTime,
      TranslationInvariantAlong v (fun x : NSSpace => S.velocitySlice t x) := by
  exact S.not_all_velocitySlices_translationInvariantAlong hv

theorem nonzero_schwartz_solution_has_non_lineInvariant_slice_regression
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {v : NSSpace} (hv : v ≠ 0) :
    ∃ t : NSTime,
      ¬ TranslationInvariantAlong v (fun x : NSSpace => S.velocitySlice t x) := by
  exact every_nonzeroSchwartzConcreteSolution_has_non_lineInvariant_slice S hv

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
