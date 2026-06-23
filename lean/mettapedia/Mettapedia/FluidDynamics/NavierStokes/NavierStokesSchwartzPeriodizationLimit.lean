import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPeriodizationSeries

/-!
# Navier-Stokes: Schwartz Periodization Limits

Semantic layer split from `NavierStokesSchwartzPeriodizationConvergence`.
-/


set_option autoImplicit false

noncomputable section

open Filter

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped BigOperators

/-- The structured boxed Schwartz partial periodizations converge pointwise to
the infinite Schwartz periodization whenever the period parameter is nonzero. -/
theorem boxedPartialPeriodizationSchwartzInitialVelocity_tendsto
    {L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzInitialVelocity) (x : NSSpace) :
    Tendsto (fun N => boxedPartialPeriodizationSchwartzInitialVelocity N L u₀ x)
      Filter.atTop (nhds (schwartzPeriodizedInitialVelocity L u₀ x)) := by
  let f : NSLatticeIndex → NSSpace := fun n => u₀ (x + periodizationShift L n)
  have hsum : HasSum f (schwartzPeriodizedInitialVelocity L u₀ x) := by
    simpa [f, schwartzPeriodizedInitialVelocity] using
      hasSum_schwartzPeriodizedInitialVelocity hL u₀ x
  simpa [f, boxedPartialPeriodizationSchwartzInitialVelocity,
    finitePartialPeriodizationSchwartzInitialVelocity] using
    hsum.comp centeredLatticeBox_tendsto_atTop

/-- The boxed partial periodizations of manuscript-style divergence-free
Schwartz data converge pointwise to the same infinite periodization candidate. -/
theorem boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity_tendsto
    {L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (x : NSSpace) :
    Tendsto
      (fun N => (boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity N L u₀).1 x)
      Filter.atTop (nhds (schwartzPeriodizedInitialVelocity L u₀.1 x)) := by
  simpa [boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity,
    boxedPartialPeriodizationSchwartzInitialVelocity,
    finitePartialPeriodizationSchwartzDivergenceFreeInitialVelocity] using
    boxedPartialPeriodizationSchwartzInitialVelocity_tendsto hL u₀.1 x

end NavierStokes
end FluidDynamics
end Mettapedia
