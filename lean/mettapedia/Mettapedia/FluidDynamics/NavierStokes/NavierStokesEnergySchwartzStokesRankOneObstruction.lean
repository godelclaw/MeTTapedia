import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzStokesKernel

/-!
# Slice-Schwartz Stokes Rank-One Obstruction

This module closes the fixed-direction rank-one shear shortcut inside the exact
Stokes-flow subroute.  In the current concrete interface, an exact nonzero
Stokes candidate has zero pointwise convection.  The existing rank-one
Schwartz rigidity theorem then forces every fixed-direction rank-one slice with
zero convection to vanish, contradicting the nonzero witness if all slices stay
in one nonzero direction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap Topology

namespace NonzeroSchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)

/-- Exact Stokes-flow candidates cannot keep every velocity slice in one
fixed nonzero rank-one Schwartz direction. -/
theorem stokesFlow_not_forall_velocitySlice_rankOne_of_fixed_direction
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {v : NSSpace} (hv : v ≠ 0) :
    ¬ ∀ t : NSTime,
      ∃ φ : NSSchwartzScalar,
        S.velocitySlice t = rankOneSchwartzVelocity φ v := by
  have _kernel : NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure :=
    S.nonzeroStokesFlowKernel hconv hpressure
  intro hall
  exact S.not_forall_velocitySlice_rankOne_zeroConvection_of_fixed_direction hv
    (by
      intro t
      rcases hall t with ⟨φ, hslice⟩
      exact ⟨φ, hslice, hconv t⟩)

/-- Positive form: an exact nonzero Stokes-flow candidate must have at least
one slice outside any prescribed nonzero rank-one direction. -/
theorem stokesFlow_exists_velocitySlice_not_rankOne_of_fixed_direction
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {v : NSSpace} (hv : v ≠ 0) :
    ∃ t : NSTime,
      ∀ φ : NSSchwartzScalar,
        S.velocitySlice t ≠ rankOneSchwartzVelocity φ v := by
  by_contra hnone
  have hall :
      ∀ t : NSTime,
        ∃ φ : NSSchwartzScalar,
          S.velocitySlice t = rankOneSchwartzVelocity φ v := by
    intro t
    by_contra ht
    exact hnone ⟨t, fun φ hslice => ht ⟨φ, hslice⟩⟩
  exact
    (S.stokesFlow_not_forall_velocitySlice_rankOne_of_fixed_direction
      hconv hpressure hv) hall

/-- Exact positive-viscosity Stokes-flow candidates, if they exist, must carry
both strict energy dissipation and a slice breaking every fixed nonzero
rank-one shear direction. -/
theorem stokesFlow_strictDissipation_and_non_rankOne_slice_packet
    (hν : 0 < ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {v : NSSpace} (hv : v ≠ 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      (∃ t : NSTime,
        0 < coordinateEnergyDissipationRate S.velocity ν t ∧
          HasDerivAt (normalizedKineticEnergy S.velocity)
            (-(coordinateEnergyDissipationRate S.velocity ν t)) t ∧
          -(coordinateEnergyDissipationRate S.velocity ν t) < 0) ∧
      ∃ t : NSTime,
        ∀ φ : NSSchwartzScalar,
          S.velocitySlice t ≠ rankOneSchwartzVelocity φ v := by
  rcases S.stokesFlow_strictDissipation_packet hν hconv hpressure with
    ⟨hkernel, hstrict⟩
  exact
    ⟨hkernel, hstrict,
      S.stokesFlow_exists_velocitySlice_not_rankOne_of_fixed_direction
        hconv hpressure hv⟩

end NonzeroSchwartzConcreteNavierStokesSolution

/-- Global no-go: no exact nonzero Stokes-flow candidate can have all velocity
slices in one fixed nonzero rank-one Schwartz direction. -/
theorem not_exists_nonzeroSchwartzStokesFlow_forall_rankOne_fixed_direction
    {ν : ℝ} {v : NSSpace} (hv : v ≠ 0) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      (∀ t x, spatialConvection S.velocity t x = 0) ∧
        (∀ t x, spatialPressureGradient S.pressure t x = 0) ∧
        ∀ t : NSTime,
          ∃ φ : NSSchwartzScalar,
            S.velocitySlice t = rankOneSchwartzVelocity φ v := by
  rintro ⟨S, hconv, hpressure, hall⟩
  exact
    (S.stokesFlow_not_forall_velocitySlice_rankOne_of_fixed_direction
      hconv hpressure hv) hall

end NavierStokes
end FluidDynamics
end Mettapedia
