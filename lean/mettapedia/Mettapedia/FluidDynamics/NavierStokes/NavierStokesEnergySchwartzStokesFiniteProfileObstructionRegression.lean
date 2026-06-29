import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzStokesFiniteProfileObstruction

/-!
# Regression checks for finite-profile Stokes Rayleigh-floor obstructions
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap Topology

namespace Regression

theorem stokes_finite_profile_rayleigh_floor_boundary_packet_regression
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {T : NSTime} (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      SchwartzNonzeroTimeSupportKernel ν S.velocity S.pressure ∧
      (∀ {s t : NSTime}, s < t → t ≤ T →
        normalizedKineticEnergy S.velocity t <
          normalizedKineticEnergy S.velocity s) ∧
      (∀ lam : ℝ, 0 < lam →
        ¬ ∀ t : NSTime, t ≤ T →
          lam ≤
            coordinateEnstrophyAt S.velocity t /
              normalizedKineticEnergy S.velocity t) ∧
      ∀ lam : ℝ, 0 < lam →
        ∃ t : NSTime,
          t ≤ T ∧
            (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
              0 < coordinateEnstrophyAt S.velocity t ∧
                0 < normalizedKineticEnergy S.velocity t ∧
                  0 <
                    coordinateEnstrophyAt S.velocity t /
                      normalizedKineticEnergy S.velocity t ∧
                    coordinateEnstrophyAt S.velocity t /
                        normalizedKineticEnergy S.velocity t < lam := by
  exact
    S.stokesFlow_finiteProfileRayleighFloorBoundary_packet
      hν hconv hpressure hneT

theorem not_stokes_finite_profile_rayleigh_floor_certificate_regression
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (C : StokesFiniteProfileRayleighFloorCertificate S) :
    False := by
  exact S.stokesFiniteProfileRayleighFloorCertificate_false_of_posViscosity hν C

theorem not_exists_stokes_finite_profile_rayleigh_floor_certificate_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ _ : StokesFiniteProfileRayleighFloorCertificate S, True := by
  exact not_exists_nonzeroSchwartzStokesFlow_finiteProfileRayleighFloorCertificate hν

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
