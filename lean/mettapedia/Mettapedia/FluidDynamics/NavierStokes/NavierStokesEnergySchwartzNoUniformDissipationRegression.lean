import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzNoUniformDissipation

/-!
# Regression checks for no-uniform past dissipation obstructions
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap Topology

namespace Regression

theorem stokes_positive_viscosity_profile_gap_obstruction_regression
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {lam T : NSTime} (hlam : 0 < lam)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      (¬ ∀ t : NSTime, t ≤ T →
        lam * normalizedKineticEnergy S.velocity t ≤
          coordinateEnergyDissipationRate S.velocity ν t) ∧
      (¬ ∀ t : NSTime, t ≤ T →
        lam * normalizedKineticEnergy S.velocity t ≤
          coordinateEnstrophyAt S.velocity t) ∧
      (¬ ∀ t : NSTime, t ≤ T →
        lam ≤
          coordinateEnstrophyAt S.velocity t /
            normalizedKineticEnergy S.velocity t) ∧
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
    S.stokesFlow_positiveViscosity_profileGapObstruction_packet
      hν hconv hpressure hlam hneT

theorem not_exists_stokes_coordinate_enstrophy_floor_regression
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      (∀ t x, spatialConvection S.velocity t x = 0) ∧
        (∀ t x, spatialPressureGradient S.pressure t x = 0) ∧
          ∃ T : NSTime,
            (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
              ∀ t : NSTime, t ≤ T →
                lam * normalizedKineticEnergy S.velocity t ≤
                  coordinateEnstrophyAt S.velocity t := by
  exact
    not_exists_nonzeroSchwartzStokesFlow_past_coordinateEnstrophy_floor_of_posViscosity
      hν hlam

theorem not_exists_stokes_coordinate_enstrophy_ratio_floor_regression
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      (∀ t x, spatialConvection S.velocity t x = 0) ∧
        (∀ t x, spatialPressureGradient S.pressure t x = 0) ∧
          ∃ T : NSTime,
            (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
              ∀ t : NSTime, t ≤ T →
                lam ≤
                  coordinateEnstrophyAt S.velocity t /
                    normalizedKineticEnergy S.velocity t := by
  exact
    not_exists_nonzeroSchwartzStokesFlow_past_coordinateEnstrophy_ratio_floor_of_posViscosity
      hν hlam

theorem not_exists_stokes_exact_coordinate_enstrophy_rayleigh_regression
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      (∀ t x, spatialConvection S.velocity t x = 0) ∧
        (∀ t x, spatialPressureGradient S.pressure t x = 0) ∧
          ∃ T : NSTime,
            (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
              ∀ t : NSTime, t ≤ T →
                coordinateEnstrophyAt S.velocity t =
                  lam * normalizedKineticEnergy S.velocity t := by
  exact
    not_exists_nonzeroSchwartzStokesFlow_past_exact_coordinateEnstrophyRayleigh_of_posViscosity
      hν hlam

theorem not_exists_stokes_exact_coordinate_enstrophy_ratio_rayleigh_regression
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      (∀ t x, spatialConvection S.velocity t x = 0) ∧
        (∀ t x, spatialPressureGradient S.pressure t x = 0) ∧
          ∃ T : NSTime,
            (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
              ∀ t : NSTime, t ≤ T →
                coordinateEnstrophyAt S.velocity t /
                  normalizedKineticEnergy S.velocity t = lam := by
  exact
    not_exists_nonzeroSchwartzStokesFlow_past_exact_coordinateEnstrophyRatioRayleigh_of_posViscosity
      hν hlam

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
