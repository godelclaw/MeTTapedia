import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzNoUniformDissipation

/-!
# Slice-Schwartz Stokes Finite-Profile Obstruction

This module names the route-facing obstruction used by finite-profile
Stokes-flow generators.  A finite profile search often tries to certify an
exact positive-viscosity Stokes candidate by proving a positive spatial
Rayleigh floor on the whole past ray of a nonzero endpoint.  The bounded
whole-time energy identity forces the opposite behavior: before every nonzero
endpoint, every positive Rayleigh threshold is beaten by an earlier nonzero
slice.

The result is an obstruction for that generator class.  It does not construct
or claim a positive-viscosity nonzero slice-Schwartz solution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap Topology

/-- A route certificate asserting that an exact Stokes-flow candidate has a
positive whole-past spatial Rayleigh floor before a chosen nonzero endpoint.
Finite-profile or spectral-gap generators should discharge this structure only
when their profile class really supplies the stated lower bound. -/
structure StokesFiniteProfileRayleighFloorCertificate
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν) where
  lam : ℝ
  lam_pos : 0 < lam
  endpoint : NSTime
  endpoint_nonzero : ∃ x : NSSpace, S.velocity endpoint x ≠ 0
  zeroConvection : ∀ t x, spatialConvection S.velocity t x = 0
  zeroPressureGradient : ∀ t x, spatialPressureGradient S.pressure t x = 0
  wholePastRayleighFloor :
    ∀ t : NSTime, t ≤ endpoint →
      lam ≤
        coordinateEnstrophyAt S.velocity t /
          normalizedKineticEnergy S.velocity t

namespace NonzeroSchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)

/-- Boundary packet for finite-profile Stokes searches: an inhabited
positive-viscosity exact Stokes candidate must carry the Stokes kernel and
strict past energy ordering, but it also must evade every positive whole-past
spatial Rayleigh floor by producing earlier nonzero slices with arbitrarily
small positive Rayleigh quotient. -/
theorem stokesFlow_finiteProfileRayleighFloorBoundary_packet
    (hν : 0 < ν)
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
  rcases S.stokesFlow_endpointStrictEnergy_and_smallPastCoordinateEnstrophyRatio_packet
      hν hconv hpressure hneT with
    ⟨hstokes, hsupport, hstrict, hsmall⟩
  refine ⟨hstokes, hsupport, hstrict, ?_, hsmall⟩
  intro lam hlam hfloor
  rcases hsmall lam hlam with
    ⟨t, htT, _hne, _hEnstpos, _hEpos, _hratio_pos, hratio_lt⟩
  exact not_le_of_gt hratio_lt (hfloor t htT)

/-- A finite-profile Rayleigh-floor certificate cannot be attached to an
inhabited positive-viscosity exact Stokes candidate. -/
theorem stokesFiniteProfileRayleighFloorCertificate_false_of_posViscosity
    (hν : 0 < ν) (C : StokesFiniteProfileRayleighFloorCertificate S) :
    False := by
  exact
    (S.stokesFlow_finiteProfileRayleighFloorBoundary_packet
      hν C.zeroConvection C.zeroPressureGradient C.endpoint_nonzero).2.2.2.1
      C.lam C.lam_pos C.wholePastRayleighFloor

end NonzeroSchwartzConcreteNavierStokesSolution

/-- Global no-go: no positive-viscosity nonzero exact Stokes candidate can
come with a finite-profile positive whole-past Rayleigh-floor certificate. -/
theorem not_exists_nonzeroSchwartzStokesFlow_finiteProfileRayleighFloorCertificate
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ _ : StokesFiniteProfileRayleighFloorCertificate S, True := by
  rintro ⟨S, C, _hC⟩
  exact S.stokesFiniteProfileRayleighFloorCertificate_false_of_posViscosity hν C

end NavierStokes
end FluidDynamics
end Mettapedia
