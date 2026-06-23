import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatScaledSelfCompatibilityPositive
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatScaledBridgeObstructions

/-!
# Scaled Windowed Route Seeded Clauses

This module was split out of `WindowedColeHopfHeatSelfCompatibilityObstruction.lean`
to keep the scaled windowed route obstruction organized by mathematical role.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatScaledSeededClauses

variable {ι X : Type*}
variable [Fintype ι]

theorem WeightedObservable.windowedColeHopfHeat_realizes_scaled_seeded_clause_of_one
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (L.windowedColeHopfHeatScaledSeededPredicateKit
        (ι := ι) (X := X)
        selector (1 : ℝ) c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.toWindowedColeHopfHeatScaledSeededAlmostBridge
    (ι := ι) (X := X)
    selector (1 : ℝ) c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_clause_of_compatibility
      (L.windowedColeHopfHeatScaledCandidate_has_selfCompatibility_of_one
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)

theorem WeightedObservable.windowedColeHopfHeat_realizes_scaled_seeded_clause_of_zero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hz :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    FeffermanGlobalRegularityClause
      (L.windowedColeHopfHeatScaledSeededPredicateKit
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.toWindowedColeHopfHeatScaledSeededAlmostBridge
    (ι := ι) (X := X)
    selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_clause_of_compatibility
      (L.windowedColeHopfHeatScaledCandidate_has_selfCompatibility_of_zero_vorticity
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hz)


end WindowedColeHopfHeatScaledSeededClauses

end NavierStokes
end FluidDynamics
end Mettapedia
