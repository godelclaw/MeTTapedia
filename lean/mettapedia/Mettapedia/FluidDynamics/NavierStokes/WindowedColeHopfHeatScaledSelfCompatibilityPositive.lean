import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatScaledSeededFrontier

/-!
# Scaled Windowed Route Positive Self-Compatibility Cases

This module was split out of `WindowedColeHopfHeatSelfCompatibilityObstruction.lean`
to keep the scaled windowed route obstruction organized by mathematical role.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatScaledSelfCompatibilityPositive

variable {ι X : Type*}
variable [Fintype ι]

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_has_selfCompatibility_of_one
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
    windowedSelfCompatibility
      (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatScaledCandidate
        (ι := ι) (X := X)
        selector (1 : ℝ) c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  intro t y
  simp [WeightedObservable.windowedColeHopfHeatScaledCandidate,
    WeightedObservable.windowedColeHopfHeatCandidate]

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_has_selfCompatibility_of_zero_vorticity
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
    windowedSelfCompatibility
      (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatScaledCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  intro t y
  simp [WeightedObservable.windowedColeHopfHeatScaledCandidate,
    WeightedObservable.windowedColeHopfHeatCandidate, hz t y]


end WindowedColeHopfHeatScaledSelfCompatibilityPositive

end NavierStokes
end FluidDynamics
end Mettapedia
