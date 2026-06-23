import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedLiveProfileEquality

/-!
# Seed/Live Profile Bridge Obstructions

This module was split out of `WindowedColeHopfHeatSeedLiveProfileObstruction.lean`
to keep seed/live profile equalities and obstruction corollaries separate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSeedLiveProfileBridgeObstructions

variable {ι X : Type*}
variable [Fintype ι]

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedLiveTopDownBridge_of_profile_ne_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (P : SeedLiveProfile)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    {t : NNReal} {y : X}
    (hprofile :
      P.profile
        ((L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y)
        ((L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) ≠
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSeedLiveInitialSlice
              (ι := ι) (X := X)
              selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (selfCompatibility (Time := NNReal) (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSeedLiveCandidate
            (ι := ι) (X := X)
            selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hprofile <|
    L.windowedColeHopfHeatSeedLiveProfile_eq_live_of_topDownBridge_of_nonzero_vorticity
      (ι := ι) (X := X)
      selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hnz


end WindowedColeHopfHeatSeedLiveProfileBridgeObstructions

end NavierStokes
end FluidDynamics
end Mettapedia
