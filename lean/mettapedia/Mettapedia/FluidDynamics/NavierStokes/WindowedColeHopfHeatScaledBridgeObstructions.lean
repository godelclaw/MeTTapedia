import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatScaledSelfCompatibilityRigidity

/-!
# Scaled Windowed Route Bridge Obstructions

This module was split out of `WindowedColeHopfHeatSelfCompatibilityObstruction.lean`
to keep the scaled windowed route obstruction organized by mathematical role.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatScaledBridgeObstructions

variable {ι X : Type*}
variable [Fintype ι]

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_eq_one_of_topDownBridge_of_nonzero_vorticity
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
    (B :
      TopDownFeffermanBridge
        (L.windowedColeHopfHeatScaledSeededPredicateKit
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatScaledCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hnz :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    a = 1 := by
  have hself :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatScaledCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  exact
    L.windowedColeHopfHeatScaledCandidate_eq_one_of_selfCompatibility_of_nonzero_vorticity
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself hnz

theorem WeightedObservable.not_exists_windowedColeHopfHeatScaledSeededTopDownBridge_of_ne_one_of_nonzero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (ha : a ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hnz :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (L.windowedColeHopfHeatScaledSeededPredicateKit
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatScaledCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact ha <|
    L.windowedColeHopfHeatScaledCandidate_eq_one_of_topDownBridge_of_nonzero_vorticity
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hnz


end WindowedColeHopfHeatScaledBridgeObstructions

end NavierStokes
end FluidDynamics
end Mettapedia
