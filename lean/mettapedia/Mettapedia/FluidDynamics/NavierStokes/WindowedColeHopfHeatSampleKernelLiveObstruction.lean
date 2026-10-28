import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSampleKernelSeedObstruction

/-!
# Diagonal Sample-Kernel Live-Coefficient Obstruction

This module was split out of `WindowedColeHopfHeatSampleKernelObstruction.lean`
to keep the diagonal sample-kernel route obstruction organized by theorem pair.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSampleKernelLiveObstruction

variable {ι X : Type*}
variable [Fintype ι]

theorem WeightedObservable.windowedColeHopfHeatDiagonalSampleKernel_b_eq_zero_of_topDownBridge_of_zero_live_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatSampleKernelInitialSlice
            (ι := ι) (X := X)
            selector (diagonalSampleKernel (X := X) a b)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector (diagonalSampleKernel (X := X) a b)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    b = 0 := by
  have hselfSample :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector (diagonalSampleKernel (X := X) a b)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  have hselfSeed :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [L.windowedColeHopfHeatDiagonalSampleKernelCandidate_eq_seedBlendCandidate
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x] using hselfSample
  exact
    L.windowedColeHopfHeatSeedBlend_b_eq_zero_of_selfCompatibility_of_zero_live_nonzero_initial
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hselfSeed hwitness

theorem WeightedObservable.not_exists_windowedColeHopfHeatDiagonalSampleKernelTopDownBridge_of_ne_zero_of_zero_live_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (hb : b ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSampleKernelInitialSlice
              (ι := ι) (X := X)
              selector (diagonalSampleKernel (X := X) a b)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSampleKernelCandidate
            (ι := ι) (X := X)
            selector (diagonalSampleKernel (X := X) a b)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hb <|
    L.windowedColeHopfHeatDiagonalSampleKernel_b_eq_zero_of_topDownBridge_of_zero_live_nonzero_initial
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness


end WindowedColeHopfHeatSampleKernelLiveObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
