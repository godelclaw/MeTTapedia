import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatGeneralShiftKernelCoefficientLaws

/-!
# General Shift-Kernel No-Bridge Corollaries

Coefficient-law failures repackaged as nonexistence results for the general
finite shift-kernel top-down bridge.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatGeneralShiftKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X] [DecidableEq X]

theorem WeightedObservable.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_of_liveCoeffSumAt_zero_ne_one_of_zero_seed_other_live_zero_witness
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hbase : SeedLiveShiftKernel.liveCoeffSumAt K 0 ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hwitness :
      ∃ t y,
        (∀ i : κ,
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
            (y + K.seedShift i) = 0) ∧
        (∀ i : κ, K.liveShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
            (y + K.liveShift i) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatShiftKernelCandidate
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  rcases hwitness with ⟨t, y, hseed, hlive, hnz⟩
  exact hbase <|
    L.windowedColeHopfHeatShiftKernel_liveCoeffSumAt_zero_eq_one_of_topDownBridge_of_zero_seed_other_live_zero_witness
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hseed hlive hnz

theorem WeightedObservable.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_of_zeroAnchorCoeffSum_ne_one_of_zero_other_anchors_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hzeroMass :
      SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0 ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hwitness :
      ∃ y,
        (∀ i : κ, K.seedShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
            (y + K.seedShift i) = 0) ∧
        (∀ i : κ, K.liveShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
            (y + K.liveShift i) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatShiftKernelCandidate
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  rcases hwitness with ⟨y, hseedOther, hliveOther, hnz⟩
  exact hzeroMass <|
    L.windowedColeHopfHeatShiftKernel_zeroAnchorCoeffSum_eq_one_of_topDownBridge_of_zero_other_anchors_nonzero_initial
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hseedOther hliveOther hnz

theorem WeightedObservable.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_of_seedCoeffSumAt_ne_zero_of_zero_live_zero_other_seed_nonzero_seed
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (u : X)
    (c ν : ℝ)
    (hseedMass : SeedLiveShiftKernel.seedCoeffSumAt K u ≠ 0)
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
        (∀ i : κ,
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
            (y + K.liveShift i) = 0) ∧
        (∀ i : κ, K.seedShift i ≠ u →
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
            (y + K.seedShift i) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + u) ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatShiftKernelCandidate
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  rcases hwitness with ⟨t, y, hzero, hlive, hseedOther, hseedNz⟩
  exact hseedMass <|
    L.windowedColeHopfHeatShiftKernel_seedCoeffSumAt_eq_zero_of_topDownBridge_of_zero_live_zero_other_seed_nonzero_seed
      (ι := ι) (X := X)
      selector K u c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hzero hlive hseedOther hseedNz

theorem WeightedObservable.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_of_liveCoeffSumAt_ne_zero_of_zero_live_zero_seed_zero_other_live_nonzero_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (u : X)
    (c ν : ℝ)
    (hliveMass : SeedLiveShiftKernel.liveCoeffSumAt K u ≠ 0)
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
        (∀ i : κ,
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
            (y + K.seedShift i) = 0) ∧
        (∀ i : κ, K.liveShift i ≠ u →
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
            (y + K.liveShift i) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + u) ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatShiftKernelCandidate
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  rcases hwitness with ⟨t, y, hzero, hseed, hliveOther, hliveNz⟩
  exact hliveMass <|
    L.windowedColeHopfHeatShiftKernel_liveCoeffSumAt_eq_zero_of_topDownBridge_of_zero_live_zero_seed_zero_other_live_nonzero_live
      (ι := ι) (X := X)
      selector K u c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hzero hseed hliveOther hliveNz


end WindowedColeHopfHeatGeneralShiftKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
