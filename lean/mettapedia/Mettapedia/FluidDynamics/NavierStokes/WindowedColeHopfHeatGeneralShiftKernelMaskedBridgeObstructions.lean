import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatGeneralShiftKernelMaskedBridgeConsequences

/-!
# Masked Common-Shift Bridge Obstructions

This module was split out of
`WindowedColeHopfHeatGeneralShiftKernelMaskedSpecialization.lean` to keep the
masked common-shift specialization organized by mathematical role.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatGeneralShiftKernelMaskedBridgeObstructions

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X] [DecidableEq X]

theorem WeightedObservable.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_of_liveBaseCoeffSum_ne_one_via_generalShiftKernel
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (hs : s ≠ 0)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
    (hbase : SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff ≠ 1)
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
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector
              (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
                (X := X) mask s seedCoeff liveCoeff)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatShiftKernelCandidate
            (ι := ι) (X := X)
            selector
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hbase <|
    L.windowedColeHopfHeatMaskedShiftKernel_liveBaseCoeffSum_eq_one_of_topDownBridge_via_generalShiftKernel
      (ι := ι) (X := X)
      selector mask s hs seedCoeff liveCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness

theorem WeightedObservable.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_of_seedCoeffSum_ne_zero_via_generalShiftKernel
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
    (hseedMass : SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff ≠ 0)
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
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + s) ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector
              (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
                (X := X) mask s seedCoeff liveCoeff)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatShiftKernelCandidate
            (ι := ι) (X := X)
            selector
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hseedMass <|
    L.windowedColeHopfHeatMaskedShiftKernel_seedCoeffSum_eq_zero_of_topDownBridge_via_generalShiftKernel
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness

theorem WeightedObservable.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_of_liveShiftCoeffSum_ne_zero_via_generalShiftKernel
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (hs : s ≠ 0)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
    (hliveMass : SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff ≠ 0)
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
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector
              (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
                (X := X) mask s seedCoeff liveCoeff)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatShiftKernelCandidate
            (ι := ι) (X := X)
            selector
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hliveMass <|
    L.windowedColeHopfHeatMaskedShiftKernel_liveShiftCoeffSum_eq_zero_of_topDownBridge_via_generalShiftKernel
      (ι := ι) (X := X)
      selector mask s hs seedCoeff liveCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness

end WindowedColeHopfHeatGeneralShiftKernelMaskedBridgeObstructions

end NavierStokes
end FluidDynamics
end Mettapedia
