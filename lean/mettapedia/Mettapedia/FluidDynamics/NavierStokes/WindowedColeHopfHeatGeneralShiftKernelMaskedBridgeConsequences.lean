import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatGeneralShiftKernelMaskedCoefficients
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatGeneralShiftKernelCoefficientLaws

/-!
# Masked Common-Shift Bridge Consequences

This module was split out of
`WindowedColeHopfHeatGeneralShiftKernelMaskedSpecialization.lean` to keep the
masked common-shift specialization organized by mathematical role.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatGeneralShiftKernelMaskedBridgeConsequences

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X] [DecidableEq X]

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_liveBaseCoeffSum_eq_one_of_topDownBridge_via_generalShiftKernel
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (hs : s ≠ 0)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
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
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
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
    SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff = 1 := by
  rcases hwitness with ⟨t, y, hseed, hshift, hnz⟩
  have hseed' :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).seedShift i) = 0 := by
    intro i
    simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel] using hseed
  have hlive' :
      ∀ i : κ,
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).liveShift i) = 0 := by
    intro i hi
    by_cases hmask : mask i = true
    · simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask] using hshift
    · have : (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).liveShift i = 0 := by
        simp [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask]
      exact False.elim (hi this)
  simpa [SeedLiveShiftKernel.liveCoeffSumAt_zero_maskedAnchoredTranslationShiftKernel_eq_maskedLiveBaseCoeffSum
      (X := X) mask s hs seedCoeff liveCoeff] using
    L.windowedColeHopfHeatShiftKernel_liveCoeffSumAt_zero_eq_one_of_topDownBridge_of_zero_seed_other_live_zero_witness
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hseed' hlive' hnz

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_seedCoeffSum_eq_zero_of_topDownBridge_via_generalShiftKernel
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
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
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
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
    SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff = 0 := by
  rcases hwitness with ⟨t, y, hzero, hshift, hseedNz⟩
  have hlive' :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).liveShift i) = 0 := by
    intro i
    by_cases hmask : mask i = true
    · simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask] using hshift
    · simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask] using hzero
  have hseedOther' :
      ∀ i : κ,
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).seedShift i ≠ s →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).seedShift i) = 0 := by
    intro i hi
    have : ¬ ((SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).seedShift i ≠ s) := by
      simp [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel]
    exact False.elim (this hi)
  simpa [SeedLiveShiftKernel.seedCoeffSumAt_maskedAnchoredTranslationShiftKernel_eq_maskedSeedCoeffSum
      (X := X) mask s seedCoeff liveCoeff] using
    L.windowedColeHopfHeatShiftKernel_seedCoeffSumAt_eq_zero_of_topDownBridge_of_zero_live_zero_other_seed_nonzero_seed
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      s c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hzero hlive' hseedOther' hseedNz

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_liveShiftCoeffSum_eq_zero_of_topDownBridge_via_generalShiftKernel
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (hs : s ≠ 0)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
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
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
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
    SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff = 0 := by
  rcases hwitness with ⟨t, y, hzero, hseed, hliveNz⟩
  have hseed' :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).seedShift i) = 0 := by
    intro i
    simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel] using hseed
  have hliveOther' :
      ∀ i : κ,
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).liveShift i ≠ s →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).liveShift i) = 0 := by
    intro i hi
    by_cases hmask : mask i = true
    · have : (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).liveShift i = s := by
        simp [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask]
      exact False.elim (hi this)
    · simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask] using hzero
  simpa [SeedLiveShiftKernel.liveCoeffSumAt_maskedAnchoredTranslationShiftKernel_eq_maskedLiveShiftCoeffSum
      (X := X) mask s hs seedCoeff liveCoeff] using
    L.windowedColeHopfHeatShiftKernel_liveCoeffSumAt_eq_zero_of_topDownBridge_of_zero_live_zero_seed_zero_other_live_nonzero_live
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      s c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hzero hseed' hliveOther' hliveNz

end WindowedColeHopfHeatGeneralShiftKernelMaskedBridgeConsequences

end NavierStokes
end FluidDynamics
end Mettapedia
