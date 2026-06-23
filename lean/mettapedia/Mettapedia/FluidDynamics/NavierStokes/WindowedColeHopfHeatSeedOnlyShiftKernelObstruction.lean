import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedOnlySampleKernelObstruction
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatShiftKernelFrontierCore

/-!
# Seed-Only Shift-Kernel Obstruction

Specializes seed-only sample-kernel obstruction to shift-kernel candidates.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSeedOnlyShiftKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatSeedOnlyShiftKernel_vorticity_eq_of_topDownBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (hzero : ∀ i, K.liveCoeff i = 0)
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
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (selfCompatibility (Time := NNReal) (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y : X} :
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y =
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y := by
  have hzeroSample : ∀ i, K.toSampleKernel.liveCoeff i = 0 := hzero
  have hCandSample :
      B.candidate =
        L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector K.toSampleKernel c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
    simpa [WeightedObservable.windowedColeHopfHeatShiftKernelCandidate] using hCand
  exact
    L.windowedColeHopfHeatSeedOnlySampleKernel_vorticity_eq_of_topDownBridge
      (ι := ι) (X := X) (κ := κ)
      selector K.toSampleKernel hzeroSample c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCandSample

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedOnlyShiftKernelTopDownBridge_of_vorticity_ne
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (hzero : ∀ i, K.liveCoeff i = 0)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    {t₁ t₂ : NNReal} {y : X}
    (hvary :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y ≠
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (selfCompatibility (Time := NNReal) (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatShiftKernelCandidate
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hvary <|
    L.windowedColeHopfHeatSeedOnlyShiftKernel_vorticity_eq_of_topDownBridge
      (ι := ι) (X := X) (κ := κ)
      selector K hzero c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand

theorem WeightedObservable.windowedColeHopfHeatSeedOnlyShiftKernel_vorticity_eq_of_topDownBridge_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (hzero : ∀ i, K.liveCoeff i = 0)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (selfCompatibility (Time := NNReal) (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y : X} :
    (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y =
    (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y := by
  simpa [WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatSeedOnlyShiftKernel_vorticity_eq_of_topDownBridge
        (ι := ι) (X := X) (κ := κ)
        selector K hzero c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand)

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedOnlyShiftKernelTopDownBridge_of_vorticity_ne_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (hzero : ∀ i, K.liveCoeff i = 0)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    {t₁ t₂ : NNReal} {y : X}
    (hvary :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y ≠
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (selfCompatibility (Time := NNReal) (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  simpa [WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.not_exists_windowedColeHopfHeatSeedOnlyShiftKernelTopDownBridge_of_vorticity_ne
        (ι := ι) (X := X) (κ := κ)
        selector K hzero c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hvary)

end WindowedColeHopfHeatSeedOnlyShiftKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
