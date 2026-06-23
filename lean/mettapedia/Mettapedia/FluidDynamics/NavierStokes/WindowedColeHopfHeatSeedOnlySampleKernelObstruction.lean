import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedOnlyOperatorObstructionCore
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSampleKernelFrontier

/-!
# Seed-Only Sample-Kernel Obstruction

Specializes seed-only operator obstruction to sample-kernel candidates whose live
coefficients vanish.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSeedOnlySampleKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ]

theorem SeedLiveSampleKernel.toSeedLiveOperator_seedOnly
    (K : SeedLiveSampleKernel κ X)
    (hzero : ∀ i, K.liveCoeff i = 0) :
    ∀ seed live₁ live₂ y, K.toSeedLiveOperator.operator seed live₁ y = K.toSeedLiveOperator.operator seed live₂ y := by
  intro seed live₁ live₂ y
  simp [SeedLiveSampleKernel.toSeedLiveOperator, hzero]

theorem WeightedObservable.windowedColeHopfHeatSeedOnlySampleKernel_vorticity_eq_of_topDownBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
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
          (L.windowedColeHopfHeatSampleKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (selfCompatibility (Time := NNReal) (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y : X} :
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y =
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y := by
  have hseedOnly :
      ∀ seed live₁ live₂ y, K.toSeedLiveOperator.operator seed live₁ y =
        K.toSeedLiveOperator.operator seed live₂ y :=
    K.toSeedLiveOperator_seedOnly hzero
  have hCandOp :
      B.candidate =
        L.windowedColeHopfHeatSeedLiveOperatorCandidate
          (ι := ι) (X := X)
          selector K.toSeedLiveOperator c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
    simpa using hCand
  exact
    L.windowedColeHopfHeatSeedOnlyOperator_vorticity_eq_of_topDownBridge
      (ι := ι) (X := X)
      selector K.toSeedLiveOperator hseedOnly c ν hc hν curlFrame curlBound curlBound_nonneg
      hcurl x B hCandOp

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedOnlySampleKernelTopDownBridge_of_vorticity_ne
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
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
            (L.windowedColeHopfHeatSampleKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (selfCompatibility (Time := NNReal) (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSampleKernelCandidate
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hvary <|
    L.windowedColeHopfHeatSeedOnlySampleKernel_vorticity_eq_of_topDownBridge
      (ι := ι) (X := X) (κ := κ)
      selector K hzero c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand

theorem WeightedObservable.windowedColeHopfHeatSeedOnlySampleKernel_vorticity_eq_of_topDownBridge_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
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
          (L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (selfCompatibility (Time := NNReal) (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSampleKernelCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y : X} :
    (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y =
    (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y := by
  simpa [WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatSeedOnlySampleKernel_vorticity_eq_of_topDownBridge
        (ι := ι) (X := X) (κ := κ)
        selector K hzero c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand)

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedOnlySampleKernelTopDownBridge_of_vorticity_ne_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
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
            (L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (selfCompatibility (Time := NNReal) (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSampleKernelCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  simpa [WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.not_exists_windowedColeHopfHeatSeedOnlySampleKernelTopDownBridge_of_vorticity_ne
        (ι := ι) (X := X) (κ := κ)
        selector K hzero c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hvary)

end WindowedColeHopfHeatSeedOnlySampleKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
