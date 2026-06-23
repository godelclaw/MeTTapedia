import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedBlendObstructionBridge

/-!
# Seed-Blend Componentwise Bridge Obstructions

Componentwise-bound transfers of the seed-blend top-down bridge laws and
no-bridge corollaries.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSeedBlendObstruction

variable {ι X : Type*}
variable [Fintype ι]

theorem WeightedObservable.windowedColeHopfHeatSeedBlend_sum_eq_one_of_topDownBridge_of_nonzero_initial_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
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
          (L.windowedColeHopfHeatSeedBlendInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector a b c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSeedBlendCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector a b c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    (hnz :
      ∃ y,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    a + b = 1 := by
  simpa [WeightedObservable.windowedColeHopfHeatSeedBlendInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSeedBlendCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatSeedBlend_sum_eq_one_of_topDownBridge_of_nonzero_initial
        (ι := ι) (X := X)
        selector a b c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand hnz)

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedBlendTopDownBridge_of_sum_ne_one_of_nonzero_initial_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (hab : a + b ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hnz :
      ∃ y,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSeedBlendInitialSlice_of_componentwise_abs_le
              (ι := ι) (X := X)
              selector a b c ν hc hν
              curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSeedBlendCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector a b c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  simpa [WeightedObservable.windowedColeHopfHeatSeedBlendInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSeedBlendCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.not_exists_windowedColeHopfHeatSeedBlendTopDownBridge_of_sum_ne_one_of_nonzero_initial
        (ι := ι) (X := X)
        selector a b c ν hab hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hnz)

theorem WeightedObservable.windowedColeHopfHeatSeedBlend_a_eq_one_of_topDownBridge_of_zero_initial_nonzero_live_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
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
          (L.windowedColeHopfHeatSeedBlendInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector a b c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSeedBlendCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector a b c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y ≠ 0) :
    a = 1 := by
  simpa [WeightedObservable.windowedColeHopfHeatSeedBlendInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSeedBlendCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatSeedBlend_a_eq_one_of_topDownBridge_of_zero_initial_nonzero_live
        (ι := ι) (X := X)
        selector a b c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand hwitness)

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedBlendTopDownBridge_of_ne_one_of_zero_initial_nonzero_live_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (ha : a ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSeedBlendInitialSlice_of_componentwise_abs_le
              (ι := ι) (X := X)
              selector a b c ν hc hν
              curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSeedBlendCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector a b c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  simpa [WeightedObservable.windowedColeHopfHeatSeedBlendInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSeedBlendCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.not_exists_windowedColeHopfHeatSeedBlendTopDownBridge_of_ne_one_of_zero_initial_nonzero_live
        (ι := ι) (X := X)
        selector a b c ν ha hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hwitness)

theorem WeightedObservable.windowedColeHopfHeatSeedBlend_b_eq_zero_of_topDownBridge_of_zero_live_nonzero_initial_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
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
          (L.windowedColeHopfHeatSeedBlendInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector a b c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSeedBlendCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector a b c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    b = 0 := by
  simpa [WeightedObservable.windowedColeHopfHeatSeedBlendInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSeedBlendCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatSeedBlend_b_eq_zero_of_topDownBridge_of_zero_live_nonzero_initial
        (ι := ι) (X := X)
        selector a b c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand hwitness)

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedBlendTopDownBridge_of_ne_zero_of_zero_live_nonzero_initial_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (hb : b ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSeedBlendInitialSlice_of_componentwise_abs_le
              (ι := ι) (X := X)
              selector a b c ν hc hν
              curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSeedBlendCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector a b c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  simpa [WeightedObservable.windowedColeHopfHeatSeedBlendInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSeedBlendCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.not_exists_windowedColeHopfHeatSeedBlendTopDownBridge_of_ne_zero_of_zero_live_nonzero_initial
        (ι := ι) (X := X)
        selector a b c ν hb hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hwitness)


end WindowedColeHopfHeatSeedBlendObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
