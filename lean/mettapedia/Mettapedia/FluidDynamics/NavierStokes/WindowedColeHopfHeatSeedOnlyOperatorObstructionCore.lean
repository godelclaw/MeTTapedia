import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedLiveOperatorObstruction

/-!
# Seed-Only Operator Obstruction Core

Operator-level consequences for a seed/live candidate whose operator ignores the
live slice on the windowed Cole-Hopf heat route.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSeedOnlyOperatorObstruction

variable {ι X : Type*}
variable [Fintype ι]

theorem WeightedObservable.windowedColeHopfHeatSeedOnlyOperator_vorticity_eq_of_selfCompatibility
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (hseedOnly : ∀ seed live₁ live₂ y, O.operator seed live₁ y = O.operator seed live₂ y)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hself :
      selfCompatibility (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSeedLiveOperatorCandidate
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity)
    {t₁ t₂ : NNReal} {y : X} :
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y =
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  have h₁ :
      O.operator
          (fun z => T.vorticity 1 z)
          (fun z => T.vorticity t₁ z)
          y =
        T.vorticity t₁ y :=
    L.windowedColeHopfHeatSeedLiveOperator_eq_live_of_selfCompatibility
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself
  have h₂ :
      O.operator
          (fun z => T.vorticity 1 z)
          (fun z => T.vorticity t₂ z)
          y =
        T.vorticity t₂ y :=
    L.windowedColeHopfHeatSeedLiveOperator_eq_live_of_selfCompatibility
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself
  calc
    T.vorticity t₁ y
        = O.operator (fun z => T.vorticity 1 z) (fun z => T.vorticity t₁ z) y := by
          symm
          exact h₁
    _ = O.operator (fun z => T.vorticity 1 z) (fun z => T.vorticity t₂ z) y := by
          exact hseedOnly (fun z => T.vorticity 1 z) (fun z => T.vorticity t₁ z)
            (fun z => T.vorticity t₂ z) y
    _ = T.vorticity t₂ y := h₂

theorem WeightedObservable.windowedColeHopfHeatSeedOnlyOperator_vorticity_eq_of_topDownBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (hseedOnly : ∀ seed live₁ live₂ y, O.operator seed live₁ y = O.operator seed live₂ y)
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
          (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
            (ι := ι) (X := X)
            selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (selfCompatibility (Time := NNReal) (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSeedLiveOperatorCandidate
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y : X} :
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y =
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y := by
  have hself :
      selfCompatibility (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSeedLiveOperatorCandidate
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  exact
    L.windowedColeHopfHeatSeedOnlyOperator_vorticity_eq_of_selfCompatibility
      (ι := ι) (X := X)
      selector O hseedOnly c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedOnlyOperatorTopDownBridge_of_vorticity_ne
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (hseedOnly : ∀ seed live₁ live₂ y, O.operator seed live₁ y = O.operator seed live₂ y)
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
            (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
              (ι := ι) (X := X)
              selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (selfCompatibility (Time := NNReal) (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSeedLiveOperatorCandidate
            (ι := ι) (X := X)
            selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hvary <|
    L.windowedColeHopfHeatSeedOnlyOperator_vorticity_eq_of_topDownBridge
      (ι := ι) (X := X)
      selector O hseedOnly c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand

theorem WeightedObservable.windowedColeHopfHeatSeedOnlyOperator_vorticity_eq_of_topDownBridge_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (hseedOnly : ∀ seed live₁ live₂ y, O.operator seed live₁ y = O.operator seed live₂ y)
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
          (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
            (ι := ι) (X := X)
            selector O c ν hc hν
            curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
            (fun x => gamma_le_card_mul_sq_of_abs_le
              (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
            x))
        (selfCompatibility (Time := NNReal) (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSeedLiveOperatorCandidate
          (ι := ι) (X := X)
          selector O c ν hc hν
          curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
          (fun x => gamma_le_card_mul_sq_of_abs_le
            (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
          x)
    {t₁ t₂ : NNReal} {y : X} :
    (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y =
    (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y := by
  simpa [WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatSeedOnlyOperator_vorticity_eq_of_topDownBridge
        (ι := ι) (X := X)
        selector O hseedOnly c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand)

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedOnlyOperatorTopDownBridge_of_vorticity_ne_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (hseedOnly : ∀ seed live₁ live₂ y, O.operator seed live₁ y = O.operator seed live₂ y)
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
            (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
              (ι := ι) (X := X)
              selector O c ν hc hν
              curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
              (fun x => gamma_le_card_mul_sq_of_abs_le
                (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
              x))
          (selfCompatibility (Time := NNReal) (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSeedLiveOperatorCandidate
            (ι := ι) (X := X)
            selector O c ν hc hν
            curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
            (fun x => gamma_le_card_mul_sq_of_abs_le
              (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
            x := by
  simpa [WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.not_exists_windowedColeHopfHeatSeedOnlyOperatorTopDownBridge_of_vorticity_ne
        (ι := ι) (X := X)
        selector O hseedOnly c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hvary)

end WindowedColeHopfHeatSeedOnlyOperatorObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
