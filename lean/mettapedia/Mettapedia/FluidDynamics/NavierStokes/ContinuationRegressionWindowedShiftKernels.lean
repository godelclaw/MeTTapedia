import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatAnchoredShiftKernelFrontier

/-!
# Windowed shift-kernel regression checks.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ContinuationRegression

section WindowedColeHopfHeatShiftKernel

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

theorem windowed_heat_shiftKernel_live_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : ∀ seed live y, K.toSampleKernel.toSeedLiveOperator.operator seed live y = live y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_live
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK

theorem windowed_heat_shiftKernel_zero_vorticity_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hzero :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_zero_vorticity
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hzero

theorem windowed_heat_shiftKernel_seed_stationary_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : ∀ seed live y, K.toSampleKernel.toSeedLiveOperator.operator seed live y = seed y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hK hstat

theorem windowed_heat_shiftKernel_bridge_retains_uniform_vorticity_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    ∀ t y,
      |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| ≤
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope := by
  exact
    L.toWindowedColeHopfHeatShiftKernelBridge_retains_uniform_vorticity
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_anchoredTranslation_shiftKernel_initialSlice_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    L.windowedColeHopfHeatShiftKernelInitialSlice
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s a b d) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatAnchoredShiftInitialSlice
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatAnchoredTranslationShiftKernelInitialSlice_eq_anchoredShiftInitialSlice
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_anchoredTranslation_shiftKernel_candidate_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s a b d) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatAnchoredShiftCandidate
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatAnchoredTranslationShiftKernelCandidate_eq_anchoredShiftCandidate
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_anchoredTranslation_shiftKernel_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_anchoredTranslation_shiftKernel_bridge_retains_uniform_vorticity_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    ∀ t y,
      |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| ≤
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope := by
  exact
    L.toWindowedColeHopfHeatShiftKernelBridge_retains_uniform_vorticity
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s a b d)
      c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_anchoredTranslation_shiftKernel_selfCompatibility_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
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
        (L.windowedColeHopfHeatAnchoredShiftCandidate
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause_of_anchoredShiftSelfCompatibility
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself

theorem windowed_heat_anchoredTranslation_shiftKernel_zero_vorticity_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hzero :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause_of_zero_vorticity
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hzero

theorem windowed_heat_anchoredTranslation_shiftKernel_live_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK :
      ∀ seed live y,
        ((anchoredTranslationShiftKernel (X := X) s a b d).toSampleKernel.toSeedLiveOperator).operator
          seed live y = live y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause_of_operator_eq_live
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK

theorem windowed_heat_anchoredTranslation_shiftKernel_seed_stationary_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK :
      ∀ seed live y,
        ((anchoredTranslationShiftKernel (X := X) s a b d).toSampleKernel.toSeedLiveOperator).operator
          seed live y = seed y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hK hstat

end WindowedColeHopfHeatShiftKernel

end ContinuationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
