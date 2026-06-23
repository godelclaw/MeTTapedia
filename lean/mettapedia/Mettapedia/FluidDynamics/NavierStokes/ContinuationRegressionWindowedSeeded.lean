import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatScaledSeededFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatScaledPressureSeededFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedLiveProfileFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedLiveOperatorFrontier

/-!
# Windowed seeded, pressure-seeded, seed-live profile, and seed-live operator regression checks.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ContinuationRegression

section WindowedColeHopfHeatScaledSeeded

variable {ι X : Type*}
variable [Fintype ι]

theorem windowed_heat_scaled_seeded_compatibility_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    windowedScaledCompatibilityPred (X := X) a
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatScaledCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  exact
    L.windowedColeHopfHeatScaledCandidate_has_scaledCompatibility
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_scaled_seeded_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (L.windowedColeHopfHeatScaledSeededPredicateKit
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) := by
  exact
    L.windowedColeHopfHeat_realizes_scaled_seeded_clause
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_scaled_seeded_bridge_retains_uniform_vorticity_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
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
    L.toWindowedColeHopfHeatScaledSeededBridge_retains_uniform_vorticity
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

end WindowedColeHopfHeatScaledSeeded

section WindowedColeHopfHeatScaledPressureSeeded

variable {ι X : Type*}
variable [Fintype ι]

theorem windowed_heat_scaled_pressure_seeded_selfCompatibility_of_one_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatScaledPressureSeededCandidate
        (ι := ι) (X := X)
        selector (1 : ℝ) c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  exact
    L.windowedColeHopfHeatScaledPressureSeededCandidate_has_selfCompatibility_of_one
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_scaled_pressure_seeded_clause_of_one_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
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
        (L.windowedColeHopfHeatScaledPressureSeededInitialSlice
          (ι := ι) (X := X)
          selector (1 : ℝ) c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_scaled_pressure_seeded_clause_of_one
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_scaled_pressure_seeded_clause_of_zero_vorticity_regression
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
    (hzero :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatScaledPressureSeededInitialSlice
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_scaled_pressure_seeded_clause_of_zero_vorticity
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hzero

end WindowedColeHopfHeatScaledPressureSeeded

section WindowedColeHopfHeatSeedLiveProfile

variable {ι X : Type*}
variable [Fintype ι]

theorem windowed_heat_seedLive_profile_eq_live_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (P : SeedLiveProfile)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hP : ∀ seed live, P.profile seed live = live) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveInitialSlice
          (ι := ι) (X := X)
          selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_seedLive_pressure_seeded_clause_of_profile_eq_live
      (ι := ι) (X := X)
      selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hP

theorem windowed_heat_seedLive_profile_eq_seed_stationary_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (P : SeedLiveProfile)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hP : ∀ seed live, P.profile seed live = seed)
    (hstat :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveInitialSlice
          (ι := ι) (X := X)
          selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_seedLive_pressure_seeded_clause_of_profile_eq_seed_of_stationary
      (ι := ι) (X := X)
      selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hP hstat

theorem windowed_heat_seedLive_zero_vorticity_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (P : SeedLiveProfile)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hP0 : P.profile 0 0 = 0)
    (hzero :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveInitialSlice
          (ι := ι) (X := X)
          selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_seedLive_pressure_seeded_clause_of_zero_vorticity
      (ι := ι) (X := X)
      selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hP0 hzero

theorem windowed_heat_seedLive_bridge_retains_uniform_vorticity_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (P : SeedLiveProfile)
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
    L.toWindowedColeHopfHeatSeedLiveBridge_retains_uniform_vorticity
      (ι := ι) (X := X)
      selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

end WindowedColeHopfHeatSeedLiveProfile

section WindowedColeHopfHeatSeedLiveOperator

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

omit [AddMonoid X] in
theorem windowed_heat_seedLiveOperator_operator_eq_live_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hO : ∀ seed live y, O.operator seed live y = live y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_seedLiveOperator_pressure_seeded_clause_of_operator_eq_live
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hO

omit [AddMonoid X] in
theorem windowed_heat_seedLiveOperator_zero_vorticity_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hO0 : ∀ y, O.operator (fun _ => 0) (fun _ => 0) y = 0)
    (hzero :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_seedLiveOperator_pressure_seeded_clause_of_zero_vorticity
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hO0 hzero

omit [AddMonoid X] in
theorem windowed_heat_seedLiveOperator_operator_eq_seed_stationary_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hO : ∀ seed live y, O.operator seed live y = seed y)
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
        (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_seedLiveOperator_pressure_seeded_clause_of_operator_eq_seed_of_stationary
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hO hstat

omit [AddMonoid X] in
theorem windowed_heat_seedLiveOperator_bridge_retains_uniform_vorticity_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
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
    L.toWindowedColeHopfHeatSeedLiveOperatorBridge_retains_uniform_vorticity
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

end WindowedColeHopfHeatSeedLiveOperator

end ContinuationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
