import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatPackage
import Mettapedia.FluidDynamics.NavierStokes.FeffermanSeedLiveShiftKernelFrontier

/-!
# Base shift-kernel frontier on the windowed Cole-Hopf heat route
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatShiftKernelFrontier

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

abbrev WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice
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
    (x : ModeState) : X → ℝ :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorInitialSlice
      K.toSampleKernel.toSeedLiveOperator

abbrev WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState) : X → ℝ :=
  (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).seedLiveOperatorInitialSlice
      K.toSampleKernel.toSeedLiveOperator

abbrev WeightedObservable.windowedColeHopfHeatShiftKernelCandidate
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
    VelocityPressureCandidate (Time := NNReal) (X := X) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorCandidate
      K.toSampleKernel.toSeedLiveOperator

abbrev WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState) :
    VelocityPressureCandidate (Time := NNReal) (X := X) :=
  (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).seedLiveOperatorCandidate
      K.toSampleKernel.toSeedLiveOperator

theorem WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_has_shiftKernelCompatibility
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
    shiftKernelCompatibilityPred (Time := NNReal) (X := X) K
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    change sampleKernelCompatibilityPred (Time := NNReal) (X := X) K.toSampleKernel
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      ((L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorCandidate
        K.toSampleKernel.toSeedLiveOperator).velocity
    exact
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorCandidate_has_seedLiveOperatorCompatibility
          K.toSampleKernel.toSeedLiveOperator

theorem WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_has_shiftKernelCompatibility_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState) :
    shiftKernelCompatibilityPred (Time := NNReal) (X := X) K
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
        (L.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).velocity := by
    change sampleKernelCompatibilityPred (Time := NNReal) (X := X) K.toSampleKernel
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
      ((L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).seedLiveOperatorCandidate
        K.toSampleKernel.toSeedLiveOperator).velocity
    exact
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).seedLiveOperatorCandidate_has_seedLiveOperatorCompatibility
          K.toSampleKernel.toSeedLiveOperator

theorem WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_has_selfCompatibility_of_zero_vorticity
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
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).shiftKernelCandidate_has_selfCompatibility_of_zero_vorticity
      K hzero

def WeightedObservable.toWindowedColeHopfHeatShiftKernelAlmostBridge
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
    AlmostFeffermanBridge
      (K := pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).toShiftKernelAlmostBridge K

def WeightedObservable.toWindowedColeHopfHeatShiftKernelBridge
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
    TopDownFeffermanBridge
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
      (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).toShiftKernelBridge K

def WeightedObservable.toWindowedColeHopfHeatShiftKernelBridge_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState) :
    TopDownFeffermanBridge
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
      (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).toShiftKernelBridge K

theorem WeightedObservable.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause
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
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.toWindowedColeHopfHeatShiftKernelBridge
    (ι := ι) (X := X)
    selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_clause

theorem WeightedObservable.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)) :=
  (L.toWindowedColeHopfHeatShiftKernelBridge_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).realizes_clause

theorem WeightedObservable.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_selfCompatibility
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
    (hcompat :
      selfCompatibility (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_shiftKernel_pressure_seeded_clause_of_selfCompatibility
      K hcompat

theorem WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_has_selfCompatibility_of_operator_eq_live
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
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).shiftKernelCandidate_has_selfCompatibility_of_operator_eq_live
      K hK

theorem WeightedObservable.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_live
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
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_live
      K hK

theorem WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
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
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).shiftKernelCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
      K hK hstat

theorem WeightedObservable.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
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
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
      K hK hstat

theorem WeightedObservable.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_zero_vorticity
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
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_shiftKernel_pressure_seeded_clause_of_zero_vorticity
      K hzero

theorem WeightedObservable.toWindowedColeHopfHeatShiftKernelBridge_retains_uniform_vorticity
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
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope :=
  (L.toWindowedColeHopfHeatShiftKernelBridge
    (ι := ι) (X := X)
    selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).retains_uniform_vorticity

end WindowedColeHopfHeatShiftKernelFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
