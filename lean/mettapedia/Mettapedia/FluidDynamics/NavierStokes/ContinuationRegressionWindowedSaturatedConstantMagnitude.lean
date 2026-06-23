import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelConstantMagnitudeFrontier

/-!
# Windowed constant-magnitude saturated shift-kernel regression checks.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ContinuationRegression

section WindowedColeHopfHeatSaturatedShiftKernelConstantMagnitude

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

theorem windowed_heat_saturated_constantMagnitude_shiftKernel_initialSlice_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (habs :
      ∀ y,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y| = r) :
    L.windowedColeHopfHeatShiftKernelInitialSlice
      (ι := ι) (X := X)
      selector (saturatedConstantMagnitudeShiftKernel X a r) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).saturatedInitialSlice a := by
  exact
    L.windowedColeHopfHeatSaturatedConstantMagnitudeShiftKernelInitialSlice_eq_saturatedInitialSlice
      (ι := ι) (X := X)
      selector a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x habs

theorem windowed_heat_saturated_constantMagnitude_shiftKernel_candidate_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (habs :
      ∀ t y,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector (saturatedConstantMagnitudeShiftKernel X a r) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatSaturatedConstantMagnitudeShiftKernelCandidate_eq_saturatedCandidate
      (ι := ι) (X := X)
      selector a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x habs

theorem windowed_heat_saturated_constantMagnitude_shiftKernel_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (habs :
      ∀ t y,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_constantMagnitudeShiftKernel
      (ι := ι) (X := X)
      selector a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x habs

theorem windowed_heat_saturated_constantMagnitude_shiftKernel_bridge_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (habs :
      ∀ t y,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector (saturatedConstantMagnitudeShiftKernel X a r) c ν hc hν
              curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := X) (saturatedConstantMagnitudeShiftKernel X a r))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.exists_windowedColeHopfHeatSaturatedConstantMagnitudeShiftKernelBridge
      (ι := ι) (X := X)
      selector a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x habs

end WindowedColeHopfHeatSaturatedShiftKernelConstantMagnitude

end ContinuationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
