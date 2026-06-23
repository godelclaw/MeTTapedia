import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatScaledSelfCompatibilityPositive

/-!
# Scaled Windowed Route Self-Compatibility Rigidity

This module was split out of `WindowedColeHopfHeatSelfCompatibilityObstruction.lean`
to keep the scaled windowed route obstruction organized by mathematical role.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatScaledSelfCompatibilityRigidity

variable {ι X : Type*}
variable [Fintype ι]

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_zero_vorticity_of_selfCompatibility_of_ne_one
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (ha : a ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hself :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatScaledCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity) :
    ∀ t y,
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 := by
  intro t y
  have hEq :
      a *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y := by
    simpa [windowedSelfCompatibility,
      WeightedObservable.windowedColeHopfHeatScaledCandidate,
      WeightedObservable.windowedColeHopfHeatCandidate] using hself t y
  have hMul :
      (a - 1) *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 := by
    linarith
  have hne : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  rcases mul_eq_zero.mp hMul with hzero | hzero
  · exact False.elim (hne hzero)
  · exact hzero

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_eq_one_of_selfCompatibility_of_nonzero_vorticity
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
    (hself :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatScaledCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity)
    (hnz :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    a = 1 := by
  by_contra ha
  rcases hnz with ⟨t, y, hne⟩
  have hzero :=
    L.windowedColeHopfHeatScaledCandidate_zero_vorticity_of_selfCompatibility_of_ne_one
      (ι := ι) (X := X)
      selector a c ν ha hc hν curlFrame curlBound curlBound_nonneg hcurl x hself t y
  exact hne hzero

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_not_selfCompatibility_of_ne_one_of_nonzero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (ha : a ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hnz :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatScaledCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  intro hself
  rcases hnz with ⟨t, y, hne⟩
  have hzero :=
    L.windowedColeHopfHeatScaledCandidate_zero_vorticity_of_selfCompatibility_of_ne_one
      (ι := ι) (X := X)
      selector a c ν ha hc hν curlFrame curlBound curlBound_nonneg hcurl x hself t y
  exact hne hzero


end WindowedColeHopfHeatScaledSelfCompatibilityRigidity

end NavierStokes
end FluidDynamics
end Mettapedia
