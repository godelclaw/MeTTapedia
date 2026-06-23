import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatAnchoredShiftKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeededModel

/-!
# Anchored Shift-Kernel Self-Compatibility Coefficient Laws

This layer extracts the coefficient laws forced directly by self-compatibility
for the three-term anchored spatial shift route.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatShiftKernelObstruction

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_selfCompatibility_eq
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
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatAnchoredShiftCandidate
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity)
    (t : NNReal) (y : X) :
    a *
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y +
      b *
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + s) +
      d *
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y := by
  simpa [windowedSelfCompatibility,
    WeightedObservable.windowedColeHopfHeatAnchoredShiftCandidate,
    UniformVorticityTendril.seedLiveOperatorCandidate,
    anchoredSeedLiveBlendOperator] using hself t y

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_a_eq_one_of_selfCompatibility_of_zero_shifted_initial_zero_shifted_live_nonzero_live
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
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatAnchoredShiftCandidate
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity)
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
    a = 1 := by
  rcases hwitness with ⟨t, y, hseed, hshift, hne⟩
  have hEq :=
    L.windowedColeHopfHeatAnchoredShift_selfCompatibility_eq
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself t y
  have hMul :
      (a - 1) *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 := by
    rw [hseed, hshift] at hEq
    linarith
  rcases mul_eq_zero.mp hMul with ha | hv
  · linarith
  · exact False.elim (hne hv)

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_b_eq_zero_of_selfCompatibility_of_zero_live_zero_shifted_live_nonzero_shifted_initial
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
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatAnchoredShiftCandidate
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity)
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
    b = 0 := by
  rcases hwitness with ⟨t, y, hlive, hshift, hne⟩
  have hEq :=
    L.windowedColeHopfHeatAnchoredShift_selfCompatibility_eq
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself t y
  have hMul :
      b *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + s) = 0 := by
    rw [hlive, hshift] at hEq
    linarith
  rcases mul_eq_zero.mp hMul with hb | hv
  · exact hb
  · exact False.elim (hne hv)

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_d_eq_zero_of_selfCompatibility_of_zero_live_zero_shifted_initial_nonzero_shifted_live
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
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatAnchoredShiftCandidate
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity)
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
    d = 0 := by
  rcases hwitness with ⟨t, y, hlive, hseed, hne⟩
  have hEq :=
    L.windowedColeHopfHeatAnchoredShift_selfCompatibility_eq
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself t y
  have hMul :
      d *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) = 0 := by
    rw [hlive, hseed] at hEq
    linarith
  rcases mul_eq_zero.mp hMul with hd | hv
  · exact hd
  · exact False.elim (hne hv)


end WindowedColeHopfHeatShiftKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
