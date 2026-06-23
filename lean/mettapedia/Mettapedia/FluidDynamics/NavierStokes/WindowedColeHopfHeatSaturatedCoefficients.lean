import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedFrontier

/-!
# Saturated Same-Route Coefficient Bounds

This module was split out of `WindowedColeHopfHeatSaturatedObstruction.lean`
to keep the saturated same-route obstruction organized by mathematical role.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedCoefficients

variable {ι X : Type*}
variable [Fintype ι]

theorem WeightedObservable.windowedColeHopfHeatSaturated_a_eq_one_add_abs_of_selfCompatibility_of_nonzero_vorticity
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
      selfCompatibility (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    a = 1 +
      |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| := by
  let w :=
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y
  have hEq :
      a * (w / (1 + |w|)) = w := by
    simpa [selfCompatibility, WeightedObservable.windowedColeHopfHeatSaturatedCandidate, w]
      using hself t y
  have hden : (1 + |w|) ≠ 0 := by positivity
  have hMul : a * w = w * (1 + |w|) := by
    have hDiv : (a * w) / (1 + |w|) = w := by
      simpa [mul_div_assoc] using hEq
    exact (div_eq_iff hden).mp hDiv
  have hZero : (a - (1 + |w|)) * w = 0 := by
    calc
      (a - (1 + |w|)) * w = a * w - w * (1 + |w|) := by ring
      _ = 0 := by linarith
  rcases mul_eq_zero.mp hZero with hfac | hw
  · linarith
  · exact False.elim (hnz hw)

theorem WeightedObservable.windowedColeHopfHeatSaturated_gt_one_of_selfCompatibility_of_nonzero_vorticity
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
      selfCompatibility (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    1 < a := by
  have hEq :=
    L.windowedColeHopfHeatSaturated_a_eq_one_add_abs_of_selfCompatibility_of_nonzero_vorticity
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself hnz
  have habs : 0 <
      |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| := by
    exact abs_pos.mpr hnz
  linarith


end WindowedColeHopfHeatSaturatedCoefficients

end NavierStokes
end FluidDynamics
end Mettapedia
