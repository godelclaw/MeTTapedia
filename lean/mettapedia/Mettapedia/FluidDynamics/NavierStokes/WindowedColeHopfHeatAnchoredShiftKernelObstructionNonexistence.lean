import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatAnchoredShiftKernelObstructionBridge

/-!
# Anchored Shift-Kernel No-Bridge Corollaries

This layer packages coefficient incompatibilities as nonexistence corollaries
for anchored shift-kernel top-down bridges.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatShiftKernelObstruction

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

theorem WeightedObservable.not_exists_windowedColeHopfHeatAnchoredShiftTopDownBridge_of_ne_one_of_zero_shifted_initial_zero_shifted_live_nonzero_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (ha : a ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
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
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatAnchoredShiftInitialSlice
              (ι := ι) (X := X)
              selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatAnchoredShiftCandidate
            (ι := ι) (X := X)
            selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact ha <|
    L.windowedColeHopfHeatAnchoredShift_a_eq_one_of_topDownBridge_of_zero_shifted_initial_zero_shifted_live_nonzero_live
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness

theorem WeightedObservable.not_exists_windowedColeHopfHeatAnchoredShiftTopDownBridge_of_nonzero_b_of_zero_live_zero_shifted_live_nonzero_shifted_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hb : b ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
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
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatAnchoredShiftInitialSlice
              (ι := ι) (X := X)
              selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatAnchoredShiftCandidate
            (ι := ι) (X := X)
            selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hb <|
    L.windowedColeHopfHeatAnchoredShift_b_eq_zero_of_topDownBridge_of_zero_live_zero_shifted_live_nonzero_shifted_initial
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness

theorem WeightedObservable.not_exists_windowedColeHopfHeatAnchoredShiftTopDownBridge_of_nonzero_d_of_zero_live_zero_shifted_initial_nonzero_shifted_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hd : d ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
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
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatAnchoredShiftInitialSlice
              (ι := ι) (X := X)
              selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatAnchoredShiftCandidate
            (ι := ι) (X := X)
            selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hd <|
    L.windowedColeHopfHeatAnchoredShift_d_eq_zero_of_topDownBridge_of_zero_live_zero_shifted_initial_nonzero_shifted_live
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness


end WindowedColeHopfHeatShiftKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
