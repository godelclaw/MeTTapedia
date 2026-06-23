import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelObstructionCore

/-!
# Saturated obstruction for anchored translation shift kernels

Specialization of the core finite shift-kernel obstruction to the anchored
translation kernel package.
-/


set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedShiftKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X] [DecidableEq X]

theorem WeightedObservable.not_exists_windowedColeHopfHeatAnchoredTranslationShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsat : satCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hwitness :
      ∃ t₁ y₁ t₂ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y₁ = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y₁ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ (y₁ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y₂ = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y₂ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ (y₂ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂|) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X)
            (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector satCoeff c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  rcases hwitness with
    ⟨t₁, y₁, t₂, y₂, hseed₁_zero, hseed₁_shift, hlive₁_shift, hnz₁,
      hseed₂_zero, hseed₂_shift, hlive₂_shift, hnz₂, habs⟩
  refine
    L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_seed_nonzero_shift_witnesses
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
      satCoeff c ν hsat hc hν curlFrame curlBound curlBound_nonneg hcurl x ?_
  refine ⟨t₁, y₁, t₂, y₂, ?_, ?_, hnz₁, ?_, ?_, hnz₂, habs⟩
  · intro i
    fin_cases i <;> simp [anchoredTranslationShiftKernel, hseed₁_zero, hseed₁_shift]
  · intro i hi
    fin_cases i
    · exact False.elim (hi (by simp [anchoredTranslationShiftKernel]))
    · exact False.elim (hi (by simp [anchoredTranslationShiftKernel]))
    · simpa [anchoredTranslationShiftKernel] using hlive₁_shift
  · intro i
    fin_cases i <;> simp [anchoredTranslationShiftKernel, hseed₂_zero, hseed₂_shift]
  · intro i hi
    fin_cases i
    · exact False.elim (hi (by simp [anchoredTranslationShiftKernel]))
    · exact False.elim (hi (by simp [anchoredTranslationShiftKernel]))
    · simpa [anchoredTranslationShiftKernel] using hlive₂_shift
end WindowedColeHopfHeatSaturatedShiftKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
