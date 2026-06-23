import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatGeneralShiftKernelBridgeEquation

/-!
# General Shift-Kernel Coefficient Laws

Witness-pattern consequences of the bridge equation: coefficient sums at
selected anchors are forced to be zero or one.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatGeneralShiftKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X] [DecidableEq X]

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_liveCoeffSumAt_zero_eq_one_of_topDownBridge_of_zero_seed_other_live_zero_witness
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
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hseed :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y + K.seedShift i) = 0)
    (hlive :
      ∀ i : κ, K.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) = 0)
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    SeedLiveShiftKernel.liveCoeffSumAt K 0 = 1 := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  let w := T.vorticity t y
  have hEq :=
    L.windowedColeHopfHeatShiftKernel_sum_eq_of_topDownBridge
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand t y
  have hEq' :
      (∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
          K.liveCoeff i * T.vorticity t (y + K.liveShift i))) =
        SeedLiveShiftKernel.liveCoeffSumAt K 0 * w := by
    rw [SeedLiveShiftKernel.liveCoeffSumAt]
    calc
      (∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
          K.liveCoeff i * T.vorticity t (y + K.liveShift i)))
          = ∑ i, ((if K.liveShift i = 0 then K.liveCoeff i else 0) * w) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hseed_i : T.vorticity 1 (y + K.seedShift i) = 0 := hseed i
            by_cases h0 : K.liveShift i = 0
            · simp [hseed_i, h0, w]
            · have hlive_i : T.vorticity t (y + K.liveShift i) = 0 := hlive i h0
              simp [hseed_i, h0, hlive_i]
      _ = (∑ i, if K.liveShift i = 0 then K.liveCoeff i else 0) * w := by
            simpa using
              (Finset.sum_mul
                (s := Finset.univ)
                (f := fun i : κ => if K.liveShift i = 0 then K.liveCoeff i else 0)
                (a := w)).symm
      _ = SeedLiveShiftKernel.liveCoeffSumAt K 0 * w := by
            rw [SeedLiveShiftKernel.liveCoeffSumAt]
  have hMul : (SeedLiveShiftKernel.liveCoeffSumAt K 0 - 1) * w = 0 := by
    rw [hEq'] at hEq
    nlinarith
  rcases mul_eq_zero.mp hMul with hsum | hw
  · linarith
  · exact False.elim (hnz hw)

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_zeroAnchorCoeffSum_eq_one_of_topDownBridge_of_zero_other_anchors_nonzero_initial
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
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {y : X}
    (hseedOther :
      ∀ i : κ, K.seedShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y + K.seedShift i) = 0)
    (hliveOther :
      ∀ i : κ, K.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y + K.liveShift i) = 0)
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0 = 1 := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  let w := T.vorticity 1 y
  have hEq :=
    L.windowedColeHopfHeatShiftKernel_sum_eq_of_topDownBridge
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand 1 y
  have hEq' :
      (∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
          K.liveCoeff i * T.vorticity 1 (y + K.liveShift i))) =
        (SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0) * w := by
    rw [SeedLiveShiftKernel.seedCoeffSumAt, SeedLiveShiftKernel.liveCoeffSumAt]
    calc
      (∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
          K.liveCoeff i * T.vorticity 1 (y + K.liveShift i)))
          = ∑ i, (((if K.seedShift i = 0 then K.seedCoeff i else 0) +
              (if K.liveShift i = 0 then K.liveCoeff i else 0)) * w) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hseed0 : K.seedShift i = 0
              · by_cases hlive0 : K.liveShift i = 0
                · simp [hseed0, hlive0, w, add_mul]
                · have hlive_i : T.vorticity 1 (y + K.liveShift i) = 0 := hliveOther i hlive0
                  simp [hseed0, hlive0, hlive_i, w]
              · have hseed_i : T.vorticity 1 (y + K.seedShift i) = 0 := hseedOther i hseed0
                by_cases hlive0 : K.liveShift i = 0
                · simp [hseed0, hlive0, hseed_i, w]
                · have hlive_i : T.vorticity 1 (y + K.liveShift i) = 0 := hliveOther i hlive0
                  simp [hseed0, hlive0, hseed_i, hlive_i]
      _ = (∑ i,
            ((if K.seedShift i = 0 then K.seedCoeff i else 0) +
              (if K.liveShift i = 0 then K.liveCoeff i else 0))) * w := by
            simpa using
              (Finset.sum_mul
                (s := Finset.univ)
                (f := fun i : κ =>
                  (if K.seedShift i = 0 then K.seedCoeff i else 0) +
                    (if K.liveShift i = 0 then K.liveCoeff i else 0))
                (a := w)).symm
      _ = ((∑ i, if K.seedShift i = 0 then K.seedCoeff i else 0) +
            (∑ i, if K.liveShift i = 0 then K.liveCoeff i else 0)) * w := by
            rw [Finset.sum_add_distrib]
      _ = (SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0) * w := by
            rw [SeedLiveShiftKernel.seedCoeffSumAt, SeedLiveShiftKernel.liveCoeffSumAt]
  have hMul :
      ((SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0) - 1) * w = 0 := by
    rw [hEq'] at hEq
    nlinarith
  rcases mul_eq_zero.mp hMul with hsum | hw
  · linarith
  · exact False.elim (hnz hw)

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_seedCoeffSumAt_eq_zero_of_topDownBridge_of_zero_live_zero_other_seed_nonzero_seed
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (u : X)
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
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hzero :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0)
    (hlive :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) = 0)
    (hseedOther :
      ∀ i : κ, K.seedShift i ≠ u →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y + K.seedShift i) = 0)
    (hseedNz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + u) ≠ 0) :
    SeedLiveShiftKernel.seedCoeffSumAt K u = 0 := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  let w := T.vorticity 1 (y + u)
  have hEq :=
    L.windowedColeHopfHeatShiftKernel_sum_eq_of_topDownBridge
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand t y
  have hEq' :
      (∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
          K.liveCoeff i * T.vorticity t (y + K.liveShift i))) =
        SeedLiveShiftKernel.seedCoeffSumAt K u * w := by
    rw [SeedLiveShiftKernel.seedCoeffSumAt]
    calc
      (∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
          K.liveCoeff i * T.vorticity t (y + K.liveShift i)))
          = ∑ i, ((if K.seedShift i = u then K.seedCoeff i else 0) * w) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hlive_i : T.vorticity t (y + K.liveShift i) = 0 := hlive i
            by_cases hu : K.seedShift i = u
            · simp [hu, hlive_i, w]
            · have hseed_i : T.vorticity 1 (y + K.seedShift i) = 0 := hseedOther i hu
              simp [hu, hseed_i, hlive_i]
      _ = (∑ i, if K.seedShift i = u then K.seedCoeff i else 0) * w := by
            simpa using
              (Finset.sum_mul
                (s := Finset.univ)
                (f := fun i : κ => if K.seedShift i = u then K.seedCoeff i else 0)
                (a := w)).symm
      _ = SeedLiveShiftKernel.seedCoeffSumAt K u * w := by
            rw [SeedLiveShiftKernel.seedCoeffSumAt]
  have hMul : SeedLiveShiftKernel.seedCoeffSumAt K u * w = 0 := by
    rw [hEq'] at hEq
    simpa [hzero]
      using hEq
  rcases mul_eq_zero.mp hMul with hsum | hw
  · exact hsum
  · exact False.elim (hseedNz hw)

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_liveCoeffSumAt_eq_zero_of_topDownBridge_of_zero_live_zero_seed_zero_other_live_nonzero_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (u : X)
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
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hzero :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0)
    (hseed :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y + K.seedShift i) = 0)
    (hliveOther :
      ∀ i : κ, K.liveShift i ≠ u →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) = 0)
    (hliveNz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + u) ≠ 0) :
    SeedLiveShiftKernel.liveCoeffSumAt K u = 0 := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  let w := T.vorticity t (y + u)
  have hEq :=
    L.windowedColeHopfHeatShiftKernel_sum_eq_of_topDownBridge
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand t y
  have hEq' :
      (∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
          K.liveCoeff i * T.vorticity t (y + K.liveShift i))) =
        SeedLiveShiftKernel.liveCoeffSumAt K u * w := by
    rw [SeedLiveShiftKernel.liveCoeffSumAt]
    calc
      (∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
          K.liveCoeff i * T.vorticity t (y + K.liveShift i)))
          = ∑ i, ((if K.liveShift i = u then K.liveCoeff i else 0) * w) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hseed_i : T.vorticity 1 (y + K.seedShift i) = 0 := hseed i
            by_cases hu : K.liveShift i = u
            · simp [hu, hseed_i, w]
            · have hlive_i : T.vorticity t (y + K.liveShift i) = 0 := hliveOther i hu
              simp [hu, hseed_i, hlive_i]
      _ = (∑ i, if K.liveShift i = u then K.liveCoeff i else 0) * w := by
            simpa using
              (Finset.sum_mul
                (s := Finset.univ)
                (f := fun i : κ => if K.liveShift i = u then K.liveCoeff i else 0)
                (a := w)).symm
      _ = SeedLiveShiftKernel.liveCoeffSumAt K u * w := by
            rw [SeedLiveShiftKernel.liveCoeffSumAt]
  have hMul : SeedLiveShiftKernel.liveCoeffSumAt K u * w = 0 := by
    rw [hEq'] at hEq
    simpa [hzero]
      using hEq
  rcases mul_eq_zero.mp hMul with hsum | hw
  · exact hsum
  · exact False.elim (hliveNz hw)


end WindowedColeHopfHeatGeneralShiftKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
