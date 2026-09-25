import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierShellFeeding

/-!
# The cascade contraction: one contracting step of the unforced cascade gives
the official statement

Along a tame solution, the shell-feeding inequality bounds the vorticity
Wiener norm above `2^(Q+1)` by the relaxation of the data plus the feeding
functional `(12/ν) ∫ V_{≥Q}(u) V(u)`, the Reynolds feeding of the next shell
from the shell `2^Q`. The Wiener norm above `2^Q` is the shell `2^Q` plus the
Wiener norm above `2^(Q+1)`, and one shell is bounded by the energy of the
data, which every tame solution keeps below its initial value.

Hence if the feeding functional at some scale `2^Q` is dominated, uniformly
along the solutions of a horizon, by a constant plus a fraction `θ < 1` of the
time integral of the Wiener norm above `2^Q`, that integral is bounded by

```text
(H · shellConst Q · √E₀ + R_{Q+1}(ω₀) + A) / (1 - θ),
```

the vorticity supremum is integrable up to every horizon, and the official
periodic statement holds. The hypothesis is one inequality per cascade step:
the content of the whole tail above `2^Q` is paid by the shell `2^Q` itself,
which the energy controls. In particular a bound on the velocity Wiener norm
gives the statement, through the scale `2^Q ≥ 12 K / (π ν)` at which the
Reynolds number of the sweeping velocity drops below one half.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierCascadeContraction

open scoped BigOperators Topology
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLatticeDecayEnvelope PancakeHigherSobolevVelocityRate
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity PancakeCoefficientLimitEquation
open PancakeGalerkinKineticEnergy PancakeSobolevVelocityRate PancakeArbitraryDataBlocks
open PancakeInfiniteFourierTime PancakeInfinitePressureCoefficients PancakeIndexedFourierMoments
open FourierTimeRegularity FourierTameContinuation FourierDyadicBlockContinuation
open FourierRegularityEquivalence FourierGlobalSolution FourierSpatialCalculus
open FourierInitialData FourierOfficialTheorems OfficialPeriodicProblem
open FourierVorticitySupContinuation FourierRelaxation FourierVorticitySource FourierShellFeeding
open InfiniteConvectionEnergy LocalKineticEnergy LocalLowDiffusionBudget

section Shell

/-- The vorticity Wiener mass of one dyadic shell. -/
def shellMass (Q : ℕ) (u : FourierVelocity) : ℝ := ∑ k ∈ dyadicShellModes Q, curlMass u k

/-- The constant of the energy bound on one shell. -/
def shellConst (Q : ℕ) : ℝ := ∑ k ∈ dyadicShellModes Q, 2 * Real.pi * (1 + ‖frequencyVec k‖)

theorem shellConst_nonneg (Q : ℕ) : 0 ≤ shellConst Q :=
  Finset.sum_nonneg fun k _ ↦ by positivity

theorem shellMass_nonneg (Q : ℕ) (u : FourierVelocity) : 0 ≤ shellMass Q u :=
  Finset.sum_nonneg fun k _ ↦ curlMass_nonneg u k

/-- One shell is bounded by any common bound on the modal energies. -/
theorem shellMass_le (Q : ℕ) (u : FourierVelocity) {E : ℝ}
    (hE : ∀ k, coefficientEnergy (u k) ≤ E) : shellMass Q u ≤ shellConst Q * Real.sqrt E := by
  unfold shellMass shellConst curlMass
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  have hk : ‖coefficientVec (u k)‖ ≤ Real.sqrt E := by
    rw [← Real.sqrt_sq (norm_nonneg (coefficientVec (u k))), norm_coefficientVec_sq]
    exact Real.sqrt_le_sqrt (hE k)
  calc ‖coefficientVec (fourierCurl u k)‖ ≤ 2 * Real.pi * fourierMoment 1 u k :=
        norm_coefficientVec_fourierCurl_le u k
    _ = 2 * Real.pi * (1 + ‖frequencyVec k‖) * ‖coefficientVec (u k)‖ := by
        simp only [fourierMoment, pow_one]
        ring
    _ ≤ 2 * Real.pi * (1 + ‖frequencyVec k‖) * Real.sqrt E := by gcongr

/-- The Wiener norm above `2^Q` is the shell `2^Q` plus the Wiener norm above
`2^(Q+1)`. -/
theorem wienerHigh_eq_shellMass_add (Q : ℕ) (u : FourierVelocity)
    (hs : Summable (fun n ↦ ∑ k ∈ dyadicShellModes (Q + n), curlMass u k)) :
    wienerHigh Q u = shellMass Q u + wienerHigh (Q + 1) u := by
  unfold wienerHigh shellMass
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.add_zero]
  congr 1
  exact tsum_congr fun n ↦ by rw [show Q + (n + 1) = Q + 1 + n from by omega]

/-- The indicator sum above `2^Q` is at most the shell sum. -/
theorem tsum_high_le_wienerHigh (Q : ℕ) (u : FourierVelocity)
    (hs : Summable (fun n ↦ ∑ k ∈ dyadicShellModes (Q + n), curlMass u k)) :
    ∑' k, (if 4 ^ Q ≤ modeSquareNat k then curlMass u k else 0) ≤ wienerHigh Q u := by
  refine Real.tsum_le_of_sum_le (fun k ↦ ?_) fun s ↦ ?_
  · show (0 : ℝ) ≤ _
    split_ifs
    · exact curlMass_nonneg u k
    · exact le_rfl
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp (tendsto_boxModes Q) s
  have hsub : s.filter (fun k ↦ 4 ^ Q ≤ modeSquareNat k) ⊆ annulusModes Q N := by
    intro k hk
    obtain ⟨hks, hkQ⟩ := Finset.mem_filter.mp hk
    have hkb : k ∈ lowModes Q ∪ annulusModes Q N := hN N le_rfl hks
    rcases Finset.mem_union.mp hkb with hlow | hann
    · exact absurd ((mem_lowModes Q k).mp hlow) (not_lt.mpr hkQ)
    · exact hann
  calc ∑ k ∈ s, (if 4 ^ Q ≤ modeSquareNat k then curlMass u k else 0)
      = ∑ k ∈ s.filter (fun k ↦ 4 ^ Q ≤ modeSquareNat k), curlMass u k :=
        (Finset.sum_filter _ _).symm
    _ ≤ ∑ k ∈ annulusModes Q N, curlMass u k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ ↦ curlMass_nonneg u k
    _ = ∑ n ∈ Finset.range N, ∑ k ∈ dyadicShellModes (Q + n), curlMass u k := by
        unfold annulusModes
        exact Finset.sum_biUnion (pairwiseDisjoint_shells Q N)
    _ ≤ wienerHigh Q u :=
        hs.sum_le_tsum _ fun n _ ↦ Finset.sum_nonneg fun k _ ↦ curlMass_nonneg u k

end Shell

section Solutions

variable {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity}

/-- Along a tame solution, the vorticity supremum is bounded by the energy of
the modes below `2^Q` plus the Wiener norm above `2^Q`. -/
theorem integral_vorticitySup_le_wienerHigh (hm : 7 ≤ m) (hnu : 0 < nu) {T : ℝ}
    (c : TameSolutionOn nu m u₀ T) (Q : ℕ) {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) T) :
    ∫ t in (0 : ℝ)..τ, vorticitySup (c.coefficients t) ≤
      τ * (lowConst Q * Real.sqrt (kineticEnergy u₀)) +
        ∫ t in (0 : ℝ)..τ, wienerHigh Q (c.coefficients t) := by
  obtain ⟨S, hτS, hST, B, s, hs, g, hg, hSum, hu3⟩ := exists_local_envelope m hm c τ hτ
  have he : Envelope s g := ⟨hg, hSum, hu3⟩
  have hu2 : ∀ t ∈ Icc (0 : ℝ) S, ∀ k, fourierMoment 2 (s.coefficients t) k ≤ g k :=
    fun t ht k ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) k).trans (hu3 t ht k)
  have hu1 : ∀ t ∈ Icc (0 : ℝ) S, ∀ k, fourierMoment 1 (s.coefficients t) k ≤ g k :=
    fun t ht k ↦ (fourierMoment_mono _ (by omega : 1 ≤ 3) k).trans (hu3 t ht k)
  have hsub : Icc (0 : ℝ) τ ⊆ Icc 0 S := Icc_subset_Icc le_rfl hτS.le
  have hpt : ∀ t ∈ Icc (0 : ℝ) τ, vorticitySup (s.coefficients t) ≤
      lowConst Q * Real.sqrt (kineticEnergy u₀) + wienerHigh Q (s.coefficients t) := by
    intro t ht
    have htS := hsub ht
    have hm1 : Summable (fourierMoment 1 (s.coefficients t)) :=
      hSum.of_nonneg_of_le (fourierMoment_nonneg 1 _) (hu1 t htS)
    have hnorm : Summable (fun q ↦ ‖s.coefficients t q‖) :=
      hm1.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun q ↦
        (PancakeIndexedFourierMoments.norm_coefficient_sup_le_euclidean _).trans
          (le_mul_of_one_le_left (norm_nonneg _) (by
            simp only [pow_one]
            linarith [norm_nonneg (frequencyVec q)]))
    have hkin := LocalKineticEnergy.energy_le_initial s hnu.le g hg hSum hu2 t htS
    have hE : ∀ k, coefficientEnergy (s.coefficients t k) ≤ kineticEnergy u₀ := fun k ↦
      (coefficientEnergy_le_kineticEnergy _ hnorm k).trans hkin
    refine ciSup_le fun x ↦ ?_
    calc ‖fullVorticity (s.coefficients t) x‖
        ≤ ‖lowVorticity Q (s.coefficients t) x‖ + highBlockSum Q (s.coefficients t) :=
          norm_fullVorticity_le_low_add_high Q _ hm1 x
      _ ≤ lowConst Q * Real.sqrt (kineticEnergy u₀) + wienerHigh Q (s.coefficients t) :=
          add_le_add (norm_lowVorticity_le Q _ hE x) (highBlockSum_le_wienerHigh Q _ hm1)
  have hVc := (continuousOn_vorticitySup s g hSum hu2).mono hsub
  have hWc := (continuousOn_wienerHigh he Q).mono hsub
  have hmono := intervalIntegral.integral_mono_on hτ.1
    (hVc.intervalIntegrable_of_Icc (μ := volume) hτ.1)
    ((continuousOn_const.add hWc).intervalIntegrable_of_Icc (μ := volume) hτ.1) hpt
  simp only [Pi.add_apply] at hmono
  rw [intervalIntegral.integral_add intervalIntegrable_const
      (hWc.intervalIntegrable_of_Icc (μ := volume) hτ.1),
    intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  rw [← hs]
  exact hmono

/-- **The shell split along a tame solution.** The Wiener norm above `2^Q`
is at most the energy bound of the shell `2^Q` plus the Wiener norm above
`2^(Q+1)`. -/
theorem integral_wienerHigh_split (hm : 7 ≤ m) (hnu : 0 < nu) {T : ℝ}
    (c : TameSolutionOn nu m u₀ T) (Q : ℕ) {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) T) :
    ∫ t in (0 : ℝ)..τ, wienerHigh Q (c.coefficients t) ≤
      τ * (shellConst Q * Real.sqrt (kineticEnergy u₀)) +
        ∫ t in (0 : ℝ)..τ, wienerHigh (Q + 1) (c.coefficients t) := by
  obtain ⟨S, hτS, hST, B, s, hs, g, hg, hSum, hu3⟩ := exists_local_envelope m hm c τ hτ
  have he : Envelope s g := ⟨hg, hSum, hu3⟩
  have hu2 : ∀ t ∈ Icc (0 : ℝ) S, ∀ k, fourierMoment 2 (s.coefficients t) k ≤ g k :=
    fun t ht k ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) k).trans (hu3 t ht k)
  have hu1 : ∀ t ∈ Icc (0 : ℝ) S, ∀ k, fourierMoment 1 (s.coefficients t) k ≤ g k :=
    fun t ht k ↦ (fourierMoment_mono _ (by omega : 1 ≤ 3) k).trans (hu3 t ht k)
  have hsub : Icc (0 : ℝ) τ ⊆ Icc 0 S := Icc_subset_Icc le_rfl hτS.le
  have hpt : ∀ t ∈ Icc (0 : ℝ) τ, wienerHigh Q (s.coefficients t) ≤
      shellConst Q * Real.sqrt (kineticEnergy u₀) + wienerHigh (Q + 1) (s.coefficients t) := by
    intro t ht
    have htS := hsub ht
    have hm1 : Summable (fourierMoment 1 (s.coefficients t)) :=
      hSum.of_nonneg_of_le (fourierMoment_nonneg 1 _) (hu1 t htS)
    have hnorm : Summable (fun q ↦ ‖s.coefficients t q‖) :=
      hm1.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun q ↦
        (PancakeIndexedFourierMoments.norm_coefficient_sup_le_euclidean _).trans
          (le_mul_of_one_le_left (norm_nonneg _) (by
            simp only [pow_one]
            linarith [norm_nonneg (frequencyVec q)]))
    have hkin := LocalKineticEnergy.energy_le_initial s hnu.le g hg hSum hu2 t htS
    have hE : ∀ k, coefficientEnergy (s.coefficients t k) ≤ kineticEnergy u₀ := fun k ↦
      (coefficientEnergy_le_kineticEnergy _ hnorm k).trans hkin
    rw [wienerHigh_eq_shellMass_add Q _ (summable_shellWiener he Q htS)]
    exact add_le_add (shellMass_le Q _ hE) le_rfl
  have hWc := (continuousOn_wienerHigh he Q).mono hsub
  have hWc' := (continuousOn_wienerHigh he (Q + 1)).mono hsub
  have hmono := intervalIntegral.integral_mono_on hτ.1
    (hWc.intervalIntegrable_of_Icc (μ := volume) hτ.1)
    ((continuousOn_const.add hWc').intervalIntegrable_of_Icc (μ := volume) hτ.1) hpt
  simp only [Pi.add_apply] at hmono
  rw [intervalIntegral.integral_add intervalIntegrable_const
      (hWc'.intervalIntegrable_of_Icc (μ := volume) hτ.1),
    intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  rw [← hs]
  exact hmono

/-- The feeding functional of the shells above `2^(Q+1)` from the shell
`2^Q` on `[0, τ]`: `(12/ν) ∫₀^τ V_{≥Q}(u) V(u)`. -/
def feeding (nu : ℝ) (Q : ℕ) (c : ℝ → FourierVelocity) (τ : ℝ) : ℝ :=
  12 / nu * ∫ t in (0 : ℝ)..τ, velocityWienerAbove Q (c t) * velocityWiener (c t)

/-- **The cascade contraction gives the official statement.** If for every
viscosity, admissible datum and horizon there are a scale `2^Q`, a constant
`A` and a fraction `θ < 1` such that along every tame solution the feeding of
the shells above `2^(Q+1)` from the shell `2^Q` is at most `A + θ` times the
time integral of the vorticity Wiener norm above `2^Q`, then the official
periodic existence-and-smoothness statement holds. -/
theorem periodicStatementB_of_cascadeContraction (m : ℕ) (hm : 7 ≤ m)
    (h : ∀ nu : ℝ, 0 < nu → ∀ u₀ : FourierVelocity, Admissible m u₀ → ∀ H, 0 < H →
      ∃ Q : ℕ, ∃ A θ : ℝ, θ < 1 ∧
        ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T, ∀ τ ∈ Ico (0 : ℝ) T,
          feeding nu Q c.coefficients τ ≤
            A + θ * ∫ t in (0 : ℝ)..τ, wienerHigh Q (c.coefficients t)) :
    PeriodicStatementB := by
  intro nu hnu u₀ hu₀
  have hadm := admissible_fluctuation hu₀ m
  obtain ⟨hr, hd, hz, E₀, hE₀⟩ := id hadm
  have hE₀0 : 0 ≤ E₀ := le_trans (by simp [velocityEnergy_eq]) (hE₀ ∅)
  have hglobal : Nonempty (GlobalSolution nu m (fluctuation u₀)) := by
    refine nonempty_globalSolution_of_vorticitySup hm hnu hr hd hz hE₀0 hE₀ fun H hH ↦ ?_
    obtain ⟨Q, A, θ, hθ, hall⟩ := h nu hnu (fluctuation u₀) hadm H hH
    have hKl0 : 0 ≤ lowConst Q * Real.sqrt (kineticEnergy (fluctuation u₀)) :=
      mul_nonneg (lowConst_nonneg Q) (Real.sqrt_nonneg _)
    have hKs0 : 0 ≤ shellConst Q * Real.sqrt (kineticEnergy (fluctuation u₀)) :=
      mul_nonneg (shellConst_nonneg Q) (Real.sqrt_nonneg _)
    refine ⟨H * (lowConst Q * Real.sqrt (kineticEnergy (fluctuation u₀))) +
      (H * (shellConst Q * Real.sqrt (kineticEnergy (fluctuation u₀))) +
        relaxConst nu (Q + 1) (fluctuation u₀) + A) / (1 - θ), fun T hT c τ hτ ↦ ?_⟩
    have hτH : τ ≤ H := hτ.2.le.trans hT
    have h1 := integral_vorticitySup_le_wienerHigh hm hnu c Q hτ
    have h2 := integral_wienerHigh_split hm hnu c Q hτ
    have h3 := integral_wienerHigh_succ_le m hm hnu c Q hτ
    have h4 := hall T hT c τ hτ
    have hlow := mul_le_mul_of_nonneg_right hτH hKl0
    have hsh := mul_le_mul_of_nonneg_right hτH hKs0
    have hI : ∫ t in (0 : ℝ)..τ, wienerHigh Q (c.coefficients t) ≤
        (H * (shellConst Q * Real.sqrt (kineticEnergy (fluctuation u₀))) +
          relaxConst nu (Q + 1) (fluctuation u₀) + A) / (1 - θ) := by
      rw [le_div_iff₀ (by linarith)]
      have e : (∫ t in (0 : ℝ)..τ, wienerHigh Q (c.coefficients t)) * (1 - θ) =
          (∫ t in (0 : ℝ)..τ, wienerHigh Q (c.coefficients t)) -
            θ * ∫ t in (0 : ℝ)..τ, wienerHigh Q (c.coefficients t) := by ring
      rw [e]
      unfold feeding at h4
      linarith
    linarith
  obtain ⟨g⟩ := hglobal
  exact exists_official_of_globalSolution hnu hu₀ hm g

/-- Under a bound `K` on the velocity Wiener norm, the feeding at any scale
`2^Q ≥ 12 K / (π ν)` is at most half the Wiener norm above `2^Q`. -/
theorem feeding_le_half (hm : 7 ≤ m) (hnu : 0 < nu) {T : ℝ} (c : TameSolutionOn nu m u₀ T)
    (Q : ℕ) {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) T) {K : ℝ}
    (hK : ∀ t ∈ Ico (0 : ℝ) T, velocityWiener (c.coefficients t) ≤ K)
    (hQ : 12 * K / (Real.pi * nu) ≤ 2 ^ Q) :
    feeding nu Q c.coefficients τ ≤
      0 + 1 / 2 * ∫ t in (0 : ℝ)..τ, wienerHigh Q (c.coefficients t) := by
  obtain ⟨S, hτS, hST, B, s, hs, g, hg, hSum, hu3⟩ := exists_local_envelope m hm c τ hτ
  have he : Envelope s g := ⟨hg, hSum, hu3⟩
  have hsub : Icc (0 : ℝ) τ ⊆ Icc 0 S := Icc_subset_Icc le_rfl hτS.le
  have hcoef : 12 / nu * (1 / (2 * Real.pi * 2 ^ Q)) * K ≤ 1 / 2 := by
    have hpi := Real.pi_pos
    have h2Q : (0 : ℝ) < 2 ^ Q := by positivity
    have hnu' := hnu.ne'
    have hpi' := hpi.ne'
    have h2Q' := h2Q.ne'
    rw [div_le_iff₀ (mul_pos hpi hnu)] at hQ
    have e : 12 / nu * (1 / (2 * Real.pi * 2 ^ Q)) * K = 12 * K / (2 * Real.pi * nu * 2 ^ Q) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  have hpt : ∀ t ∈ Icc (0 : ℝ) τ,
      12 / nu * (velocityWienerAbove Q (s.coefficients t) * velocityWiener (s.coefficients t)) ≤
        1 / 2 * wienerHigh Q (s.coefficients t) := by
    intro t ht
    have htS := hsub ht
    have hme : MomentEnvelope (s.coefficients t) g := ⟨hg, hSum, hu3 t htS⟩
    have hV := velocityWienerAbove_le hme (s.zero t) (s.transverse t) Q
    have hW := tsum_high_le_wienerHigh Q (s.coefficients t) (summable_shellWiener he Q htS)
    have hKt : velocityWiener (s.coefficients t) ≤ K := by
      rw [hs]
      exact hK t ⟨ht.1, lt_of_le_of_lt ht.2 hτ.2⟩
    have hW0 := wienerHigh_nonneg Q (s.coefficients t)
    have hVa : velocityWienerAbove Q (s.coefficients t) ≤
        1 / (2 * Real.pi * 2 ^ Q) * wienerHigh Q (s.coefficients t) :=
      hV.trans (mul_le_mul_of_nonneg_left hW (by positivity))
    have hprod := mul_le_mul hVa hKt (velocityWiener_nonneg _) (mul_nonneg (by positivity) hW0)
    calc 12 / nu * (velocityWienerAbove Q (s.coefficients t) * velocityWiener (s.coefficients t))
        ≤ 12 / nu * (1 / (2 * Real.pi * 2 ^ Q) * wienerHigh Q (s.coefficients t) * K) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 12 / nu * (1 / (2 * Real.pi * 2 ^ Q)) * K * wienerHigh Q (s.coefficients t) := by ring
      _ ≤ 1 / 2 * wienerHigh Q (s.coefficients t) := mul_le_mul_of_nonneg_right hcoef hW0
  have hc1 : ContinuousOn (fun t ↦ velocityWienerAbove Q (s.coefficients t) *
      velocityWiener (s.coefficients t)) (Icc 0 τ) :=
    ((continuousOn_velocityWienerAbove he Q).mono hsub).mul
      ((continuousOn_velocityWiener he).mono hsub)
  have hc2 : ContinuousOn (fun t ↦ wienerHigh Q (s.coefficients t)) (Icc 0 τ) :=
    (continuousOn_wienerHigh he Q).mono hsub
  have hmono : ∫ t in (0 : ℝ)..τ, 12 / nu * (velocityWienerAbove Q (s.coefficients t) *
      velocityWiener (s.coefficients t)) ≤ ∫ t in (0 : ℝ)..τ, 1 / 2 * wienerHigh Q (s.coefficients t) :=
    intervalIntegral.integral_mono_on hτ.1
      ((continuousOn_const.mul hc1).intervalIntegrable_of_Icc (μ := volume) hτ.1)
      ((continuousOn_const.mul hc2).intervalIntegrable_of_Icc (μ := volume) hτ.1) hpt
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  unfold feeding
  rw [← hs, zero_add]
  exact hmono

/-- **A velocity Wiener bound gives the official statement.** If on every
horizon the velocity Wiener norm of every tame solution stays below a constant
`K`, the cascade contracts at the scale `2^Q ≥ 12 K / (π ν)`: the Reynolds
number of the sweeping velocity at that scale is below one half. -/
theorem periodicStatementB_of_velocityWienerBound (m : ℕ) (hm : 7 ≤ m)
    (h : ∀ nu : ℝ, 0 < nu → ∀ u₀ : FourierVelocity, Admissible m u₀ → ∀ H, 0 < H →
      ∃ K, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T, ∀ t ∈ Ico (0 : ℝ) T,
        velocityWiener (c.coefficients t) ≤ K) :
    PeriodicStatementB := by
  refine periodicStatementB_of_cascadeContraction m hm fun nu hnu u₀ hadm H hH ↦ ?_
  obtain ⟨K, hK⟩ := h nu hnu u₀ hadm H hH
  obtain ⟨Q, hQ⟩ := pow_unbounded_of_one_lt (12 * K / (Real.pi * nu)) (by norm_num : (1 : ℝ) < 2)
  exact ⟨Q, 0, 1 / 2, by norm_num, fun T hT c τ hτ ↦
    feeding_le_half hm hnu c Q hτ (hK T hT c) hQ.le⟩

end Solutions

end Mettapedia.FluidDynamics.NavierStokes.FourierCascadeContraction
