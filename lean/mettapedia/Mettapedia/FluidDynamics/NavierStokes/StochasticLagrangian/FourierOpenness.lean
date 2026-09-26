import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierStability
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierSmallDataOne

/-!
# Regular data form an open set

Every global solution has arbitrarily late times at which its order-one energy is
as small as desired: the energy identity pays the time integral of the
enstrophy, so on a long enough interval its minimum is small
(`exists_time_small_one_of_global`). From such a time the order-one small-data
theorem keeps the order-one energy small forever, so every global solution has a
bounded order-one energy (`exists_bound_velocityEnergy_one_of_global`).

With that bound, the stability argument for planar flows works around every
global solution: up to a late time `T₀` where the global solution's order-one
energy is small, a perturbation stays close by continuous dependence, and from
`T₀` the order-one small-data theorem takes over. Hence the data with global
solutions form an open set in the order-eleven energy
(`exists_nhds_globalSolution_of_global`), and in official form, smooth periodic
data near data of a global Fourier solution have smooth periodic solutions for all
time (`exists_official_nhds_of_globalSolution`).

The set of data whose solutions break down, if it is not empty, is therefore
closed and keeps a positive distance from every regular datum.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierOpenness

open scoped BigOperators Topology
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeCurlOutputTail PancakeLatticeDecayEnvelope
open PancakeHigherLocalVelocity PancakeGalerkinKineticEnergy PancakeLocalInfiniteVelocity
open PancakeHigherDerivativeMoments PancakeBlockReality
open FourierTameTriad FourierContinuation FourierTameContinuation FourierInfiniteTameRate
open FourierVorticitySupContinuation FourierGlobalSolution FourierRegularityEquivalence
open FourierUniqueness FourierStability FourierSmallData FourierSmallDataOne
open LocalEnstrophyDiffusion LocalLowDiffusionBudget FourierEighthMomentControl

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity}

section EventualSmallness

/-- **Late times of small order-one energy.** For every global solution, every
threshold and every time `T'`, some later time has order-one energy below the
threshold. -/
theorem exists_time_small_one_of_global (hm : 7 ≤ m) (hnu : 0 < nu)
    (g : GlobalSolution nu m u₀) {η : ℝ} (hη : 0 < η) {T' : ℝ} (hT' : 0 ≤ T') :
    ∃ t, T' ≤ t ∧ ∀ F, velocityEnergy 1 F (g.coefficients t) ≤ η := by
  set A := InfiniteConvectionEnergy.kineticEnergy u₀ / (2 * nu) with hA
  have hA0 : 0 ≤ A := by
    have := LocalKineticEnergy.kineticEnergy_nonneg u₀
    positivity
  set L := A / (η * Real.pi ^ 2) + 1 with hL
  have hL0 : 0 < L := by positivity
  set H := T' + L with hH
  obtain ⟨B, s, hs, e, he, hSum, hu3⟩ := GlobalSolution.local_envelope hm g H
  have hu2 : ∀ τ ∈ Icc (0 : ℝ) H, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ e q := fun τ hτ q ↦
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu3 τ hτ q)
  have hH0 : 0 ≤ H := by linarith
  have hZc : ContinuousOn (fun τ ↦ meanEnstrophy (s.coefficients τ)) (Icc 0 H) :=
    continuousOn_meanEnstrophy s e hSum hu3
  have hKc := LocalKineticEnergy.continuousOn_enstrophy s e he hSum hu2
  have hint := LocalKineticEnergy.enstrophy_integral_le_initial s e he hSum hu2 H ⟨hH0, le_rfl⟩
  -- the minimum of the enstrophy on `[T', T' + L]`
  have hsub : Icc T' H ⊆ Icc 0 H := Icc_subset_Icc hT' le_rfl
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by linarith))
    (hZc.mono hsub)
  have hZ0 : ∀ τ, 0 ≤ meanEnstrophy (s.coefficients τ) := fun τ ↦ integral_nonneg fun x ↦ by
    unfold LocalEnstrophyDiffusion.energy
    positivity
  have hmono1 : (∫ τ in T'..H, meanEnstrophy (s.coefficients t)) ≤
      ∫ τ in T'..H, meanEnstrophy (s.coefficients τ) :=
    intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      ((hZc.mono hsub).intervalIntegrable_of_Icc (by linarith)) fun τ hτ ↦ hmin hτ
  have hsplit : (∫ τ in T'..H, meanEnstrophy (s.coefficients τ)) ≤
      ∫ τ in (0 : ℝ)..H, meanEnstrophy (s.coefficients τ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hZc.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc hT')
      ((hZc.mono hsub).intervalIntegrable_of_Icc (by linarith))]
    have := intervalIntegral.integral_nonneg (μ := volume) hT' fun τ _ ↦ hZ0 τ
    linarith
  have hle : (∫ τ in (0 : ℝ)..H, meanEnstrophy (s.coefficients τ)) ≤
      ∫ τ in (0 : ℝ)..H, InfiniteConvectionEnergy.kineticEnergy (fourierCurl (s.coefficients τ)) := by
    refine intervalIntegral.integral_mono_on hH0 (hZc.intervalIntegrable_of_Icc hH0)
      (hKc.intervalIntegrable_of_Icc hH0) fun τ hτ ↦ ?_
    have hu1 : Summable (fourierMoment 1 (s.coefficients τ)) :=
      hSum.of_nonneg_of_le (fourierMoment_nonneg 1 _)
        (fun k ↦ (fourierMoment_mono _ (by omega : 1 ≤ 3) k).trans (hu3 τ hτ k))
    exact integral_norm_fullVorticity_sq_le _ hu1
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono1
  have hZt : meanEnstrophy (s.coefficients t) * L ≤ A := by
    have e1 : H - T' = L := by rw [hH]; ring
    rw [e1] at hmono1
    rw [hA, le_div_iff₀ (by positivity)]
    nlinarith
  have hZt' : meanEnstrophy (s.coefficients t) ≤ η * Real.pi ^ 2 := by
    have hAL : A ≤ η * Real.pi ^ 2 * L := by
      rw [hL, mul_add, mul_div_cancel₀ _ (by positivity)]
      have : 0 ≤ η * Real.pi ^ 2 * 1 := by positivity
      linarith
    have := le_trans hZt hAL
    exact le_of_mul_le_mul_right (by linarith) hL0
  refine ⟨t, ht.1, fun F ↦ ?_⟩
  obtain ⟨B', hB'⟩ := g.order_local t
  have hB5 : ∀ G : Finset Wavevector, velocityEnergy 5 G (g.coefficients t) ≤ B' := fun G ↦
    (velocityEnergy_le_of_order_le (by omega) _ G).trans (hB' t ⟨by linarith [ht.1], le_rfl⟩ G)
  have h1 := velocityEnergy_one_le _ (summable_fourierMoment_one _ hB5) (g.reality t)
    (g.transverse t) (g.zero t) F
  have h2 : meanEnstrophy (g.coefficients t) ≤ η * Real.pi ^ 2 := by rw [← hs]; exact hZt'
  calc velocityEnergy 1 F (g.coefficients t)
      ≤ (∫ x : UnitAddTorus (Fin 3), ‖fullVorticity (g.coefficients t) x‖ ^ 2) / Real.pi ^ 2 := h1
    _ ≤ η * Real.pi ^ 2 / Real.pi ^ 2 := div_le_div_of_nonneg_right h2 (by positivity)
    _ = η := by field_simp

/-- **Every global solution has a bounded order-one energy.** -/
theorem exists_bound_velocityEnergy_one_of_global (hm : 7 ≤ m) (hnu : 0 < nu)
    (g : GlobalSolution nu m u₀) :
    ∃ K, 0 ≤ K ∧ ∀ t, 0 ≤ t → ∀ F, velocityEnergy 1 F (g.coefficients t) ≤ K := by
  set δ := smallRadiusOne nu with hδdef
  have hδ : 0 < δ := smallRadiusOne_pos hnu
  obtain ⟨t₀, ht₀, hsmall⟩ := exists_time_small_one_of_global hm hnu g
    (η := δ ^ 2 / 8) (by positivity) le_rfl
  have hκ : smallRateConstOne * δ ≤ nu * (2 * Real.pi) ^ 2 :=
    (smallRateConstOne_mul_smallRadiusOne nu).le
  -- before `t₀`, compactness
  let c₀ : TameSolutionOn nu (1 + 2) u₀ (t₀ + 1) := (g.toTame (t₀ + 1)).ofLe (by omega)
  have hec := continuousOn_fullEnergy (m := 1) c₀ (S := t₀) (by linarith)
  obtain ⟨M, hM0, hM⟩ := exists_bound_on _ hec
  refine ⟨max M (δ ^ 2 / 4), le_trans hM0 (le_max_left _ _), fun t ht F ↦ ?_⟩
  rcases le_or_gt t t₀ with htt | htt
  · obtain ⟨B, hB⟩ := c₀.order_local t (by linarith)
    have h := velocityEnergy_le_fullEnergy 1 _ (hB t ⟨ht, le_rfl⟩) F
    exact (h.trans (hM t ⟨ht, htt⟩)).trans (le_max_left _ _)
  · -- after `t₀`, the order-one small-data bootstrap
    let c' := ((g.toTame (t + 1)).shift ht₀).ofLe (by omega : 3 ≤ m)
    have hdata : ∀ F, velocityEnergy 1 F (c'.coefficients 0) ≤ δ ^ 2 / 8 := by
      intro F
      have e : c'.coefficients 0 = g.coefficients t₀ := by
        show g.coefficients (0 + t₀) = g.coefficients t₀
        rw [zero_add]
      rw [e]
      exact hsmall F
    have hb := velocityEnergy_le_of_small_one hnu c' hδ hκ
      (by rw [show c'.coefficients 0 = (g.toTame (t + 1)).coefficients t₀ from by
            show g.coefficients (0 + t₀) = g.coefficients t₀; rw [zero_add]] at hdata
          exact hdata)
      (t - t₀) ⟨by linarith, by linarith⟩ F
    have e : c'.coefficients (t - t₀) = g.coefficients t := by
      show g.coefficients (t - t₀ + t₀) = g.coefficients t
      rw [sub_add_cancel]
    rw [e] at hb
    exact hb.trans (le_max_right _ _)

end EventualSmallness

section Openness

set_option maxHeartbeats 1000000 in
/-- **Regular data form an open set.** For every global solution of order eleven
there is `ε > 0` such that every admissible datum within `ε` of its datum in the
order-eleven energy has a unique global solution. -/
theorem exists_nhds_globalSolution_of_global (hnu : 0 < nu) {v₀ : FourierVelocity}
    (g : GlobalSolution nu 11 v₀) {E₁₁v : ℝ} (hEv : ∀ F, velocityEnergy 11 F v₀ ≤ E₁₁v) :
    ∃ ε > 0, ∀ u₀ : FourierVelocity, (∀ q, u₀ (-q) = coefficientConjugate (u₀ q)) →
      (∀ q, modeDot q (u₀ q) = 0) → u₀ 0 = 0 →
      (∀ F, velocityEnergy 11 F (FourierUniqueness.diff u₀ v₀) ≤ ε) →
      Nonempty (GlobalSolution nu 11 u₀) := by
  have hEv0 : 0 ≤ E₁₁v := le_trans (velocityEnergy_nonneg' 11 ∅ _) (hEv ∅)
  obtain ⟨Kv, hKv0, hvK⟩ := exists_bound_velocityEnergy_one_of_global (by norm_num) hnu g
  set δ := smallRadiusOne nu with hδdef
  have hδ : 0 < δ := smallRadiusOne_pos hnu
  have hκs : smallRateConstOne * δ ≤ nu * (2 * Real.pi) ^ 2 :=
    (smallRateConstOne_mul_smallRadiusOne nu).le
  obtain ⟨T₀, hT₀1, hT₀small⟩ := exists_time_small_one_of_global (by norm_num) hnu g
    (η := δ ^ 2 / 32) (by positivity) (T' := 1) (by norm_num)
  have hT₀0 : 0 < T₀ := by linarith
  set K := 2 * Kv + 1 with hKdef
  set Eu := 2 * E₁₁v + 1 with hEudef
  set M₂ := stabM nu 2 K Eu T₀ with hM₂
  set M₇ := stabM nu 7 K Eu T₀ with hM₇
  set κ := stabKappa nu M₇ with hκdef
  have hM₂0 : 0 ≤ M₂ := by
    have := tameRateConst_nonneg 2 hnu
    rw [hM₂]
    unfold stabM
    positivity
  set η₀ := min (1 / 4) (δ ^ 2 / 32) with hη₀def
  have hη₀0 : 0 < η₀ := lt_min (by norm_num) (by positivity)
  have hη₀ : η₀ ≤ 1 / 4 := min_le_left _ _
  have hη₀δ : η₀ ≤ δ ^ 2 / 32 := min_le_right _ _
  set E := Real.exp (κ * T₀) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  set ε := min η₀ (η₀ ^ 2 / (E * (4 * M₂) + 1)) with hεdef
  have hε0 : 0 < ε := lt_min hη₀0 (by positivity)
  have hεη : ε ≤ η₀ := min_le_left _ _
  have hεsmall : ε * Real.exp (stabKappa nu (stabM nu 7 (2 * Kv + 1) (2 * E₁₁v + 1) T₀) * T₀) *
      (4 * stabM nu 2 (2 * Kv + 1) (2 * E₁₁v + 1) T₀) ≤ η₀ ^ 2 := by
    change ε * E * (4 * M₂) ≤ η₀ ^ 2
    have h := min_le_right η₀ (η₀ ^ 2 / (E * (4 * M₂) + 1))
    rw [← hεdef, le_div_iff₀ (by positivity)] at h
    nlinarith [hε0.le, mul_nonneg hE0.le hM₂0]
  refine ⟨ε, hε0, fun u₀ hr hd hz hw ↦ ?_⟩
  have hEu0 : ∀ F, velocityEnergy 11 F u₀ ≤ 2 * E₁₁v + 2 * ε := fun F ↦ by
    have h1 := velocityEnergy_le_two_diff 11 F u₀ v₀
    have h2 := hEv F
    have h3 := hw F
    linarith
  refine nonempty_globalSolution (by norm_num) hnu ?_
  refine exists_tameSolutionOn_of_orderOne 11 (by norm_num) hnu u₀ hr hd hz
    (by positivity) hEu0 ?_
  intro H _
  refine ⟨max K (δ ^ 2 / 4), fun T _ c τ hτ F ↦ ?_⟩
  have hvK' : ∀ t, 0 ≤ t → t ≤ T₀ → ∀ F, velocityEnergy 1 F (g.coefficients t) ≤ Kv :=
    fun t ht _ F ↦ hvK t ht F
  have hboot := bootstrap hnu g c hKv0 hvK' hEv hη₀0 hη₀ hεη hεsmall hw
  rcases le_or_gt τ T₀ with hτT₀ | hτT₀
  · exact ((hboot τ hτ hτT₀).1 F).trans (le_max_left _ _)
  · have hT₀T : T₀ < T := hτT₀.trans hτ.2
    have hbT₀ := hboot T₀ ⟨hT₀0.le, hT₀T⟩ le_rfl
    have hdata : ∀ F, velocityEnergy 1 F (c.coefficients T₀) ≤ δ ^ 2 / 8 := by
      intro F
      have h := velocityEnergy_le_two_diff 1 F (c.coefficients T₀) (g.coefficients T₀)
      have h1 := hT₀small F
      have h2 := hbT₀.2 F
      linarith
    let c' := (c.shift hT₀0.le).ofLe (by norm_num : 3 ≤ 11)
    have hsm := velocityEnergy_le_of_small_one hnu c' hδ hκs hdata (τ - T₀)
      ⟨by linarith, by linarith [hτ.2]⟩ F
    have e : c'.coefficients (τ - T₀) = c.coefficients τ := by
      show c.coefficients (τ - T₀ + T₀) = c.coefficients τ
      rw [sub_add_cancel]
    rw [e] at hsm
    exact hsm.trans (le_max_right _ _)

end Openness

section Official

open FourierOfficialTheorems FourierInitialData OfficialPeriodicProblem

/-- **Regular periodic data form an open set, official form.** If the fluctuation
of a smooth, divergence-free, one-periodic initial velocity `v₀` has a global
Fourier solution of order eleven, then every smooth, divergence-free, one-periodic
initial velocity whose fluctuation lies within some `ε > 0` of that of `v₀` in
the order-eleven energy has a smooth periodic solution for all time. -/
theorem exists_official_nhds_of_globalSolution (hnu : 0 < nu)
    {v₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hv₀ : InitialVelocityConditionPeriodic v₀) (g : GlobalSolution nu 11 (fluctuation v₀)) :
    ∃ ε > 0, ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      InitialVelocityConditionPeriodic u₀ →
      (∀ F, velocityEnergy 11 F (FourierUniqueness.diff (fluctuation u₀) (fluctuation v₀)) ≤ ε) →
      ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ (fun _ _ ↦ 0) v p := by
  obtain ⟨-, -, -, E₀, hE₀⟩ := admissible_fluctuation hv₀ 11
  obtain ⟨ε, hε, h⟩ := exists_nhds_globalSolution_of_global hnu g hE₀
  refine ⟨ε, hε, fun u₀ hu₀ hw ↦ ?_⟩
  obtain ⟨hr', hd', hz', -⟩ := admissible_fluctuation hu₀ 11
  obtain ⟨g'⟩ := h (fluctuation u₀) hr' hd' hz' hw
  exact exists_official_of_globalSolution hnu hu₀ (by norm_num) g'

end Official

end Mettapedia.FluidDynamics.NavierStokes.FourierOpenness
