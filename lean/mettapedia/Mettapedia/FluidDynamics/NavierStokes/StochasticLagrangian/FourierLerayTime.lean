import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierOpenness

/-!
# Leray's time: surviving an explicit interval means surviving forever

The energy identity pays the time integral of the enstrophy by the initial kinetic
energy, `2ν ∫₀ᵗ |ω|² ≤ |u₀|²`. On an interval of length `T_L`, the minimum of the
enstrophy is therefore at most `|u₀|² / (2ν T_L)`. With the Leray time

```text
T_L = 8 |u₀|² / (2ν π² δ₁²) + 1,     δ₁ = smallRadiusOne ν,
```

every tame solution that lives past `T_L` reaches, before `T_L`, an order-one
energy below `δ₁² / 8` (`exists_time_small_one_of_tame`), and from there the
order-one small-data bootstrap keeps it small forever. So a solution that
survives past `T_L` survives for all time (`nonempty_globalSolution_of_lerayTime`):
any singular time is at most `T_L`, a bound set by the kinetic energy and the
viscosity alone. The periodic problem is equivalent to existence on the single
explicit interval `[0, T_L]` for every admissible datum
(`periodicRegularity_iff_lerayTime`), and that gives the official periodic
statement (`periodicStatementB_of_lerayTime`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierLerayTime

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

/-- **Leray's time**, set by the kinetic energy and the viscosity. -/
def lerayTime (nu : ℝ) (u₀ : FourierVelocity) : ℝ :=
  8 * (InfiniteConvectionEnergy.kineticEnergy u₀ / (2 * nu)) /
    (Real.pi ^ 2 * smallRadiusOne nu ^ 2) + 1

theorem one_le_lerayTime (hnu : 0 < nu) (u₀ : FourierVelocity) : 1 ≤ lerayTime nu u₀ := by
  unfold lerayTime
  have := LocalKineticEnergy.kineticEnergy_nonneg u₀
  have := smallRadiusOne_pos hnu
  have : 0 ≤ 8 * (InfiniteConvectionEnergy.kineticEnergy u₀ / (2 * nu)) /
      (Real.pi ^ 2 * smallRadiusOne nu ^ 2) := by positivity
  linarith

/-- **Before Leray's time the order-one energy dips below the small-data radius.** -/
theorem exists_time_small_one_of_tame (hm : 7 ≤ m) (hnu : 0 < nu) {T : ℝ}
    (c : TameSolutionOn nu m u₀ T) (hT : lerayTime nu u₀ < T) :
    ∃ t, 0 ≤ t ∧ t ≤ lerayTime nu u₀ ∧
      ∀ F, velocityEnergy 1 F (c.coefficients t) ≤ smallRadiusOne nu ^ 2 / 8 := by
  set δ := smallRadiusOne nu with hδdef
  have hδ : 0 < δ := smallRadiusOne_pos hnu
  set A := InfiniteConvectionEnergy.kineticEnergy u₀ / (2 * nu) with hA
  have hA0 : 0 ≤ A := by
    have := LocalKineticEnergy.kineticEnergy_nonneg u₀
    positivity
  set L := lerayTime nu u₀ with hLdef
  have hL1 : 1 ≤ L := one_le_lerayTime hnu u₀
  have hL0 : 0 < L := by linarith
  set S := (L + T) / 2 with hSdef
  have hLS : L < S := by linarith
  have hST : S < T := by linarith
  obtain ⟨B, s, hs, e, he, hSum, hu3⟩ := local_envelope_at hm c hST
  have hS0 : 0 ≤ S := by linarith
  have hu2 : ∀ τ ∈ Icc (0 : ℝ) S, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ e q := fun τ hτ q ↦
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu3 τ hτ q)
  have hZc : ContinuousOn (fun τ ↦ meanEnstrophy (s.coefficients τ)) (Icc 0 S) :=
    continuousOn_meanEnstrophy s e hSum hu3
  have hKc := LocalKineticEnergy.continuousOn_enstrophy s e he hSum hu2
  have hsub : Icc (0 : ℝ) L ⊆ Icc 0 S := Icc_subset_Icc le_rfl hLS.le
  have hint := LocalKineticEnergy.enstrophy_integral_le_initial s e he hSum hu2 L ⟨hL0.le, hLS.le⟩
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL0.le) (hZc.mono hsub)
  have hmono1 : (∫ τ in (0 : ℝ)..L, meanEnstrophy (s.coefficients t)) ≤
      ∫ τ in (0 : ℝ)..L, meanEnstrophy (s.coefficients τ) :=
    intervalIntegral.integral_mono_on hL0.le intervalIntegrable_const
      ((hZc.mono hsub).intervalIntegrable_of_Icc hL0.le) fun τ hτ ↦ hmin hτ
  have hle : (∫ τ in (0 : ℝ)..L, meanEnstrophy (s.coefficients τ)) ≤
      ∫ τ in (0 : ℝ)..L, InfiniteConvectionEnergy.kineticEnergy (fourierCurl (s.coefficients τ)) := by
    refine intervalIntegral.integral_mono_on hL0.le ((hZc.mono hsub).intervalIntegrable_of_Icc hL0.le)
      ((hKc.mono hsub).intervalIntegrable_of_Icc hL0.le) fun τ hτ ↦ ?_
    have hu1 : Summable (fourierMoment 1 (s.coefficients τ)) :=
      hSum.of_nonneg_of_le (fourierMoment_nonneg 1 _)
        (fun k ↦ (fourierMoment_mono _ (by omega : 1 ≤ 3) k).trans (hu3 τ (hsub hτ) k))
    exact integral_norm_fullVorticity_sq_le _ hu1
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono1
  have hZt : meanEnstrophy (s.coefficients t) * L ≤ A := by
    rw [hA, le_div_iff₀ (by positivity)]
    nlinarith
  have hAL : A ≤ Real.pi ^ 2 * δ ^ 2 / 8 * L := by
    have hq : A ≤ Real.pi ^ 2 * δ ^ 2 / 8 * (8 * A / (Real.pi ^ 2 * δ ^ 2)) := by
      apply le_of_eq
      field_simp
    have hL' : 8 * A / (Real.pi ^ 2 * δ ^ 2) ≤ L := by
      rw [hLdef]
      unfold lerayTime
      rw [← hA, ← hδdef]
      linarith
    exact hq.trans (mul_le_mul_of_nonneg_left hL' (by positivity))
  have hZt' : meanEnstrophy (s.coefficients t) ≤ Real.pi ^ 2 * δ ^ 2 / 8 :=
    le_of_mul_le_mul_right (hZt.trans hAL) hL0
  refine ⟨t, ht.1, ht.2, fun F ↦ ?_⟩
  have htT : t < T := by linarith [ht.2]
  obtain ⟨B', hB'⟩ := c.order_local t htT
  have hB5 : ∀ G : Finset Wavevector, velocityEnergy 5 G (c.coefficients t) ≤ B' := fun G ↦
    (velocityEnergy_le_of_order_le (by omega) _ G).trans (hB' t ⟨ht.1, le_rfl⟩ G)
  have h1 := velocityEnergy_one_le _ (summable_fourierMoment_one _ hB5) (c.reality t)
    (c.transverse t) (c.zero t) F
  have h2 : meanEnstrophy (c.coefficients t) ≤ Real.pi ^ 2 * δ ^ 2 / 8 := by
    rw [← hs]
    exact hZt'
  calc velocityEnergy 1 F (c.coefficients t)
      ≤ (∫ x : UnitAddTorus (Fin 3), ‖fullVorticity (c.coefficients t) x‖ ^ 2) / Real.pi ^ 2 := h1
    _ ≤ Real.pi ^ 2 * δ ^ 2 / 8 / Real.pi ^ 2 := div_le_div_of_nonneg_right h2 (by positivity)
    _ = δ ^ 2 / 8 := by field_simp

/-- **A solution that survives Leray's time survives forever.** If a tame solution
of order at least seven exists beyond `T_L`, the data have a unique global
solution. -/
theorem nonempty_globalSolution_of_lerayTime (hm : 7 ≤ m) (hnu : 0 < nu)
    (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q)) (hd : ∀ q, modeDot q (u₀ q) = 0)
    (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀) (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀)
    {T : ℝ} (c : TameSolutionOn nu m u₀ T) (hT : lerayTime nu u₀ < T) :
    Nonempty (GlobalSolution nu m u₀) := by
  set δ := smallRadiusOne nu with hδdef
  have hδ : 0 < δ := smallRadiusOne_pos hnu
  have hκ : smallRateConstOne * δ ≤ nu * (2 * Real.pi) ^ 2 :=
    (smallRateConstOne_mul_smallRadiusOne nu).le
  obtain ⟨t₀, ht₀0, ht₀L, hsmall⟩ := exists_time_small_one_of_tame hm hnu c hT
  have ht₀T : t₀ < T := lt_of_le_of_lt ht₀L hT
  -- a bound before `t₀`, by compactness
  have hec := continuousOn_fullEnergy (m := 1) (c.ofLe (by omega : 1 + 2 ≤ m)) (S := t₀) ht₀T
  obtain ⟨M, hM0, hM⟩ := exists_bound_on _ hec
  refine nonempty_globalSolution hm hnu ?_
  refine exists_tameSolutionOn_of_orderOne m (by omega) hnu u₀ hr hd hz hE₀0 hE₀ ?_
  intro H _
  refine ⟨max M (δ ^ 2 / 4), fun T' _ d τ hτ F ↦ ?_⟩
  rcases le_or_gt τ t₀ with hτt | hτt
  · have hτT : τ < T := lt_of_le_of_lt hτt ht₀T
    have he : d.coefficients τ = c.coefficients τ :=
      coefficients_eq_of_lt hm hnu d c hτ.1 hτ.2 hτT
    rw [he]
    obtain ⟨B, hB⟩ := (c.ofLe (by omega : 1 + 2 ≤ m)).order_local τ hτT
    have h := velocityEnergy_le_fullEnergy 1 _ (hB τ ⟨hτ.1, le_rfl⟩) F
    exact (h.trans (hM τ ⟨hτ.1, hτt⟩)).trans (le_max_left _ _)
  · have ht₀T' : t₀ < T' := hτt.trans hτ.2
    have hd0 : d.coefficients t₀ = c.coefficients t₀ :=
      coefficients_eq_of_lt hm hnu d c ht₀0 ht₀T' ht₀T
    let d' := (d.shift ht₀0).ofLe (by omega : 3 ≤ m)
    have hdata : ∀ F, velocityEnergy 1 F (d.coefficients t₀) ≤ δ ^ 2 / 8 := by
      intro F
      rw [hd0]
      exact hsmall F
    have hb := velocityEnergy_le_of_small_one hnu d' hδ hκ hdata (τ - t₀)
      ⟨by linarith, by linarith [hτ.2]⟩ F
    have e : d'.coefficients (τ - t₀) = d.coefficients τ := by
      show d.coefficients (τ - t₀ + t₀) = d.coefficients τ
      rw [sub_add_cancel]
    rw [e] at hb
    exact hb.trans (le_max_right _ _)

/-- **The periodic problem on one explicit interval.** For order `m ≥ 7`, global
regularity holds if and only if every admissible datum, for every viscosity, has
a tame solution beyond its Leray time. -/
theorem periodicRegularity_iff_lerayTime (hm : 7 ≤ m) :
    PeriodicRegularity m ↔ ∀ nu : ℝ, 0 < nu → ∀ u₀ : FourierVelocity, Admissible m u₀ →
      Nonempty (TameSolutionOn nu m u₀ (lerayTime nu u₀ + 1)) := by
  constructor
  · intro h nu hnu u₀ hu
    obtain ⟨g⟩ := h nu hnu u₀ hu
    exact ⟨g.toTame _⟩
  · intro h nu hnu u₀ hu
    obtain ⟨c⟩ := h nu hnu u₀ hu
    obtain ⟨hr, hd, hz, E₀, hE₀⟩ := hu
    have hE₀0 : 0 ≤ E₀ := le_trans (by simp [velocityEnergy_eq]) (hE₀ ∅)
    exact nonempty_globalSolution_of_lerayTime hm hnu hr hd hz hE₀0 hE₀ c (by linarith)

/-- **Existence up to Leray's time gives the official periodic statement.** -/
theorem periodicStatementB_of_lerayTime (hm : 7 ≤ m)
    (h : ∀ nu : ℝ, 0 < nu → ∀ u₀ : FourierVelocity, Admissible m u₀ →
      Nonempty (TameSolutionOn nu m u₀ (lerayTime nu u₀ + 1))) :
    OfficialPeriodicProblem.PeriodicStatementB :=
  FourierOfficialTheorems.periodicStatementB_of_periodicRegularity hm
    ((periodicRegularity_iff_lerayTime hm).mpr h)

end Mettapedia.FluidDynamics.NavierStokes.FourierLerayTime
