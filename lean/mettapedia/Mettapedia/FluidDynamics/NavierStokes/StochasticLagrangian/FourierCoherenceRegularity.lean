import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalCoherenceBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierVorticitySupContinuation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierGlobalSolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierOfficialTheorems
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteVelocityLipschitz

/-!
# Coherence of the vorticity direction where the vorticity is large

A field is *coherent above* `Ω` with constant `K` when any two points at which
the vorticity exceeds `Ω` satisfy

```text
|ω(x) × ω(y)| ≤ K |x - y| |ω(x)| |ω(y)|,
```

that is, the sine of the angle between the two vorticity directions is at most
`K` times their distance. This is the geometric condition of Constantin and
Fefferman: where the vorticity is intense, its direction varies in a Lipschitz
way.

The periodic problem is regular exactly when this coherence holds on every
finite horizon (`periodicRegularity_iff_thresholdCoherent`).

* Coherence gives regularity. The actual stretching source splits into an
  increment paid by the eighth-moment dissipation and an angular remainder.
  Where both vorticities exceed `Ω`, coherence makes the angular remainder a
  product of the eighth moment and the enstrophy. Where one of them is at most
  `Ω`, the cross product is at most `Ω` times the larger vorticity, and the
  kernel's first moment bounds that part by `Ω²` times the eighth moment. The
  enstrophy is integrable in time by the energy identity, so the eighth moment
  obeys a Grönwall bound with a finite exponent on every finite horizon, and
  continuation gives a global solution (`nonempty_globalSolution_of_thresholdCoherent`).
* Regularity gives coherence. Along a global solution the vorticity is
  Lipschitz on each finite horizon with a uniform constant `L`, and
  `ω(x) × ω(y) = ω(x) × (ω(y) - ω(x))`, so coherence holds above every
  `Ω > 0` with `K = L/Ω` (`thresholdCoherent_of_globalSolution`).

A threshold is needed. Coherence at all amplitudes fails at every
nondegenerate zero of the vorticity, where the direction takes every value
nearby, so it cannot hold for general data.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierCoherenceRegularity

open MeasureTheory Filter Set PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget VorticityRegularizedSource VorticityAngularPayment PancakeBlockReality
open Mettapedia.Analysis SignedCrossKernel EuclideanCrossProduct PancakeGalerkinKineticEnergy
open VorticityCoherenceBudget LocalCoherenceBudget
open scoped Topology
local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Hk" => PeriodicRieszOperator.kernel (d := 3)
local notation "C₁" => PeriodicRieszNearMoment.firstMomentBound 3
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

/-- **Coherence of the vorticity direction above the amplitude `Ω`.** -/
def ThresholdCoherent (u : FourierVelocity) (Ω K : ℝ) : Prop :=
  ∀ x y : T3, Ω < ‖fullVorticity u x‖ → Ω < ‖fullVorticity u y‖ →
    ‖cross (fullVorticity u x) (fullVorticity u y)‖ ≤
      K * ‖x - y‖ * ‖fullVorticity u x‖ * ‖fullVorticity u y‖

section Kernel

/-- **The angular cost under coherence above a threshold.** Coherent pairs pay
through the kernel's cubic bound; a pair with one vorticity at most `Ω` pays
`Ω²` times the kernel's first moment times the eighth powers. -/
theorem angularCost_le_threshold (r K C Ω : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (Hop : R3 →L[ℝ] R3) (a b : R3) (hH : r ^ 3 * ‖Hop‖ ≤ C)
    (hc : Ω < ‖a‖ → Ω < ‖b‖ → ‖cross a b‖ ≤ K * r * ‖a‖ * ‖b‖) :
    angularCost 3 r Hop a b ≤ K ^ 2 * C * (‖a‖ ^ 8 * ‖b‖ ^ 2 + ‖a‖ ^ 2 * ‖b‖ ^ 8) +
      Ω ^ 2 * (r * ‖Hop‖) * (‖a‖ ^ 8 + ‖b‖ ^ 8) := by
  have hA : 0 ≤ Ω ^ 2 * (r * ‖Hop‖) * (‖a‖ ^ 8 + ‖b‖ ^ 8) := by positivity
  have hB : 0 ≤ K ^ 2 * C * (‖a‖ ^ 8 * ‖b‖ ^ 2 + ‖a‖ ^ 2 * ‖b‖ ^ 8) := by positivity
  by_cases hab : Ω < ‖a‖ ∧ Ω < ‖b‖
  · have h := angularCost_le_of_cross_bound 3 r K C hr hC Hop a b hH (hc hab.1 hab.2)
    norm_num at h
    linarith
  · have hlow : ‖a‖ ≤ Ω ∨ ‖b‖ ≤ Ω := by
      rcases not_and_or.mp hab with h | h
      · exact Or.inl (not_lt.mp h)
      · exact Or.inr (not_lt.mp h)
    have hmin : ‖a‖ * ‖b‖ ≤ Ω * max ‖a‖ ‖b‖ := by
      rcases hlow with h | h
      · calc ‖a‖ * ‖b‖ ≤ Ω * ‖b‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
          _ ≤ Ω * max ‖a‖ ‖b‖ :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) ((norm_nonneg _).trans h)
      · calc ‖a‖ * ‖b‖ ≤ ‖a‖ * Ω := mul_le_mul_of_nonneg_left h (norm_nonneg _)
          _ = Ω * ‖a‖ := mul_comm _ _
          _ ≤ Ω * max ‖a‖ ‖b‖ :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) ((norm_nonneg _).trans h)
    have hΩ : 0 ≤ Ω := by
      rcases hlow with h | h
      · exact (norm_nonneg _).trans h
      · exact (norm_nonneg _).trans h
    have h2 : ‖cross a b‖ ≤ Ω * max ‖a‖ ‖b‖ := (norm_cross_le a b).trans hmin
    have hcr : ‖cross a b‖ ^ 2 ≤ Ω ^ 2 * max ‖a‖ ‖b‖ ^ 2 := by
      calc ‖cross a b‖ ^ 2 ≤ (Ω * max ‖a‖ ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ = _ := by ring
    have hmax8 : max ‖a‖ ‖b‖ ^ 8 ≤ ‖a‖ ^ 8 + ‖b‖ ^ 8 := by
      rcases le_total ‖b‖ ‖a‖ with h | h
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (by positivity)
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (by positivity)
    have hcost : angularCost 3 r Hop a b ≤ Ω ^ 2 * (r * ‖Hop‖) * (‖a‖ ^ 8 + ‖b‖ ^ 8) := by
      unfold angularCost
      have hrH : 0 ≤ r * ‖Hop‖ := mul_nonneg hr (norm_nonneg _)
      calc r * ‖Hop‖ * max ‖a‖ ‖b‖ ^ (2 * 3) * ‖cross a b‖ ^ 2
          ≤ r * ‖Hop‖ * max ‖a‖ ‖b‖ ^ (2 * 3) * (Ω ^ 2 * max ‖a‖ ‖b‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hcr (by positivity)
        _ = Ω ^ 2 * (r * ‖Hop‖) * max ‖a‖ ‖b‖ ^ 8 := by ring
        _ ≤ Ω ^ 2 * (r * ‖Hop‖) * (‖a‖ ^ 8 + ‖b‖ ^ 8) :=
            mul_le_mul_of_nonneg_left hmax8 (by positivity)
    linarith

private theorem integral_displacement_mul' (f g : T3 → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ h : T3, ∫ x : T3, f x * g (x - h)) = (∫ x : T3, f x) * ∫ x : T3, g x := by
  have hi : Integrable (fun p : T3 × T3 ↦ f p.2 * g (p.2 - p.1))
      ((volume : Measure T3).prod volume) :=
    ((hf.comp continuous_snd).mul (hg.comp (continuous_snd.sub continuous_fst))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_integral_swap hi]
  simp only [integral_const_mul, integral_sub_left_eq_self, integral_mul_const]

/-- **The angular remainder under coherence above a threshold.** -/
theorem angularIntegral_le_of_thresholdCoherent (C : ℝ) (hC : 0 ≤ C)
    (hH : ∀ N (h : T3), ‖h‖ ^ 3 * ‖Hk N h‖ ≤ C) (Ω K : ℝ) (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hc : ThresholdCoherent u Ω K) :
    angularIntegral N u ≤ 2 * K ^ 2 * C * LocalVorticityEighthMoment.meanEnergy u *
        InfiniteConvectionEnergy.kineticEnergy (fourierCurl u) +
      2 * Ω ^ 2 * C₁ * LocalVorticityEighthMoment.meanEnergy u := by
  have hw := (continuous_fullVorticity u hu).norm
  have h₂ := hw.fun_pow 2
  have h₈ := hw.fun_pow 8
  have hi₁ : Integrable (fun p : T3 × T3 ↦ ‖fullVorticity u p.2‖ ^ 8 *
      ‖fullVorticity u (p.2 - p.1)‖ ^ 2) ((volume : Measure T3).prod volume) :=
    ((h₈.comp continuous_snd).mul (h₂.comp (continuous_snd.sub continuous_fst))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi₂ : Integrable (fun p : T3 × T3 ↦ ‖fullVorticity u p.2‖ ^ 2 *
      ‖fullVorticity u (p.2 - p.1)‖ ^ 8) ((volume : Measure T3).prod volume) :=
    ((h₂.comp continuous_snd).mul (h₈.comp (continuous_snd.sub continuous_fst))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let f : C(T3 × T3, ℝ) := ⟨fun p ↦ ‖fullVorticity u p.2‖ ^ 8 + ‖fullVorticity u (p.2 - p.1)‖ ^ 8,
    (h₈.comp continuous_snd).add (h₈.comp (continuous_snd.sub continuous_fst))⟩
  have hi₃ : Integrable (fun p : T3 × T3 ↦ (‖p.1‖ * ‖Hk N p.1‖) *
      (‖fullVorticity u p.2‖ ^ 8 + ‖fullVorticity u (p.2 - p.1)‖ ^ 8))
      ((volume : Measure T3).prod volume) := by
    have hi := IntegrableKernelPairing.integrable_mul _ _
      ((PeriodicRieszNearMoment.integrable_firstMoment (d := 3) N).comp_fst (volume : Measure T3)) f
    simpa only [f, ContinuousMap.coe_mk] using hi
  have hb := integral_mono (integrable_angularDensity N u hu)
    (((hi₁.add hi₂).const_mul (K ^ 2 * C)).add (hi₃.const_mul (Ω ^ 2))) (fun p ↦ by
      have hp : Ω < ‖fullVorticity u p.2‖ → Ω < ‖fullVorticity u (p.2 - p.1)‖ →
          ‖cross (fullVorticity u p.2) (fullVorticity u (p.2 - p.1))‖ ≤
            K * ‖p.1‖ * ‖fullVorticity u p.2‖ * ‖fullVorticity u (p.2 - p.1)‖ := by
        intro h1 h2
        have := hc p.2 (p.2 - p.1) h1 h2
        simpa only [sub_sub_cancel] using this
      have := angularCost_le_threshold ‖p.1‖ K C Ω (norm_nonneg _) hC (Hk N p.1) _ _ (hH N p.1) hp
      simp only [Pi.add_apply]
      linarith)
  simp only [Pi.add_apply] at hb
  have hE8 : (∫ p : T3 × T3, (‖p.1‖ * ‖Hk N p.1‖) *
      (‖fullVorticity u p.2‖ ^ 8 + ‖fullVorticity u (p.2 - p.1)‖ ^ 8) ∂((volume : Measure T3).prod volume)) =
      2 * (∫ x : T3, ‖fullVorticity u x‖ ^ 8) * ∫ h : T3, ‖h‖ * ‖Hk N h‖ := by
    rw [integral_prod _ hi₃]
    have hin : ∀ h : T3, (∫ x : T3, (‖h‖ * ‖Hk N h‖) *
        (‖fullVorticity u x‖ ^ 8 + ‖fullVorticity u (x - h)‖ ^ 8)) =
        (‖h‖ * ‖Hk N h‖) * (2 * ∫ x : T3, ‖fullVorticity u x‖ ^ 8) := by
      intro h
      have hc8 : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 8) :=
        h₈.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hc8' : Integrable (fun x : T3 ↦ ‖fullVorticity u (x - h)‖ ^ 8) :=
        (h₈.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      rw [integral_const_mul, integral_add hc8 hc8',
        integral_sub_right_eq_self (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 8) h]
      ring
    simp only [hin]
    rw [integral_mul_const]
    ring
  have hI1 : Integrable (fun p : T3 × T3 ↦ K ^ 2 * C *
      (‖fullVorticity u p.2‖ ^ 8 * ‖fullVorticity u (p.2 - p.1)‖ ^ 2 +
        ‖fullVorticity u p.2‖ ^ 2 * ‖fullVorticity u (p.2 - p.1)‖ ^ 8))
      ((volume : Measure T3).prod volume) := (hi₁.add hi₂).const_mul _
  have hI2 : Integrable (fun p : T3 × T3 ↦ Ω ^ 2 * (‖p.1‖ * ‖Hk N p.1‖ *
      (‖fullVorticity u p.2‖ ^ 8 + ‖fullVorticity u (p.2 - p.1)‖ ^ 8)))
      ((volume : Measure T3).prod volume) := hi₃.const_mul _
  have hR : (∫ p : T3 × T3, K ^ 2 * C *
      (‖fullVorticity u p.2‖ ^ 8 * ‖fullVorticity u (p.2 - p.1)‖ ^ 2 +
        ‖fullVorticity u p.2‖ ^ 2 * ‖fullVorticity u (p.2 - p.1)‖ ^ 8) +
      Ω ^ 2 * (‖p.1‖ * ‖Hk N p.1‖ *
        (‖fullVorticity u p.2‖ ^ 8 + ‖fullVorticity u (p.2 - p.1)‖ ^ 8))
      ∂((volume : Measure T3).prod volume)) =
      K ^ 2 * C * ((∫ p : T3 × T3, ‖fullVorticity u p.2‖ ^ 8 * ‖fullVorticity u (p.2 - p.1)‖ ^ 2
          ∂((volume : Measure T3).prod volume)) +
        ∫ p : T3 × T3, ‖fullVorticity u p.2‖ ^ 2 * ‖fullVorticity u (p.2 - p.1)‖ ^ 8
          ∂((volume : Measure T3).prod volume)) +
      Ω ^ 2 * (2 * (∫ x : T3, ‖fullVorticity u x‖ ^ 8) * ∫ h : T3, ‖h‖ * ‖Hk N h‖) := by
    rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul, integral_add hi₁ hi₂, hE8]
  rw [hR, integral_prod _ hi₁, integral_prod _ hi₂,
    integral_prod _ (integrable_angularDensity N u hu)] at hb
  have hd₁ := integral_displacement_mul' (fun x ↦ ‖fullVorticity u x‖ ^ 8)
    (fun x ↦ ‖fullVorticity u x‖ ^ 2) h₈ h₂
  have hd₂ := integral_displacement_mul' (fun x ↦ ‖fullVorticity u x‖ ^ 2)
    (fun x ↦ ‖fullVorticity u x‖ ^ 8) h₂ h₈
  dsimp only at hb hd₁ hd₂
  rw [hd₁, hd₂] at hb
  have hp := integral_norm_fullVorticity_sq_le u hu
  have hm1 := PeriodicRieszNearMoment.firstMoment_le (d := 3) N
  have hE : 0 ≤ ∫ x : T3, ‖fullVorticity u x‖ ^ 8 := integral_nonneg (fun _ ↦ by positivity)
  have hZ : 0 ≤ ∫ x : T3, ‖fullVorticity u x‖ ^ 2 := integral_nonneg (fun _ ↦ by positivity)
  have hA : angularIntegral N u = ∫ h : T3, ∫ x : T3, angularCost 3 ‖h‖ (Hk N h)
      (fullVorticity u x) (fullVorticity u (x - h)) := rfl
  have hk1 := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * K ^ 2 * C *
    (∫ x : T3, ‖fullVorticity u x‖ ^ 8) by positivity)
  have hk2 := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ 2 * Ω ^ 2 *
    (∫ x : T3, ‖fullVorticity u x‖ ^ 8) by positivity)
  simp only [LocalVorticityEighthMoment.meanEnergy, LocalVorticityEighthMoment.energy_eq_norm_pow]
  rw [← hA] at hb
  nlinarith only [hb, hk1, hk2]

/-- **The regularized source under coherence above a threshold.** The constant
is uniform in the threshold, the coherence constant, the cutoff and the field. -/
theorem exists_uniform_source_bound_threshold (nu : ℝ) (hnu : 0 < nu) :
    ∃ C ≥ (0 : ℝ), ∀ Ω K N u, Summable (fourierMoment 3 u) → ThresholdCoherent u Ω K →
      |source 6 N u| ≤ nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u +
        (growthCoefficient nu C K u + C * Ω ^ 2 / nu) * LocalVorticityEighthMoment.meanEnergy u := by
  obtain ⟨C, hC, hH⟩ := PeriodicRieszSingularity.exists_uniform_operator_bound (d := 3)
  have h₁ := PeriodicRieszNearMoment.firstMomentBound_nonneg 3
  refine ⟨48 * (C₁ + 1) * (C + C₁), by positivity, ?_⟩
  intro Ω K N u hu hc
  have hs := abs_source_le_half_dissipation_add_angular nu hnu N u hu
  have ha := angularIntegral_le_of_thresholdCoherent C hC hH Ω K N u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu) hc
  have hm := mul_le_mul_of_nonneg_left ha (show 0 ≤ 24 * (C₁ + 1) / nu by positivity)
  have hE := LocalVorticityEighthMoment.meanEnergy_nonneg u
  have hZ := LocalKineticEnergy.kineticEnergy_nonneg (fourierCurl u)
  set E := LocalVorticityEighthMoment.meanEnergy u with hEdef
  set Z := InfiniteConvectionEnergy.kineticEnergy (fourierCurl u) with hZdef
  have key : (24 * (C₁ + 1) / nu) * (2 * K ^ 2 * C * E * Z + 2 * Ω ^ 2 * C₁ * E) ≤
      (growthCoefficient nu (48 * (C₁ + 1) * (C + C₁)) K u +
        48 * (C₁ + 1) * (C + C₁) * Ω ^ 2 / nu) * E := by
    unfold growthCoefficient
    rw [← hZdef]
    have hdiff : (48 * (C₁ + 1) * (C + C₁) * K ^ 2 / nu * Z +
        48 * (C₁ + 1) * (C + C₁) * Ω ^ 2 / nu) * E -
        (24 * (C₁ + 1) / nu) * (2 * K ^ 2 * C * E * Z + 2 * Ω ^ 2 * C₁ * E) =
        (48 * (C₁ + 1) / nu) * (C₁ * K ^ 2 * Z * E + C * Ω ^ 2 * E) := by
      field_simp
      ring
    have hnn : 0 ≤ (48 * (C₁ + 1) / nu) * (C₁ * K ^ 2 * Z * E + C * Ω ^ 2 * E) := by positivity
    linarith
  linarith

/-- **The actual stretching under coherence above a threshold.** -/
theorem exists_stretching_bound_threshold (nu : ℝ) (hnu : 0 < nu) :
    ∃ C ≥ (0 : ℝ), ∀ Ω K u, Summable (fourierMoment 3 u) →
      (∀ k, u (-k) = coefficientConjugate (u k)) → (∀ k, modeDot k (u k) = 0) →
      ThresholdCoherent u Ω K →
      |LocalVorticityEighthMoment.stretching u| ≤
        nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u +
          (growthCoefficient nu C K u + C * Ω ^ 2 / nu) * LocalVorticityEighthMoment.meanEnergy u := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_source_bound_threshold nu hnu
  refine ⟨C, hC, ?_⟩
  intro Ω K u hu hr hd hc
  apply le_of_tendsto ((tendsto_eighthMoment_source u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu) hr hd).abs)
  exact Eventually.of_forall (fun N ↦ hb Ω K N u hu hc)

end Kernel

section Lipschitz

open PancakeInfiniteSpatialCurl PancakeDyadicDirectionEvolution PancakeInfiniteVelocityLipschitz
open LocalVorticityDiffusion PancakeFourierMaterialPaths PancakeInfiniteFourierDerivative

theorem cross_self' (a : R3) : cross a a = 0 := by
  have h := norm_cross_sq a a
  rw [real_inner_self_eq_norm_sq] at h
  have h2 : ‖cross a a‖ ^ 2 = 0 := by rw [h]; ring
  exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)

/-- **Two torus points have real representatives at the torus distance.** -/
theorem exists_lifts (x y : T3) :
    ∃ a b : X3, torusPoint a = x ∧ torusPoint b = y ∧ ‖a - b‖ ≤ ‖x - y‖ := by
  obtain ⟨a, ha, -⟩ := PancakePeriodicLipschitz.torusPoint_bounded_rep x
  set d : T3 := y - x with hd
  let e : X3 := fun i ↦ (AddCircle.equivIco 1 0 (d i)).1
  have he : ∀ i, ((e i : ℝ) : UnitAddCircle) = d i := fun i ↦ AddCircle.coe_equivIco
  let δ : X3 := fun i ↦ e i - round (e i)
  have hround : ∀ i, (((round (e i) : ℤ) : ℝ) : UnitAddCircle) = 0 := fun i ↦
    (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨round (e i), by simp⟩
  have hδ : ∀ i, ((δ i : ℝ) : UnitAddCircle) = d i := by
    intro i
    change (((e i - (round (e i) : ℝ) : ℝ)) : UnitAddCircle) = d i
    rw [AddCircle.coe_sub, hround i, sub_zero, he i]
  have hδn : ∀ i, |δ i| = ‖d i‖ := by
    intro i
    rw [← he i, AddCircle.norm_eq]
    simp [δ]
  refine ⟨a, a + δ, ha, ?_, ?_⟩
  · funext i
    have hai : ((a i : ℝ) : UnitAddCircle) = x i := congrFun ha i
    change (((a i + δ i : ℝ)) : UnitAddCircle) = y i
    rw [AddCircle.coe_add, hδ i, hai, hd]
    simp
  · have h1 : a - (a + δ) = -δ := by abel
    rw [h1, norm_neg]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ ?_
    rw [Real.norm_eq_abs, hδn i]
    calc ‖d i‖ ≤ ‖d‖ := norm_le_pi_norm d i
      _ = ‖x - y‖ := by rw [hd, ← norm_neg, neg_sub]

/-- **The vorticity is Lipschitz on the torus**, with a constant from any summable
bound on the second Fourier moment of the velocity. -/
theorem norm_fullVorticity_sub_le (u : FourierVelocity) (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q)
    (hSum : Summable g) (hu : ∀ q, fourierMoment 2 u q ≤ g q) (x y : T3) :
    ‖fullVorticity u x - fullVorticity u y‖ ≤
      ‖complexRealPartEuclideanCLM‖ * (3 * (2 * Real.pi) * ∑' q, (2 * Real.pi) * g q) * ‖x - y‖ := by
  have hu2 : Summable (fourierMoment 2 u) := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) hu
  obtain ⟨a, b, ha, hb, hab⟩ := exists_lifts x y
  have hc : ∀ q, fourierMoment 1 (fourierCurl u) q ≤ (2 * Real.pi) * g q := fun q ↦
    (fourierMoment_curl_le 1 u q).trans (mul_le_mul_of_nonneg_left (hu q) (by positivity))
  have hL := norm_fullFourierField_lift_sub_le (fourierCurl u) (fun q ↦ (2 * Real.pi) * g q)
    (fun q ↦ mul_nonneg (by positivity) (hg q)) (hSum.mul_left _) hc a b
  have hx : fullVorticity u x - fullVorticity u y =
      complexRealPartEuclideanCLM (fullFourierField id (fourierCurl u) (torusPoint a) -
        fullFourierField id (fourierCurl u) (torusPoint b)) := by
    rw [← ha, ← hb]
    simp only [fullVorticity, spatialCurl_velocity u (summable_firstMoment_of_second u hu2)]
    rw [map_sub]
  rw [hx]
  have hL0 : 0 ≤ 3 * (2 * Real.pi) * ∑' q, (2 * Real.pi) * g q :=
    mul_nonneg (by positivity) (tsum_nonneg fun q ↦ mul_nonneg (by positivity) (hg q))
  calc ‖complexRealPartEuclideanCLM (fullFourierField id (fourierCurl u) (torusPoint a) -
        fullFourierField id (fourierCurl u) (torusPoint b))‖
      ≤ ‖complexRealPartEuclideanCLM‖ * ‖fullFourierField id (fourierCurl u) (torusPoint a) -
          fullFourierField id (fourierCurl u) (torusPoint b)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖complexRealPartEuclideanCLM‖ * ((3 * (2 * Real.pi) * ∑' q, (2 * Real.pi) * g q) * ‖a - b‖) :=
        mul_le_mul_of_nonneg_left hL (norm_nonneg _)
    _ ≤ ‖complexRealPartEuclideanCLM‖ * ((3 * (2 * Real.pi) * ∑' q, (2 * Real.pi) * g q) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hab hL0) (norm_nonneg _)
    _ = ‖complexRealPartEuclideanCLM‖ * (3 * (2 * Real.pi) * ∑' q, (2 * Real.pi) * g q) * ‖x - y‖ := by
        ring

/-- **A Lipschitz vorticity is coherent above every positive threshold.** -/
theorem thresholdCoherent_of_lipschitz (u : FourierVelocity) {L Ω : ℝ} (hL0 : 0 ≤ L) (hΩ : 0 < Ω)
    (hL : ∀ x y : T3, ‖fullVorticity u x - fullVorticity u y‖ ≤ L * ‖x - y‖) :
    ThresholdCoherent u Ω (L / Ω) := by
  intro x y _ hy
  set a := fullVorticity u x
  set b := fullVorticity u y
  have hcross : cross a b = cross a (b - a) := by
    rw [cross_sub_right, cross_self', sub_zero]
  have hdiff := hL y x
  calc ‖cross a b‖ = ‖cross a (b - a)‖ := by rw [hcross]
    _ ≤ ‖a‖ * ‖b - a‖ := norm_cross_le _ _
    _ ≤ ‖a‖ * (L * ‖y - x‖) := mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)
    _ ≤ L / Ω * ‖x - y‖ * ‖a‖ * ‖b‖ := by
        rw [norm_sub_rev y x]
        have key : L / Ω * ‖x - y‖ * ‖a‖ * ‖b‖ - ‖a‖ * (L * ‖x - y‖) =
            (L * ‖x - y‖ * ‖a‖ / Ω) * (‖b‖ - Ω) := by
          field_simp
        have hnn : 0 ≤ (L * ‖x - y‖ * ‖a‖ / Ω) * (‖b‖ - Ω) :=
          mul_nonneg (by positivity) (by linarith)
        linarith

end Lipschitz

section Dynamics

open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeLatticeDecayEnvelope PancakeHigherLocalVelocity
open PancakeLocalInfiniteVelocity InfiniteConvectionEnergy
open FourierTameTriad FourierContinuation FourierTameContinuation FourierEighthMomentControl
open FourierVorticitySupContinuation FourierGlobalSolution FourierRegularityEquivalence
open PancakeDyadicDirectionEvolution

variable {m : ℕ} {nu : ℝ} {u₀ : FourierVelocity}

/-- **The eighth vorticity moment stays bounded under coherence above a
threshold.** The exponent is paid by the initial kinetic energy and by the
threshold times the elapsed time. -/
theorem meanEnergy_le_of_thresholdCoherent (hm : 7 ≤ m) (hnu : 0 < nu) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ Ω K u, Summable (fourierMoment 3 u) →
      (∀ k, u (-k) = coefficientConjugate (u k)) → (∀ k, modeDot k (u k) = 0) →
      ThresholdCoherent u Ω K →
      |LocalVorticityEighthMoment.stretching u| ≤
        nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u +
          (growthCoefficient nu C K u + C * Ω ^ 2 / nu) * LocalVorticityEighthMoment.meanEnergy u)
    {T : ℝ} (c : TameSolutionOn nu m u₀ T) (Ω K : ℝ)
    (hK : ∀ τ ∈ Ico (0 : ℝ) T, ThresholdCoherent (c.coefficients τ) Ω K)
    (τ : ℝ) (hτ : τ ∈ Ico (0 : ℝ) T) :
    LocalVorticityEighthMoment.meanEnergy (c.coefficients τ) ≤
      LocalVorticityEighthMoment.meanEnergy u₀ *
        Real.exp (8 * (C * K ^ 2 * kineticEnergy u₀ / (2 * nu ^ 2) + C * Ω ^ 2 / nu * τ)) := by
  set S := (τ + T) / 2 with hSdef
  have hτS : τ < S := by linarith [hτ.2]
  have hST : S < T := by linarith [hτ.2]
  have hS0 : 0 < S := lt_of_le_of_lt hτ.1 hτS
  obtain ⟨B, hB⟩ := c.sobolev_local S hST
  obtain ⟨E, hE⟩ := c.order_local S hST
  let s : LocalInfiniteVelocitySolution nu u₀ S B := restrictLocal c.toSolutionOn hST hB
  have h7 : ∀ t ∈ Icc (0 : ℝ) S, ∀ F : Finset Wavevector,
      velocityEnergy (3 + 4) F (s.coefficients t) ≤ E :=
    fun t ht F ↦ (velocityEnergy_le_of_order_le (by omega) _ F).trans (hE t ht F)
  let g : Wavevector → ℝ := fun k ↦ Real.sqrt E * latticeDecayWeight k
  have hg : ∀ k, 0 ≤ g k := fun k ↦ mul_nonneg (Real.sqrt_nonneg E) (latticeDecayWeight_pos k).le
  have hSum : Summable g := summable_latticeDecayWeight.mul_left _
  have hu3 : ∀ t ∈ Icc (0 : ℝ) S, ∀ k, fourierMoment 3 (s.coefficients t) k ≤ g k :=
    fun t ht k ↦ orderMoment_le_latticeEnvelope 3 _ E (h7 t ht) k
  set b : ℝ → ℝ := fun t ↦ growthCoefficient nu C K (s.coefficients t) + C * Ω ^ 2 / nu with hbdef
  have hbc : ContinuousOn b (Icc 0 S) :=
    (continuousOn_growthCoefficient s g hg hSum hu3 C K).add continuousOn_const
  have hb0 : ∀ t, 0 ≤ b t := fun t ↦
    add_nonneg (growthCoefficient_nonneg nu C K hnu.le hC _) (by positivity)
  have hEc := LocalVorticityEighthMoment.continuousOn_meanEnergy s g hSum hu3
  have hGc := LocalVorticityEighthMoment.continuousOn_weightedPalinstrophy s g hSum hu3
  have hSc := LocalVorticityEighthMoment.continuousOn_stretching s g hSum hu3
  have hs : ∀ t ∈ Icc (0 : ℝ) S, |LocalVorticityEighthMoment.stretching (s.coefficients t)| ≤
      nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy (s.coefficients t) +
        b t * LocalVorticityEighthMoment.meanEnergy (s.coefficients t) := fun t ht ↦
    hb Ω K _ (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu3 t ht)) (s.reality t)
      (s.transverse t) (hK t ⟨ht.1, ht.2.trans_lt hST⟩)
  have hineq : ∀ t ∈ Icc (0 : ℝ) τ, LocalVorticityEighthMoment.meanEnergy (s.coefficients t) ≤
      LocalVorticityEighthMoment.meanEnergy u₀ +
        8 * ∫ r in (0 : ℝ)..t, b r * LocalVorticityEighthMoment.meanEnergy (s.coefficients r) := by
    intro t ht
    have htS : t ∈ Icc (0 : ℝ) S := ⟨ht.1, ht.2.trans hτS.le⟩
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 S := Icc_subset_Icc le_rfl htS.2
    have hG := (hGc.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hS := (hSc.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hbE : IntervalIntegrable
        (fun r ↦ b r * LocalVorticityEighthMoment.meanEnergy (s.coefficients r)) volume 0 t :=
      ((hbc.mul hEc).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hi := intervalIntegral.integral_mono_on ht.1 hS ((hG.const_mul (nu / 2)).add hbE)
      (fun r hr ↦ (le_abs_self _).trans (hs r (hsub hr)))
    rw [intervalIntegral.integral_add (hG.const_mul (nu / 2)) hbE,
      intervalIntegral.integral_const_mul] at hi
    have he := LocalVorticityEighthMoment.energy_add_half_dissipation_le_of_stretching_bound
      s g hg hSum hu3 hnu.le hS0 t htS _ hi
    have hG0 : 0 ≤ ∫ r in (0 : ℝ)..t, LocalVorticityEighthMoment.weightedPalinstrophy (s.coefficients r) :=
      intervalIntegral.integral_nonneg ht.1
        (fun r _ ↦ LocalVorticityEighthMoment.weightedPalinstrophy_nonneg _)
    nlinarith [mul_nonneg hnu.le hG0]
  have hsubτ : Icc (0 : ℝ) τ ⊆ Icc 0 S := Icc_subset_Icc le_rfl hτS.le
  have hG := le_mul_exp_of_le_add_integral hτ.1 (by norm_num : (0 : ℝ) ≤ 8) (hEc.mono hsubτ)
    (hbc.mono hsubτ) (fun t _ ↦ hb0 t) hineq
  have hint : (∫ r in (0 : ℝ)..τ, b r) ≤
      C * K ^ 2 * kineticEnergy u₀ / (2 * nu ^ 2) + C * Ω ^ 2 / nu * τ := by
    have h1 := integral_growthCoefficient_le s g hg hSum hu3 hnu C K hC τ ⟨hτ.1, hτS.le⟩
    have he : (∫ r in (0 : ℝ)..τ, b r) =
        (∫ r in (0 : ℝ)..τ, growthCoefficient nu C K (s.coefficients r)) + τ * (C * Ω ^ 2 / nu) := by
      simp only [hbdef]
      rw [intervalIntegral.integral_add h1.1 intervalIntegrable_const, intervalIntegral.integral_const,
        smul_eq_mul, sub_zero]
    rw [he]
    nlinarith [h1.2]
  have hexp : Real.exp (8 * ∫ r in (0 : ℝ)..τ, b r) ≤
      Real.exp (8 * (C * K ^ 2 * kineticEnergy u₀ / (2 * nu ^ 2) + C * Ω ^ 2 / nu * τ)) :=
    Real.exp_le_exp.mpr (by linarith)
  exact hG.trans (mul_le_mul_of_nonneg_left hexp (LocalVorticityEighthMoment.meanEnergy_nonneg _))

/-- **Coherence above a threshold on every finite horizon gives a global
solution.** -/
theorem nonempty_globalSolution_of_thresholdCoherent (hm : 7 ≤ m) (hnu : 0 < nu)
    (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q)) (hd : ∀ q, modeDot q (u₀ q) = 0)
    (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀) (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀)
    (hcoh : ∀ H, 0 < H → ∃ Ω K, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
      ∀ τ ∈ Ico (0 : ℝ) T, ThresholdCoherent (c.coefficients τ) Ω K) :
    Nonempty (GlobalSolution nu m u₀) := by
  obtain ⟨C, hC, hb⟩ := exists_stretching_bound_threshold nu hnu
  refine nonempty_globalSolution_of_meanEnergy hm hnu hr hd hz hE₀0 hE₀ fun H hH ↦ ?_
  obtain ⟨Ω, K, hK⟩ := hcoh H hH
  refine ⟨LocalVorticityEighthMoment.meanEnergy u₀ *
    Real.exp (8 * (C * K ^ 2 * kineticEnergy u₀ / (2 * nu ^ 2) + C * Ω ^ 2 / nu * H)),
    fun T hT c τ hτ ↦ ?_⟩
  have h := meanEnergy_le_of_thresholdCoherent hm hnu hC hb c Ω K (fun r hr ↦ hK T hT c r hr) τ hτ
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (LocalVorticityEighthMoment.meanEnergy_nonneg _))
  have hτH : τ ≤ H := hτ.2.le.trans hT
  have hc0 : 0 ≤ C * Ω ^ 2 / nu := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hτH hc0]

/-- **Along a global solution, the vorticity is coherent above every positive
threshold on every finite horizon.** -/
theorem thresholdCoherent_of_globalSolution (hm : 7 ≤ m) (hnu : 0 < nu)
    (g : GlobalSolution nu m u₀) (H Ω : ℝ) (hΩ : 0 < Ω) :
    ∃ K, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T, ∀ τ ∈ Ico (0 : ℝ) T,
      ThresholdCoherent (c.coefficients τ) Ω K := by
  obtain ⟨B, s, hs, e, he, hSum, hu⟩ := GlobalSolution.local_envelope hm g H
  refine ⟨‖complexRealPartEuclideanCLM‖ * (3 * (2 * Real.pi) * ∑' q, (2 * Real.pi) * e q) / Ω,
    fun T hT c τ hτ ↦ ?_⟩
  have hτH : τ ∈ Icc (0 : ℝ) H := ⟨hτ.1, hτ.2.le.trans hT⟩
  have hcg : c.coefficients τ = g.coefficients τ :=
    TameSolutionOn.coefficients_eq_global hm hnu g c hτ
  have hmom : ∀ q, fourierMoment 2 (c.coefficients τ) q ≤ e q := by
    intro q
    rw [hcg, ← hs]
    exact (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτH q)
  have hL0 : 0 ≤ ‖complexRealPartEuclideanCLM‖ * (3 * (2 * Real.pi) * ∑' q, (2 * Real.pi) * e q) :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (by positivity)
      (tsum_nonneg fun q ↦ mul_nonneg (by positivity) (he q)))
  exact thresholdCoherent_of_lipschitz _ hL0 hΩ
    (norm_fullVorticity_sub_le (c.coefficients τ) e he hSum hmom)

/-- **Periodic regularity is exactly coherence of the vorticity direction above
a threshold on every finite horizon.** For order `m ≥ 7`: every admissible datum
has a global solution, for every viscosity, if and only if on every finite
horizon some threshold and constant make every tame solution coherent above
the threshold. -/
theorem periodicRegularity_iff_thresholdCoherent (hm : 7 ≤ m) :
    PeriodicRegularity m ↔ ∀ nu : ℝ, 0 < nu → ∀ u₀ : FourierVelocity, Admissible m u₀ →
      ∀ H, 0 < H → ∃ Ω K, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
        ∀ τ ∈ Ico (0 : ℝ) T, ThresholdCoherent (c.coefficients τ) Ω K := by
  constructor
  · intro h nu hnu u₀ hu H _
    obtain ⟨g⟩ := h nu hnu u₀ hu
    obtain ⟨K, hK⟩ := thresholdCoherent_of_globalSolution hm hnu g H 1 one_pos
    exact ⟨1, K, hK⟩
  · intro h nu hnu u₀ hu
    have hcoh := h nu hnu u₀ hu
    obtain ⟨hr, hd, hz, E₀, hE₀⟩ := hu
    have hE₀0 : 0 ≤ E₀ := le_trans (by simp [velocityEnergy_eq]) (hE₀ ∅)
    exact nonempty_globalSolution_of_thresholdCoherent hm hnu hr hd hz hE₀0 hE₀ hcoh

/-- **Coherence above a threshold gives the official periodic statement.** -/
theorem periodicStatementB_of_thresholdCoherent (hm : 7 ≤ m)
    (h : ∀ nu : ℝ, 0 < nu → ∀ u₀ : FourierVelocity, Admissible m u₀ →
      ∀ H, 0 < H → ∃ Ω K, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
        ∀ τ ∈ Ico (0 : ℝ) T, ThresholdCoherent (c.coefficients τ) Ω K) :
    OfficialPeriodicProblem.PeriodicStatementB :=
  FourierOfficialTheorems.periodicStatementB_of_periodicRegularity hm
    ((periodicRegularity_iff_thresholdCoherent hm).mpr h)

end Dynamics

end Mettapedia.FluidDynamics.NavierStokes.FourierCoherenceRegularity
