import Mettapedia.Analysis.PeriodicRieszSingularity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityAngularPayment

/-!
# Conditional payment of the actual angular remainder

An explicit projective Lipschitz condition bounds the angular remainder by
the product of the eighth moment and enstrophy. The constant is uniform in
the Fourier cutoff. This file does not infer direction coherence from NS;
the unconditional source split lives in `VorticityAngularPayment`.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityCoherenceBudget

open MeasureTheory Filter PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget VorticityRegularizedSource VorticityAngularPayment PancakeBlockReality
open Mettapedia.Analysis SignedCrossKernel EuclideanCrossProduct PancakeGalerkinKineticEnergy
open scoped Topology
local notation "T3" => UnitAddTorus (Fin 3)
local notation "H" => PeriodicRieszOperator.kernel (d := 3)
local notation "C₁" => PeriodicRieszNearMoment.firstMomentBound 3
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

/-- A direction condition on the actual field, including zero vorticity
and antiparallel pairs. Its derivation from the dynamics is not assumed. -/
def ProjectiveLipschitz (u : FourierVelocity) (K : ℝ) : Prop :=
  ∀ x y : T3, ‖cross (fullVorticity u x) (fullVorticity u y)‖ ≤
    K * ‖x - y‖ * ‖fullVorticity u x‖ * ‖fullVorticity u y‖

private theorem integral_displacement_mul (f g : T3 → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ h : T3, ∫ x : T3, f x * g (x - h)) = (∫ x : T3, f x) * ∫ x : T3, g x := by
  have hi : Integrable (fun p : T3 × T3 ↦ f p.2 * g (p.2 - p.1))
      ((volume : Measure T3).prod volume) :=
    ((hf.comp continuous_snd).mul (hg.comp (continuous_snd.sub continuous_fst))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_integral_swap hi]
  simp only [integral_const_mul, integral_sub_left_eq_self, integral_mul_const]

theorem angularIntegral_le_of_projectiveLipschitz (C : ℝ) (hC : 0 ≤ C)
    (hH : ∀ N (h : T3), ‖h‖ ^ 3 * ‖H N h‖ ≤ C)
    (K : ℝ) (N : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hc : ProjectiveLipschitz u K) :
    angularIntegral N u ≤ 2 * K ^ 2 * C * LocalVorticityEighthMoment.meanEnergy u *
      InfiniteConvectionEnergy.kineticEnergy (fourierCurl u) := by
  have hw := (continuous_fullVorticity u hu).norm
  have h₂ := hw.pow 2
  have h₈ := hw.pow 8
  have hi₁ : Integrable (fun p : T3 × T3 ↦ ‖fullVorticity u p.2‖ ^ 8 *
      ‖fullVorticity u (p.2 - p.1)‖ ^ 2) ((volume : Measure T3).prod volume) :=
    ((h₈.comp continuous_snd).mul (h₂.comp (continuous_snd.sub continuous_fst))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi₂ : Integrable (fun p : T3 × T3 ↦ ‖fullVorticity u p.2‖ ^ 2 *
      ‖fullVorticity u (p.2 - p.1)‖ ^ 8) ((volume : Measure T3).prod volume) :=
    ((h₂.comp continuous_snd).mul (h₈.comp (continuous_snd.sub continuous_fst))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb := integral_mono (integrable_angularDensity N u hu)
    ((hi₁.add hi₂).const_mul (K ^ 2 * C)) (fun p ↦ by
      have hp := hc p.2 (p.2 - p.1)
      simp only [sub_sub_cancel] at hp
      exact angularCost_le_of_cross_bound 3 ‖p.1‖ K C (norm_nonneg _) hC
        (H N p.1) _ _ (hH N p.1) hp)
  simp only [Pi.add_apply] at hb
  rw [integral_prod _ (integrable_angularDensity N u hu), integral_const_mul,
    integral_add hi₁ hi₂, integral_prod _ hi₁, integral_prod _ hi₂,
    integral_displacement_mul _ _ h₈ h₂, integral_displacement_mul _ _ h₂ h₈] at hb
  have hp := integral_norm_fullVorticity_sq_le u hu
  have hE : 0 ≤ ∫ x : T3, ‖fullVorticity u x‖ ^ 8 := integral_nonneg (fun _ ↦ by positivity)
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * K ^ 2 * C *
    (∫ x : T3, ‖fullVorticity u x‖ ^ 8) by positivity)
  simp only [LocalVorticityEighthMoment.meanEnergy, LocalVorticityEighthMoment.energy_eq_norm_pow]
  change angularIntegral N u ≤ _ at hb
  nlinarith only [hb, hm]

/-- The same constant works for all fields, coherence bounds and cutoffs. -/
theorem exists_uniform_source_bound (nu : ℝ) (hnu : 0 < nu) :
    ∃ C ≥ (0 : ℝ), ∀ K N u, Summable (fourierMoment 3 u) → ProjectiveLipschitz u K →
      |source 6 N u| ≤ nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u +
        (C * K ^ 2 / nu * InfiniteConvectionEnergy.kineticEnergy (fourierCurl u)) *
          LocalVorticityEighthMoment.meanEnergy u := by
  obtain ⟨C, hC, hH⟩ := PeriodicRieszSingularity.exists_uniform_operator_bound (d := 3)
  have h₁ := PeriodicRieszNearMoment.firstMomentBound_nonneg 3
  refine ⟨48 * (C₁ + 1) * C, by positivity, ?_⟩
  intro K N u hu hc
  have hs := abs_source_le_half_dissipation_add_angular nu hnu N u hu
  have ha := angularIntegral_le_of_projectiveLipschitz C hC hH K N u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu) hc
  have hm := mul_le_mul_of_nonneg_left ha (show 0 ≤ 24 * (C₁ + 1) / nu by positivity)
  have he : (24 * (C₁ + 1) / nu) * (2 * K ^ 2 * C *
      LocalVorticityEighthMoment.meanEnergy u * InfiniteConvectionEnergy.kineticEnergy (fourierCurl u)) =
      (48 * (C₁ + 1) * C * K ^ 2 / nu * InfiniteConvectionEnergy.kineticEnergy (fourierCurl u)) *
        LocalVorticityEighthMoment.meanEnergy u := by ring
  rw [he] at hm
  linarith only [hs, hm]

/-- Passing to the actual source preserves the explicit coherence hypothesis. -/
theorem exists_stretching_bound (nu : ℝ) (hnu : 0 < nu) :
    ∃ C ≥ (0 : ℝ), ∀ K u, Summable (fourierMoment 3 u) →
      (∀ k, u (-k) = coefficientConjugate (u k)) → (∀ k, modeDot k (u k) = 0) →
      ProjectiveLipschitz u K →
      |LocalVorticityEighthMoment.stretching u| ≤
        nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u +
          (C * K ^ 2 / nu * InfiniteConvectionEnergy.kineticEnergy (fourierCurl u)) *
            LocalVorticityEighthMoment.meanEnergy u := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_source_bound nu hnu
  refine ⟨C, hC, ?_⟩
  intro K u hu hr hd hc
  apply le_of_tendsto ((tendsto_eighthMoment_source u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu) hr hd).abs)
  exact Eventually.of_forall (fun N ↦ hb K N u hu hc)

end Mettapedia.FluidDynamics.NavierStokes.VorticityCoherenceBudget
