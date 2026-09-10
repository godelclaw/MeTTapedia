import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalTiltSource

/-!
# Actual alignment energy with the direct-tilt excess

The physical material-rate identity and weak spatial diffusion estimate
give an energy inequality from arbitrary admissible periodic data. The
source is measurable through spectral collisions; integrable primitives,
not source continuity, extend the estimate to the time endpoints. One
quarter of the spectral residual remains on the left. No uniform global
time or frequency budget is assumed or obtained.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalTiltAlignmentEnergy

open scoped ComplexConjugate
open Filter MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks
open PancakeHigherLocalVelocity LocalMeanAlignmentBalance LocalLowDiffusionBudget
open LocalAlignmentForcing (materialRate residual)
open LocalAlignmentContinuity LocalExcessDiffusionEnergy LocalTiltSource

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def budgetSource (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3) : ℝ :=
  excessCost chi modes u delta nu x + forcingEnvelope chi modes outputs u delta x

theorem integral_budgetSource_eq (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (delta nu : ℝ)
    (hd : 0 < delta) (hnu : 0 ≤ nu) :
    (∫ x : T3, budgetSource chi modes outputs u delta nu x) =
      (∫ x : T3, excessCost chi modes u delta nu x) + ∫ x : T3, forcingEnvelope chi modes outputs u delta x :=
  integral_add (integrable_excessCost chi modes u hu delta nu hd hnu)
    (integrable_forcingEnvelope chi modes outputs u hu delta)

theorem intervalIntegrable_budgetSource {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 ≤ nu)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (delta : ℝ) (hd : 0 < delta)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ ∫ x : T3, budgetSource chi modes outputs (s.coefficients τ) delta nu x) volume 0 t := by
  have hD := intervalIntegrable_excessCost s hnu g hSum hu chi modes delta hd t ht
  have hR := LocalTiltSource.intervalIntegrable_forcingEnvelope s g hg hSum hu chi C hchi modes outputs delta t ht
  apply (hD.add hR).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with τ hτ
  have hτ' : τ ∈ Set.Icc (0 : ℝ) T := by
    rw [Set.uIoc_of_le ht.1] at hτ
    exact ⟨hτ.1.le, hτ.2.trans ht.2⟩
  exact (integral_budgetSource_eq chi modes outputs _
    (summable_fourierMoment_of_le _ (by omega : 1 ≤ 2)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτ'))) delta nu hd hnu).symm

section Solution

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 < nu) (hT : 0 < T) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
  (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
  (hchir : ∀ q, chi (-q) = conj (chi q))
  (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
  (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
  (delta : ℝ) (hd : 0 < delta)

include hnu hT hB hg hSum hu hchi hcut hchir hsub hout hs hk hd

theorem meanEnergy_add_quarter_integral_residual_le
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    meanEnergy chi modes (s.coefficients b) delta +
      (1 / 4 : ℝ) * (∫ τ in a..b, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes (s.coefficients a) delta +
        ∫ τ in a..b, ∫ x : T3, budgetSource chi modes outputs (s.coefficients τ) delta nu x := by
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hsubI : Set.Icc a b ⊆ Set.Icc (0 : ℝ) T := fun _ hτ ↦ Set.Ioo_subset_Icc_self (hI hτ)
  have hR : IntervalIntegrable (fun τ ↦ ∫ x : T3,
      budgetSource chi modes outputs (s.coefficients τ) delta nu x) volume a b :=
    (intervalIntegrable_budgetSource s hnu.le g hg hSum hu2 chi C hchi modes outputs delta hd T
      ⟨hT.le, le_rfl⟩).mono_set (by simpa only [Set.uIcc_of_le hab, Set.uIcc_of_le hT.le] using hsubI)
  have hz : IntervalIntegrable (fun τ ↦ ∫ x : T3,
      ‖residual chi modes (s.coefficients τ) x‖ ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab ((continuousOn_spatialIntegral _
      ((continuous_residual_spaceTime s g hSum hu2 chi modes).norm.pow 2)).mono hsubI)
  obtain ⟨hf, hbalance⟩ := LocalAlignmentEnergyBudget.intervalIntegral_materialRate_eq_energy
    s hB g hg hSum hu chi C hchi modes outputs hcut hchir hsub hout hs hk delta a b hab hI
  have hdom : ∀ᵐ τ ∂volume.restrict (Set.Ioo a b),
      (∫ x : T3, materialRate chi modes outputs (s.coefficients τ) delta nu x) +
        (1 / 4 : ℝ) * (∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
        ∫ x : T3, budgetSource chi modes outputs (s.coefficients τ) delta nu x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      LocalAlignmentEnergyBudget.ae_integrable_materialRate s hB g hg hSum hu chi C hchi modes outputs
        hcut hchir hsub hout hs hk delta a b hab hI] with τ hτ hF
    have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsubI (Set.Ioo_subset_Icc_self hτ)))
    rw [integral_budgetSource_eq chi modes outputs _
      (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hm) delta nu hd hnu.le]
    exact integral_materialRate_add_quarter_residual_le chi modes outputs _ hm delta nu hd hnu.le hF
  rw [restrict_Ioo_eq_restrict_Icc] at hdom
  have h := intervalIntegral.integral_mono_ae_restrict hab (hf.add (hz.const_mul (1 / 4 : ℝ))) hR hdom
  rw [intervalIntegral.integral_add hf (hz.const_mul (1 / 4 : ℝ)), intervalIntegral.integral_const_mul,
    hbalance] at h
  linarith only [h]

theorem meanEnergy_add_quarter_integral_residual_le_initial
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    meanEnergy chi modes (s.coefficients t) delta +
      (1 / 4 : ℝ) * (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes u₀ delta +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, budgetSource chi modes outputs (s.coefficients τ) delta nu x := by
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hA : ContinuousOn (fun τ ↦ meanEnergy chi modes (s.coefficients τ) delta) (Set.Icc 0 T) :=
    continuousOn_spatialIntegral _ (continuous_alignmentEnergy_spaceTime s g hSum hu2 chi modes delta)
  have hZ : ContinuousOn (fun τ ↦ (1 / 4 : ℝ) * (∫ x : T3,
      ‖residual chi modes (s.coefficients τ) x‖ ^ 2)) (Set.Icc 0 T) :=
    continuousOn_const.mul (continuousOn_spatialIntegral _ ((continuous_residual_spaceTime s g hSum hu2 chi modes).norm.pow 2))
  have hR : IntegrableOn (fun τ ↦ ∫ x : T3,
      budgetSource chi modes outputs (s.coefficients τ) delta nu x) (Set.Icc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mp
      (intervalIntegrable_budgetSource s hnu.le g hg hSum hu2 chi C hchi modes outputs delta hd T ⟨hT.le, le_rfl⟩)
  have h := intervalIntegral.endpoint_estimate_of_interior_of_integrable (C := 0) hT hA hZ.integrableOn_Icc hR
    (fun a b ha hab hb ↦ by
      simpa only [add_zero, intervalIntegral.integral_const_mul] using meanEnergy_add_quarter_integral_residual_le
        s hnu hT hB g hg hSum hu chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd a b hab.le
        (fun _ hτ ↦ ⟨ha.trans_le hτ.1, hτ.2.trans_lt hb⟩)) t ht
  simpa only [s.initial, add_zero, intervalIntegral.integral_const_mul] using h

end Solution

/-- One actual unforced local solution satisfies the direct-tilt budget
for every admissible finite strain filter and positive energy regularizer. -/
theorem exists_physical_localTiltAlignmentEnergy (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hdiv : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B,
      ∀ (chi : Wavevector → ℂ) (C : ℝ), (∀ q, ‖chi q‖ ≤ C) →
      ∀ modes outputs : Finset Wavevector, (∀ q, q ∉ modes → chi q = 0) →
      (∀ q, chi (-q) = conj (chi q)) → modes ⊆ outputs →
      (∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs) →
      (∀ k, -k ∈ modes ↔ k ∈ modes) → (∀ k ∈ modes, frequencyVec k ≠ 0) →
      ∀ delta > (0 : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) T,
      meanEnergy chi modes (s.coefficients t) delta +
        (1 / 4 : ℝ) * (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes (torusFourierVelocity f) delta +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, budgetSource chi modes outputs (s.coefficients τ) delta nu x := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hdiv hzero
  refine ⟨T, hT, B, hB, s, ?_⟩
  intro chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd t ht
  exact meanEnergy_add_quarter_integral_residual_le_initial
    s hnu hT hB g hg hSum hu chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd t ht

end Mettapedia.FluidDynamics.NavierStokes.LocalTiltAlignmentEnergy
