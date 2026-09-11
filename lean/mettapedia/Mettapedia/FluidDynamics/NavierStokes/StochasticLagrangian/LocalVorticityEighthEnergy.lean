import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityEighthContinuity
import Mettapedia.Analysis.IntegralEndpointEstimate

/-!+# The eighth-moment balance for an actual local periodic solution

Incompressible transport preserves the spatial mean. Combining its weak
chain rule with the full vorticity equation gives the time-integrated
eighth-moment identity, including the initial endpoint. The signed stretching
source is retained; the identity alone does not bound it or continue a solution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment

open scoped Topology ComplexConjugate
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeLocalInfiniteVelocity PancakeHigherDerivativeMoments
open PancakeMaterialChainRule LocalAlignmentContinuity LocalSpaceTimeExtension
open GaussianRootWeightedIncrement (weightedPalinstrophyDensity)

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance eighthEnergyCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance eighthEnergyCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance eighthEnergyCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def meanEnergy (u : FourierVelocity) : ℝ := ∫ x : T3, energy u x
def weightedPalinstrophy (u : FourierVelocity) : ℝ := ∫ x : T3, weightedPalinstrophyDensity u x
def radialDissipation (u : FourierVelocity) : ℝ := ∫ x : T3, radialGradientDensity u x
def stretching (u : FourierVelocity) : ℝ := ∫ x : T3, stretchingDensity u x

theorem meanEnergy_nonneg (u : FourierVelocity) : 0 ≤ meanEnergy u :=
  integral_nonneg (fun x ↦ by unfold energy; positivity)

theorem weightedPalinstrophy_nonneg (u : FourierVelocity) : 0 ≤ weightedPalinstrophy u :=
  integral_nonneg (fun x ↦ by unfold weightedPalinstrophyDensity; positivity)

theorem radialDissipation_nonneg (u : FourierVelocity) : 0 ≤ radialDissipation u :=
  integral_nonneg (radialGradientDensity_nonneg u)

def frozenMaterialRate (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) : ℝ :=
  scalarMaterialRate (fun τ ↦ energy (u τ)) (LocalMeanAlignmentBalance.velocity (u t)) t x

theorem frozenMaterialRate_eq_deriv (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) :
    frozenMaterialRate u t x = deriv (frozenEnergy u t x) 0 := rfl

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)

include hSum hu in
theorem continuousOn_meanEnergy : ContinuousOn (fun t ↦ meanEnergy (s.coefficients t)) (Set.Icc 0 T) :=
  continuousOn_spatialIntegral _ (continuous_energy_spaceTime s g hSum hu)

include hSum hu in
theorem continuousOn_weightedPalinstrophy :
    ContinuousOn (fun t ↦ weightedPalinstrophy (s.coefficients t)) (Set.Icc 0 T) :=
  continuousOn_spatialIntegral _ (continuous_weightedPalinstrophyDensity_spaceTime s g hSum hu)

include hSum hu in
theorem continuousOn_radialDissipation :
    ContinuousOn (fun t ↦ radialDissipation (s.coefficients t)) (Set.Icc 0 T) :=
  continuousOn_spatialIntegral _ (continuous_radialGradientDensity_spaceTime s g hSum hu)

include hSum hu in
theorem continuousOn_stretching : ContinuousOn (fun t ↦ stretching (s.coefficients t)) (Set.Icc 0 T) :=
  continuousOn_spatialIntegral _ (continuous_stretchingDensity_spaceTime s g hSum hu)

section Interior

variable (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)

include hI hSum hu in
theorem continuous_extendedEnergy :
    Continuous (fun z : ℝ × T3 ↦ energy (coefficients s a b hab z.1) z.2) := by
  let time : ℝ → Set.Icc (0 : ℝ) T := fun t ↦
    ⟨Set.projIcc a b hab t, Set.Ioo_subset_Icc_self (hI (Set.projIcc a b hab t).2)⟩
  have hp : Continuous (fun t : ℝ ↦ (Set.projIcc a b hab t : ℝ)) :=
    continuous_subtype_val.comp (LipschitzWith.projIcc hab).continuous
  have hc : Continuous time := hp.subtype_mk _
  exact (continuous_energy_spaceTime s g hSum hu).comp
    (f := fun z : ℝ × T3 ↦ (time z.1, z.2)) ((hc.comp continuous_fst).prodMk continuous_snd)

include hI hg hSum hu in
theorem locallyLipschitz_extendedEnergy :
    LocallyLipschitz (fun z : ℝ × X3 ↦ energy (coefficients s a b hab z.1) (torusPoint z.2)) := by
  have hp : ContDiff ℝ 1 (fun w : R3 ↦ (‖w‖ ^ 2) ^ 4) := (contDiff_id.norm_sq ℝ).pow 4
  exact hp.locallyLipschitz.comp
    (LocalSpaceTimeExtension.locallyLipschitz_fullVorticity s a b hab hI g hg hSum hu)

theorem frozenMaterialRate_extension_eq (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : T3) :
    frozenMaterialRate (coefficients s a b hab) t x = frozenMaterialRate s.coefficients t x := by
  unfold frozenMaterialRate scalarMaterialRate
  rw [coefficients_eq s a b hab t (Set.Ioo_subset_Icc_self ht)]
  apply Filter.EventuallyEq.deriv_eq
  have hc : Filter.Tendsto (fun h : ℝ ↦ t + h) (𝓝 0) (𝓝 t) := by
    have hc : ContinuousAt (fun h : ℝ ↦ t + h) 0 := by fun_prop
    simpa only [ContinuousAt, add_zero] using hc
  filter_upwards [hc.eventually (Icc_mem_nhds ht.1 ht.2)] with h hh
  rw [coefficients_eq s a b hab (t + h) hh]

include hab hI hg hSum hu in
/-- The material rate is integrable in time and has the actual endpoint difference. -/
theorem intervalIntegral_materialRate_eq_meanEnergy :
    IntervalIntegrable (fun t ↦ ∫ x : T3, materialRate (s.coefficients t) nu x) volume a b ∧
      (∫ t in a..b, ∫ x : T3, materialRate (s.coefficients t) nu x) =
        meanEnergy (s.coefficients b) - meanEnergy (s.coefficients a) := by
  have h := PancakeMeanMaterialBalance.intervalIntegral_materialRate_eq
    (fun t ↦ energy (coefficients s a b hab t))
    (fun t ↦ LocalMeanAlignmentBalance.velocity (coefficients s a b hab t))
    (continuous_extendedEnergy s g hSum hu a b hab hI)
    (fun _ ↦ LocalMeanAlignmentBalance.continuous_velocity _)
    (locallyLipschitz_extendedEnergy s g hg hSum hu a b hab hI)
    (LocalMeanAlignmentBalance.locallyLipschitz_extendedVelocity s a b hab hI g hSum hu)
    (fun t ↦ Filter.Eventually.of_forall
      (LocalMeanAlignmentBalance.divergence_extendedVelocity s a b hab hI g hSum hu t)) a b
  change IntervalIntegrable (fun t ↦ ∫ x : T3, frozenMaterialRate (coefficients s a b hab) t x) volume a b ∧
    (∫ t in a..b, ∫ x : T3, frozenMaterialRate (coefficients s a b hab) t x) =
      meanEnergy (coefficients s a b hab b) - meanEnergy (coefficients s a b hab a) at h
  rw [coefficients_eq s a b hab b ⟨hab, le_rfl⟩, coefficients_eq s a b hab a ⟨le_rfl, hab⟩] at h
  have he : Set.EqOn
      (fun t ↦ ∫ x : T3, frozenMaterialRate (coefficients s a b hab) t x)
      (fun t ↦ ∫ x : T3, materialRate (s.coefficients t) nu x) (Set.uIoo a b) := by
    intro t ht
    have ht' : t ∈ Set.Ioo a b := by simpa only [Set.uIoo_of_le hab] using ht
    apply integral_congr_ae
    filter_upwards [] with x
    rw [frozenMaterialRate_extension_eq s a b hab t ht' x, frozenMaterialRate_eq_deriv]
    exact (hasDerivAt_frozenEnergy s g hg hSum hu a b hab hI t ht' x).deriv
  exact ⟨h.1.congr_uIoo he, (intervalIntegral.integral_congr_uIoo he).symm.trans h.2⟩

include hab hI hg hSum hu in
theorem interior_energy_identity :
    meanEnergy (s.coefficients b) / 8 +
      (∫ t in a..b, nu * weightedPalinstrophy (s.coefficients t) +
        6 * nu * radialDissipation (s.coefficients t)) =
    meanEnergy (s.coefficients a) / 8 + ∫ t in a..b, stretching (s.coefficients t) := by
  have hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) T := hI.trans Set.Ioo_subset_Icc_self
  have hG := ((continuousOn_weightedPalinstrophy s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hR := ((continuousOn_radialDissipation s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hab
  obtain ⟨hM, he⟩ := intervalIntegral_materialRate_eq_meanEnergy s g hg hSum hu a b hab hI
  have hid : (∫ t in a..b, (∫ x : T3, materialRate (s.coefficients t) nu x) / 8 +
      (nu * weightedPalinstrophy (s.coefficients t) + 6 * nu * radialDissipation (s.coefficients t))) =
      ∫ t in a..b, stretching (s.coefficients t) := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) T := hsub
      (Set.Ioo_subset_Icc_self (by simpa only [Set.uIoo_of_le hab] using ht))
    have hu' := hSum.of_nonneg_of_le (fourierMoment_nonneg 3 _) (hu t ht')
    simpa only [weightedPalinstrophy, radialDissipation, stretching, add_assoc] using
      integral_materialRate_add_dissipation_eq (s.coefficients t) nu hu'
  have hsplit := intervalIntegral.integral_add (hM.div_const 8)
    ((hG.const_mul nu).add (hR.const_mul (6 * nu)))
  rw [hsplit, intervalIntegral.integral_div, he] at hid
  linarith only [hid]

end Interior

include hg hSum hu in
/-- Exact initial-data identity on the supplied local interval. In particular,
the signed stretching integral has not been replaced by an assumed bound. -/
theorem energy_identity (hT : 0 < T) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    meanEnergy (s.coefficients t) / 8 + nu * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) +
      6 * nu * (∫ τ in (0 : ℝ)..t, radialDissipation (s.coefficients τ)) =
    meanEnergy u₀ / 8 + ∫ τ in (0 : ℝ)..t, stretching (s.coefficients τ) := by
  have hA := (continuousOn_meanEnergy s g hSum hu).div_const 8
  have hG := continuousOn_weightedPalinstrophy s g hSum hu
  have hR := continuousOn_radialDissipation s g hSum hu
  have hS := continuousOn_stretching s g hSum hu
  have he := intervalIntegral.endpoint_identity_of_interior hT hA
    ((hG.const_mul nu).add (hR.const_mul (6 * nu))) hS
    (fun a b ha hab hb ↦ interior_energy_identity s g hg hSum hu a b hab.le
      (fun _ hτ ↦ ⟨ha.trans_le hτ.1, hτ.2.trans_lt hb⟩)) t ht
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hsplit := intervalIntegral.integral_add
    (((hG.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1).const_mul nu)
    (((hR.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1).const_mul (6 * nu))
  simp only [Pi.add_apply] at he
  rw [hsplit, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, s.initial] at he
  simpa only [add_assoc] using he

include hg hSum hu in
/-- Conditional absorption exposes the missing estimate on signed stretching.
It does not construct that estimate or assert a bound for its remainder. -/
theorem energy_add_half_dissipation_le_of_stretching_bound (hnu : 0 ≤ nu) (hT : 0 < T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (remainder : ℝ)
    (hsource : (∫ τ in (0 : ℝ)..t, stretching (s.coefficients τ)) ≤
      nu / 2 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) + remainder) :
    meanEnergy (s.coefficients t) / 8 +
      nu / 2 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) ≤
        meanEnergy u₀ / 8 + remainder := by
  have he := energy_identity s g hg hSum hu hT t ht
  have hr : 0 ≤ 6 * nu * (∫ τ in (0 : ℝ)..t, radialDissipation (s.coefficients τ)) :=
    mul_nonneg (mul_nonneg (by norm_num) hnu)
      (intervalIntegral.integral_nonneg_of_forall ht.1 (fun τ ↦ radialDissipation_nonneg _))
  linarith only [he, hr, hsource]

/-- Real, transverse, zero-mean periodic data construct the actual solution
and its common Fourier envelope. No energy identity is assumed as a field. -/
theorem exists_physical_local_energy_identity (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, PancakeContinuousCoordinateJet.HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (PancakeArbitraryDataBlocks.torusFourierVelocity f q) = 0)
    (hzero : PancakeArbitraryDataBlocks.torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (PancakeArbitraryDataBlocks.torusFourierVelocity f) T B,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          meanEnergy (s.coefficients t) / 8 +
            nu * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) +
            6 * nu * (∫ τ in (0 : ℝ)..t, radialDissipation (s.coefficients τ)) =
          meanEnergy (PancakeArbitraryDataBlocks.torusFourierVelocity f) / 8 +
            ∫ τ in (0 : ℝ)..t, stretching (s.coefficients τ) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    PancakeHigherLocalVelocity.exists_physical_localMomentEnvelope 3 nu hnu f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, energy_identity s g hg hSum hu hT⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment
