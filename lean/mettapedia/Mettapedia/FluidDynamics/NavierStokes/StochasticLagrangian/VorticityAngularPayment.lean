import Mettapedia.Analysis.PeriodicRieszNearMoment
import Mettapedia.Analysis.SignedCrossKernelAngular
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedPayment

/-!
# Dissipation and angular costs for the actual stretching source

The inverse-distance radial increment is paid by weighted palinstrophy,
uniformly in the frequency cutoff. The accompanying angular integral is
constructed from the actual vorticity; no bound on its dynamics is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityAngularPayment

open MeasureTheory Filter PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget VorticityRegularizedIncrement VorticityRegularizedPairing
open VorticityRegularizedSource Mettapedia.Analysis SignedCrossKernel RadialPower
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

def radialIncrement (u : FourierVelocity) (h : T3) : ℝ :=
  ∫ x : T3, ‖radialPower 3 (fullVorticity u x) -
    radialPower 3 (fullVorticity u (x - h))‖ ^ 2

def inverseDistanceIncrement (N : ℕ) (u : FourierVelocity) : ℝ :=
  ∫ h : T3, (‖H N h‖ / ‖h‖) * radialIncrement u h

def angularIntegral (N : ℕ) (u : FourierVelocity) : ℝ :=
  ∫ h : T3, ∫ x : T3, angularCost 3 ‖h‖ (H N h)
    (fullVorticity u x) (fullVorticity u (x - h))

theorem radialIncrement_nonneg (u : FourierVelocity) (h : T3) :
    0 ≤ radialIncrement u h := integral_nonneg (fun _ ↦ sq_nonneg _)

theorem inverseDistanceIncrement_nonneg (N : ℕ) (u : FourierVelocity) :
    0 ≤ inverseDistanceIncrement N u :=
  integral_nonneg (fun h ↦ mul_nonneg (by positivity) (radialIncrement_nonneg u h))

theorem angularIntegral_nonneg (N : ℕ) (u : FourierVelocity) :
    0 ≤ angularIntegral N u :=
  integral_nonneg (fun _ ↦ integral_nonneg (fun _ ↦ angularCost_nonneg _ _ (norm_nonneg _) _ _ _))

theorem inverseDistanceIncrement_density_le (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) :
    (‖H N h‖ / ‖h‖) * radialIncrement u h ≤
      (48 * LocalVorticityEighthMoment.weightedPalinstrophy u) * (‖h‖ * ‖H N h‖) := by
  by_cases hh : h = 0
  · simp [hh]
  have hh' : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
  calc
    _ ≤ (‖H N h‖ / ‖h‖) * (48 * ‖h‖ ^ 2 *
        LocalVorticityEighthMoment.weightedPalinstrophy u) :=
      mul_le_mul_of_nonneg_left (increment_at_displacement_le u hu h) (by positivity)
    _ = _ := by field_simp

theorem integrable_inverseDistanceIncrement (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    Integrable (fun h : T3 ↦ (‖H N h‖ / ‖h‖) * radialIncrement u h) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hg := (continuous_radialPower 3).comp hw
  have hc : Continuous (fun p : T3 × T3 ↦
      ‖radialPower 3 (fullVorticity u p.2) -
        radialPower 3 (fullVorticity u (p.2 - p.1))‖ ^ 2) :=
    ((hg.comp continuous_snd).sub (hg.comp (continuous_snd.sub continuous_fst))).norm.pow 2
  have hm : AEStronglyMeasurable (fun h : T3 ↦ (‖H N h‖ / ‖h‖) * radialIncrement u h)
      (volume : Measure T3) :=
    ((PeriodicRieszOperator.measurable_kernel (d := 3) N).norm.div continuous_norm.measurable).aestronglyMeasurable.mul
      (hc.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure T3))).aestronglyMeasurable
  apply ((PeriodicRieszNearMoment.integrable_firstMoment N).const_mul
    (48 * LocalVorticityEighthMoment.weightedPalinstrophy u)).mono' hm
  filter_upwards [] with h
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (radialIncrement_nonneg u h))]
  exact inverseDistanceIncrement_density_le N u hu h

theorem inverseDistanceIncrement_le (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    inverseDistanceIncrement N u ≤ 48 * C₁ * LocalVorticityEighthMoment.weightedPalinstrophy u := by
  have hb := integral_mono (integrable_inverseDistanceIncrement N u hu)
    ((PeriodicRieszNearMoment.integrable_firstMoment N).const_mul
      (48 * LocalVorticityEighthMoment.weightedPalinstrophy u))
    (inverseDistanceIncrement_density_le N u hu)
  rw [integral_const_mul] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left (PeriodicRieszNearMoment.firstMoment_le (d := 3) N)
    (by positivity [LocalVorticityEighthMoment.weightedPalinstrophy_nonneg u])).trans_eq (by ring))

theorem integrable_angularDensity (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    Integrable (fun p : T3 × T3 ↦ angularCost 3 ‖p.1‖ (H N p.1)
      (fullVorticity u p.2) (fullVorticity u (p.2 - p.1)))
        ((volume : Measure T3).prod volume) := by
  have hw := continuous_fullVorticity u hu
  have ha : Continuous (fun p : T3 × T3 ↦ fullVorticity u p.2) := hw.comp continuous_snd
  have hb : Continuous (fun p : T3 × T3 ↦ fullVorticity u (p.2 - p.1)) :=
    hw.comp (continuous_snd.sub continuous_fst)
  let f : C(T3 × T3, ℝ) := ⟨fun p ↦
      max ‖fullVorticity u p.2‖ ‖fullVorticity u (p.2 - p.1)‖ ^ 6 *
        ‖EuclideanCrossProduct.cross (fullVorticity u p.2) (fullVorticity u (p.2 - p.1))‖ ^ 2,
    ((ha.norm.max hb.norm).pow 6).mul ((continuous_cross.comp (ha.prodMk hb)).norm.pow 2)⟩
  have hi := IntegrableKernelPairing.integrable_mul _ _
    ((PeriodicRieszNearMoment.integrable_firstMoment (d := 3) N).comp_fst (volume : Measure T3)) f
  simpa only [angularCost, show 2 * 3 = 6 from rfl, f, ContinuousMap.coe_mk, mul_assoc] using hi

theorem integrable_pairedDensity (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    Integrable (fun p : T3 × T3 ↦ pairedStretch n (H N p.1)
      (fullVorticity u p.2) (fullVorticity u (p.2 - p.1)))
        ((volume : Measure T3).prod volume) := by
  have hm := ((MeasurePreserving.id (volume : Measure T3)).prod
    (Measure.measurePreserving_neg (volume : Measure T3))).comp
      (measurePreserving_prod_sub_swap (volume : Measure T3) volume)
  have hi := hm.integrable_comp_of_integrable
    (VorticityRegularizedPayment.integrable_pairedStretch n N u hu)
  simpa only [Function.comp_def, Prod.map_apply, id_eq, neg_sub, sub_sub_cancel] using hi

theorem source_eq_displacement (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    source n N u = (1 / 2 : ℝ) * ∫ h : T3, ∫ x : T3,
      pairedStretch n (H N h) (fullVorticity u x) (fullVorticity u (x - h)) := by
  rw [source_eq_pairedSource n N u hu, pairedSource]
  congr 1
  have he : (∫ x : T3, ∫ y : T3, pairedStretch n (H N (x - y))
      (fullVorticity u x) (fullVorticity u y)) =
      ∫ x : T3, ∫ h : T3, pairedStretch n (H N h)
        (fullVorticity u x) (fullVorticity u (x - h)) := by
    apply integral_congr_ae
    filter_upwards [] with x
    simpa only [sub_sub_cancel] using
      (integral_sub_left_eq_self (fun y : T3 ↦ pairedStretch n (H N (x - y))
        (fullVorticity u x) (fullVorticity u y)) volume x).symm
  rw [he]
  exact (integral_integral_swap (integrable_pairedDensity n N u hu)).symm

theorem abs_source_le_increment_add_angular (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    |source 6 N u| ≤ ε / 2 * inverseDistanceIncrement N u + (2 * ε)⁻¹ * angularIntegral N u := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hp := integrable_pairedDensity 6 N u hu1
  have ha := integrable_angularDensity N u hu1
  have hr := integrable_inverseDistanceIncrement N u hu
  have hg := (continuous_radialPower 3).comp (continuous_fullVorticity u hu1)
  have hb : ∀ᵐ h : T3, |∫ x : T3, pairedStretch 6 (H N h)
      (fullVorticity u x) (fullVorticity u (x - h))| ≤
      ε * ((‖H N h‖ / ‖h‖) * radialIncrement u h) +
        ε⁻¹ * ∫ x : T3, angularCost 3 ‖h‖ (H N h)
          (fullVorticity u x) (fullVorticity u (x - h)) := by
    filter_upwards [hp.prod_right_ae, ha.prod_right_ae] with h hp' ha'
    have hd : Integrable (fun x : T3 ↦ ‖radialPower 3 (fullVorticity u x) -
        radialPower 3 (fullVorticity u (x - h))‖ ^ 2) :=
      ((hg.sub (hg.comp (continuous_id.sub continuous_const))).norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have he := (hd.const_mul (‖H N h‖ / ‖h‖)).const_mul ε
    have hb' := integral_mono hp'.abs (he.add (ha'.const_mul ε⁻¹)) (fun x ↦ by
      by_cases hh : h = 0
      · simp [hh, pairedStretch, angularCost]
      · exact abs_pairedStretch_le_increment_add_angular 3 ε ‖h‖ hε (norm_pos_iff.mpr hh)
          (H N h) (fullVorticity u x) (fullVorticity u (x - h)))
    simp only [Pi.add_apply] at hb'
    rw [integral_add he (ha'.const_mul ε⁻¹), integral_const_mul, integral_const_mul,
      integral_const_mul] at hb'
    exact abs_integral_le_integral_abs.trans hb'
  have hm := integral_mono_ae hp.integral_prod_left.abs
    ((hr.const_mul ε).add (ha.integral_prod_left.const_mul ε⁻¹)) hb
  simp only [Pi.add_apply] at hm
  rw [integral_add (hr.const_mul ε) (ha.integral_prod_left.const_mul ε⁻¹),
    integral_const_mul, integral_const_mul] at hm
  rw [source_eq_displacement 6 N u hu1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * ∫ h : T3, |∫ x : T3, pairedStretch 6 (H N h)
        (fullVorticity u x) (fullVorticity u (x - h))| :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (ε * inverseDistanceIncrement N u + ε⁻¹ * angularIntegral N u) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by simp only [mul_inv_rev]; ring

def angularAbsorptionScale (nu : ℝ) : ℝ := nu / (48 * (C₁ + 1))

theorem angularAbsorptionScale_pos (nu : ℝ) (hnu : 0 < nu) :
    0 < angularAbsorptionScale nu := by
  unfold angularAbsorptionScale
  positivity [PeriodicRieszNearMoment.firstMomentBound_nonneg 3]

/-- The unpaid term is the actual angular integral, not a free budget field. -/
theorem abs_source_le_half_dissipation_add_angular (nu : ℝ) (hnu : 0 < nu) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    |source 6 N u| ≤ nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u +
      (24 * (C₁ + 1) / nu) * angularIntegral N u := by
  have hC := PeriodicRieszNearMoment.firstMomentBound_nonneg 3
  have hε := angularAbsorptionScale_pos nu hnu
  have hs := abs_source_le_increment_add_angular _ hε N u hu
  have hp := mul_le_mul_of_nonneg_left (inverseDistanceIncrement_le N u hu)
    (show 0 ≤ angularAbsorptionScale nu / 2 by positivity)
  have hc : angularAbsorptionScale nu / 2 * (48 * C₁) ≤ nu / 2 := by
    unfold angularAbsorptionScale
    apply (mul_le_mul_iff_left₀ (show 0 < 48 * (C₁ + 1) by positivity)).mp
    field_simp
    nlinarith
  have hg := mul_le_mul_of_nonneg_right hc (LocalVorticityEighthMoment.weightedPalinstrophy_nonneg u)
  have he : (2 * angularAbsorptionScale nu)⁻¹ = 24 * (C₁ + 1) / nu := by
    unfold angularAbsorptionScale
    field_simp
    ring
  rw [he] at hs
  nlinarith only [hs, hp, hg]

end Mettapedia.FluidDynamics.NavierStokes.VorticityAngularPayment
