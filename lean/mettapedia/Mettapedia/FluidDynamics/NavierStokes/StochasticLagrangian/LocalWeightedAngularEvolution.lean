import Mettapedia.Analysis.WeightedCrossProductEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TraceFreeWeightedAngularRate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityPairAngle
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityAngularPayment

/-!
# Smooth angular cost and its actual material endpoint rate

A symmetric polynomial cost bounds the previously constructed angular
integral within a factor of two. Its endpoint evolution is derived from
the actual local vorticity equation, including zero vorticity. Amplitude
growth, strain variation and viscosity remain signed and explicit.
Kernel transport and a time-integrated upper bound are not supplied here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalWeightedAngularEvolution

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths PancakeLocalMaterialTrajectories
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentForcing LocalVorticityPairAngle
open Mettapedia.Analysis WeightedCrossProduct VorticityAngularPayment

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "H" => PeriodicRieszOperator.kernel (d := 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def pairEnergy (n : ℕ) (u : FourierVelocity) (x y : T3) : ℝ :=
  energy n (fullVorticity u x) (fullVorticity u y)

def materialPairRate (n : ℕ) (u : FourierVelocity) (nu : ℝ) (x y : T3) : ℝ :=
  strainRate n (fullStrainOperator u x) (fullStrainOperator u y)
      (fullVorticity u x) (fullVorticity u y) +
    perturbationRate n (fullStrainOperator u x) (fullStrainOperator u y)
      (fullVorticity u x) (fullVorticity u y)
      (nu • fullVorticityLaplacian u x) (nu • fullVorticityLaplacian u y)

theorem continuous_pairEnergy (n : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    Continuous (fun p : T3 × T3 ↦ pairEnergy n u p.1 p.2) := by
  have hw := continuous_fullVorticity u hu
  have ha : Continuous (fun p : T3 × T3 ↦ fullVorticity u p.1) := hw.comp continuous_fst
  have hb : Continuous (fun p : T3 × T3 ↦ fullVorticity u p.2) := hw.comp continuous_snd
  unfold pairEnergy WeightedCrossProduct.energy WeightedCrossProduct.amplitudeWeight
  exact ((ha.norm.pow _).add (hb.norm.pow _)).mul
    ((SignedCrossKernel.continuous_cross.comp (ha.prodMk hb)).norm.pow 2)

def symmetricAngularIntegral (N : ℕ) (u : FourierVelocity) : ℝ :=
  ∫ h : T3, ∫ x : T3, ‖h‖ * ‖H N h‖ * pairEnergy 2 u x (x - h)

theorem integrable_symmetricAngularDensity (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    Integrable (fun p : T3 × T3 ↦ ‖p.1‖ * ‖H N p.1‖ * pairEnergy 2 u p.2 (p.2 - p.1))
      ((volume : Measure T3).prod volume) := by
  have ht : Continuous (fun p : T3 × T3 ↦ (p.2, p.2 - p.1)) :=
    continuous_snd.prodMk (continuous_snd.sub continuous_fst)
  have hc := (continuous_pairEnergy 2 u hu).comp ht
  let f : C(T3 × T3, ℝ) := ⟨fun p ↦ pairEnergy 2 u p.2 (p.2 - p.1), hc⟩
  exact IntegrableKernelPairing.integrable_mul _ _
    ((PeriodicRieszNearMoment.integrable_firstMoment (d := 3) N).comp_fst (volume : Measure T3)) f

theorem angularIntegral_le_symmetric (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    angularIntegral N u ≤ symmetricAngularIntegral N u := by
  have ha := integrable_angularDensity N u hu
  have hs := integrable_symmetricAngularDensity N u hu
  rw [angularIntegral, symmetricAngularIntegral, ← integral_prod _ ha, ← integral_prod _ hs]
  apply integral_mono ha hs
  intro p
  have h := mul_le_mul_of_nonneg_left
    (max_weight_le_energy 2 (fullVorticity u p.2) (fullVorticity u (p.2 - p.1)))
      (show 0 ≤ ‖p.1‖ * ‖H N p.1‖ by positivity)
  simpa only [pairEnergy, SignedCrossKernel.angularCost, show 2 * (2 + 1) = 2 * 3 from rfl,
    mul_assoc] using h

theorem symmetricAngularIntegral_le_two (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    symmetricAngularIntegral N u ≤ 2 * angularIntegral N u := by
  have ha := integrable_angularDensity N u hu
  have hs := integrable_symmetricAngularDensity N u hu
  rw [angularIntegral, symmetricAngularIntegral, ← integral_prod _ ha, ← integral_prod _ hs,
    ← integral_const_mul]
  apply integral_mono hs (ha.const_mul 2)
  intro p
  have h := mul_le_mul_of_nonneg_left
    (energy_le_two_max_weight 2 (fullVorticity u p.2) (fullVorticity u (p.2 - p.1)))
      (show 0 ≤ ‖p.1‖ * ‖H N p.1‖ by positivity)
  simpa only [pairEnergy, SignedCrossKernel.angularCost, show 2 * (2 + 1) = 2 * 3 from rfl,
    mul_assoc, mul_left_comm] using h

theorem abs_source_le_half_dissipation_add_symmetric (nu : ℝ) (hnu : 0 < nu) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    |VorticityRegularizedSource.source 6 N u| ≤
      nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u +
        (24 * (PeriodicRieszNearMoment.firstMomentBound 3 + 1) / nu) * symmetricAngularIntegral N u := by
  have hc : 0 ≤ 24 * (PeriodicRieszNearMoment.firstMomentBound 3 + 1) / nu := by
    positivity [PeriodicRieszNearMoment.firstMomentBound_nonneg 3]
  exact (abs_source_le_half_dissipation_add_angular nu hnu N u hu).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left (angularIntegral_le_symmetric N u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)) hc) _)

theorem materialPairRate_add_defect_le_growth (n : ℕ) (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ k, modeDot k (u k) = 0) (x y : T3) :
    materialPairRate n u nu x y + (2 * (n + 1) : ℝ) *
      TraceFreeWeightedAngularRate.weightedTopDefect n (LocalInitialSpectral.fullSymmetricStrain u x)
        (LocalInitialSpectral.fullSymmetricStrain u y) (fullVorticity u x) (fullVorticity u y) *
          ‖EuclideanCrossProduct.cross (fullVorticity u x) (fullVorticity u y)‖ ^ 2 ≤
      TraceFreeWeightedAngularRate.growthWeight n (LocalInitialSpectral.fullSymmetricStrain u x)
        (LocalInitialSpectral.fullSymmetricStrain u y) (fullVorticity u x) (fullVorticity u y) *
          ‖EuclideanCrossProduct.cross (fullVorticity u x) (fullVorticity u y)‖ ^ 2 +
        perturbationRate n (fullStrainOperator u x) (fullStrainOperator u y)
          (fullVorticity u x) (fullVorticity u y)
          (nu • fullVorticityLaplacian u x) (nu • fullVorticityLaplacian u y) := by
  have h := TraceFreeWeightedAngularRate.strainRate_add_defect_le_growth n
    (LocalInitialSpectral.fullSymmetricStrain u x) (LocalInitialSpectral.fullSymmetricStrain u y)
    (trace_fullStrainOperator_eq_zero u hu hd x) (trace_fullStrainOperator_eq_zero u hu hd y)
    (fullVorticity u x) (fullVorticity u y)
  unfold materialPairRate
  change strainRate n (fullStrainOperator u x) (fullStrainOperator u y)
    (fullVorticity u x) (fullVorticity u y) + _ ≤ _ at h
  linarith only [h]

/-- Actual endpoint evolution. Unlike the normalized angle equation,
this identity needs no nonvanishing hypotheses at either endpoint. -/
theorem hasDerivAt_pairEnergy_path {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X Y : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
    (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t) (n : ℕ) :
    HasDerivAt (fun τ ↦ pairEnergy n (s.coefficients τ) (torusPoint (X τ)) (torusPoint (Y τ)))
      (materialPairRate n (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t))) t := by
  have hx := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  have hy := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI Y t ht hY
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
    (hu t (Set.Ioo_subset_Icc_self (hI (Set.Ioo_subset_Icc_self ht))))
  have hm₂ := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hm
  exact hasDerivAt_energy_strain n _ _ _ _ hx hy
    (cross_fullStrain_apply_add _ hm₂ (s.transverse t) _ _ _)
    (cross_fullStrain_apply_add _ hm₂ (s.transverse t) _ _ _)

end Mettapedia.FluidDynamics.NavierStokes.LocalWeightedAngularEvolution
