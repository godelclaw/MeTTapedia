import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LongitudinalEnergyBalance

/-!
# Combined longitudinal flux and its diffusion remainder

The stretching and viscous fluxes are combined before taking a norm.
Completing the square absorbs half the longitudinal diffusion. The remaining
joint-flux square is explicit, not asserted to have an initial-data budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LongitudinalJointFlux

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeLocalInfiniteVelocity
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalAlignmentForcing LocalAlignmentContinuity
open LocalLongitudinalVorticity LongitudinalVorticityDiffusion LongitudinalCurvatureWork
open LongitudinalVorticityTime LongitudinalEnergyBalance

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def flux (ν : ℝ) (u : FourierVelocity) (j : Fin 3) (x : T3) : R3 :=
  -(fullVorticity u x j • fullStrainOperator u x (fullVorticity u x)) +
    (2 * ν) • ∑ k, fullCurlGradient u k x j • fullCurlGradient u k x

def fluxSquare (ν : ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ∑ j : Fin 3, ‖flux ν u j x‖ ^ 2

theorem fluxSquare_nonneg (ν : ℝ) (u : FourierVelocity) : 0 ≤ fluxSquare ν u :=
  integral_nonneg (fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

theorem continuous_flux (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (j : Fin 3) : Continuous (flux ν u j) := by
  have hw := continuous_fullVorticity u hu
  have hd := LocalSquaredGapGradient.continuous_fullCurlGradient u
  have hs : Continuous (fun x ↦ fullStrainOperator u x (fullVorticity u x)) := by
    exact (continuous_vorticityStretch u hu).congr (vorticityStretch_eq u hu)
  exact (((EuclideanSpace.proj j).continuous.comp hw).smul hs).neg.add
    (continuous_const.smul (continuous_finsetSum _ (fun k _ ↦
      ((EuclideanSpace.proj j).continuous.comp (hd k)).smul (hd k))))

theorem pairing_eq (ν : ℝ) (u : FourierVelocity) (x : T3) :
    (∑ j, ⟪longitudinalGradient u j x, flux ν u j x⟫) =
      -⟪∑ j, fullVorticity u x j • longitudinalGradient u j x,
          fullStrainOperator u x (fullVorticity u x)⟫ +
        (2 * ν) * ∑ k, ⟪∑ j, fullCurlGradient u k x j • longitudinalGradient u j x,
          fullCurlGradient u k x⟫ := by
  simp only [flux, inner_add_right, inner_add_left, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right, Fin.sum_univ_three]
  ring

theorem sourceWork_eq_pairing (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    sourceWork ν u = ∫ x : T3, ∑ j, ⟪longitudinalGradient u j x, flux ν u j x⟫ := by
  have hw := continuous_fullVorticity u hu
  have hd := LocalSquaredGapGradient.continuous_fullCurlGradient u
  have hq := continuous_longitudinalGradient u hu
  have hs : Continuous (fun x ↦ fullStrainOperator u x (fullVorticity u x)) :=
    (continuous_vorticityStretch u hu).congr (vorticityStretch_eq u hu)
  have hi : Integrable (fun x : T3 ↦ ⟪∑ j, fullVorticity u x j • longitudinalGradient u j x,
      fullStrainOperator u x (fullVorticity u x)⟫) :=
    ((continuous_finsetSum Finset.univ (fun j _ ↦
    ((EuclideanSpace.proj j).continuous.comp hw).smul (hq j))).inner hs).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj (k : Fin 3) : Integrable (fun x : T3 ↦
      ⟪∑ j, fullCurlGradient u k x j • longitudinalGradient u j x, fullCurlGradient u k x⟫) :=
    ((continuous_finsetSum Finset.univ (fun j _ ↦
    ((EuclideanSpace.proj j).continuous.comp (hd k)).smul (hq j))).inner (hd k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [pairing_eq]
  have hadd := integral_add hi.neg ((integrable_finsetSum Finset.univ (fun k _ ↦ hj k)).const_mul (2 * ν))
  simp only [Pi.neg_apply] at hadd
  rw [hadd, integral_neg, integral_const_mul, integral_finsetSum _ (fun k _ ↦ hj k)]
  rfl

theorem scaled_pairing_le (ν : ℝ) (u : FourierVelocity) (x : T3) :
    (2 * ν) * (∑ j, ⟪longitudinalGradient u j x, flux ν u j x⟫) ≤
      ν ^ 2 * (∑ j, ‖longitudinalGradient u j x‖ ^ 2) + ∑ j, ‖flux ν u j x‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have h := sq_nonneg ‖ν • longitudinalGradient u j x - flux ν u j x‖
  rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, mul_pow, Real.norm_eq_abs, sq_abs] at h
  nlinarith

theorem scaled_sourceWork_le (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    (2 * ν) * sourceWork ν u ≤ ν ^ 2 * dissipation u + fluxSquare ν u := by
  have hq := continuous_longitudinalGradient u hu
  have hj := continuous_flux ν u hu
  have hI : Integrable (fun x : T3 ↦ ∑ j, ⟪longitudinalGradient u j x, flux ν u j x⟫) :=
    (continuous_finsetSum Finset.univ (fun j _ ↦ (hq j).inner (hj j))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hD (j : Fin 3) : Integrable (fun x : T3 ↦ ‖longitudinalGradient u j x‖ ^ 2) :=
    ((hq j).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hJ : Integrable (fun x : T3 ↦ ∑ j, ‖flux ν u j x‖ ^ 2) :=
    (continuous_finsetSum Finset.univ (fun j _ ↦ (hj j).norm.pow 2)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have h := integral_mono (hI.const_mul (2 * ν))
    (((integrable_finsetSum Finset.univ (fun j _ ↦ hD j)).const_mul (ν ^ 2)).add hJ)
    (scaled_pairing_le ν u)
  simp only [Pi.add_apply] at h
  rw [integral_add ((integrable_finsetSum Finset.univ (fun j _ ↦ hD j)).const_mul (ν ^ 2)) hJ,
    integral_const_mul, integral_const_mul, integral_finsetSum _ (fun j _ ↦ hD j),
    ← sourceWork_eq_pairing ν u hu] at h
  exact h

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)

include hSum hu in
theorem continuous_flux_spaceTime (j : Fin 3) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ flux ν (s.coefficients z.1) j z.2) := by
  have hw := continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 4) q).trans (hu t ht q))
  have hd := LocalVorticityEighthMoment.continuous_fullCurlGradient_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu t ht q))
  have hs := continuous_fullStrainOperator_parametric (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t)
    (fun q i ↦ (s.continuous q i).comp continuous_subtype_val) g hSum
    (fun t q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 4) q).trans (hu t t.2 q))
  exact (((EuclideanSpace.proj j).continuous.comp hw).smul (hs.clm_apply hw)).neg.add
    (continuous_const.smul (continuous_finsetSum _ (fun k _ ↦
      ((EuclideanSpace.proj j).continuous.comp (hd k)).smul (hd k))))

include hSum hu in
theorem continuousOn_fluxSquare :
    ContinuousOn (fun t ↦ fluxSquare ν (s.coefficients t)) (Set.Icc (0 : ℝ) T) :=
  continuousOn_spatialIntegral _ (continuous_finsetSum _
    (fun j _ ↦ (continuous_flux_spaceTime s g hSum hu j).norm.pow 2))

include hg hSum hu in
/-- A local inequality with the exact remaining joint-flux cost. This is
not a bound for that cost in terms of initial data. -/
theorem energy_le_initial_add_fluxSquare (hB : 0 ≤ B)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ν * meanEnergy (s.coefficients t) + ν ^ 2 * (∫ τ in (0 : ℝ)..t, dissipation (s.coefficients τ)) ≤
      ν * meanEnergy u₀ + ∫ τ in (0 : ℝ)..t, fluxSquare ν (s.coefficients τ) := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have hs : IntervalIntegrable (fun τ ↦ sourceWork ν (s.coefficients τ)) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_sourceWork s g hg hSum hu hB).mono hsub)
  have hd : IntervalIntegrable (fun τ ↦ dissipation (s.coefficients τ)) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_dissipation s g hSum hu).mono hsub)
  have hf : IntervalIntegrable (fun τ ↦ fluxSquare ν (s.coefficients τ)) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_fluxSquare s g hSum hu).mono hsub)
  have h := intervalIntegral.integral_mono_on ht.1 (hs.const_mul (2 * ν))
    ((hd.const_mul (ν ^ 2)).add hf) (fun τ hτ ↦ scaled_sourceWork_le ν _
      (summable_fourierMoment_of_le _ (by omega : 1 ≤ 4)
        (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub hτ)))))
  rw [intervalIntegral.integral_add (hd.const_mul (ν ^ 2)) hf,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  have he := congrArg (fun r : ℝ ↦ ν * r) (energy_identity s g hg hSum hu hB t ht)
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.LongitudinalJointFlux
