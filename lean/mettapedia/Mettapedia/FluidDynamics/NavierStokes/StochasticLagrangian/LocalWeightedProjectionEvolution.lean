import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalHelicityRotationFlux

/-!
# Sixth-power-weighted projection energy on actual material paths

The weighted projection functional is controlled spatially by octic
dissipation, not by the octic energy. Its exact material derivative retains
the change of weight, as well as the full viscous contribution. The rotation
flux identity does not justify discarding these terms or claiming coercivity
of an energy minus this gradient-dependent functional.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalWeightedProjectionEvolution

open MeasureTheory Mettapedia.Analysis
open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories
open PancakeFourierMaterialPaths LocalMaterialVorticity LocalLowDiffusionBudget LocalJointDiffusionBudget
open LocalAlignmentForcing LocalVariableHelicityCenter LocalWeightedCurlCancellation
open LocalHelicityProjectionEvolution LocalHelicityProjectionDiffusion LocalHelicityRotationFlux
open GaussianRootWeightedIncrement
open LocalVorticityEighthMoment

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def weightedProjectionDensity (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ‖fullVorticity u x‖ ^ 6 * projectionEnergy δ u x

def weightedProjectionEnergy (δ : ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, weightedProjectionDensity δ u x

def amplitudeStrainRate (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  6 * ‖fullVorticity u x‖ ^ 4 *
    ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫ * projectionEnergy δ u x

def weightedViscousRate (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  6 * ‖fullVorticity u x‖ ^ 4 *
    ⟪fullVorticity u x, fullVorticityLaplacian u x⟫ * projectionEnergy δ u x +
  ‖fullVorticity u x‖ ^ 6 * projectionViscousRate δ u x

theorem weightedProjectionDensity_nonneg (δ : ℝ) (hδ : 0 ≤ δ) (u : FourierVelocity) (x : T3) :
    0 ≤ weightedProjectionDensity δ u x :=
  mul_nonneg (by positivity) (RegularizedProjection.energy_nonneg δ hδ _ _)

theorem weightedProjectionDensity_le (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (x : T3) :
    weightedProjectionDensity δ u x ≤ 2 * weightedPalinstrophyDensity u x := by
  have hJ := RegularizedProjection.energy_le_norm_sq δ hδ
    (fullVorticity u x) (fullVorticity (fourierCurl u) x)
  have hc := WeightedCurlCancellation.norm_curlJet_sq_le (fun j ↦ LocalSpatialVorticityJets.fullCurlGradient u j x)
  rw [← fullVorticity_curl_eq_curlJet u hu x] at hc
  apply (mul_le_mul_of_nonneg_left (hJ.trans hc) (by positivity : 0 ≤ ‖fullVorticity u x‖ ^ 6)).trans_eq
  unfold weightedPalinstrophyDensity
  ring

theorem continuous_weightedProjectionDensity (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) : Continuous (weightedProjectionDensity δ u) := by
  have ha := continuous_fullVorticity u (summable_firstMoment_of_second u hu)
  have hr := continuous_projectionResidual δ hδ u hu
  have hc := continuous_regularizedCenter δ hδ u hu
  exact (ha.norm.pow 6).mul ((hr.norm.pow 2).add ((hc.pow 2).const_mul δ))

/-- The payer here is dissipation, not the eighth-moment energy itself. -/
theorem weightedProjectionEnergy_le (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    weightedProjectionEnergy δ u ≤ 2 * weightedPalinstrophy u := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu
  have hI : Integrable (weightedProjectionDensity δ u) :=
    (continuous_weightedProjectionDensity δ hδ u hu2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hG : Integrable (fun x : T3 ↦ 2 * weightedPalinstrophyDensity u x) :=
    ((continuous_weightedPalinstrophyDensity u hu).const_mul 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact (integral_mono hI hG (weightedProjectionDensity_le δ hδ u hu2)).trans_eq (integral_const_mul _ _)

theorem hasDerivAt_weightedProjectionDensity {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ weightedProjectionDensity δ (s.coefficients τ) (torusPoint (X τ)))
      (amplitudeStrainRate δ (s.coefficients t) (torusPoint (X t)) +
        ‖fullVorticity (s.coefficients t) (torusPoint (X t))‖ ^ 6 *
          projectionInviscidRate δ (s.coefficients t) (torusPoint (X t)) +
        ν * weightedViscousRate δ (s.coefficients t) (torusPoint (X t))) t := by
  have ha := hasDerivAt_vorticityAlong s g hg hSum
    (fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu τ hτ q)) X hX t ht
  have hJ := hasDerivAt_projectionEnergy s g hg hSum hu X hX δ hδ t ht
  have h := (ha.norm_sq.fun_pow 3).mul hJ
  simp only [← pow_mul, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat] at h
  apply h.congr_deriv
  simp only [amplitudeStrainRate, weightedViscousRate, vorticityAlong, strainAlong, diffusionAlong,
    fullVorticity, fullStrainOperator, fullVorticityLaplacian, PancakeLocalSpatialVelocity.spatialField,
    inner_add_right, real_inner_smul_right]
  ring

end Mettapedia.FluidDynamics.NavierStokes.LocalWeightedProjectionEvolution
