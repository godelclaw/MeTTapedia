import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityEighthMoment
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalClusterMaterialRate

/-!
# Spatial integration of the eighth-moment vorticity balance

The polynomial energy flux has zero periodic divergence. This removes the
energy Laplacian after spatial integration and leaves both positive
dissipation densities against the signed vortex-stretching source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment

open scoped RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeHaarTransportRate PancakeFourierTranslationCurve
open PancakeDyadicDirectionEvolution
open PancakeHigherDerivativeMoments LocalLowDiffusionBudget LocalSpatialVorticityJets
open LocalJointDiffusionBudget LocalAlignmentForcing PancakePeriodicWeakDerivative
open GaussianRootWeightedIncrement (weightedPalinstrophyDensity)

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem locallyLipschitz_fullCurlGradient_lift (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) :
    LocallyLipschitz (fun r : X3 ↦ fullCurlGradient u j (torusPoint r)) :=
  complexRealPartEuclideanCLM.lipschitz.locallyLipschitz.comp
    (InfiniteFourierTransport.lipschitzWith_fullFourierField_lift _
      (summable_fourierMoment_derivative 1 _ (summable_secondMoment_curl u hu) j)).locallyLipschitz

def energyFlux (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  8 * (‖fullVorticity u x‖ ^ 2) ^ 3 * ⟪fullVorticity u x, fullCurlGradient u j x⟫

theorem continuous_energyFlux (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (j : Fin 3) :
    Continuous (energyFlux u j) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  exact (((hw.norm.pow 2).pow 3).const_mul 8).mul
    (hw.inner (LocalSquaredGapGradient.continuous_fullCurlGradient u j))

theorem locallyLipschitz_energyFlux_lift (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) :
    LocallyLipschitz (fun r : X3 ↦ energyFlux u j (torusPoint r)) := by
  have hn : ContDiff ℝ 1 (fun p : R3 × R3 ↦ (‖p.1‖ ^ 2) ^ 3) :=
    (contDiff_fst.norm_sq ℝ).pow 3
  have hinner : ContDiff ℝ 1 (fun p : R3 × R3 ↦ ⟪p.1, p.2⟫) :=
    contDiff_fst.inner ℝ contDiff_snd
  have hp : ContDiff ℝ 1 (fun p : R3 × R3 ↦ 8 * (‖p.1‖ ^ 2) ^ 3 * ⟪p.1, p.2⟫) :=
    (contDiff_const.mul hn).mul hinner
  have hw := LocalAlignmentTransport.locallyLipschitz_fullVorticity u
    (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu)
  have hd := locallyLipschitz_fullCurlGradient_lift u hu j
  exact hp.locallyLipschitz.comp (g := fun r : X3 ↦
    (fullVorticity u (torusPoint r), fullCurlGradient u j (torusPoint r))) (hw.prodMk hd)

theorem hasDerivAt_energyFlux_shift (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) (x : T3) :
    HasDerivAt (fun h ↦ energyFlux u j (x + coordinateShift j h)) (energySecond u j x) 0 := by
  have hw := hasDerivAt_fullVorticity_shift u hu j x 0
  have hd := hasDerivAt_fullCurlGradient_shift u hu j x 0
  have h := ((((hw.norm_sq).fun_pow 3).const_mul 8).mul (hw.inner ℝ hd))
  apply h.congr_deriv
  rw [energySecond_eq u hu j x]
  simp only [coordinateShift_zero, add_zero, real_inner_self_eq_norm_sq, Nat.cast_ofNat]
  ring

theorem integrable_energySecond_and_integral_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) :
    Integrable (energySecond u j) ∧ (∫ x : T3, energySecond u j x) = 0 := by
  have he : shiftRate (energyFlux u j) (coordinateShift j) = energySecond u j :=
    funext (fun x ↦ (hasDerivAt_energyFlux_shift u hu j x).deriv)
  simpa only [he] using integral_coordinateRate_zero (energyFlux u j) j
    (continuous_energyFlux u hu j) (locallyLipschitz_energyFlux_lift u hu j)

theorem integrable_energyLaplacian_and_integral_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    Integrable (energyLaplacian u) ∧ (∫ x : T3, energyLaplacian u x) = 0 := by
  have h (j : Fin 3) := integrable_energySecond_and_integral_zero u hu j
  refine ⟨integrable_finsetSum _ (fun j _ ↦ (h j).1), ?_⟩
  change (∫ x : T3, ∑ j : Fin 3, energySecond u j x) = 0
  rw [integral_finsetSum _ (fun j _ ↦ (h j).1)]
  simp only [(h _).2, Finset.sum_const_zero]

theorem continuous_weightedPalinstrophyDensity (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) : Continuous (weightedPalinstrophyDensity u) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  exact (hw.norm.pow 6).mul (continuous_finsetSum _
    (fun j _ ↦ (LocalSquaredGapGradient.continuous_fullCurlGradient u j).norm.pow 2))

theorem continuous_radialGradientDensity (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) : Continuous (radialGradientDensity u) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  exact (hw.norm.pow 4).mul (continuous_finsetSum _
    (fun j _ ↦ (hw.inner (LocalSquaredGapGradient.continuous_fullCurlGradient u j)).pow 2))

theorem continuous_stretchingDensity (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) : Continuous (stretchingDensity u) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hw := continuous_fullVorticity u hu1
  exact (hw.norm.pow 6).mul (hw.inner ((continuous_fullStrainOperator u hu1).clm_apply hw))

theorem continuous_materialRate (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 3 u)) : Continuous (materialRate u nu) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hw := continuous_fullVorticity u hu1
  exact ((hw.norm.pow 6).const_mul 8).mul (hw.inner
    (((continuous_fullStrainOperator u hu1).clm_apply hw).add
      ((LocalClusterMaterialRate.continuous_fullVorticityLaplacian u hu).const_smul nu)))

/-- The spatial mean balance retains both dissipations and the signed source. -/
theorem integral_materialRate_add_dissipation_eq (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T3, materialRate u nu x) / 8 + nu * (∫ x : T3, weightedPalinstrophyDensity u x) +
      6 * nu * (∫ x : T3, radialGradientDensity u x) = ∫ x : T3, stretchingDensity u x := by
  have hiG : Integrable (weightedPalinstrophyDensity u) :=
    (continuous_weightedPalinstrophyDensity u hu).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hiR : Integrable (radialGradientDensity u) :=
    (continuous_radialGradientDensity u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiS : Integrable (stretchingDensity u) :=
    (continuous_stretchingDensity u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨hiL, hzero⟩ := integrable_energyLaplacian_and_integral_zero u hu
  have he : (∫ x : T3, materialRate u nu x) =
      ∫ x : T3, nu * energyLaplacian u x + 8 * stretchingDensity u x -
        (8 * nu) * weightedPalinstrophyDensity u x - (48 * nu) * radialGradientDensity u x := by
    apply integral_congr_ae
    filter_upwards [] with x
    have h := materialRate_sub_diffusion_add_dissipation_eq u nu hu x
    linarith only [h]
  have h1 := integral_sub (((hiL.const_mul nu).add (hiS.const_mul 8)).sub (hiG.const_mul (8 * nu)))
    (hiR.const_mul (48 * nu))
  have h2 := integral_sub ((hiL.const_mul nu).add (hiS.const_mul 8)) (hiG.const_mul (8 * nu))
  have h3 := integral_add (hiL.const_mul nu) (hiS.const_mul 8)
  simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 h3
  rw [h1, h2, h3] at he
  simp only [integral_const_mul, hzero, mul_zero, zero_add] at he
  linarith only [he]

end Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment
