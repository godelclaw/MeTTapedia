import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAlignmentContinuity

/-!
# Signed unresolved stretching in the actual alignment budget

The discarded-strain pairing is retained with its sign. In contrast to
the Young-inequality envelope, this keeps the full residual damping and
does not introduce a squared mismatch source. The sign is not asserted
to be favorable, and the remaining nonlinear integral is not paid here.

The final theorem cancels actual full-velocity transport and pays joint
diffusion from initial energy. The scalar Eulerian chain-rule comparison
and its integrability remain explicit hypotheses.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSignedAlignmentBudget

open scoped RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeFilteredStrainDynamics PancakeGalerkinKineticEnergy PancakePhysicalLaplacian
open PancakeFourierMaterialPaths PancakeTopEigenvalueDerivative
open PancakeSpectralFiniteDifference
open PancakeSpectralDefectEvolution PancakeRegularizedMaterialRate PancakeSpectralDefectBudget
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeFourierStrainGradient
open PancakeWeakIncompressibleTransport PancakeLocalInfiniteVelocity InfiniteConvectionEnergy
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentTransport
open LocalAlignmentForcing LocalAlignmentContinuity LocalKineticEnergy

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def signedForcingEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) : ℝ :=
  2 * ‖nonviscousRemainder chi modes outputs u x‖ * ‖fullVorticity u x‖ ^ 2 +
    2 * ⟪residual chi modes u x, strainMismatch chi modes u x⟫ +
    2 * delta * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫

theorem resolved_add_strainMismatch (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    (spatialStrain modes (filteredVelocity chi u) x).1 (fullVorticity u x) +
      strainMismatch chi modes u x = fullStrainOperator u x (fullVorticity u x) := by
  simp only [strainMismatch, sub_apply]
  abel

theorem materialRate_signed_le (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3) :
    materialRate chi modes outputs u delta nu x + ‖residual chi modes u x‖ ^ 2 ≤
      nu * linearRate (spatialStrain modes (filteredVelocity chi u) x) delta (fullVorticity u x)
        (strainLaplacian modes (filteredVelocity chi u) x) (fullVorticityLaplacian u x) +
      signedForcingEnvelope chi modes outputs u delta x := by
  have hR := (le_abs_self (remainderAnisotropy (nonviscousRemainder chi modes outputs u x)
    (topVector (spatialStrain modes (filteredVelocity chi u) x)) (fullVorticity u x))).trans
      (abs_remainderAnisotropy_le _ _ _ (topVector_norm _))
  unfold materialRate
  rw [linearRate_viscous_split, resolved_add_strainMismatch]
  unfold signedForcingEnvelope LocalAlignmentForcing.residual
  linarith

theorem continuous_signedForcingEnvelope (chi : Wavevector → ℂ)
    (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (delta : ℝ) :
    Continuous (signedForcingEnvelope chi modes outputs u delta) := by
  have hw := continuous_fullVorticity u hu
  exact (((continuous_const.mul (continuous_nonviscousRemainder chi modes outputs u).norm).mul
      (hw.norm.pow 2)).add
    (continuous_const.mul ((continuous_residual chi modes u hu).inner
      (continuous_strainMismatch chi modes u hu)))).add
    (continuous_const.mul (hw.inner ((continuous_fullStrainOperator u hu).clm_apply hw)))

theorem integral_materialRate_lower_bound_paid
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu)
    (F : T3 → ℝ) (hF : Integrable F)
    (hpoint : ∀ᵐ x : T3, F x ≤ materialRate chi modes outputs u delta nu x) :
    (∫ x : T3, F x) + (∫ x : T3, ‖residual chi modes u x‖ ^ 2) ≤
      (16 * nu / delta) * strainGradientCutoffWeight modes chi * kineticEnergy u * kineticEnergy (fourierCurl u) +
      ∫ x : T3, signedForcingEnvelope chi modes outputs u delta x := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hres : Integrable (fun x : T3 ↦ ‖residual chi modes u x‖ ^ 2) volume :=
    ((continuous_residual chi modes u hu1).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (signedForcingEnvelope chi modes outputs u delta) volume :=
    (continuous_signedForcingEnvelope chi modes outputs u hu1 delta).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_laplacian_diffusion_energy_paid modes chi u hu
    (fun x ↦ F x + ‖residual chi modes u x‖ ^ 2)
    (signedForcingEnvelope chi modes outputs u delta) delta nu hd hnu (hF.add hres) hR (by
      filter_upwards [hpoint] with x hx
      have hr := materialRate_signed_le chi modes outputs u delta nu x
      linarith)
  rw [integral_add hF hres] at h
  exact h

/-- Weak periodic transport is canceled for the actual full fields. -/
theorem integral_eulerian_lower_bound_paid
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hdiv : ∀ q, modeDot q (u q) = 0)
    (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu)
    (F : T3 → ℝ) (hF : Integrable F)
    (hpoint : ∀ᵐ x : T3, F x + coordinateTransport (alignmentEnergy chi modes u delta)
      (InfiniteFourierTransport.velocityComponent u) x ≤ materialRate chi modes outputs u delta nu x) :
    (∫ x : T3, F x) + (∫ x : T3, ‖residual chi modes u x‖ ^ 2) ≤
      (16 * nu / delta) * strainGradientCutoffWeight modes chi * kineticEnergy u * kineticEnergy (fourierCurl u) +
      ∫ x : T3, signedForcingEnvelope chi modes outputs u delta x := by
  have ht := integral_alignmentEnergy_transport_zero chi modes u
    (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) hdiv delta
  have h := integral_materialRate_lower_bound_paid chi modes outputs u hu delta nu hd hnu _
    (hF.add ht.1) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hF ht.1, ht.2, add_zero] at h
  exact h

variable {nu T B : ℝ} {u₀ : FourierVelocity}

theorem continuous_signedForcingEnvelope_spaceTime
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (delta : ℝ) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      signedForcingEnvelope chi modes outputs (s.coefficients z.1) delta z.2) := by
  have hc (q : Wavevector) (i : Fin 3) :
      Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q i) :=
    (s.continuous q i).comp continuous_subtype_val
  have hw := continuous_fullVorticity_spaceTime s g hSum hu
  have hR := continuous_nonviscousRemainder_parametric _ hc g hg hSum (fun t ↦ hu t t.2)
    chi C hchi modes outputs
  have hS := continuous_fullStrainOperator_parametric _ hc g hSum (fun t ↦ hu t t.2)
  exact (((continuous_const.mul hR.norm).mul (hw.norm.pow 2)).add
    (continuous_const.mul ((continuous_residual_spaceTime s g hSum hu chi modes).inner
      (continuous_strainMismatch_spaceTime s g hSum hu chi modes)))).add
    (continuous_const.mul (hw.inner (hS.clm_apply hw)))

/-- This is an initial-energy diffusion payment with signed nonlinear
feedback. It does not assert that the supplied F is the time derivative. -/
theorem spacetime_eulerian_lower_bound_paid
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 < nu)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (delta : ℝ) (hd : 0 < delta)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (F : ℝ → T3 → ℝ)
    (hFx : ∀ᵐ τ ∂volume.restrict (Set.Icc (0 : ℝ) t), Integrable (F τ))
    (hFt : IntervalIntegrable (fun τ ↦ ∫ x : T3, F τ x) volume 0 t)
    (hpoint : ∀ᵐ τ ∂volume.restrict (Set.Icc (0 : ℝ) t), ∀ᵐ x : T3,
      F τ x + coordinateTransport (alignmentEnergy chi modes (s.coefficients τ) delta)
        (InfiniteFourierTransport.velocityComponent (s.coefficients τ)) x ≤
          materialRate chi modes outputs (s.coefficients τ) delta nu x) :
    (∫ τ in (0 : ℝ)..t, ∫ x : T3, F τ x) +
      (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      4 * strainGradientCutoffWeight modes chi * kineticEnergy u₀ ^ 2 / delta +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, signedForcingEnvelope chi modes outputs (s.coefficients τ) delta x := by
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hRt : IntervalIntegrable (fun τ ↦ ∫ x : T3,
      signedForcingEnvelope chi modes outputs (s.coefficients τ) delta x) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_spatialIntegral _
      (continuous_signedForcingEnvelope_spaceTime s g hg hSum hu2 chi C hchi modes outputs delta)).mono
        (fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩))
  have hres := intervalIntegrable_residual_sq s g hSum hu2 chi modes t ht
  have hb : ∀ᵐ τ ∂volume.restrict (Set.Icc (0 : ℝ) t),
      (∫ x : T3, F τ x) + (∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) -
        (∫ x : T3, signedForcingEnvelope chi modes outputs (s.coefficients τ) delta x) ≤
      ((16 * nu / delta) * strainGradientCutoffWeight modes chi) *
        (kineticEnergy (s.coefficients τ) * kineticEnergy (fourierCurl (s.coefficients τ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hFx, hpoint] with τ hτ hx hp
    have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ ⟨hτ.1, hτ.2.trans ht.2⟩)
    have h := integral_eulerian_lower_bound_paid chi modes outputs _ hm (s.transverse τ)
      delta nu hd hnu.le (F τ) hx hp
    nlinarith
  have h := integral_le_of_energy_enstrophy_majorant_ae s hnu g hg hSum hu2 t ht
    (fun τ ↦ (∫ x : T3, F τ x) + (∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) -
      ∫ x : T3, signedForcingEnvelope chi modes outputs (s.coefficients τ) delta x)
    ((16 * nu / delta) * strainGradientCutoffWeight modes chi)
    (mul_nonneg (by positivity) (strainGradientCutoffWeight_nonneg modes chi))
    ((hFt.add hres).sub hRt) hb
  rw [intervalIntegral.integral_sub (hFt.add hres) hRt,
    intervalIntegral.integral_add hFt hres] at h
  have he : (16 * nu / delta * strainGradientCutoffWeight modes chi) * kineticEnergy u₀ ^ 2 /
      (4 * nu) = 4 * strainGradientCutoffWeight modes chi * kineticEnergy u₀ ^ 2 / delta := by
    field_simp
    ring
  rw [he] at h
  linarith

end Mettapedia.FluidDynamics.NavierStokes.LocalSignedAlignmentBudget
