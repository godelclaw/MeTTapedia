import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalHelicityCenterParabolic
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPairedDiffusion

/-!
# Diffusion of the actual regularized curl-projection defect

The minimized defect energy has an indefinite Hessian. Completing its
rank-one square bounds the unfavorable viscous production by a pairing
of the projection residual with the first vorticity derivatives. The
remaining bound has no second derivative of curl vorticity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalHelicityProjectionDiffusion

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis RegularizedProjectionParabolic
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeFourierTranslationCurve PancakeHaarTransportRate
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalSpatialVorticityJets
open LocalWeightedCurlCancellation LocalVariableHelicityCenter LocalHelicityCenterParabolic

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def projectionEnergy (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  RegularizedProjection.energy δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)

def projectionFirst (δ : ℝ) (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  energyRate δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
    (fullCurlGradient u j x) (fullCurlGradient (fourierCurl u) j x)

def projectionSecond (δ : ℝ) (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  energyRate δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
      (fullCurlSecond u j x) (fullCurlSecond (fourierCurl u) j x) +
    energyCurvature δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
      (fullCurlGradient u j x) (fullCurlGradient (fourierCurl u) j x)

def projectionLaplacian (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, deriv (deriv (fun h ↦ projectionEnergy δ u (x + coordinateShift j h))) 0

def projectionViscousRate (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  energyRate δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
    (fullVorticityLaplacian u x) (fullVorticityLaplacian (fourierCurl u) x)

def projectionCurvature (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, energyCurvature δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
    (fullCurlGradient u j x) (fullCurlGradient (fourierCurl u) j x)

def residualGradientPairing (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, ⟪RegularizedProjection.residual δ (fullVorticity u x)
    (fullVorticity (fourierCurl u) x), fullCurlGradient u j x⟫ ^ 2

theorem hasDerivAt_projectionEnergy_shift (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ projectionEnergy δ u (x + coordinateShift j t))
      (projectionFirst δ u j (x + coordinateShift j h)) h :=
  RegularizedProjection.hasDerivAt_energy δ hδ
    (hasDerivAt_fullVorticity_shift u (summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu) j x h)
    (hasDerivAt_fullVorticity_shift (fourierCurl u) (summable_fourierMoment_curl 3 u hu) j x h)

theorem hasDerivAt_projectionFirst_shift (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ projectionFirst δ u j (x + coordinateShift j t))
      (projectionSecond δ u j (x + coordinateShift j h)) h := by
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu
  have hw3 := summable_fourierMoment_curl 3 u hu
  exact hasDerivAt_energyRate δ hδ
    (hasDerivAt_fullVorticity_shift u hu3 j x h)
    (hasDerivAt_fullVorticity_shift (fourierCurl u) hw3 j x h)
    (hasDerivAt_fullCurlGradient_shift u hu3 j x h)
    (hasDerivAt_fullCurlGradient_shift (fourierCurl u) hw3 j x h)

theorem projectionLaplacian_eq_sum (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (x : T3) :
    projectionLaplacian δ u x = ∑ j : Fin 3, projectionSecond δ u j x := by
  apply Finset.sum_congr rfl
  intro j _
  have hd : deriv (fun h ↦ projectionEnergy δ u (x + coordinateShift j h)) =
      fun h ↦ projectionFirst δ u j (x + coordinateShift j h) :=
    funext (fun h ↦ (hasDerivAt_projectionEnergy_shift δ hδ u hu j x h).deriv)
  rw [hd]
  simpa only [coordinateShift_zero, add_zero] using
    (hasDerivAt_projectionFirst_shift δ hδ u hu j x 0).deriv

theorem projectionViscousRate_eq (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (x : T3) :
    projectionViscousRate δ u x = projectionLaplacian δ u x - projectionCurvature δ u x := by
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu
  have hw3 := summable_fourierMoment_curl 3 u hu
  rw [projectionLaplacian_eq_sum δ hδ u hu]
  unfold projectionViscousRate
  rw [← sum_fullCurlSecond u hu3 x, ← sum_fullCurlSecond (fourierCurl u) hw3 x]
  simp only [projectionSecond, projectionCurvature, energyRate, Fin.sum_univ_three,
    smul_add, inner_add_right, inner_sub_right, real_inner_smul_right]
  ring

theorem projectionCurvature_ge (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity) (x : T3) :
    -(2 / δ) * residualGradientPairing δ u x ≤ projectionCurvature δ u x := by
  unfold residualGradientPairing projectionCurvature
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ ↦ energyCurvature_ge δ hδ _ _ _ _)

/-- The unfavorable part of the actual viscous rate only needs a
first-derivative residual pairing, not the full second curl derivative. -/
theorem projectionViscousRate_le (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (x : T3) :
    projectionViscousRate δ u x ≤ projectionLaplacian δ u x +
      (2 / δ) * residualGradientPairing δ u x := by
  rw [projectionViscousRate_eq δ hδ u hu]
  linarith only [projectionCurvature_ge δ hδ u x]

theorem continuous_projectionFirst (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (j : Fin 3) :
    Continuous (projectionFirst δ u j) := by
  have ha := continuous_fullVorticity u (summable_firstMoment_of_second u hu)
  have hb := continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu)
  have hc := continuous_regularizedCenter δ hδ u hu
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient
  exact ((hb.sub (hc.smul ha)).inner ((hD (fourierCurl u) j).sub (hc.smul (hD u j)))).const_mul 2

theorem continuous_projectionSecond (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (j : Fin 3) :
    Continuous (projectionSecond δ u j) := by
  have ha := continuous_fullVorticity u (summable_firstMoment_of_second u hu)
  have hb := continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu)
  have hc := continuous_regularizedCenter δ hδ u hu
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient
  have hS := LocalPairedDiffusion.continuous_fullCurlSecond
  have hR := hb.sub (hc.smul ha)
  have hrate : Continuous (fun x : T3 ↦ coefficientRate δ (fullVorticity u x)
      (fullVorticity (fourierCurl u) x) (fullCurlGradient u j x) (fullCurlGradient (fourierCurl u) j x)) :=
    (((hD u j).inner hb |>.add (ha.inner (hD (fourierCurl u) j))).sub
      ((hc.const_mul 2).mul (ha.inner (hD u j)))).div
        (continuous_const.add (ha.norm.pow 2)) (fun _ ↦ by positivity)
  exact ((hR.inner ((hS (fourierCurl u) j).sub (hc.smul (hS u j)))).const_mul 2).add
    ((((hD (fourierCurl u) j).sub (hc.smul (hD u j))).norm.pow 2 |>.const_mul 2).sub
      (((continuous_const.add (ha.norm.pow 2)).const_mul 2).mul (hrate.pow 2)))

theorem integral_projectionLaplacian_eq_zero (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) :
    (∫ x : T3, projectionLaplacian δ u x) = 0 := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hi (j : Fin 3) : Integrable (projectionSecond δ u j) :=
    (continuous_projectionSecond δ hδ u hu2 j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz (j : Fin 3) : (∫ x : T3, projectionSecond δ u j x) = 0 :=
    UnitTorusContinuousRate.integral_rate_eq_zero (projectionFirst δ u j) (projectionSecond δ u j)
      (coordinateShift j) (continuous_projectionFirst δ hδ u hu2 j)
      (continuous_projectionSecond δ hδ u hu2 j) (continuous_coordinateShift j) (coordinateShift_zero j)
      (hasDerivAt_projectionFirst_shift δ hδ u hu j)
  simp_rw [projectionLaplacian_eq_sum δ hδ u hu]
  rw [integral_finsetSum _ (fun j _ ↦ hi j)]
  simp only [hz, Finset.sum_const_zero]

theorem continuous_projectionViscousRate (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) :
    Continuous (projectionViscousRate δ u) := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have ha := continuous_fullVorticity u (summable_firstMoment_of_second u hu2)
  have hb := continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu2)
  have hc := continuous_regularizedCenter δ hδ u hu2
  have hLa := LocalPairedDiffusion.continuous_fullVorticityLaplacian u
    (summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu)
  have hLb := LocalPairedDiffusion.continuous_fullVorticityLaplacian (fourierCurl u)
    (summable_fourierMoment_curl 3 u hu)
  exact ((hb.sub (hc.smul ha)).inner (hLb.sub (hc.smul hLa))).const_mul 2

theorem continuous_residualGradientPairing (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    Continuous (residualGradientPairing δ u) := by
  have ha := continuous_fullVorticity u (summable_firstMoment_of_second u hu)
  have hb := continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu)
  have hc := continuous_regularizedCenter δ hδ u hu
  exact continuous_finsetSum _ (fun j _ ↦
    ((hb.sub (hc.smul ha)).inner (LocalSquaredGapGradient.continuous_fullCurlGradient u j)).pow 2)

/-- After spatial integration the ordinary Laplacian disappears. The
remaining residual-gradient product still requires a dynamical budget. -/
theorem integral_projectionViscousRate_le (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) :
    (∫ x : T3, projectionViscousRate δ u x) ≤
      (2 / δ) * ∫ x : T3, residualGradientPairing δ u x := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hL : Continuous (projectionLaplacian δ u) := by
    have he : projectionLaplacian δ u = fun x ↦ ∑ j : Fin 3, projectionSecond δ u j x :=
      funext (projectionLaplacian_eq_sum δ hδ u hu)
    rw [he]
    exact continuous_finsetSum _ (fun j _ ↦ continuous_projectionSecond δ hδ u hu2 j)
  have hiL : Integrable (projectionLaplacian δ u) :=
    hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiV : Integrable (projectionViscousRate δ u) :=
    (continuous_projectionViscousRate δ hδ u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiR : Integrable (fun x ↦ (2 / δ) * residualGradientPairing δ u x) :=
    ((continuous_residualGradientPairing δ hδ u hu2).const_mul (2 / δ)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_mono hiV (hiL.add hiR) (projectionViscousRate_le δ hδ u hu)
  simp only [Pi.add_apply] at h
  rw [integral_add hiL hiR, integral_projectionLaplacian_eq_zero δ hδ u hu,
    integral_const_mul, zero_add] at h
  exact h

end Mettapedia.FluidDynamics.NavierStokes.LocalHelicityProjectionDiffusion
