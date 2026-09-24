import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalProjectionCoherentRate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalHelicityRotationFlux

/-!
# Projection material work after separating rotation

The amplitude rate and symmetric-strain rate form one spatial integral.
The difference from the complete projection material rate is precisely
the already identified rotation flux. The coherent lower bound keeps the
normal-alignment defect and the symmetric-strain derivative source signed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalProjectionStrainRate

open scoped RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeBlockReality
open LocalLowDiffusionBudget LocalAlignmentForcing LocalVariableHelicityCenter
open LocalHelicityProjectionDiffusion LocalHelicityProjectionEvolution
open LocalWeightedProjectionEvolution LocalProjectionInviscidWork
open LocalHelicityRotationFlux LocalProjectionCoherentRate HelicitySourceStrainSplit

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def strainMaterialRate (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  amplitudeStrainRate δ u x + ‖fullVorticity u x‖ ^ 6 * strainProjectionRate δ u x

def strainMaterialWork (δ : ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, strainMaterialRate δ u x

def strainSourceRate (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  2 * ‖fullVorticity u x‖ ^ 6 * ⟪projectionResidual δ u x, strainSource u x⟫

theorem continuous_amplitudeStrainRate (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) : Continuous (amplitudeStrainRate δ u) := by
  have hu1 := summable_firstMoment_of_second u hu
  have ha := continuous_fullVorticity u hu1
  have hS := continuous_fullStrainOperator u hu1
  have hr := continuous_projectionResidual δ hδ u hu
  have hc := continuous_regularizedCenter δ hδ u hu
  have hE : Continuous (projectionEnergy δ u) := (hr.norm.pow 2).add ((hc.pow 2).const_mul δ)
  exact (((ha.norm.pow 4).const_mul 6).mul (ha.inner (hS.clm_apply ha))).mul hE

theorem continuous_strainMaterialRate (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) : Continuous (strainMaterialRate δ u) :=
  (continuous_amplitudeStrainRate δ hδ u hu).add
    (((continuous_fullVorticity u (summable_firstMoment_of_second u hu)).norm.pow 6).mul
      (continuous_strainProjectionRate δ hδ u hu))

theorem strainMaterialWork_eq (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    strainMaterialWork δ u = (∫ x : T3, amplitudeStrainRate δ u x) + weightedStrainRate δ u := by
  have hiA : Integrable (amplitudeStrainRate δ u) :=
    (continuous_amplitudeStrainRate δ hδ u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiS : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 * strainProjectionRate δ u x) :=
    (((continuous_fullVorticity u (summable_firstMoment_of_second u hu)).norm.pow 6).mul
      (continuous_strainProjectionRate δ hδ u hu)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  exact integral_add hiA hiS

theorem integral_projectionMaterialRate_eq (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∫ x : T3, projectionMaterialRate δ u x) =
      (∫ x : T3, amplitudeStrainRate δ u x) + weightedInviscidRate δ u := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hiA : Integrable (amplitudeStrainRate δ u) :=
    (continuous_amplitudeStrainRate δ hδ u hu2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiP : Integrable (projectionMaterialRate δ u) :=
    (continuous_projectionMaterialRate δ hδ u hu hd hr).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiI : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 * projectionInviscidRate δ u x) :=
    (hiP.sub hiA).congr (Filter.Eventually.of_forall (fun x ↦ by
      simp only [Pi.sub_apply, projectionMaterialRate_eq]; ring))
  simp_rw [projectionMaterialRate_eq]
  exact integral_add hiA hiI

/-- Only rotation separates these two work integrals. -/
theorem integral_projectionMaterialRate_eq_strain (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∫ x : T3, projectionMaterialRate δ u x) = strainMaterialWork δ u +
      centerTransportIntegral (regularizedCenter δ u) u / 4 := by
  rw [integral_projectionMaterialRate_eq δ hδ u hu hd hr,
    weightedInviscidRate_eq δ hδ u hu hd hr,
    strainMaterialWork_eq δ hδ u (summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu)]
  ring

theorem strainMaterialRate_eq_coherent (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0) (hr : ∀ q, u (-q) = coefficientConjugate (u q))
    (x : T3) (σ : ℝ) :
    strainMaterialRate δ u x = coherentRate δ u x σ + normalRate δ u x σ + strainSourceRate δ u x := by
  have h := projectionMaterialRate_eq_split δ hδ u x σ
  rw [projectionMaterialRate_eq, projectionInviscidRate_eq_strain_add_rotation δ u hu hd hr x] at h
  simp only [sourceRate, source_eq_strain_add_rotation u hu hd hr, inner_add_right] at h
  unfold strainMaterialRate strainSourceRate
  linarith only [h]

theorem normalRate_add_strainSourceRate_le (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0) (hr : ∀ q, u (-q) = coefficientConjugate (u q))
    (x : T3) (σ : ℝ) (hσ : 0 ≤ σ)
    (hmax : ∀ z : R3, ⟪z, fullStrainOperator u x z⟫ ≤ σ * ‖z‖ ^ 2) :
    normalRate δ u x σ + strainSourceRate δ u x ≤ strainMaterialRate δ u x := by
  rw [strainMaterialRate_eq_coherent δ hδ u hu hd hr x σ]
  linarith only [coherentRate_nonneg δ hδ.le u x σ hσ hmax]

end Mettapedia.FluidDynamics.NavierStokes.LocalProjectionStrainRate
