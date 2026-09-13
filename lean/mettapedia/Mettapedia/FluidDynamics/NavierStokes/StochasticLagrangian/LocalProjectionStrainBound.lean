import Mettapedia.Analysis.WeightedProjectionRateBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalProjectionStrainRate

/-!
# A regularization-uniform envelope for the actual strain projection work

The envelope depends on the fixed spatial field and its ordinary jets,
but not on the positive regularization parameter. It is finite on each
regular spatial snapshot. No time budget, supremum estimate, or bound
from kinetic energy alone is supplied by this envelope.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalProjectionStrainBound

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open RegularizedProjection RegularizedProjectionParabolic WeightedProjectionParabolic
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget LocalWeightedCurlCancellation LocalAlignmentForcing
open LocalHelicityProjectionDiffusion LocalHelicityProjectionEvolution LocalVariableHelicityCenter
open LocalHelicityRotationFlux LocalWeightedProjectionEvolution LocalProjectionStrainRate
open HelicitySourceStrainSplit

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem strainMaterialRate_eq_weightedRate (δ : ℝ) (u : FourierVelocity) (x : T3) :
    strainMaterialRate δ u x =
      weightedRate δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
        (fullStrainOperator u x (fullVorticity u x))
        (-fullStrainOperator u x (fullVorticity (fourierCurl u) x) + strainSource u x) := by
  have hb : fullStrainOperator u x (fullVorticity (fourierCurl u) x) =
      fullStrainOperator u x (projectionResidual δ u x) +
        regularizedCenter δ u x • fullStrainOperator u x (fullVorticity u x) := by
    simp only [projectionResidual, RegularizedProjection.residual, map_sub, map_smul,
      regularizedCenter, coefficient]
    abel
  simp only [strainMaterialRate, amplitudeStrainRate, strainProjectionRate, weightedRate,
    energyRate, projectionEnergy, hb, neg_add, inner_sub_right, inner_add_right,
    inner_neg_right, real_inner_smul_right]
  change _ = _ + ‖fullVorticity u x‖ ^ 6 *
    (2 * (-⟪projectionResidual δ u x, fullStrainOperator u x (projectionResidual δ u x)⟫ -
      regularizedCenter δ u x * ⟪projectionResidual δ u x, fullStrainOperator u x (fullVorticity u x)⟫ +
      ⟪projectionResidual δ u x, strainSource u x⟫ -
      regularizedCenter δ u x * ⟪projectionResidual δ u x, fullStrainOperator u x (fullVorticity u x)⟫))
  ring

def strainRateEnvelope (u : FourierVelocity) (x : T3) : ℝ :=
  10 * ‖fullVorticity u x‖ ^ 6 * ‖fullStrainOperator u x‖ * ‖fullVorticity (fourierCurl u) x‖ ^ 2 +
    2 * ‖fullVorticity u x‖ ^ 6 * ‖fullVorticity (fourierCurl u) x‖ * ‖strainSource u x‖

def strainWorkEnvelope (u : FourierVelocity) : ℝ := ∫ x : T3, strainRateEnvelope u x

theorem strainRateEnvelope_nonneg (u : FourierVelocity) (x : T3) : 0 ≤ strainRateEnvelope u x := by
  unfold strainRateEnvelope
  positivity

theorem strainWorkEnvelope_nonneg (u : FourierVelocity) : 0 ≤ strainWorkEnvelope u :=
  integral_nonneg (strainRateEnvelope_nonneg u)

theorem abs_strainMaterialRate_le (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity) (x : T3) :
    |strainMaterialRate δ u x| ≤ strainRateEnvelope u x := by
  rw [strainMaterialRate_eq_weightedRate]
  exact WeightedProjectionRateBound.abs_strain_weightedRate_le δ hδ _ _ _ _

theorem continuous_strainRateEnvelope (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    Continuous (strainRateEnvelope u) := by
  have hu1 := summable_firstMoment_of_second u hu
  have ha := continuous_fullVorticity u hu1
  have hb := continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu)
  have hS := continuous_fullStrainOperator u hu1
  have hf := continuous_strainSource u hu1
  exact ((((ha.norm.pow 6).const_mul 10).mul hS.norm).mul (hb.norm.pow 2)).add
    ((((ha.norm.pow 6).const_mul 2).mul hb.norm).mul hf.norm)

/-- The field is fixed before regularization is varied. The envelope's
dependence on the field is explicit and is not dynamically controlled. -/
theorem abs_strainMaterialWork_le (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) : |strainMaterialWork δ u| ≤ strainWorkEnvelope u := by
  have hiT : Integrable (strainMaterialRate δ u) :=
    (continuous_strainMaterialRate δ hδ u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiB : Integrable (strainRateEnvelope u) :=
    (continuous_strainRateEnvelope u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact abs_integral_le_integral_abs.trans (integral_mono hiT.abs hiB (abs_strainMaterialRate_le δ hδ u))

end Mettapedia.FluidDynamics.NavierStokes.LocalProjectionStrainBound
