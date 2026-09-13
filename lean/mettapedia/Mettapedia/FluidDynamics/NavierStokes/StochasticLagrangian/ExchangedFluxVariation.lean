import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatFlow

/-!
# Three-slot variation of the exchanged flux

The linear variation inserts a velocity rate into each input slot.
Inserting the actual inviscid velocity RHS recovers the already defined
nonlinear mode source. This separates variation from the choice of rate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxVariation

open Mettapedia.Analysis.UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge
open LocalFilteredVorticity PancakeCoefficientLimitEquation
open PeriodicGradientFluxTriple FourierVorticityPairDynamics ExchangedFluxModeDynamics

local notation "H" => TensorL2 (Fin 3) (EuclideanSpace ℝ (Fin 3))

def mixedTensor (u v w : FourierVelocity) (p : TripleIndex) (j : Fin 3) : VelocityCoefficient :=
  (1 / 2 : ℝ) • (fourierCurl u p.1 j •
    differenceCLM p (coefficientCross (fourierCurl v p.2.1) (fourierCurl w p.2.2)))

def mixedMode (u v w : FourierVelocity) (p : TripleIndex) : H :=
  tensorModeCLM (tripleFrequency p) (mixedTensor u v w p)

def variationMode (u v : FourierVelocity) (p : TripleIndex) : H :=
  mixedMode v u u p + mixedMode u v u p + mixedMode u u v p

theorem mixedMode_self (u : FourierVelocity) (p : TripleIndex) : mixedMode u u u p = mode u p := rfl

theorem coefficientCross_add_left (u v w : VelocityCoefficient) :
    coefficientCross (u + v) w = coefficientCross u w + coefficientCross v w := by
  ext i
  fin_cases i <;> simp [coefficientCross] <;> ring

theorem coefficientCross_smul_smul (u v : VelocityCoefficient) (a b : ℂ) :
    coefficientCross (a • u) (b • v) = (a * b) • coefficientCross u v := by
  ext i
  fin_cases i <;> simp [coefficientCross] <;> ring

theorem mixedTensor_add_first (u v w z : FourierVelocity) (p : TripleIndex) :
    mixedTensor (u + v) w z p = mixedTensor u w z p + mixedTensor v w z p := by
  funext j
  simp only [mixedTensor, fourierCurl_add, Pi.add_apply, add_smul, smul_add]

theorem mixedTensor_add_second (u v w z : FourierVelocity) (p : TripleIndex) :
    mixedTensor u (v + w) z p = mixedTensor u v z p + mixedTensor u w z p := by
  funext j
  simp only [mixedTensor, fourierCurl_add, Pi.add_apply, coefficientCross_add_left, map_add, smul_add]

theorem mixedTensor_add_third (u v w z : FourierVelocity) (p : TripleIndex) :
    mixedTensor u v (w + z) p = mixedTensor u v w p + mixedTensor u v z p := by
  funext j
  simp only [mixedTensor, fourierCurl_add, Pi.add_apply, cross_add_right, map_add, smul_add]

theorem variationMode_add (u v w : FourierVelocity) (p : TripleIndex) :
    variationMode u (v + w) p = variationMode u v p + variationMode u w p := by
  simp only [variationMode, mixedMode, mixedTensor_add_first, mixedTensor_add_second,
    mixedTensor_add_third, map_add]
  abel

theorem sourceMode_eq_variationMode (u : FourierVelocity) (p : TripleIndex) :
    sourceMode u p = variationMode u (infiniteVelocityRHS 0 u) p := by
  have h : sourceTensor u p =
      mixedTensor (infiniteVelocityRHS 0 u) u u p +
        mixedTensor u (infiniteVelocityRHS 0 u) u p +
          mixedTensor u u (infiniteVelocityRHS 0 u) p := by
    funext j
    simp only [sourceTensor, mixedTensor, pairCross, pairSource, nonlinearCurl,
      Pi.add_apply, map_add, smul_add]
    abel
  simp only [sourceMode, h, map_add, variationMode, mixedMode]

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxVariation
