import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalStrainEquation

/-!
# Reality and trace-free geometry of the actual strain

Conjugate symmetry survives the physical derivative multiplier. The
ordinary velocity gradient, strain, and spin are consequently real, and
incompressibility makes the strain trace vanish.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalStrainReality

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeInfiniteRealCurl
open PancakeIndexedFourierMoments PancakeCurlOutputTail PancakePeriodicVorticityEquation
open PancakeLocalGradientEquation PancakeLocalStrainEquation PancakeFilteredStrainDynamics
open PancakeLocalProjectedEquation PancakeFrequencyProjectorCommutator

local notation "T3" => UnitAddTorus (Fin 3)

theorem indexedDerivativeCoeff_conjugate (u : FourierVelocity)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (j : Fin 3) (q : Wavevector) :
    indexedDerivativeCoeff id j u (-q) =
      coefficientConjugate (indexedDerivativeCoeff id j u q) := by
  funext i
  simp [indexedDerivativeCoeff, hr, coefficientConjugate, unitTorusDerivativePhase, map_ofNat]

theorem spatialVelocityGradient_reality (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) (i j : Fin 3) :
    conj (spatialVelocityGradient (fullFourierField id u) x i j) =
      spatialVelocityGradient (fullFourierField id u) x i j := by
  have hm : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu
  simp only [spatialVelocityGradient, coordinateDerivative_fullFourierField id u hm]
  exact fullFourierField_conj _ (summable_norm_derivativeCoefficients id u hm j)
    (indexedDerivativeCoeff_conjugate u hr j) x i

theorem spatialStrain_reality (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) (i j : Fin 3) :
    conj (spatialStrain (fullFourierField id u) x i j) =
      spatialStrain (fullFourierField id u) x i j := by
  change conj ((1 / 2 : ℂ) *
    (spatialVelocityGradient (fullFourierField id u) x i j +
      spatialVelocityGradient (fullFourierField id u) x j i)) = _
  simp only [map_mul, map_add, map_div₀, map_one, map_ofNat, spatialVelocityGradient_reality u hu hr]
  norm_num
  rfl

theorem spatialSpin_reality (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) (i j : Fin 3) :
    conj (spatialSpin (fullFourierField id u) x i j) =
      spatialSpin (fullFourierField id u) x i j := by
  change conj ((1 / 2 : ℂ) *
    (spatialVelocityGradient (fullFourierField id u) x i j -
      spatialVelocityGradient (fullFourierField id u) x j i)) = _
  simp only [map_mul, map_sub, map_div₀, map_one, map_ofNat, spatialVelocityGradient_reality u hu hr]
  norm_num
  rfl

theorem trace_spatialStrain (u : T3 → VelocityCoefficient) (x : T3) :
    (spatialStrain u x).trace = (spatialVelocityGradient u x).trace := by
  change ((1 / 2 : ℂ) • (spatialVelocityGradient u x + (spatialVelocityGradient u x).transpose)).trace = _
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_transpose]
  simp only [smul_eq_mul]
  ring

theorem spatialStrain_trace_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    (spatialStrain (fullFourierField id u) x).trace = 0 := by
  rw [trace_spatialStrain]
  exact spatialDivergence_fullFourierField u hu hd x

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalStrainReality
