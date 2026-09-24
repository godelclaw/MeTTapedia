import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxPolarization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalStretchingFluxTime

/-!
# Identification of the Fourier and physical stretching-flux variations

Both constructions have the same cubic polarization. Thus the infinite
exchange-symmetric variation is the actual continuous-field product rule
followed by gradient projection, with all three differentiated slots.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StretchingFluxVariation

open Mettapedia.Analysis UnitTorusGradientProjection ContinuousFieldBilinear
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeHigherDerivativeMoments
open PancakeCurlOutputTail PancakeDyadicDirectionEvolution PancakeBlockReality
open PancakeInfiniteSpatialLaplacian PancakeLocalPressureEquation PancakeCoefficientLimitEquation
open PancakeGalerkinKineticEnergy LocalFilteredVorticity CurlEigenfieldDefect
open LocalStretchingFluxTime LongitudinalVorticityTime LongitudinalGradientFlux
open ExchangedFluxHeatRepresentation ExchangedFluxPolarization

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem realField_add (u v : FourierVelocity)
    (hu : Summable (fun q ↦ ‖u q‖)) (hv : Summable (fun q ↦ ‖v q‖)) :
    realField (u + v) = realField u + realField v := by
  apply ContinuousMap.ext
  intro x
  change complexRealPartEuclideanCLM (fullFourierField id (fun q ↦ u q + v q) x) = _
  rw [fullFourierField_add u v hu hv]
  exact map_add _ _ _

theorem realField_sub (u v : FourierVelocity)
    (hu : Summable (fun q ↦ ‖u q‖)) (hv : Summable (fun q ↦ ‖v q‖)) :
    realField (u - v) = realField u - realField v := by
  apply ContinuousMap.ext
  intro x
  change complexRealPartEuclideanCLM (fullFourierField id (fun q ↦ u q - v q) x) = _
  rw [fullFourierField_sub u v hu hv]
  exact map_sub _ _ _

theorem vorticityField_add (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) :
    vorticityField (u + v) = vorticityField u + vorticityField v := by
  simp only [vorticityField, fourierCurl_add]
  exact realField_add _ _ (summable_norm_curl u hu) (summable_norm_curl v hv)

theorem vorticityField_sub (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) :
    vorticityField (u - v) = vorticityField u - vorticityField v := by
  simp only [vorticityField, fourierCurl_sub]
  exact realField_sub _ _ (summable_norm_curl u hu) (summable_norm_curl v hv)

theorem velocityDerivativeField_add (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) (j : Fin 3) :
    velocityDerivativeField (u + v) j = velocityDerivativeField u j + velocityDerivativeField v j := by
  have he : indexedDerivativeCoeff id j (u + v) =
      indexedDerivativeCoeff id j u + indexedDerivativeCoeff id j v := by
    funext q
    simp only [indexedDerivativeCoeff, Pi.add_apply, smul_add]
  rw [velocityDerivativeField, he]
  exact realField_add _ _
    (summable_norm_derivativeCoefficients id u (by simpa only [indexedFirstMoment_id] using hu) j)
    (summable_norm_derivativeCoefficients id v (by simpa only [indexedFirstMoment_id] using hv) j)

theorem velocityDerivativeField_sub (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) (j : Fin 3) :
    velocityDerivativeField (u - v) j = velocityDerivativeField u j - velocityDerivativeField v j := by
  have he : indexedDerivativeCoeff id j (u - v) =
      indexedDerivativeCoeff id j u - indexedDerivativeCoeff id j v := by
    funext q
    simp only [indexedDerivativeCoeff, Pi.sub_apply, smul_sub]
  rw [velocityDerivativeField, he]
  exact realField_sub _ _
    (summable_norm_derivativeCoefficients id u (by simpa only [indexedFirstMoment_id] using hu) j)
    (summable_norm_derivativeCoefficients id v (by simpa only [indexedFirstMoment_id] using hv) j)

def stretchingVariationField (u v : FourierVelocity) : C(T3, R3) :=
  ∑ j, (pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (vorticityField u)) (velocityDerivativeField v j) +
      pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
        (componentField j (vorticityField v)) (velocityDerivativeField u j))

def variationField (u v : FourierVelocity) (j : Fin 3) : C(T3, R3) :=
  -(pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (vorticityField u)) (stretchingVariationField u v) +
      pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
        (componentField j (vorticityField v)) (stretchingField u))

theorem variationField_eq_polarization (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) (j : Fin 3) :
    variationField u v j = (1 / 2 : ℝ) • (fluxField 0 (u + v) j - fluxField 0 (u - v) j) -
      fluxField 0 v j := by
  apply ContinuousMap.ext
  intro x
  simp only [variationField, stretchingVariationField, fluxField_zero_eq, stretchingField,
    vorticityField_add u v hu hv, vorticityField_sub u v hu hv,
    velocityDerivativeField_add u v hu hv, velocityDerivativeField_sub u v hu hv]
  ext i
  simp only [pointwise, ContinuousMap.coe_mk, ContinuousLinearMap.lsmul_apply, componentField_apply,
    ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply,
    Fin.sum_univ_three, PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem projected_variationField_eq_polarization (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) :
    gradientProjection (toTensorL2 (variationField u v)) =
      (1 / 2 : ℝ) • (projectedFlux 0 (u + v) - projectedFlux 0 (u - v)) - projectedFlux 0 v := by
  have he : variationField u v = (1 / 2 : ℝ) • (fluxField 0 (u + v) - fluxField 0 (u - v)) -
      fluxField 0 v := funext (variationField_eq_polarization u v hu hv)
  rw [he]
  change ((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))) ((1 / 2 : ℝ) • (_ - _) - _) = _
  rw [map_sub, map_smul, map_sub]
  rfl

/-- The Fourier and continuous-field variations are the same tensor L2 element. -/
theorem fluxVariation_eq_projected_variationField (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v))
    (hdu : ∀ q, modeDot q (u q) = 0) (hdv : ∀ q, modeDot q (v q) = 0)
    (hru : ∀ q, u (-q) = coefficientConjugate (u q))
    (hrv : ∀ q, v (-q) = coefficientConjugate (v q)) :
    fluxVariation u v = gradientProjection (toTensorL2 (variationField u v)) := by
  rw [fluxVariation_eq_polarization u v hu hv hdu hdv hru hrv,
    projected_variationField_eq_polarization u v hu hv]

theorem variationField_velocityRHS (ν : ℝ) (u : FourierVelocity) :
    variationField u (infiniteVelocityRHS ν u) = fluxRateField ν u := rfl

end Mettapedia.FluidDynamics.NavierStokes.StretchingFluxVariation
