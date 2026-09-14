import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxSpatialDiffusion

/-!
# Exact projected stretching-flux dissipation

The gradient projection commutes with the constructed first derivatives
of the entire cubic flux. Integration by parts extracts its full squared
gradient norm. The mixed derivative contribution remains a signed work
term; it is not included in the nonnegative dissipation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StretchingFluxProjectedDiffusion

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeHigherDerivativeMoments
open PancakeCurlOutputTail PancakeFourierTranslationCurve PancakeHaarTransportRate
open PancakeBlockReality PeriodicGradientFluxTriple PeriodicProjectedTensorJet
open LongitudinalProjectedTransport LongitudinalGradientFlux LocalStretchingFluxTime
open StretchingFluxMaterialRate StretchingFluxProjectedEvolution StretchingFluxSpatialDiffusion

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem rawFluxJet_gradient_eq (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (j k : Fin 3) :
    (rawFluxJet u hu j).gradient k = fluxGradientField u j k := by
  apply ContinuousMap.ext
  intro x
  rw [rawFluxJet_gradient u hu hr]
  simpa only [PancakeInfiniteRealCurl.realCoordinateDerivative, coordinateShift_zero, add_zero] using
    (hasDerivAt_fluxField_shift u hu j k x 0).deriv

theorem projection_rawFluxJet_gradient (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (k : Fin 3) :
    gradientProjection (toTensorL2 (fun j ↦ (rawFluxJet u hu j).gradient k)) =
      toTensorL2 (fun j ↦ (projectedFluxJet u hu j).gradient k) := by
  have hraw : (fun j ↦ (rawFluxJet u hu j).gradient k) =
      -∑ r, fun j ↦ indexedRealField tripleFrequency
        (indexedDerivativeCoeff tripleFrequency k (rawCoefficient u r j)) := by
    funext j
    simp only [rawFluxJet, negSumJet, fieldJet, Pi.neg_apply, Finset.sum_apply]
  have hproj : (fun j ↦ (projectedFluxJet u hu j).gradient k) =
      -∑ r, fun j ↦ (projectedJet tripleFrequency (rawCoefficient u r)
        (summable_rawCoefficient u hu r) (summable_derivative_rawCoefficient u hu r) j).gradient k := by
    funext j
    simp only [projectedFluxJet, negSumJet, Pi.neg_apply, Finset.sum_apply]
  rw [hraw, hproj]
  change ((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))) (-∑ r, _) =
      (tensorEmbedding (d := Fin 3) (E := R3)) (-∑ r, _)
  rw [map_neg, map_sum, map_neg, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact PeriodicProjectedTensorDiffusion.gradientProjection_derivative_field tripleFrequency
    (rawCoefficient u r) (summable_rawCoefficient u hu r) (summable_derivative_rawCoefficient u hu r) k

theorem projection_fluxGradientField (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (k : Fin 3) :
    gradientProjection (toTensorL2 (fun j ↦ fluxGradientField u j k)) =
      toTensorL2 (fun j ↦ (projectedFluxJet u hu j).gradient k) := by
  simpa only [rawFluxJet_gradient_eq u hu hr] using projection_rawFluxJet_gradient u hu k

theorem inner_projected_fluxSecondDerivative (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (k : Fin 3) :
    ⟪projectedFlux 0 u, toTensorL2 (fun j ↦ fluxSecondDerivativeField u j k)⟫ =
      -‖gradientProjection (toTensorL2 (fun j ↦ fluxGradientField u j k))‖ ^ 2 := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  let F := projectedFluxJet u hu2
  let D (j : Fin 3) := fluxGradientField u j k
  let DD (j : Fin 3) := fluxSecondDerivativeField u j k
  have hi (j : Fin 3) : (∫ x : T3, ⟪(F j).value x, DD j x⟫) =
      -(∫ x : T3, ⟪(F j).gradient k x, D j x⟫) := by
    apply UnitTorusTransportPairing.integral_inner_rate
      (F j).value (D j) ((F j).gradient k) (DD j) (coordinateShift k)
      (F j).value.continuous (D j).continuous ((F j).gradient k).continuous (DD j).continuous
      (UnitTorusWeakDerivative.continuous_coordinateShift k) (coordinateShift_zero k)
      ((F j).hasDerivAt k)
    exact hasDerivAt_fluxGradientField_shift u hu j k
  have hD : gradientProjection (toTensorL2 D) =
      toTensorL2 (fun j ↦ (F j).gradient k) := projection_fluxGradientField u hu2 hr k
  have hpair : ⟪toTensorL2 (fun j ↦ (F j).gradient k), toTensorL2 D⟫ =
      ‖gradientProjection (toTensorL2 D)‖ ^ 2 := by
    rw [← hD, ← inner_gradientProjection_gradientProjection, real_inner_self_eq_norm_sq]
  change ⟪_, toTensorL2 DD⟫ = -‖gradientProjection (toTensorL2 D)‖ ^ 2
  rw [← projectedFluxJet_eq u hu2 hr, ← hpair, inner_toTensorL2, inner_toTensorL2]
  rw [integral_finsetSum _ (fun j _ ↦
    ((F j).value.continuous.inner (DD j).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)),
    integral_finsetSum _ (fun j _ ↦
      (((F j).gradient k).continuous.inner (D j).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
  change (∑ j, ∫ x : T3, ⟪(F j).value x, DD j x⟫) =
    -(∑ j, ∫ x : T3, ⟪(F j).gradient k x, D j x⟫)
  simp only [hi, Finset.sum_neg_distrib]

/-- The entire projected flux is differentiated before its norm is squared. -/
def dissipation (u : FourierVelocity) : ℝ :=
  ∑ k, ‖gradientProjection (toTensorL2 (fun j ↦ fluxGradientField u j k))‖ ^ 2

theorem dissipation_nonneg (u : FourierVelocity) : 0 ≤ dissipation u := by
  exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

/-- The dissipative norm is that of the ordinary projected spatial gradient. -/
theorem dissipation_eq_integral (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    dissipation u = ∫ x : T3, ∑ k, ∑ j, ‖(projectedFluxJet u hu j).gradient k x‖ ^ 2 := by
  simp only [dissipation, projection_fluxGradientField u hu hr, norm_toTensorL2_sq]
  symm
  apply integral_finsetSum
  intro k _
  exact (continuous_finsetSum _ (fun j _ ↦
    ((projectedFluxJet u hu j).gradient k).continuous.norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem inner_projected_fluxLaplacian (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    ⟪projectedFlux 0 u, toTensorL2 (fluxLaplacianField u)⟫ = -dissipation u := by
  have he : fluxLaplacianField u = ∑ k, fun j ↦ fluxSecondDerivativeField u j k := by
    funext j
    simp only [fluxLaplacianField, Finset.sum_apply]
  rw [he]
  change ⟪_, (tensorEmbedding (d := Fin 3) (E := R3)) (∑ k, _)⟫ = _
  rw [map_sum, inner_sum]
  change (∑ k, ⟪projectedFlux 0 u, toTensorL2 (fun j ↦ fluxSecondDerivativeField u j k)⟫) = _
  simp only [inner_projected_fluxSecondDerivative u hu hr,
    Finset.sum_neg_distrib, dissipation]

def mixedWork (u : FourierVelocity) : ℝ :=
  ⟪projectedFlux 0 u, toTensorL2 (viscousCrossField u)⟫

/-- This is an identity, not a sign assertion about the mixed work. -/
theorem materialWork_add_dissipation (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    materialWork ν u + ν * dissipation u = materialWork 0 u + 2 * ν * mixedWork u := by
  have he : fluxMaterialRateField ν u = fluxMaterialRateField 0 u +
      ν • (fluxLaplacianField u + (2 : ℝ) • viscousCrossField u) :=
    funext (fluxMaterialRateField_eq_laplacian_add_cross ν u hu hd hr)
  simp only [materialWork, he]
  change ⟪_, (tensorEmbedding (d := Fin 3) (E := R3)) (_ + ν • (_ + (2 : ℝ) • _))⟫ + _ = _
  rw [map_add, map_smul, map_add, map_smul]
  simp only [inner_add_right, real_inner_smul_right]
  change ⟪projectedFlux 0 u, toTensorL2 (fluxMaterialRateField 0 u)⟫ +
    ν * (⟪projectedFlux 0 u, toTensorL2 (fluxLaplacianField u)⟫ + 2 * mixedWork u) +
      ν * dissipation u = _
  rw [inner_projected_fluxLaplacian u hu hr]
  ring

end Mettapedia.FluidDynamics.NavierStokes.StretchingFluxProjectedDiffusion
