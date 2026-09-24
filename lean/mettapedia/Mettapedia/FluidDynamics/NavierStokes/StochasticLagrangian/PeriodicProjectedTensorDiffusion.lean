import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicProjectedTensorJet

/-!
# Dissipation of the actual gradient-projected Fourier tensor

The Fourier projection commutes with each spatial derivative. Periodic
integration by parts therefore turns the pairing with the raw second
derivative into the negative squared norm of the projected first derivative.
All derivative fields come from the same indexed coefficient family.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicProjectedTensorDiffusion

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis UnitTorusGradientProjection UnitTorusWeakDerivative
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeInfiniteFourierDerivative
open PancakeDyadicDirectionEvolution PeriodicProjectedTensorJet

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {ι : Type*} (freq : ι → Wavevector) (J : Fin 3 → ι → VelocityCoefficient)
  (hJ : ∀ j, Summable (fun q ↦ ‖J j q‖))
  (hdJ : ∀ j k, Summable (fun q ↦ ‖indexedDerivativeCoeff freq k (J j) q‖))

include hJ hdJ

theorem gradientProjection_derivative_field (k : Fin 3) :
    gradientProjection (toTensorL2 (fun j ↦ indexedRealField freq (indexedDerivativeCoeff freq k (J j)))) =
      toTensorL2 (fun j ↦ (projectedJet freq J hJ hdJ j).gradient k) := by
  rw [gradientProjection_eq_field freq _ (fun j ↦ hdJ j k)]
  simp only [projectedJet, fieldJet, derivative_projectedFamily]

/-- One coordinate of the full viscous dissipation, with coefficient one. -/
theorem inner_projected_secondDerivative (k : Fin 3)
    (hddJ : ∀ j, Summable (fun q ↦
      ‖indexedDerivativeCoeff freq k (indexedDerivativeCoeff freq k (J j)) q‖)) :
    ⟪gradientProjection (toTensorL2 (fun j ↦ indexedRealField freq (J j))),
      toTensorL2 (fun j ↦ indexedRealField freq
        (indexedDerivativeCoeff freq k (indexedDerivativeCoeff freq k (J j))))⟫ =
      -‖gradientProjection (toTensorL2 (fun j ↦
        indexedRealField freq (indexedDerivativeCoeff freq k (J j))))‖ ^ 2 := by
  let F := projectedJet freq J hJ hdJ
  let D (j : Fin 3) := indexedRealField freq (indexedDerivativeCoeff freq k (J j))
  let DD (j : Fin 3) := indexedRealField freq
    (indexedDerivativeCoeff freq k (indexedDerivativeCoeff freq k (J j)))
  have hi (j : Fin 3) : (∫ x : T3, ⟪(F j).value x, DD j x⟫) =
      -(∫ x : T3, ⟪(F j).gradient k x, D j x⟫) := by
    apply UnitTorusTransportPairing.integral_inner_rate
      (F j).value (D j) ((F j).gradient k) (DD j) (coordinateShift k)
      (F j).value.continuous (D j).continuous ((F j).gradient k).continuous (DD j).continuous
      (continuous_coordinateShift k) (coordinateShift_zero k) ((F j).hasDerivAt k)
    intro x h
    exact complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivAt h
      (hasDerivAt_fullFourierField_shift freq _ (hdJ j k) k (hddJ j) h x)
  have hF : gradientProjection (toTensorL2 (fun j ↦ indexedRealField freq (J j))) =
      toTensorL2 (fun j ↦ (F j).value) := gradientProjection_eq_field freq J hJ
  have hD : gradientProjection (toTensorL2 D) =
      toTensorL2 (fun j ↦ (F j).gradient k) := gradientProjection_derivative_field freq J hJ hdJ k
  have hpair : ⟪toTensorL2 (fun j ↦ (F j).gradient k), toTensorL2 D⟫ =
      ‖gradientProjection (toTensorL2 D)‖ ^ 2 := by
    rw [← hD, ← inner_gradientProjection_gradientProjection, real_inner_self_eq_norm_sq]
  change ⟪_, toTensorL2 DD⟫ = -‖gradientProjection (toTensorL2 D)‖ ^ 2
  rw [hF, ← hpair, inner_toTensorL2, inner_toTensorL2]
  rw [integral_finsetSum _ (fun j _ ↦
    ((F j).value.continuous.inner (DD j).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)),
    integral_finsetSum _ (fun j _ ↦
      (((F j).gradient k).continuous.inner (D j).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
  simp only [hi, Finset.sum_neg_distrib]

end Mettapedia.FluidDynamics.NavierStokes.PeriodicProjectedTensorDiffusion
