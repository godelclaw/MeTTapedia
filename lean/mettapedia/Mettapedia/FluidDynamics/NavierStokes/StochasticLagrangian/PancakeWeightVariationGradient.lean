import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalWeightedTransport

/-!
# Actual weak strain-weight variation and its gradient bound

The coordinate derivative of the spectral weight is identified almost
everywhere with the gap derivative of the actual reconstructed strain.
The bound has no inverse spectral gap and no regularization parameter.
The transporting velocity and strain-gradient factors remain explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeWeightVariationGradient

open MeasureTheory
open scoped RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakeFourierMaterialPaths PancakeFilteredStrainDynamics
open PancakePhysicalWeightedTransport PancakeWeightedOperatorTransport PancakeWeightedMatrixTransport
open PancakeWeakIncompressibleTransport PancakePeriodicWeakDerivative PancakeHaarTransportRate
open PancakeFourierTranslationCurve PancakeFourierStrainGradient PancakePhysicalDiffusionLimit
open PancakeLocallyLipschitzEnergy PancakeTopEigenvalueDerivative PancakeRegularizedDiffusion
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralDefectEvolution PancakePhysicalTransportCancellation
open PancakePhysicalSpectralDefect PancakeMaterialDiffusionBudget

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem hasDerivAt_spatialStrain_shift (modes : Finset Wavevector) (u : FourierVelocity)
    (j : Fin 3) (h : ℝ) (x : T3) :
    HasDerivAt (fun t ↦ (spatialStrain modes u (x + coordinateShift j t)).1)
      (strainGradient modes u (x + coordinateShift j h) j) h := by
  have hd := PancakeMappedFourierDiffusion.hasDerivAt_mappedField_shift
    realMatrixOperatorCLM modes (PancakeFourierPressureStrain.strainCoeff u) j h x
  simpa only [mappedField_strain, mappedField_strainGradient] using hd

def physicalGapGradient (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) (j : Fin 3) : R3 →L[ℝ] R3 :=
  gapDerivative (spatialStrain modes (filteredVelocity chi u) x)
    (strainGradient modes (filteredVelocity chi u) x j)

theorem ae_hasDerivAt_physicalGapWeight (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) :
    ∀ᵐ x : T3, ∀ j : Fin 3,
      HasDerivAt (fun h ↦ physicalGapWeight chi modes u delta (x + coordinateShift j h))
        (physicalGapGradient chi modes u x j) 0 := by
  have hL := locallyLipschitz_topEigenvalue _ (contDiff_spatial_strain chi modes u)
  have hc := lipschitzWith_topEigenvalue.continuous.comp (continuous_strain modes (filteredVelocity chi u))
  have ha := MeasureTheory.ae_all_iff.mpr (fun j : Fin 3 ↦
    ae_coordinate_differentiable _ j hc hL)
  filter_upwards [ha] with x hx
  intro j
  have hd := hasDerivAt_regularizedGap
    (fun h ↦ spatialStrain modes (filteredVelocity chi u) (x + coordinateShift j h))
    (strainGradient modes (filteredVelocity chi u) x j) delta 0
    (by simpa only [coordinateShift_zero, add_zero] using
      hasDerivAt_spatialStrain_shift modes (filteredVelocity chi u) j 0 x) (hx j)
  simpa only [physicalGapWeight, physicalGapGradient,
    coordinateShift_zero, add_zero] using hd

theorem ae_shiftRate_operatorEntries (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) :
    ∀ᵐ x : T3, ∀ k i j : Fin 3,
      shiftRate (operatorEntries (physicalGapWeight chi modes u delta) i j) (coordinateShift k) x =
        (physicalGapGradient chi modes u x k (EuclideanSpace.basisFun (Fin 3) ℝ j)) i := by
  filter_upwards [ae_hasDerivAt_physicalGapWeight chi modes u delta] with x hx
  intro k i j
  have hd := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).hasFDerivAt.comp_hasDerivAt 0
    ((hx k).clm_apply (hasDerivAt_const 0 (EuclideanSpace.basisFun (Fin 3) ℝ j)))
  simpa only [shiftRate, operatorEntries, map_zero, add_zero, PiLp.proj_apply, Function.comp_def] using hd.deriv

theorem matrixWeightVariation_eq_quadratic
    (K : T3 → R3 →L[ℝ] R3) (G : Fin 3 → R3 →L[ℝ] R3)
    (w : T3 → R3) (v : Fin 3 → T3 → ℝ) (x : T3)
    (hd : ∀ k i j, shiftRate (operatorEntries K i j) (coordinateShift k) x =
      (G k (EuclideanSpace.basisFun (Fin 3) ℝ j)) i) :
    matrixWeightVariation (operatorEntries K) (fun i y ↦ w y i) v x =
      ∑ k : Fin 3, v k x * ⟪w x, G k (w x)⟫ := by
  simp only [matrixWeightVariation, coordinateTransport, hd, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  change (∑ j : Fin 3, ∑ i : Fin 3,
    (G k (EuclideanSpace.basisFun (Fin 3) ℝ j)) i * v k x * w x i * w x j) =
      v k x * (∑ i : Fin 3, (G k (w x)) i * w x i)
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [operator_apply_coordinate, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem ae_physicalWeightVariation_eq (chi beta : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) :
    ∀ᵐ x : T3, physicalWeightVariation chi beta modes u delta x =
      ∑ j : Fin 3, velocityComponent beta modes u j x *
        ⟪spatialVorticity modes u x, physicalGapGradient chi modes u x j (spatialVorticity modes u x)⟫ := by
  filter_upwards [ae_shiftRate_operatorEntries chi modes u delta] with x hx
  exact matrixWeightVariation_eq_quadratic _ _ _ _ x hx

theorem abs_gapGradient_quadratic_le (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) (j : Fin 3) (w : R3) :
    |⟪w, physicalGapGradient chi modes u x j w⟫| ≤
      2 * ‖strainGradient modes (filteredVelocity chi u) x j‖ * ‖w‖ ^ 2 := by
  exact (abs_quadratic_le_opNorm _ w).trans
    (mul_le_mul_of_nonneg_right (gapDerivative_norm _ _) (sq_nonneg _))

theorem ae_abs_physicalWeightVariation_le (chi beta : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) :
    ∀ᵐ x : T3, |physicalWeightVariation chi beta modes u delta x| ≤
      2 * (∑ j : Fin 3, |velocityComponent beta modes u j x| *
        ‖strainGradient modes (filteredVelocity chi u) x j‖) * ‖spatialVorticity modes u x‖ ^ 2 := by
  filter_upwards [ae_physicalWeightVariation_eq chi beta modes u delta] with x hx
  rw [hx]
  calc
    _ ≤ ∑ j : Fin 3, |velocityComponent beta modes u j x *
      ⟪spatialVorticity modes u x, physicalGapGradient chi modes u x j (spatialVorticity modes u x)⟫| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, |velocityComponent beta modes u j x| *
      (2 * ‖strainGradient modes (filteredVelocity chi u) x j‖ * ‖spatialVorticity modes u x‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_gapGradient_quadratic_le chi modes u x j _) (abs_nonneg _)
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]; congr 1; ext j; ring

theorem ae_abs_physicalWeightVariation_le_gradient_norm
    (chi beta : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (delta : ℝ) :
    ∀ᵐ x : T3, |physicalWeightVariation chi beta modes u delta x| ≤
      2 * ‖PancakeMeasurableMaterialRate.spatialVelocity beta modes u x‖ *
        Real.sqrt (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2) *
          ‖spatialVorticity modes u x‖ ^ 2 := by
  filter_upwards [ae_abs_physicalWeightVariation_le chi beta modes u delta] with x hx
  have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun j : Fin 3 ↦ |velocityComponent beta modes u j x|)
    (fun j : Fin 3 ↦ ‖strainGradient modes (filteredVelocity chi u) x j‖)
  have he : (∑ j : Fin 3, |velocityComponent beta modes u j x| ^ 2) =
      ‖PancakeMeasurableMaterialRate.spatialVelocity beta modes u x‖ ^ 2 := by
    simp only [velocityComponent, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs]
  rw [he, Real.sqrt_sq (norm_nonneg _)] at hc
  apply hx.trans
  calc
    _ ≤ 2 * (‖PancakeMeasurableMaterialRate.spatialVelocity beta modes u x‖ *
      Real.sqrt (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2)) *
        ‖spatialVorticity modes u x‖ ^ 2 := by gcongr
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PancakeWeightVariationGradient
