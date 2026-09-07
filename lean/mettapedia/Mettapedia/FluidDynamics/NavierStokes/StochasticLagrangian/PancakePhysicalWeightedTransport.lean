import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeWeightedOperatorTransport
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalMeanBalance

/-!
# Signed transport of actual vorticity in the spectral alignment weight

The operator weight is constructed from the low strain and its largest
eigenvalue. Local Lipschitz regularity suffices at spectral collisions.
The transporting velocity may use any scalar Fourier multiplier, including
the difference between the filtered and full retained velocity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalWeightedTransport

open MeasureTheory
open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakeFourierMaterialPaths PancakeFilteredStrainDynamics
open PancakeRegularizedDiffusion PancakeSpectralFiniteDifference PancakePhysicalSpectralDefect
open PancakeLocallyLipschitzEnergy PancakeTopEigenvalueDerivative PancakeSpacetimeSpectralDifferentiability
open PancakePhysicalMeanBalance PancakePhysicalTransportCancellation PancakeMaterialDiffusionBudget
open PancakeWeightedOperatorTransport PancakeWeightedMatrixTransport
open PancakeWeightedWeakTransport
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem locallyLipschitz_regularizedGap
    (S : X3 → SymmetricStrain) (delta : ℝ) (hS : ContDiff ℝ 1 (fun r ↦ (S r).1)) :
    LocallyLipschitz (fun r ↦ regularizedGap (S r) delta) := by
  have hG : LipschitzWith 2 (fun A : SymmetricStrain ↦ regularizedGap A delta) := by
    apply LipschitzWith.of_dist_le_mul
    intro A C
    simpa only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_ofNat] using regularizedGap_sub_norm C A delta
  intro r
  obtain ⟨C, s, hs, hC⟩ := hS.contDiffAt.exists_lipschitzOnWith
  have hCS : LipschitzOnWith C S s := hC
  exact ⟨2 * C, s, hs, hG.comp_lipschitzOnWith hCS⟩

theorem contDiff_timeSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × X3 → E) (hf : ContDiff ℝ 1 f) (t : ℝ) : ContDiff ℝ 1 (fun r : X3 ↦ f (t, r)) :=
  hf.comp (contDiff_const.prodMk contDiff_id)

theorem contDiff_spatial_strain (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) :
    ContDiff ℝ 1 (fun r : X3 ↦ (spatialStrain modes (filteredVelocity chi u) (torusPoint r)).1) := by
  have h := contDiff_real_strain chi modes (fun _ : ℝ ↦ u) (fun _ _ _ ↦ contDiff_const)
  exact contDiff_timeSlice _ h 0

theorem contDiff_spatial_vorticity (modes : Finset Wavevector) (u : FourierVelocity) :
    ContDiff ℝ 1 (fun r : X3 ↦ spatialVorticity modes u (torusPoint r)) := by
  have h := contDiff_real_vorticity modes (fun _ : ℝ ↦ u) (fun _ _ _ ↦ contDiff_const)
  exact contDiff_timeSlice _ h 0

def physicalGapWeight (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (delta : ℝ) (x : T3) : R3 →L[ℝ] R3 := regularizedGap (spatialStrain modes (filteredVelocity chi u) x) delta

def physicalWeightVariation (chi beta : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) : T3 → ℝ :=
  matrixWeightVariation (operatorEntries (physicalGapWeight chi modes u delta))
    (fun i x ↦ spatialVorticity modes u x i) (velocityComponent beta modes u)

theorem operatorEntries_physicalGapWeight_add (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (i j : Fin 3) (x : T3) :
    operatorEntries (physicalGapWeight chi modes u delta) i j x =
      operatorEntries (physicalGapWeight chi modes u 0) i j x +
        delta * (EuclideanSpace.basisFun (Fin 3) ℝ j) i := by
  simp only [operatorEntries, physicalGapWeight, regularizedGap, sub_apply, smul_apply,
    one_apply_eq_self, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, add_zero]
  ring

/-- Adding delta times the constant identity operator has no spatial
transport derivative. This is an exact identity, including at collisions. -/
theorem physicalWeightVariation_delta (chi beta : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) :
    physicalWeightVariation chi beta modes u delta x = physicalWeightVariation chi beta modes u 0 x := by
  have he : ∀ i j, operatorEntries (physicalGapWeight chi modes u delta) i j =
      fun y ↦ operatorEntries (physicalGapWeight chi modes u 0) i j y +
        delta * (EuclideanSpace.basisFun (Fin 3) ℝ j) i :=
    fun i j ↦ funext (operatorEntries_physicalGapWeight_add chi modes u delta i j)
  simp only [physicalWeightVariation, matrixWeightVariation, he, coordinateTransport_add_const]

theorem continuous_physicalGapWeight (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) : Continuous (physicalGapWeight chi modes u delta) := by
  have hS := continuous_strain modes (filteredVelocity chi u)
  exact (((lipschitzWith_topEigenvalue.continuous.comp hS).add continuous_const).smul continuous_const).sub
    (continuous_subtype_val.comp hS)

theorem integral_physical_weighted_transport
    (chi beta : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (delta : ℝ)
    (hu : ∀ q ∈ modes, modeDot q (u q) = 0) :
    Integrable (fun x : T3 ↦ ⟪physicalGapWeight chi modes u delta x (spatialVorticity modes u x),
      vectorTransport (spatialVorticity modes u) (velocityComponent beta modes u) x⟫) ∧
    Integrable (physicalWeightVariation chi beta modes u delta) ∧
      2 * (∫ x : T3, ⟪physicalGapWeight chi modes u delta x (spatialVorticity modes u x),
        vectorTransport (spatialVorticity modes u) (velocityComponent beta modes u) x⟫) =
        -(∫ x : T3, physicalWeightVariation chi beta modes u delta x) := by
  exact integral_operatorTransport (physicalGapWeight chi modes u delta) (spatialVorticity modes u)
    (velocityComponent beta modes u) (continuous_physicalGapWeight chi modes u delta)
    (continuous_vorticity modes u)
    (locallyLipschitz_regularizedGap _ delta (contDiff_spatial_strain chi modes u))
    (contDiff_spatial_vorticity modes u).locallyLipschitz
    (fun x a b ↦ regularizedGap_symmetric _ delta a b)
    (continuous_velocityComponent beta modes u)
    (fun j ↦ (contDiff_real_velocityComponent beta modes u j).locallyLipschitz)
    (Filter.Eventually.of_forall (coordinateDivergence_velocity_zero beta modes u hu))

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalWeightedTransport
