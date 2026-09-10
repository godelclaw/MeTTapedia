import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAlignmentTransport
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalJointDiffusionBudget

/-!
# Actual Eulerian forcing in the filtered alignment budget

These fields are the spatial versions of the material-path quantities.
In particular the nonviscous remainder retains the pressure-projected
all-input subgrid force and transport by the discarded velocity.

Spatial continuity is proved from the actual fields. The weak budget
does not assume that a separately chosen top eigenvector is measurable.
Identification of an integrable scalar lower bound with the Eulerian
time derivative remains a distinct chain-rule obligation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAlignmentForcing

open scoped RealInnerProductSpace Matrix.Norms.Elementwise
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail
open PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeSpatialStrainEvolution
open PancakeLocalGradientEquation PancakeDyadicDirectionEvolution PancakeGalerkinKineticEnergy
open PancakeMaterialDiffusionBudget PancakeRegularizedDiffusion PancakeRegularizedMaterialRate
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeLowDiffusionBudget
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentTransport
open PancakeMeasurableMaterialRate PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories
open PancakeLocalSpatialVelocity
open PancakePhysicalLaplacian PancakeFourierStrainGradient InfiniteConvectionEnergy
open PancakeFourierTranslationCurve PancakePhysicalDiffusionLimit

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def fullStrainOperator (u : FourierVelocity) (x : T3) : R3 →L[ℝ] R3 :=
  realMatrixOperator (PancakeLocalStrainEquation.spatialStrain (fullFourierField id u) x)

def strainMismatch (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 :=
  (fullStrainOperator u x - (spatialStrain modes (filteredVelocity chi u) x).1) (fullVorticity u x)

def nonviscousRemainder (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 →L[ℝ] R3 :=
  -(spatialSpin modes (filteredVelocity chi u) x * spatialSpin modes (filteredVelocity chi u) x) +
    realMatrixOperator (matrixReconstruction outputs (LocalFilteredStrain.forcingCoeff chi modes u 0) x) +
    realMatrixOperator (matrixReconstruction outputs
      (LocalFilteredStrain.transportCorrectionCoeff modes (filteredVelocity chi u)
        (fun i ↦ InfiniteFourierTransport.velocityComponent u i x) x) x)

def forcingEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) : ℝ :=
  nonviscousEnvelope (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x)
    (nonviscousRemainder chi modes outputs u x) (strainMismatch chi modes u x) delta

def materialRate (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi u) x
  let w := fullVorticity u x
  linearRate S delta w
    (-S.1 * S.1 + nonviscousRemainder chi modes outputs u x +
      nu • strainLaplacian modes (filteredVelocity chi u) x)
    (S.1 w + strainMismatch chi modes u x + nu • fullVorticityLaplacian u x)

def residual (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 :=
  spectralResidual (spatialStrain modes (filteredVelocity chi u) x).1
    (topEigenvalue (spatialStrain modes (filteredVelocity chi u) x)) (fullVorticity u x)

theorem continuous_fullStrainOperator (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : Continuous (fullStrainOperator u) := by
  have hm : Summable (indexedFirstMoment id u) := by
    simpa only [indexedFirstMoment_id] using hu
  have hg : Continuous (spatialVelocityGradient (fullFourierField id u)) := by
    refine continuous_pi (fun i ↦ continuous_pi (fun j ↦ ?_))
    simp only [spatialVelocityGradient, coordinateDerivative_fullFourierField id u hm]
    exact (continuous_apply i).comp (fullFourierField id _).continuous
  apply realMatrixOperatorCLM.continuous.comp
  refine continuous_pi (fun i ↦ continuous_pi (fun j ↦ ?_))
  change Continuous (fun x : T3 ↦ (1 / 2 : ℂ) * (_ + _))
  exact continuous_const.mul
    (((continuous_apply j).comp ((continuous_apply i).comp hg)).add
      ((continuous_apply i).comp ((continuous_apply j).comp hg)))

theorem continuous_strainMismatch (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (strainMismatch chi modes u) :=
  ((continuous_fullStrainOperator u hu).sub
    (continuous_subtype_val.comp (continuous_strain modes (filteredVelocity chi u)))).clm_apply
      (continuous_fullVorticity u hu)

theorem continuous_nonviscousRemainder (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) : Continuous (nonviscousRemainder chi modes outputs u) := by
  have hW : Continuous (spatialSpin modes (filteredVelocity chi u)) :=
    realMatrixOperatorCLM.continuous.comp (continuous_matrixReconstruction _ _)
  have hF := realMatrixOperatorCLM.continuous.comp
    (continuous_matrixReconstruction outputs (LocalFilteredStrain.forcingCoeff chi modes u 0))
  have hC : Continuous (fun x : T3 ↦ matrixReconstruction outputs
      (LocalFilteredStrain.transportCorrectionCoeff modes (filteredVelocity chi u)
        (fun i ↦ InfiniteFourierTransport.velocityComponent u i x) x) x) := by
    refine continuous_pi (fun i ↦ continuous_pi (fun j ↦ ?_))
    simp only [matrixReconstruction_apply]
    apply continuous_finsetSum
    intro q _
    have hv (k : Fin 3) := InfiniteFourierTransport.continuous_velocityComponent u k
    have hrec : Continuous (finiteFourierReconstruction modes (filteredVelocity chi u)) := by
      have hc := (fourierField modes (filteredVelocity chi u)).continuous
      change Continuous (fun x ↦ fourierField modes (filteredVelocity chi u) x) at hc
      simpa only [fourierField_vector_eq] using hc
    have hf (k : Fin 3) : Continuous (fun x : T3 ↦
        (finiteFourierReconstruction modes (filteredVelocity chi u) x k).re) :=
      Complex.continuous_re.comp ((continuous_apply k).comp hrec)
    simp only [LocalFilteredStrain.transportCorrectionCoeff, realModeDot,
      Pi.sub_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  exact ((hW.mul hW).neg.add hF).add (realMatrixOperatorCLM.continuous.comp hC)

theorem continuous_forcingEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (delta : ℝ) :
    Continuous (forcingEnvelope chi modes outputs u delta) :=
  continuous_nonviscousEnvelope _ _ _ _ delta
    (continuous_strain modes (filteredVelocity chi u)) (continuous_fullVorticity u hu)
    (continuous_nonviscousRemainder chi modes outputs u) (continuous_strainMismatch chi modes u hu)

theorem continuous_residual (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (residual chi modes u) :=
  PancakeMaterialDiffusionBudget.continuous_residual _ _
    (continuous_strain modes (filteredVelocity chi u)) (continuous_fullVorticity u hu)

/-- The spatial definition is exactly the previously derived material rate. -/
theorem materialRate_along {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (chi : Wavevector → ℂ)
    (modes outputs : Finset Wavevector) (delta : ℝ) (X : ℝ → X3) (t : ℝ) :
    materialRate chi modes outputs (s.coefficients t) delta nu (torusPoint (X t)) =
      LocalFilteredViscousDefect.rateAlong s chi modes outputs delta X t := rfl

theorem materialRate_le (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3) :
    materialRate chi modes outputs u delta nu x + (1 / 2 : ℝ) * ‖residual chi modes u x‖ ^ 2 ≤
      nu * linearRate (spatialStrain modes (filteredVelocity chi u) x) delta (fullVorticity u x)
        (strainLaplacian modes (filteredVelocity chi u) x) (fullVorticityLaplacian u x) +
          forcingEnvelope chi modes outputs u delta x :=
  material_linearRate_le _ _ _ _ _ _ _ _

/-- Only the scalar lower bound is assumed integrable. The actual remainder
and residual are proved integrable, without choosing measurable eigenvectors. -/
theorem integral_materialRate_lower_bound_paid
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu)
    (F : T3 → ℝ) (hF : Integrable F)
    (hpoint : ∀ᵐ x : T3, F x ≤ materialRate chi modes outputs u delta nu x) :
    (∫ x : T3, F x) + (1 / 2 : ℝ) * (∫ x : T3, ‖residual chi modes u x‖ ^ 2) ≤
      (16 * nu / delta) * strainGradientCutoffWeight modes chi *
        kineticEnergy u * kineticEnergy (fourierCurl u) +
      ∫ x : T3, forcingEnvelope chi modes outputs u delta x := by
  have hu1 := PancakeHigherDerivativeMoments.summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hres : Integrable (fun x : T3 ↦ ‖residual chi modes u x‖ ^ 2) volume :=
    ((continuous_residual chi modes u hu1).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (forcingEnvelope chi modes outputs u delta) volume :=
    (continuous_forcingEnvelope chi modes outputs u hu1 delta).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_laplacian_diffusion_energy_paid modes chi u hu
    (fun x ↦ F x + (1 / 2 : ℝ) * ‖residual chi modes u x‖ ^ 2)
    (forcingEnvelope chi modes outputs u delta) delta nu hd hnu
    (hF.add (hres.const_mul _)) hR (by
      filter_upwards [hpoint] with x hx
      have hr := materialRate_le chi modes outputs u delta nu x
      linarith)
  rw [integral_add hF (hres.const_mul _), integral_const_mul] at h
  exact h

end Mettapedia.FluidDynamics.NavierStokes.LocalAlignmentForcing
