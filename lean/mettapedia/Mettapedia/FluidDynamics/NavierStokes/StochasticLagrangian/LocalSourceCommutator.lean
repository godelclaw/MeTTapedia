import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalLimitingAlignmentSource

/-!
# Actual source tilt: spin, pressure, subgrid feedback and transport

The commutator is formed from the complete nonviscous source before taking
its norm. Its exact decomposition preserves cancellation between the
physical channels. These identities do not bound their all-scale budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSourceCommutator

open scoped RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeMeasurableMaterialRate PancakeFourierMaterialPaths
open PancakeFilteredStrainDynamics PancakeFourierPressureStrain PancakeSpatialStrainEvolution
open PancakePhysicalViscousSplit PancakeDyadicDirectionEvolution
open LocalLowDiffusionBudget LocalAlignmentForcing LocalAlignmentContinuity LocalLimitingAlignmentSource
open SpectralSourceCommutator SpectralDiffusionWeightLimit
open PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def pressureOperator (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 →L[ℝ] R3 :=
  realMatrixOperator (matrixReconstruction outputs (pressureHessianCoeff modes (filteredVelocity chi u)) x)

def subgridOperator (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 →L[ℝ] R3 :=
  realMatrixOperator (matrixReconstruction outputs (strainCoeff (InfiniteFilteredEquation.subgridForce chi u)) x)

def transportOperator (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 →L[ℝ] R3 :=
  realMatrixOperator (matrixReconstruction outputs
    (LocalFilteredStrain.transportCorrectionCoeff modes (filteredVelocity chi u)
      (fun i ↦ InfiniteFourierTransport.velocityComponent u i x) x) x)

def sourceCommutator (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 →L[ℝ] R3 :=
  commutator (spatialStrain modes (filteredVelocity chi u) x) (nonviscousRemainder chi modes outputs u x)

theorem nonviscousRemainder_eq (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    nonviscousRemainder chi modes outputs u x =
      -(spatialSpin modes (filteredVelocity chi u) x * spatialSpin modes (filteredVelocity chi u) x) -
      pressureOperator chi modes outputs u x + subgridOperator chi outputs u x +
      transportOperator chi modes outputs u x := by
  have hF : LocalFilteredStrain.forcingCoeff chi modes u 0 = fun q ↦
      -pressureHessianCoeff modes (filteredVelocity chi u) q +
        strainCoeff (InfiniteFilteredEquation.subgridForce chi u) q := by
    funext q
    simp only [LocalFilteredStrain.forcingCoeff, viscousStrainCoeff_zero, add_zero]
  simp only [nonviscousRemainder, hF, matrixReconstruction_add, matrixReconstruction_neg,
    realMatrixOperator_add, realMatrixOperator_neg, pressureOperator, subgridOperator, transportOperator]
  abel

theorem sourceCommutator_eq (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    let W := spatialSpin modes (filteredVelocity chi u) x
    sourceCommutator chi modes outputs u x =
      -(commutator S W * W + W * commutator S W) -
      commutator S (pressureOperator chi modes outputs u x) +
      commutator S (subgridOperator chi outputs u x) +
      commutator S (transportOperator chi modes outputs u x) := by
  dsimp only
  rw [sourceCommutator, nonviscousRemainder_eq]
  simp only [sub_eq_add_neg, commutator_add, commutator_neg, commutator_mul]

theorem continuous_sourceCommutator (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) : Continuous (sourceCommutator chi modes outputs u) :=
  continuous_commutator _ _
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
    (continuous_nonviscousRemainder chi modes outputs u)

theorem continuous_sourceCommutator_spaceTime {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      sourceCommutator chi modes outputs (s.coefficients z.1) z.2) := by
  have hc (q : Wavevector) (i : Fin 3) :
      Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q i) :=
    (s.continuous q i).comp continuous_subtype_val
  exact continuous_commutator _ _
    (continuous_parametric_strain modes chi
      (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t) (fun q _ i ↦ hc q i))
    (continuous_nonviscousRemainder_parametric _ hc g hg hSum (fun t ↦ hu t t.2) chi C hchi modes outputs)

theorem limitingForcingEnvelope_le_refined (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    let w := fullVorticity u x
    limitingForcingEnvelope chi modes outputs u delta x ≤
      (2 * ‖nonviscousRemainder chi modes outputs u x‖ * limitingWeight S w +
        2 * (‖sourceCommutator chi modes outputs u x‖ / topGap S) * ‖w‖ * Real.sqrt (limitingWeight S w)) +
      2 * ⟪residual chi modes u x, strainMismatch chi modes u x⟫ +
      2 * delta * ⟪w, fullStrainOperator u x w⟫ := by
  have h := SpectralCommutatorLimit.limitingEnvelope_le_refined
    (spatialStrain modes (filteredVelocity chi u) x) (nonviscousRemainder chi modes outputs u x)
    (fullVorticity u x) hg
  dsimp only
  unfold limitingForcingEnvelope sourceCommutator
  linarith only [h]

theorem limitingForcingEnvelope_le_of_commutator_eq_zero (chi : Wavevector → ℂ)
    (modes outputs : Finset Wavevector) (u : FourierVelocity) (delta : ℝ) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x))
    (hc : sourceCommutator chi modes outputs u x = 0) :
    limitingForcingEnvelope chi modes outputs u delta x ≤
      2 * ‖nonviscousRemainder chi modes outputs u x‖ *
        limitingWeight (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x) +
      2 * ⟪residual chi modes u x, strainMismatch chi modes u x⟫ +
      2 * delta * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫ := by
  simpa only [hc, norm_zero, zero_div, mul_zero, zero_mul, add_zero] using
    limitingForcingEnvelope_le_refined chi modes outputs u delta x hg

end Mettapedia.FluidDynamics.NavierStokes.LocalSourceCommutator
