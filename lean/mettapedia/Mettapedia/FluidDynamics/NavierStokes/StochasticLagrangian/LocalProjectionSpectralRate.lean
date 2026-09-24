import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalProjectionStrainRate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpectralResidual

/-!
# The actual top-strain choice in the projection material rate

The coherent scalar is the largest eigenvalue of the reconstructed
symmetric strain. Incompressibility proves its nonnegativity. Rayleigh's
inequality supplies the operator upper bound, including at eigenvalue
collisions; no alignment or gap hypothesis is introduced.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalProjectionSpectralRate

open scoped RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeBlockReality PancakeFourierMaterialPaths
open PancakeInfiniteSpatialCurl PancakeInfiniteFourierDerivative
open PancakeLocalStrainReality PancakeLocalStrainEquation PancakeDyadicDirectionEvolution
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralClusterDichotomy PancakeTopEigenvalueDerivative
open LocalAlignmentForcing LocalProjectionCoherentRate LocalProjectionStrainRate
open LocalLowDiffusionBudget LocalVariableHelicityCenter LocalHelicityRotationFlux
open LocalHelicityProjectionDiffusion LocalRadialCoherentBound

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def symmetricStrain (u : FourierVelocity) (x : T3) : SymmetricStrain :=
  ⟨fullStrainOperator u x, realMatrixOperator_symmetric _ (spatialStrain_symmetric _ _)⟩

def topStrain (u : FourierVelocity) (x : T3) : ℝ := topEigenvalue (symmetricStrain u x)

theorem continuous_topStrain (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (topStrain u) :=
  lipschitzWith_topEigenvalue.continuous.comp ((continuous_fullStrainOperator u hu).subtype_mk _)

theorem topStrain_nonneg (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hd : ∀ q, modeDot q (u q) = 0) (x : T3) : 0 ≤ topStrain u x := by
  have hdiag (i : Fin 3) := LocalSpectralResidual.realMatrix_diagonal_le_topEigenvalue
    (spatialStrain (fullFourierField id u) x) (spatialStrain_symmetric _ _) i
  have htr := congrArg Complex.re (spatialStrain_trace_zero u hu hd x)
  simp only [Matrix.trace, Fin.sum_univ_three, Matrix.diag_apply, Complex.add_re, Complex.zero_re] at htr
  change 0 ≤ topEigenvalue ⟨realMatrixOperator (spatialStrain (fullFourierField id u) x),
    realMatrixOperator_symmetric _ (spatialStrain_symmetric _ _)⟩
  linarith [hdiag 0, hdiag 1, hdiag 2]

theorem rayleigh_le_topStrain (u : FourierVelocity) (x : T3) (z : R3) :
    ⟪z, fullStrainOperator u x z⟫ ≤ topStrain u x * ‖z‖ ^ 2 :=
  rayleigh_le_topEigenvalue_mul_norm_sq (symmetricStrain u x).1 (symmetricStrain u x).2 z

theorem coherentRate_topStrain_nonneg (δ : ℝ) (hδ : 0 ≤ δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    0 ≤ coherentRate δ u x (topStrain u x) :=
  coherentRate_nonneg δ hδ u x _ (topStrain_nonneg u hu hd x) (rayleigh_le_topStrain u x)

/-- The only remaining quantities are actual signed misalignment and
strain-source rates; positivity of the coherent part is now unconditional
for an incompressible field with the stated Fourier regularity. -/
theorem normalRate_add_strainSourceRate_le (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0) (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    normalRate δ u x (topStrain u x) + strainSourceRate δ u x ≤ strainMaterialRate δ u x :=
  LocalProjectionStrainRate.normalRate_add_strainSourceRate_le δ hδ u hu hd hr x _
    (topStrain_nonneg u (summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu) hd x)
    (rayleigh_le_topStrain u x)

theorem continuous_normalRate (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    Continuous (fun x : T3 ↦ normalRate δ u x (topStrain u x)) := by
  have hu1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 2) hu
  have ha := continuous_fullVorticity u hu1
  have hr := continuous_projectionResidual δ hδ u hu
  have hc := continuous_regularizedCenter δ hδ u hu
  have hS := continuous_fullStrainOperator u hu1
  have ht := continuous_topStrain u hu1
  have he : Continuous (fun x : T3 ↦ normalDefect u x (topStrain u x) (fullVorticity u x)) :=
    (hS.clm_apply ha).sub (ht.smul ha)
  have hE : Continuous (projectionEnergy δ u) := (hr.norm.pow 2).add ((hc.pow 2).const_mul δ)
  exact ((((ha.norm.pow 4).const_mul 6).mul (ha.inner he)).mul hE).sub
    (((hc.const_mul 4).mul (ha.norm.pow 6)).mul (hr.inner he))

theorem continuous_strainSourceRate (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) : Continuous (strainSourceRate δ u) := by
  have hu1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 2) hu
  exact (((continuous_fullVorticity u hu1).norm.pow 6).const_mul 2).mul
    ((continuous_projectionResidual δ hδ u hu).inner (continuous_strainSource u hu1))

/-- Spatial integrability is proved from the actual fields. This is not
a time-uniform bound on either surviving signed contribution. -/
theorem integral_normalRate_add_strainSourceRate_le (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0) (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∫ x : T3, normalRate δ u x (topStrain u x) + strainSourceRate δ u x) ≤ strainMaterialWork δ u := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu
  have hiN : Integrable (fun x : T3 ↦ normalRate δ u x (topStrain u x) + strainSourceRate δ u x) :=
    ((continuous_normalRate δ hδ u hu2).add (continuous_strainSourceRate δ hδ u hu2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiS : Integrable (strainMaterialRate δ u) :=
    (continuous_strainMaterialRate δ hδ u hu2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact integral_mono hiN hiS (normalRate_add_strainSourceRate_le δ hδ u hu hd hr)

end Mettapedia.FluidDynamics.NavierStokes.LocalProjectionSpectralRate
