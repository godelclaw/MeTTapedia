import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalViscousSplit

/-!
# Joint material-rate estimate with a fixed-low diffusion payment

The nonlinear and regularization terms have an explicit continuous
envelope. The spatial estimate retains half the spectral-residual damping
and pays viscosity using the actual finite Fourier Laplacian. A single
integrable full material rate is an explicit input; no selected-frame
coordinate rate is assumed measurable.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeMaterialDiffusionBudget

open scoped Topology RealInnerProductSpace Matrix.Norms.Elementwise
open MeasureTheory PeriodicFourierTriad PancakePeriodicVorticityEquation PancakePeriodicCoherentSplit
open PancakeFourierMaterialPaths PancakeFourierStrainGradient PancakeMappedFourierDiffusion
open PancakePhysicalLaplacian PancakePhysicalDiffusionLimit PancakePhysicalSpectralDefect
open PancakeDyadicDirectionEvolution PancakeRegularizedMaterialRate PancakeFilteredStrainDynamics
open PancakeGalerkinKineticEnergy PancakeSpatialStrainEvolution PancakePhysicalViscousSplit
open PancakeMovingBlockEvolution PancakeFourierPressureStrain PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeRegularizedDiffusion
open PancakeSpectralDefectEvolution PancakeSpectralFiniteDifference PancakeLowDiffusionBudget
open PancakeTopEigenvalueDerivative PancakeFourierTranslationCurve
open PancakeWeakDiffusionLimit

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def nonviscousEnvelope (S : SymmetricStrain) (w : R3) (R : R3 →L[ℝ] R3) (f : R3) (delta : ℝ) : ℝ :=
  2 * ‖R‖ * ‖w‖ ^ 2 + 2 * ‖f‖ ^ 2 + 2 * delta * ⟪w, S.1 w + f⟫

theorem material_linearRate_le (S : SymmetricStrain) (w : R3) (R A : R3 →L[ℝ] R3)
    (f b : R3) (delta nu : ℝ) :
    linearRate S delta w (-S.1 * S.1 + R + nu • A) (S.1 w + f + nu • b) +
      (1 / 2 : ℝ) * ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 ≤
      nu * linearRate S delta w A b + nonviscousEnvelope S w R f delta := by
  rw [linearRate_viscous_split]
  have hR := (le_abs_self (remainderAnisotropy R (topVector S) w)).trans
    (abs_remainderAnisotropy_le R (topVector S) w (topVector_norm S))
  have hf := spectralDefect_forcing_young (spectralResidual S.1 (topEigenvalue S) w) f (1 / 2) (by norm_num)
  norm_num at hf
  unfold nonviscousEnvelope
  linarith

theorem continuous_matrixReconstruction (modes : Finset Wavevector) (a : FourierMatrix) :
    Continuous (matrixReconstruction modes a) := by
  have hc : Continuous (fun x : T3 ↦ fourierField modes a x) := (fourierField modes a).continuous
  simpa only [fourierField_matrix_eq] using hc

theorem continuous_strain (modes : Finset Wavevector) (u : FourierVelocity) :
    Continuous (spatialStrain modes u) := by
  apply Continuous.subtype_mk
  exact realMatrixOperatorCLM.continuous.comp (continuous_matrixReconstruction modes (strainCoeff u))

theorem continuous_vorticity (modes : Finset Wavevector) (u : FourierVelocity) :
    Continuous (spatialVorticity modes u) := by
  rw [← mappedField_vorticity]
  exact continuous_mappedField _ _ _

theorem continuous_strainRemainder (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) : Continuous (spatialStrainRemainder chi modes outputs u nu) := by
  have hW : Continuous (spatialSpin modes (filteredVelocity chi u)) :=
    realMatrixOperatorCLM.continuous.comp (continuous_matrixReconstruction modes (spinCoeff (filteredVelocity chi u)))
  have hR : Continuous (spatialStrainForcing chi modes outputs u nu) :=
    realMatrixOperatorCLM.continuous.comp (continuous_matrixReconstruction outputs (strainForcingCoeff chi modes u nu))
  exact (hW.mul hW).neg.add hR

theorem continuous_vorticityForcing (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) : Continuous (spatialVorticityForcing chi modes u nu) := by
  have hv : Continuous (fun x : T3 ↦ finiteFourierReconstruction modes (filteredVelocity chi u) x) := by
    have hc : Continuous (fun x : T3 ↦ fourierField modes (filteredVelocity chi u) x) :=
      (fourierField modes (filteredVelocity chi u)).continuous
    simpa only [fourierField_vector_eq] using hc
  have hphase : ∀ q, Continuous (fun x : T3 ↦ finiteVelocityCharacterRate modes (filteredVelocity chi u) q x) := by
    intro q
    simp only [finiteVelocityCharacterRate_eq, modeDot]
    fun_prop
  have hM : Continuous (spatialVorticityMaterialRate chi modes u nu) := by
    apply complexRealPartEuclideanCLM.continuous.comp
    change Continuous (fun x : T3 ↦ movingFiniteFourierDerivative modes (fourierCurl u)
      (finiteUnitTorusVorticityRHS modes modes (fourierCurl u) (fourierCurl u) nu)
      (fun q ↦ finiteVelocityCharacterRate modes (filteredVelocity chi u) q x) x)
    unfold movingFiniteFourierDerivative
    apply continuous_finsetSum
    intro q _
    exact ((hphase q).smul continuous_const).add ((UnitAddTorus.mFourier q).continuous.smul continuous_const)
  exact hM.sub (((continuous_subtype_val.comp (continuous_strain modes (filteredVelocity chi u))).clm_apply
    (continuous_vorticity modes u)))

theorem continuous_nonviscousEnvelope (S : T3 → SymmetricStrain) (w : T3 → R3)
    (R : T3 → R3 →L[ℝ] R3) (f : T3 → R3) (delta : ℝ)
    (hS : Continuous S) (hw : Continuous w) (hR : Continuous R) (hf : Continuous f) :
    Continuous (fun x ↦ nonviscousEnvelope (S x) (w x) (R x) (f x) delta) := by
  unfold nonviscousEnvelope
  have hO := continuous_subtype_val.comp hS
  fun_prop

theorem continuous_residual (S : T3 → SymmetricStrain) (w : T3 → R3)
    (hS : Continuous S) (hw : Continuous w) :
    Continuous (fun x ↦ spectralResidual (S x).1 (topEigenvalue (S x)) (w x)) := by
  exact ((lipschitzWith_topEigenvalue.continuous.comp hS).smul hw).sub
    ((continuous_subtype_val.comp hS).clm_apply hw)

def physicalMaterialRate (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi u) x
  let w := spatialVorticity modes u x
  linearRate S delta w (-S.1 * S.1 + spatialStrainRemainder chi modes outputs u nu x)
    (S.1 w + spatialVorticityForcing chi modes u nu x)

def physicalNonviscousEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) : ℝ :=
  nonviscousEnvelope (spatialStrain modes (filteredVelocity chi u) x) (spatialVorticity modes u x)
    (spatialStrainRemainder chi modes outputs u 0 x) (spatialVorticityForcing chi modes u 0 x) delta

def physicalMaterialAbsEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi u) x
  let w := spatialVorticity modes u x
  2 * ‖-S.1 * S.1 + spatialStrainRemainder chi modes outputs u nu x‖ * ‖w‖ ^ 2 +
    2 * ‖regularizedGap S delta w‖ * ‖S.1 w + spatialVorticityForcing chi modes u nu x‖

theorem abs_physicalMaterialRate_le (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3) :
    |physicalMaterialRate chi modes outputs u delta nu x| ≤
      physicalMaterialAbsEnvelope chi modes outputs u delta nu x :=
  abs_linearRate_le _ _ _ _ _

theorem continuous_physicalMaterialAbsEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) : Continuous (physicalMaterialAbsEnvelope chi modes outputs u delta nu) := by
  have hS := continuous_strain modes (filteredVelocity chi u)
  have hO := continuous_subtype_val.comp hS
  have hw := continuous_vorticity modes u
  have hA := (hO.neg.mul hO).add (continuous_strainRemainder chi modes outputs u nu)
  have hb := (hO.clm_apply hw).add (continuous_vorticityForcing chi modes u nu)
  have hK := continuous_gapApplied _ _ delta hS hw
  exact (((hA.norm.const_mul 2).mul (hw.norm.pow 2)).add ((hK.norm.const_mul 2).mul hb.norm))

theorem continuous_physicalNonviscousEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) : Continuous (physicalNonviscousEnvelope chi modes outputs u delta) :=
  continuous_nonviscousEnvelope _ _ _ _ delta (continuous_strain modes (filteredVelocity chi u))
    (continuous_vorticity modes u) (continuous_strainRemainder chi modes outputs u 0)
    (continuous_vorticityForcing chi modes u 0)

theorem physicalMaterialRate_le (chi : Wavevector → ℂ) (low modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3)
    (hlow : low ⊆ modes) (hout : modes ⊆ outputs) (hchi : ∀ q, q ∉ low → chi q = 0) :
    physicalMaterialRate chi modes outputs u delta nu x + (1 / 2 : ℝ) *
      ‖spectralResidual (spatialStrain modes (filteredVelocity chi u) x).1
        (topEigenvalue (spatialStrain modes (filteredVelocity chi u) x)) (spatialVorticity modes u x)‖ ^ 2 ≤
      nu * linearRate (spatialStrain low (filteredVelocity chi u) x) delta (spatialVorticity modes u x)
        (strainLaplacian low (filteredVelocity chi u) x) (vorticityLaplacian modes u x) +
      physicalNonviscousEnvelope chi modes outputs u delta x := by
  have hR := spatialStrainRemainder_viscous_split chi modes outputs u nu x
  rw [strainLaplacian_filtered_subset low outputs chi u x (hlow.trans hout) hchi] at hR
  have hf := spatialVorticityForcing_viscous_split chi modes u nu x
  unfold physicalMaterialRate physicalNonviscousEnvelope
  dsimp only
  rw [hR, hf, ← add_assoc, ← add_assoc]
  have hm := material_linearRate_le (spatialStrain modes (filteredVelocity chi u) x) (spatialVorticity modes u x)
    (spatialStrainRemainder chi modes outputs u 0 x) (strainLaplacian low (filteredVelocity chi u) x)
    (spatialVorticityForcing chi modes u 0 x) (vorticityLaplacian modes u x) delta nu
  rw [spatialStrain_filtered_subset low modes chi u x hlow hchi] at hm ⊢
  exact hm

/-- A full material-rate estimate, conditional only on an integrable
AE lower envelope of that rate. The physical forcing envelope's
integrability and the diffusion payment are proved here. -/
theorem integral_materialRate_paid (chi : Wavevector → ℂ) (low modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (F : T3 → ℝ)
    (hd : 0 < delta) (hnu : 0 ≤ nu) (hlow : low ⊆ modes) (hout : modes ⊆ outputs)
    (hchi : ∀ q, q ∉ low → chi q = 0) (hF : Integrable F)
    (hpoint : ∀ᵐ x : T3, F x ≤ physicalMaterialRate chi modes outputs u delta nu x) :
    (∫ x : T3, F x) + (1 / 2 : ℝ) * (∫ x : T3,
      ‖spectralResidual (spatialStrain modes (filteredVelocity chi u) x).1
        (topEigenvalue (spatialStrain modes (filteredVelocity chi u) x)) (spatialVorticity modes u x)‖ ^ 2) ≤
      (16 * nu / delta) * strainGradientCutoffWeight low chi *
        PancakeViscousMisalignmentAbsorption.fullEnergy modes u *
        PancakeViscousMisalignmentAbsorption.fullEnergy modes (fourierCurl u) +
      ∫ x : T3, physicalNonviscousEnvelope chi modes outputs u delta x := by
  let Z := fun x ↦ ‖spectralResidual (spatialStrain modes (filteredVelocity chi u) x).1
    (topEigenvalue (spatialStrain modes (filteredVelocity chi u) x)) (spatialVorticity modes u x)‖ ^ 2
  have hZ : Integrable Z := ((continuous_residual _ _ (continuous_strain modes (filteredVelocity chi u))
    (continuous_vorticity modes u)).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (physicalNonviscousEnvelope chi modes outputs u delta) :=
    (continuous_physicalNonviscousEnvelope chi modes outputs u delta).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp : ∀ᵐ x : T3, F x + (1 / 2 : ℝ) * Z x ≤
      nu * linearRate (spatialStrain low (filteredVelocity chi u) x) delta (spatialVorticity modes u x)
        (strainLaplacian low (filteredVelocity chi u) x) (vorticityLaplacian modes u x) +
      physicalNonviscousEnvelope chi modes outputs u delta x := by
    filter_upwards [hpoint] with x hx
    have hm := physicalMaterialRate_le chi low modes outputs u delta nu x hlow hout hchi
    dsimp only [Z]
    linarith
  have hm := integral_laplacian_diffusion_energy_paid low modes chi u (fun x ↦ F x + (1 / 2 : ℝ) * Z x)
    (physicalNonviscousEnvelope chi modes outputs u delta) delta nu hd hnu hlow
    (hF.add (hZ.const_mul _)) hB hp
  rw [integral_add hF (hZ.const_mul (1 / 2)), integral_const_mul] at hm
  exact hm

end Mettapedia.FluidDynamics.NavierStokes.PancakeMaterialDiffusionBudget
