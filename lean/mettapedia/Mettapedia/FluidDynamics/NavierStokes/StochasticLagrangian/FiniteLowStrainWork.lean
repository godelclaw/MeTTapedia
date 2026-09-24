import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteStrainKineticEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularSourceBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeWeightVariationGradient
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredAngularStrainIntegral

/-!
# Actual low-strain payment in the corrected angular balance

The source strain is reconstructed from a fixed finite set of modes of
the full velocity. It acts on the separately retained vorticity. Its work
is paid by the full kinetic energy, with no bound assumed for the full
strain or the vorticity gradient. The residual retains the difference
between retained strain and full-velocity low strain, together with every
output of the subgrid force. No relation between the two cutoffs is needed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork

open scoped RealInnerProductSpace Matrix.Norms.Elementwise
open MeasureTheory
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeFourierMaterialPaths PancakeFourierStrainGradient PancakePhysicalDiffusionLimit
open PancakeHaarTransportRate PancakeFourierTranslationCurve PancakeFilteredStrainDynamics
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticityEighthMoment
open LocalAlignmentForcing FourierFiniteSupport FiniteAngularSourceWork FiniteAngularInviscidWork
open FiniteStrainKineticEnergy FiniteAngularSourceBound FilteredAngularStrainIntegral
open PancakeLocalInfiniteVelocity LocalKineticEnergy InfiniteConvectionEnergy
open PancakeCurlOutputTail

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def lowStrainSource (Q : Finset Wavevector) (u v : FourierVelocity) (x : T3) : R3 :=
  (spatialStrain Q u x).1 (fullVorticity v x)

def lowStrainSourceDerivative (Q : Finset Wavevector) (u v : FourierVelocity)
    (j : Fin 3) (x : T3) : R3 :=
  strainGradient Q u x j (fullVorticity v x) +
    (spatialStrain Q u x).1 (fullCurlGradient v j x)

def lowStrainWork (κ : ℝ) (Q : Finset Wavevector) (u v : FourierVelocity) : ℝ :=
  ∫ x : T3, ⟪correctedGradient κ v x, lowStrainSource Q u v x⟫

def lowStrainGrowthCoefficient (Q : Finset Wavevector) (E : ℝ) : ℝ :=
  577 * strainEnergyBound Q E + 360 * strainGradientEnergyBound Q E

theorem lowStrainGrowthCoefficient_nonneg (Q : Finset Wavevector) (E : ℝ) :
    0 ≤ lowStrainGrowthCoefficient Q E := by
  unfold lowStrainGrowthCoefficient
  exact add_nonneg (mul_nonneg (by norm_num) (strainEnergyBound_nonneg Q E))
    (mul_nonneg (by norm_num) (strainGradientEnergyBound_nonneg Q E))

theorem continuous_lowStrainSource (P Q : Finset Wavevector) (u v : FourierVelocity)
    (hv : ∀ q, q ∉ P → v q = 0) : Continuous (lowStrainSource Q u v) :=
  (continuous_subtype_val.comp (PancakeMaterialDiffusionBudget.continuous_strain Q u)).clm_apply
    (continuous_fullVorticity v (summable_fourierMoment P v hv 1))

theorem continuous_lowStrainSourceDerivative (P Q : Finset Wavevector) (u v : FourierVelocity)
    (hv : ∀ q, q ∉ P → v q = 0) (j : Fin 3) : Continuous (lowStrainSourceDerivative Q u v j) := by
  have hS : Continuous (fun x : T3 ↦ strainGradient Q u x j) := by
    rw [← mappedField_strainGradient]
    exact PancakeMappedFourierDiffusion.continuous_mappedField _ _ _
  exact (hS.clm_apply (continuous_fullVorticity v (summable_fourierMoment P v hv 1))).add
    ((continuous_subtype_val.comp (PancakeMaterialDiffusionBudget.continuous_strain Q u)).clm_apply
      (LocalSquaredGapGradient.continuous_fullCurlGradient v j))

theorem hasDerivAt_lowStrainSource_shift (P Q : Finset Wavevector) (u v : FourierVelocity)
    (hv : ∀ q, q ∉ P → v q = 0) (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ lowStrainSource Q u v (x + coordinateShift j t))
      (lowStrainSourceDerivative Q u v j (x + coordinateShift j h)) h := by
  have hS := PancakeWeightVariationGradient.hasDerivAt_spatialStrain_shift Q u j h x
  have ha := hasDerivAt_fullVorticity_shift v (summable_fourierMoment P v hv 3) j x h
  simpa only [lowStrainSource, lowStrainSourceDerivative] using hS.clm_apply ha

theorem norm_lowStrainSource_le (Q : Finset Wavevector) (u v : FourierVelocity)
    (hu : Summable (fun q ↦ ‖coefficientVec (u q)‖ ^ 2))
    (E : ℝ) (hE : kineticEnergy u ≤ E) (x : T3) :
    ‖lowStrainSource Q u v x‖ ≤ strainEnergyBound Q E * ‖fullVorticity v x‖ :=
  ((spatialStrain Q u x).1.le_opNorm _).trans (mul_le_mul_of_nonneg_right
    (norm_spatialStrain_le_energyBound Q u hu E hE x) (norm_nonneg _))

theorem norm_lowStrainSourceDerivative_le (Q : Finset Wavevector) (u v : FourierVelocity)
    (hu : Summable (fun q ↦ ‖coefficientVec (u q)‖ ^ 2))
    (E : ℝ) (hE : kineticEnergy u ≤ E) (j : Fin 3) (x : T3) :
    ‖lowStrainSourceDerivative Q u v j x‖ ≤
      strainEnergyBound Q E * ‖fullCurlGradient v j x‖ +
        strainGradientEnergyBound Q E * ‖fullVorticity v x‖ := by
  apply (norm_add_le _ _).trans
  calc
    _ ≤ ‖strainGradient Q u x j‖ * ‖fullVorticity v x‖ +
        ‖(spatialStrain Q u x).1‖ * ‖fullCurlGradient v j x‖ :=
      add_le_add ((strainGradient Q u x j).le_opNorm _) ((spatialStrain Q u x).1.le_opNorm _)
    _ ≤ strainGradientEnergyBound Q E * ‖fullVorticity v x‖ +
        strainEnergyBound Q E * ‖fullCurlGradient v j x‖ := by
      gcongr
      · exact norm_strainGradient_le_energyBound Q u hu E hE x j
      · exact norm_spatialStrain_le_energyBound Q u hu E hE x
    _ = _ := add_comm _ _

theorem abs_lowStrainWork_le (P Q : Finset Wavevector) (u v : FourierVelocity)
    (hv : ∀ q, q ∉ P → v q = 0)
    (hu : Summable (fun q ↦ ‖coefficientVec (u q)‖ ^ 2))
    (E : ℝ) (hE : kineticEnergy u ≤ E) (κ R : ℝ) (hκ : 0 < κ)
    (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R) (hscale : 1 + (8 * Real.pi * R) ^ 2 ≤ κ) :
    |lowStrainWork κ Q u v| ≤ lowStrainGrowthCoefficient Q E * meanEnergy v :=
  abs_integral_correctedGradient_source_le P v hv (lowStrainSource Q u v)
    (lowStrainSourceDerivative Q u v) (continuous_lowStrainSource P Q u v hv)
    (continuous_lowStrainSourceDerivative P Q u v hv) (hasDerivAt_lowStrainSource_shift P Q u v hv)
    _ _ (strainEnergyBound_nonneg Q E) (strainGradientEnergyBound_nonneg Q E)
    (norm_lowStrainSource_le Q u v hu E hE) (norm_lowStrainSourceDerivative_le Q u v hu E hE)
    κ R hκ hP hscale

/-- The low source uses the full solution, not the retained velocity.
Its coefficient depends only on fixed source modes and initial energy. -/
theorem abs_lowStrainWork_solution_le {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 ≤ ν)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (P Q : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (κ R : ℝ) (hκ : 0 < κ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (hscale : 1 + (8 * Real.pi * R) ^ 2 ≤ κ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    |lowStrainWork κ Q (s.coefficients t) (filteredVelocity χ (s.coefficients t))| ≤
      lowStrainGrowthCoefficient Q (kineticEnergy u₀) * meanEnergy (filteredVelocity χ (s.coefficients t)) :=
  abs_lowStrainWork_le P Q _ _ (fun q hq ↦ by simp [filteredVelocity, hcut q hq])
    (local_kineticEnergy s t ht).1 _ (energy_le_initial s hν g hg hSum hu t ht) κ R hκ hP hscale

def residualStrainSource (Q : Finset Wavevector) (u v : FourierVelocity) (x : T3) : R3 :=
  (fullStrainOperator v x - (spatialStrain Q u x).1) (fullVorticity v x)

def residualStrainSubgridWork (κ : ℝ) (Q : Finset Wavevector)
    (χ : Wavevector → ℂ) (u : FourierVelocity) : ℝ :=
  (∫ x : T3, ⟪correctedGradient κ (filteredVelocity χ u) x,
    residualStrainSource Q u (filteredVelocity χ u) x⟫) + fullSubgridWork κ χ u

theorem strainSubgridWork_eq_low_add_residual (κ : ℝ) (P Q : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity) :
    strainSubgridWork κ χ u = lowStrainWork κ Q u (filteredVelocity χ u) +
      residualStrainSubgridWork κ Q χ u := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ u q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have ha := continuous_fullVorticity _ (summable_fourierMoment P _ hs 1)
  have hF := continuous_correctedGradient κ P _ hs
  have hS := continuous_fullStrainOperator _ (summable_fourierMoment P _ hs 1)
  have hi : Integrable (fun x : T3 ↦ ⟪correctedGradient κ (filteredVelocity χ u) x,
      fullStrainOperator (filteredVelocity χ u) x (fullVorticity (filteredVelocity χ u) x)⟫) :=
    (hF.inner (hS.clm_apply ha)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hl : Integrable (fun x : T3 ↦ ⟪correctedGradient κ (filteredVelocity χ u) x,
      lowStrainSource Q u (filteredVelocity χ u) x⟫) :=
    (hF.inner (continuous_lowStrainSource P Q u _ hs)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold residualStrainSubgridWork residualStrainSource
  simp only [sub_apply, inner_sub_right]
  have hdiff := integral_sub hi hl
  simp only [lowStrainSource] at hdiff
  rw [hdiff, integral_correctedGradient_strain κ P _ hs]
  unfold strainSubgridWork lowStrainWork lowStrainSource
  ring

end Mettapedia.FluidDynamics.NavierStokes.FiniteLowStrainWork
