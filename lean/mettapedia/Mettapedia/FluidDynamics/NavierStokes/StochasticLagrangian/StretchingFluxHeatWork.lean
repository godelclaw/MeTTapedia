import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxVariation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalStretchingFluxDissipation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxHeatAdjoint
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullVelocityRHSReality

/-!
# Material and pressure resolution of the actual heat-work budget

The physical cubic product rule identifies the resolved Fourier variation
with the actual material work minus transport. The independent heat
commutator remains paired with its constructed coefficient test. All
terms stay signed throughout the infinite heat and physical-time integrals.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StretchingFluxHeatWork

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeCurlOutputTail PancakeHigherDerivativeMoments PancakeBlockReality
open PancakeFrequencyProjectorCommutator PancakePeriodicVorticityEquation
open PancakeCoefficientLimitEquation FullVelocityRHSReality
open LongitudinalGradientFlux LocalStretchingFluxTime StretchingFluxVariation
open LongitudinalProjectedTransport LongitudinalVorticityTime StretchingFluxMaterialRate FullLambVector
open StretchingFluxProjectedEvolution StretchingFluxProjectedDiffusion
open ExchangedFluxSeriesBudget ExchangedFluxHeatRepresentation ExchangedFluxHeatAdjoint
open FourierHeatFlow

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem infiniteVelocityRHS_transverse (ν : ℝ) (u : FourierVelocity)
    (hd : ∀ q, modeDot q (u q) = 0) (q : Wavevector) :
    modeDot q (infiniteVelocityRHS ν u q) = 0 := by
  by_cases hq : q = 0
  · subst q
    simp only [modeDot, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero]
  have hp := modeDot_lerayMode_eq_zero q ((-unitTorusDerivativePhase) • infiniteConvection u q)
    (modeSquare_ne_zero_of_frequencyVec_ne_zero (frequencyVec_ne_zero hq))
  have hv : modeDot q (unitTorusViscousVorticityCoeff ν u q) = 0 := by
    rw [unitTorusViscousVorticityCoeff, modeDot_smul, hd, mul_zero]
  simpa [infiniteVelocityRHS, modeDot, mul_add, Finset.sum_add_distrib] using
    congrArg₂ (· + ·) hp hv

/-- No Fourier rate or physical time derivative is supplied as an extra object. -/
theorem fluxVariation_velocityRHS (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    fluxVariation u (infiniteVelocityRHS ν u) = projectedRate ν u := by
  rw [fluxVariation_eq_projected_variationField u _
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
    (VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS 1 ν u hu)
    hd (infiniteVelocityRHS_transverse ν u hd) hr (infiniteVelocityRHS_conjugate ν u hr),
    variationField_velocityRHS]
  rfl

theorem inner_fluxVariation_velocityRHS (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    ⟪fluxVariation u (infiniteVelocityRHS ν u), projectedFlux 0 u⟫ =
      materialWork ν u - transportWork u := by
  rw [fluxVariation_velocityRHS ν u hu hd hr, real_inner_comm]
  exact eulerianWork_eq_material_sub_transport ν u hu hd hr

/-- The same Fourier work has the exact physical viscous dissipation. -/
theorem inner_fluxVariation_velocityRHS_add_dissipation (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    ⟪fluxVariation u (infiniteVelocityRHS ν u), projectedFlux 0 u⟫ + ν * dissipation u =
      LocalStretchingFluxDissipation.drivingWork ν u := by
  rw [inner_fluxVariation_velocityRHS ν u hu hd hr,
    LocalStretchingFluxDissipation.drivingWork_eq ν u hu hd hr]

/-- The resolved source exposes the pressure-Hessian action and the exact
off-diagonal projection residual as signed spatial integrals. -/
theorem inner_inviscidVariation_eq_spatial_work (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    let F := projectedFluxJet u (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu)
    ⟪fluxVariation u (infiniteVelocityRHS 0 u), projectedFlux 0 u⟫ =
      (∫ x : T3, ∑ j, ⟪(F j).value x,
        -(stretchingField u x j • stretchingField u x) +
          vorticityField u x j • pressureAction u x⟫) -
      ∫ x : T3, ∑ j, ∑ k, velocityJet u j x k *
        ⟪(F k).value x, fluxField 0 u j x - (F j).value x⟫ := by
  dsimp only
  rw [inner_fluxVariation_velocityRHS 0 u hu hd hr, materialWork_eq_integral 0 u hu hd hr,
    transportWork_eq_integral u (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) hd hr]
  simp only [stretchingDiffusion, zero_smul, PiLp.zero_apply, smul_zero,
    add_zero, Finset.sum_const_zero, sub_zero]

/-- The material-resolved heat source, with the actual commutator test. -/
def materialHeatWork (ν σ : ℝ) (u : FourierVelocity) : ℝ :=
  materialWork 0 (FourierHeatFlow.coefficients ν σ u) -
    transportWork (FourierHeatFlow.coefficients ν σ u) +
      ∑' q, ⟪coefficientVec (nonlinearCommutator ν σ u q), heatCoefficientTest ν σ u q⟫

theorem coefficientWorkDensity_eq_materialHeatWork {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    coefficientWorkDensity ν σ u = materialHeatWork ν σ u := by
  rw [coefficientWorkDensity, inner_fluxVariation_velocityRHS 0 _
    (summable_fourierMoment_coefficients hν hσ u 3 hu)
    (coefficients_transverse ν σ u hd) (coefficients_reality ν σ u hr)]
  rfl

theorem fullGramWork_eq_integral_materialHeatWork {ν : ℝ} (hν : 0 < ν)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    fullGramWork ν u = ∫ σ : ℝ in Set.Ioi 0, materialHeatWork ν σ u := by
  rw [fullGramWork_eq_integral_coefficientWorkDensity hν u hu hd hr]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro σ hσ
  exact coefficientWorkDensity_eq_materialHeatWork hν.le hσ.le u hu hd hr

theorem integrableOn_materialHeatWork {ν : ℝ} (hν : 0 < ν)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    IntegrableOn (fun σ ↦ materialHeatWork ν σ u) (Set.Ioi 0) := by
  apply (integrableOn_coefficientWorkDensity hν u hu hd hr).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  exact coefficientWorkDensity_eq_materialHeatWork hν.le hσ.le u hu hd hr

open PancakeLocalInfiniteVelocity

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)

include hν hB hg hSum hu

theorem intervalIntegrable_integral_materialHeatWork (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ ∫ σ : ℝ in Set.Ioi 0, materialHeatWork ν σ (s.coefficients τ))
      volume 0 t := by
  apply (intervalIntegrable_fullGramWork s hν hB g hg hSum hu t ht).congr
  intro τ hτ
  have hτT : τ ∈ Set.Icc (0 : ℝ) T :=
    (Set.Icc_subset_Icc le_rfl ht.2) (Set.uIcc_of_le ht.1 ▸ Set.uIoc_subset_uIcc hτ)
  exact fullGramWork_eq_integral_materialHeatWork hν _
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτT)) (s.transverse τ) (s.reality τ)

theorem full_material_heat_gram_energy_identity (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    fullGramEnergy ν (s.coefficients t) +
        (∫ τ in (0 : ℝ)..t, ‖projectedFlux 0 (s.coefficients τ)‖ ^ 2) =
      fullGramEnergy ν u₀ +
        2 * (∫ τ in (0 : ℝ)..t, ∫ σ : ℝ in Set.Ioi 0, materialHeatWork ν σ (s.coefficients τ)) := by
  have he : (∫ τ in (0 : ℝ)..t, fullGramWork ν (s.coefficients τ)) =
      ∫ τ in (0 : ℝ)..t, ∫ σ : ℝ in Set.Ioi 0, materialHeatWork ν σ (s.coefficients τ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro τ hτ
    have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le.trans ht.2⟩
    exact fullGramWork_eq_integral_materialHeatWork hν _
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτT)) (s.transverse τ) (s.reality τ)
  simpa only [he] using full_gram_energy_identity s hν hB g hg hSum hu t ht

open PancakeHigherLocalVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks

omit hν hB hg hSum hu in
/-- Smooth physical data construct the complete material-resolved heat balance. -/
theorem exists_physical_local_material_heat_balance (ν : ℝ) (hν : 0 < ν)
    (f : UnitAddTorus (Fin 3) → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          fullGramEnergy ν (s.coefficients t) +
              (∫ τ in (0 : ℝ)..t, ‖projectedFlux 0 (s.coefficients τ)‖ ^ 2) =
            fullGramEnergy ν (torusFourierVelocity f) +
              2 * (∫ τ in (0 : ℝ)..t, ∫ σ : ℝ in Set.Ioi 0, materialHeatWork ν σ (s.coefficients τ)) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, full_material_heat_gram_energy_identity s hν hB g hg hSum hu⟩

end Mettapedia.FluidDynamics.NavierStokes.StretchingFluxHeatWork
