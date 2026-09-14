import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxCoefficients
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxHeatWork

/-!
# Signed output-frequency work along the actual Navier--Stokes equation

The canonical coefficient pairing is the physical Eulerian work, with its
pressure and transport terms intact. Subtracting viscosities isolates the
ordinary heat direction. Its work is twice the mixed contribution minus
the projected gradient dissipation; no favorable sign is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StretchingFluxSpectralEvolution

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis UnitTorusGradientProjection ContinuousFieldBilinear
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeBlockReality PancakePeriodicVorticityEquation PancakeCoefficientLimitEquation
open PancakeInfiniteSpatialLaplacian FullVelocityRHSReality
open LongitudinalVorticityTime LongitudinalGradientFlux LocalStretchingFluxTime
open StretchingFluxVariation StretchingFluxCoefficients StretchingFluxHeatWork
open StretchingFluxProjectedEvolution StretchingFluxProjectedDiffusion

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def spectralRHSWork (ν : ℝ) (u : FourierVelocity) : ℝ :=
  spectralVariationWork u (infiniteVelocityRHS ν u)

theorem spectralRHSWork_eq_eulerianWork (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    spectralRHSWork ν u = LocalStretchingFluxTime.eulerianWork ν u := by
  rw [spectralRHSWork, ← physical_variation_work u _
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
    (VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS 1 ν u hu)
    hr (infiniteVelocityRHS_conjugate ν u hr), variationField_velocityRHS]
  exact (inner_gradientProjection_gradientProjection _ _).symm

theorem spectralRHSWork_eq_material_sub_transport (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    spectralRHSWork ν u = materialWork ν u - transportWork u := by
  rw [spectralRHSWork_eq_eulerianWork ν u hu hr]
  exact eulerianWork_eq_material_sub_transport ν u hu hd hr

theorem spectralRHSWork_add_dissipation (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    spectralRHSWork ν u + ν * dissipation u =
      LocalStretchingFluxDissipation.drivingWork ν u := by
  rw [spectralRHSWork_eq_material_sub_transport ν u hu hd hr,
    LocalStretchingFluxDissipation.drivingWork_eq ν u hu hd hr]

theorem spectralRHSWork_affine_viscosity (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    spectralRHSWork ν u = spectralRHSWork 0 u + ν * (2 * mixedWork u - dissipation u) := by
  rw [spectralRHSWork_eq_material_sub_transport ν u hu hd hr,
    spectralRHSWork_eq_material_sub_transport 0 u hu hd hr]
  have h := materialWork_add_dissipation ν u hu hd hr
  linarith

theorem variationField_sub_right (u v w : FourierVelocity)
    (hv : Summable (fourierMoment 1 v)) (hw : Summable (fourierMoment 1 w)) (j : Fin 3) :
    variationField u (v - w) j = variationField u v j - variationField u w j := by
  apply ContinuousMap.ext
  intro x
  ext i
  simp only [variationField, stretchingVariationField,
    vorticityField_sub v w hv hw, velocityDerivativeField_sub v w hv hw,
    pointwise, ContinuousMap.coe_mk, ContinuousLinearMap.lsmul_apply, componentField_apply,
    ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.neg_apply,
    Fin.sum_univ_three, PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply,
    smul_eq_mul]
  ring

theorem velocityRHS_one_sub_zero (u : FourierVelocity) :
    infiniteVelocityRHS 1 u - infiniteVelocityRHS 0 u = laplacianCoeff u := by
  ext q i
  simp [infiniteVelocityRHS, unitTorusViscousVorticityCoeff, laplacianCoeff]

theorem summable_fourierMoment_laplacian (m : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (m + 2) u)) :
    Summable (fourierMoment m (laplacianCoeff u)) := by
  rw [← velocityRHS_one_sub_zero]
  exact CurlEigenfieldDefect.summable_fourierMoment_sub m _ _
    (VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS m 1 u hu)
    (VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS m 0 u hu)

theorem laplacianCoeff_reality (u : FourierVelocity)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (q : Wavevector) :
    laplacianCoeff u (-q) = coefficientConjugate (laplacianCoeff u q) := by
  rw [← velocityRHS_one_sub_zero]
  ext i
  simp [Pi.sub_apply, infiniteVelocityRHS_conjugate _ u hr, coefficientConjugate]

/-- The spectral expression is the actual heat-direction work, not a
Laplacian applied to the already formed cubic flux. -/
theorem spectral_heat_work_eq_difference (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    spectralVariationWork u (laplacianCoeff u) = spectralRHSWork 1 u - spectralRHSWork 0 u := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hv := VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS 1 1 u hu
  have hw := VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS 1 0 u hu
  rw [← physical_variation_work u _ hu1 (summable_fourierMoment_laplacian 1 u hu)
    hr (laplacianCoeff_reality u hr)]
  have he : variationField u (laplacianCoeff u) =
      variationField u (infiniteVelocityRHS 1 u) - variationField u (infiniteVelocityRHS 0 u) := by
    rw [← velocityRHS_one_sub_zero]
    exact funext (variationField_sub_right u _ _ hv hw)
  rw [he]
  change ⟪_, (tensorEmbedding (d := Fin 3) (E := R3)) (_ - _)⟫ = _
  rw [map_sub, inner_sub_right]
  change ⟪projectedFlux 0 u, toTensorL2 (variationField u (infiniteVelocityRHS 1 u))⟫ -
    ⟪projectedFlux 0 u, toTensorL2 (variationField u (infiniteVelocityRHS 0 u))⟫ = _
  rw [
    physical_variation_work u _ hu1 hv hr (infiniteVelocityRHS_conjugate 1 u hr),
    physical_variation_work u _ hu1 hw hr (infiniteVelocityRHS_conjugate 0 u hr)]
  rfl

theorem spectral_heat_work_eq_mixed_sub_dissipation (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    spectralVariationWork u (laplacianCoeff u) = 2 * mixedWork u - dissipation u := by
  rw [spectral_heat_work_eq_difference u hu hr,
    spectralRHSWork_affine_viscosity 1 u hu hd hr]
  ring

open PancakeLocalInfiniteVelocity PancakeHigherLocalVelocity PancakeContinuousCoordinateJet
open PancakeArbitraryDataBlocks

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hB hg hSum hu

theorem continuousOn_spectralRHSWork :
    ContinuousOn (fun t ↦ spectralRHSWork ν (s.coefficients t)) (Set.Icc (0 : ℝ) T) := by
  apply (LocalStretchingFluxBalance.continuousOn_eulerianWork s hB g hg hSum hu).congr
  intro t ht
  exact spectralRHSWork_eq_eulerianWork ν _
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)) (s.reality t)

theorem intervalIntegrable_spectralRHSWork {a b : ℝ} (hab : a ≤ b)
    (hI : Set.Icc a b ⊆ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun t ↦ spectralRHSWork ν (s.coefficients t)) volume a b :=
  ContinuousOn.intervalIntegrable_of_Icc hab
    ((continuousOn_spectralRHSWork s hB g hg hSum hu).mono hI)

theorem energy_identity_from_initial (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    projectedFluxSquare 0 (s.coefficients t) = projectedFluxSquare 0 u₀ +
      2 * ∫ τ in (0 : ℝ)..t, spectralRHSWork ν (s.coefficients τ) := by
  rw [LocalStretchingFluxBalance.energy_identity_from_initial s hB g hg hSum hu t ht]
  congr 2
  apply intervalIntegral.integral_congr_Ioo_of_le ht.1
  intro τ hτ
  have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le.trans ht.2⟩
  exact (spectralRHSWork_eq_material_sub_transport ν _
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτT))
    (s.transverse τ) (s.reality τ)).symm

omit hB hg hSum hu in
/-- Physical initial data construct the local solution and its signed
output-frequency balance. The high moment is not a global a priori bound. -/
theorem exists_physical_local_spectral_balance (ν : ℝ) (hν : 0 < ν)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          projectedFluxSquare 0 (s.coefficients t) = projectedFluxSquare 0 (torusFourierVelocity f) +
            2 * ∫ τ in (0 : ℝ)..t, spectralRHSWork ν (s.coefficients τ) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, energy_identity_from_initial s hB g hg hSum hu⟩

end Mettapedia.FluidDynamics.NavierStokes.StretchingFluxSpectralEvolution
