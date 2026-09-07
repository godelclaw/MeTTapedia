import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeParametricForcing

/-!
# A time-integrated Eulerian alignment budget for supplied finite NS solutions

The actual mean material derivative is integrated using weak incompressible
transport cancellation. The spectral residual and nonviscous forcing are
continuous in time after spatial integration; their integrability is proved,
not supplied as a budget. The cutoff-dependent diffusion price and the full
nonviscous forcing remain explicit. No arbitrary-data existence or uniform
all-scale estimate is concluded.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeEulerianAlignmentBudget

open MeasureTheory
open scoped ComplexConjugate
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeMeasurableMaterialRate
open PancakeMaterialDiffusionBudget PancakeMaterialSpatialEstimate PancakePhysicalMeanBalance
open PancakeParametricForcing PancakeFourierStrainGradient PancakeSpectralDefectEvolution
open PancakePhysicalSpectralDefect PancakeFrequencyProjectorCommutator PancakeLowDiffusionBudget
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeViscousMisalignmentAbsorption
open PancakeTopEigenvalueDerivative

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def meanResidualSquare (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖spectralResidual (spatialStrain modes (filteredVelocity chi u) x).1
    (topEigenvalue (spatialStrain modes (filteredVelocity chi u) x)) (spatialVorticity modes u x)‖ ^ 2

def meanNonviscousEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) : ℝ :=
  ∫ x : T3, physicalNonviscousEnvelope chi modes outputs u delta x

theorem continuous_spatialMean (f : ℝ → T3 → ℝ) (hf : Continuous f.uncurry) :
    Continuous (fun t ↦ ∫ x : T3, f t x) := by
  have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure T3)) hf isCompact_univ
  simpa only [Measure.restrict_univ] using h

theorem continuous_meanResidualSquare (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i)) :
    Continuous (fun t ↦ meanResidualSquare chi modes (u t)) := by
  have hS := continuous_parametric_strain modes chi u hc
  have hw := continuous_parametric_spatialVorticity modes u hc
  have hz := ((lipschitzWith_topEigenvalue.continuous.comp hS).smul hw).sub
    ((continuous_subtype_val.comp hS).clm_apply hw)
  exact continuous_spatialMean _ (hz.norm.pow 2)

theorem continuous_meanNonviscousEnvelope
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity) (delta : ℝ)
    (hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i))
    (hk : ∀ q ∈ modes, frequencyVec q ≠ 0)
    (hu : ∀ t, ∀ q ∈ modes, modeDot q (u t q) = 0) :
    Continuous (fun t ↦ meanNonviscousEnvelope chi modes outputs (u t) delta) :=
  continuous_spatialMean _ (continuous_parametric_nonviscousEnvelope chi modes outputs u delta hc hk hu)

theorem continuous_kineticEnstrophyProduct (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i)) :
    Continuous (fun t ↦ fullEnergy modes (u t) * fullEnergy modes (fourierCurl (u t))) := by
  have hU := continuousOn_univ.mp (continuousOn_fullEnergy modes u Set.univ
    (fun q hq i ↦ (hc q hq i).continuousOn))
  have hO := continuousOn_univ.mp (continuousOn_fullEnergy modes (fun t ↦ fourierCurl (u t)) Set.univ
    (fun q hq i ↦ continuousOn_fourierCurl_coefficient u Set.univ q
      (fun j ↦ (hc q hq j).continuousOn) i))
  exact hU.mul hO

/-- The full finite-cutoff Eulerian inequality. Coefficient C1 regularity,
transport cancellation, collision-safe differentiation, and time
integrability are all discharged from the displayed finite-solution data. -/
theorem meanAlignmentEnergy_budget_of_velocityRHS
    (chi : Wavevector → ℂ) (low modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity)
    (delta nu a b : ℝ) (hdelt : 0 < delta) (hnu : 0 ≤ nu) (hab : a ≤ b)
    (hlow : low ⊆ modes) (hsub : modes ⊆ outputs)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hchi : ∀ q, q ∉ low → chi q = 0) (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t q, u t (-q) = PancakeBlockReality.coefficientConjugate (u t q))
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ t, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ t, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun s ↦ u s q i) (velocityRHS modes (u t) nu q i) t) :
    meanAlignmentEnergy chi modes (u b) delta +
      (1 / 2 : ℝ) * (∫ t in a..b, meanResidualSquare chi modes (u t)) ≤
        meanAlignmentEnergy chi modes (u a) delta +
          (16 * nu / delta) * strainGradientCutoffWeight low chi *
            (∫ t in a..b, fullEnergy modes (u t) * fullEnergy modes (fourierCurl (u t))) +
          (∫ t in a..b, meanNonviscousEnvelope chi modes outputs (u t) delta) := by
  have hc1 := contDiff_coefficients_of_velocityRHS modes u nu hk hu hd
  have hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i) := fun q hq i ↦ (hc1 q hq i).continuous
  obtain ⟨hIm, hbalance⟩ := intervalIntegral_frozenMaterialRate_eq_energy chi modes u delta a b hc1 hu
  have hIz := (continuous_meanResidualSquare chi modes u hc).intervalIntegrable (μ := volume) a b
  have hIB := (continuous_meanNonviscousEnvelope chi modes outputs u delta hc hk hu).intervalIntegrable (μ := volume) a b
  have hIU := (continuous_kineticEnstrophyProduct modes u hc).intervalIntegrable (μ := volume) a b
  have hpaid := ae_integral_frozenMaterialRate_paid_of_velocityRHS chi low modes outputs u delta nu
    hdelt hnu hlow hsub hout hchi hchir hs hr hk hu hd
  have hpaid' : ∀ᵐ t : ℝ,
      (∫ x : T3, frozenMaterialRate chi modes u delta t x) + (1 / 2 : ℝ) * meanResidualSquare chi modes (u t) ≤
        ((16 * nu / delta) * strainGradientCutoffWeight low chi) *
          (fullEnergy modes (u t) * fullEnergy modes (fourierCurl (u t))) +
        meanNonviscousEnvelope chi modes outputs (u t) delta := by
    simpa only [meanResidualSquare, meanNonviscousEnvelope, mul_assoc] using hpaid
  have hi := intervalIntegral.integral_mono_ae hab (hIm.add (hIz.const_mul (1 / 2)))
    ((hIU.const_mul ((16 * nu / delta) * strainGradientCutoffWeight low chi)).add hIB) hpaid'
  rw [intervalIntegral.integral_add hIm (hIz.const_mul (1 / 2)),
    intervalIntegral.integral_add (hIU.const_mul ((16 * nu / delta) * strainGradientCutoffWeight low chi)) hIB,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hbalance] at hi
  linarith

theorem kineticEnstrophyProduct_integral_le_initial
    (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (nu T : ℝ)
    (hnu : 0 < nu) (hT : 0 ≤ T)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t q, u t (-q) = PancakeBlockReality.coefficientConjugate (u t q))
    (hu : ∀ t, ∀ q ∈ modes, modeDot q (u t q) = 0)
    (hd : ∀ t, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun s ↦ u s q i) (velocityRHS modes (u t) nu q i) t) :
    (∫ t in (0 : ℝ)..T, fullEnergy modes (u t) * fullEnergy modes (fourierCurl (u t))) ≤
      fullEnergy modes (u 0) ^ 2 / (2 * nu) := by
  have hc := continuousOn_coefficients_of_velocityRHS modes u nu (Set.Icc 0 T) (fun t _ ↦ hd t)
  have hOc := continuousOn_enstrophy_of_velocityRHS modes u nu (Set.Icc 0 T) (fun t _ ↦ hd t)
  have hUc := continuousOn_fullEnergy modes u (Set.Icc 0 T) hc
  have hOI := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hT hOc
  have hUOI := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hT (hUc.mul hOc)
  have hU := kineticEnergy_le_initial_on modes u nu T hnu.le hs (fun t _ ↦ hr t)
    (fun t _ ↦ hu t) (fun t _ ↦ hd t)
  have hi := intervalIntegral.integral_mono_on hT hUOI (hOI.const_mul (fullEnergy modes (u 0)))
    (fun t ht ↦ mul_le_mul_of_nonneg_right (hU t ht) (fullEnergy_nonneg _ _))
  rw [intervalIntegral.integral_const_mul] at hi
  apply hi.trans
  apply (le_div_iff₀ (by positivity : 0 < 2 * nu)).mpr
  have hO := enstrophy_integral_le_initial modes u nu T hT hs (fun t _ ↦ hr t)
    (fun t _ ↦ hu t) (fun t _ ↦ hd t)
  have hh := mul_le_mul_of_nonneg_left hO (fullEnergy_nonneg modes (u 0))
  nlinarith

/-- The diffusion contribution is paid solely by initial kinetic energy.
The nonviscous forcing remains an explicit time integral and the price
still grows with the low-frequency cutoff and with inverse regularization. -/
theorem meanAlignmentEnergy_budget_initial_paid
    (chi : Wavevector → ℂ) (low modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity)
    (delta nu T : ℝ) (hdelt : 0 < delta) (hnu : 0 < nu) (hT : 0 ≤ T)
    (hlow : low ⊆ modes) (hsub : modes ⊆ outputs)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hchi : ∀ q, q ∉ low → chi q = 0) (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t q, u t (-q) = PancakeBlockReality.coefficientConjugate (u t q))
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ t, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ t, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun s ↦ u s q i) (velocityRHS modes (u t) nu q i) t) :
    meanAlignmentEnergy chi modes (u T) delta +
      (1 / 2 : ℝ) * (∫ t in (0 : ℝ)..T, meanResidualSquare chi modes (u t)) ≤
        meanAlignmentEnergy chi modes (u 0) delta +
          8 * strainGradientCutoffWeight low chi * fullEnergy modes (u 0) ^ 2 / delta +
          (∫ t in (0 : ℝ)..T, meanNonviscousEnvelope chi modes outputs (u t) delta) := by
  have h := meanAlignmentEnergy_budget_of_velocityRHS chi low modes outputs u delta nu 0 T
    hdelt hnu.le hT hlow hsub hout hchi hchir hs hr hk hu hd
  have hUO := kineticEnstrophyProduct_integral_le_initial modes u nu T hnu hT hs hr hu hd
  have hc : 0 ≤ (16 * nu / delta) * strainGradientCutoffWeight low chi :=
    mul_nonneg (by positivity) (strainGradientCutoffWeight_nonneg low chi)
  have hp := mul_le_mul_of_nonneg_left hUO hc
  have he : ((16 * nu / delta) * strainGradientCutoffWeight low chi) *
      (fullEnergy modes (u 0) ^ 2 / (2 * nu)) =
      8 * strainGradientCutoffWeight low chi * fullEnergy modes (u 0) ^ 2 / delta := by
    field_simp
    ring
  rw [he] at hp
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeEulerianAlignmentBudget
