import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeReducedMaterialBudget

/-!
# Time integrability of the reduced forcing and signed weight variation

The weak derivatives of the spectral weight need not be continuous.
Their spatial mean is nevertheless identified with a difference of
continuous physical forcing pairings. This proves the time integrability
needed to integrate the reduced material estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeReducedForcingContinuity

open MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
open PeriodicFourierTriad PancakePhysicalSpectralDefect PancakeSignedTransportForcing
open PancakePhysicalWeightedTransport PancakeReducedMaterialBudget PancakeParametricForcing
open PancakeMeasurableMaterialRate PancakeMaterialDiffusionBudget PancakeLowDiffusionBudget
open PancakeEulerianAlignmentBudget PancakeFrequencyProjectorCommutator PancakeTopEigenvalueDerivative

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def meanReducedEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) : ℝ := ∫ x : T3, physicalReducedEnvelope chi modes outputs u delta x

def meanWeightVariation (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) : ℝ :=
  ∫ x : T3, physicalWeightVariation chi (fun q ↦ chi q - 1) modes u delta x

theorem meanWeightVariation_delta (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) :
    meanWeightVariation chi modes u delta = meanWeightVariation chi modes u 0 := by
  simp only [meanWeightVariation, physicalWeightVariation_delta]

theorem continuous_parametric_reducedForcing
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i))
    (hk : ∀ q ∈ modes, frequencyVec q ≠ 0)
    (hu : ∀ t, ∀ q ∈ modes, modeDot q (u t q) = 0) :
    Continuous (fun z : ℝ × T3 ↦ reducedVorticityForcing chi modes (u z.1) 0 z.2) :=
  (continuous_parametric_vorticityForcing_zero (fun _ ↦ 1) modes u hc hk hu).add
    (((continuous_subtype_val.comp (continuous_parametric_strain modes (fun _ ↦ 1) u hc)).sub
      (continuous_subtype_val.comp (continuous_parametric_strain modes chi u hc))).clm_apply
        (continuous_parametric_spatialVorticity modes u hc))

theorem continuous_meanReducedEnvelope
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity) (delta : ℝ)
    (hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i))
    (hk : ∀ q ∈ modes, frequencyVec q ≠ 0)
    (hu : ∀ t, ∀ q ∈ modes, modeDot q (u t q) = 0) :
    Continuous (fun t ↦ meanReducedEnvelope chi modes outputs (u t) delta) := by
  have hS := continuous_subtype_val.comp (continuous_parametric_strain modes chi u hc)
  have hw := continuous_parametric_spatialVorticity modes u hc
  have hR := continuous_parametric_strainRemainder_zero chi modes outputs u hc
  have hg := continuous_parametric_reducedForcing chi modes u hc hk hu
  apply continuous_spatialMean
  change Continuous (fun z : ℝ × T3 ↦ nonviscousEnvelope _ _ _ _ delta)
  unfold nonviscousEnvelope
  exact (((hR.norm.const_mul 2).mul (hw.norm.pow 2)).add ((hg.norm.pow 2).const_mul 2)).add
    ((hw.inner ((hS.clm_apply hw).add hg)).const_mul (2 * delta))

theorem continuous_parametric_gapPairing
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (delta : ℝ)
    (hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i))
    (f : ℝ → T3 → R3) (hf : Continuous f.uncurry) :
    Continuous (fun z : ℝ × T3 ↦ gapForcingPairing chi modes (u z.1) delta (f z.1) z.2) := by
  have hS := continuous_parametric_strain modes chi u hc
  have hw := continuous_parametric_spatialVorticity modes u hc
  have hK : Continuous (fun z : ℝ × T3 ↦ physicalGapWeight chi modes (u z.1) delta z.2) :=
    (((lipschitzWith_topEigenvalue.continuous.comp hS).add continuous_const).smul continuous_const).sub
      (continuous_subtype_val.comp hS)
  exact ((hK.clm_apply hw).inner hf).const_mul 2

theorem continuous_meanWeightVariation
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (delta : ℝ)
    (hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i))
    (hk : ∀ q ∈ modes, frequencyVec q ≠ 0)
    (hu : ∀ t, ∀ q ∈ modes, modeDot q (u t q) = 0)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hr : ∀ t q, u t (-q) = PancakeBlockReality.coefficientConjugate (u t q))
    (hchi : ∀ q, chi (-q) = conj (chi q)) :
    Continuous (fun t ↦ meanWeightVariation chi modes (u t) delta) := by
  have hG := continuous_spatialMean
    (fun t x ↦ gapForcingPairing chi modes (u t) delta (reducedVorticityForcing chi modes (u t) 0) x)
    (continuous_parametric_gapPairing chi modes u delta hc
    (fun t ↦ reducedVorticityForcing chi modes (u t) 0)
    (continuous_parametric_reducedForcing chi modes u hc hk hu))
  have hF := continuous_spatialMean
    (fun t x ↦ gapForcingPairing chi modes (u t) delta (spatialVorticityForcing chi modes (u t) 0) x)
    (continuous_parametric_gapPairing chi modes u delta hc
    (fun t ↦ spatialVorticityForcing chi modes (u t) 0)
    (continuous_parametric_vorticityForcing_zero chi modes u hc hk hu))
  apply (hG.sub hF).congr
  intro t
  have h := integral_gapForcingPairing_reduced chi modes (u t) delta 0 hs (hr t) hchi (hu t)
  change _ = ∫ x : T3, physicalWeightVariation chi (fun q ↦ chi q - 1) modes (u t) delta x
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeReducedForcingContinuity
