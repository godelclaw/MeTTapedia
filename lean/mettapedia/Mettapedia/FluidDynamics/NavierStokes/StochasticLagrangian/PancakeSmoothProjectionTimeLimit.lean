import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSmoothProjectionPairing
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeEulerianAlignmentBudget

/-!
# Time-integrated consistency of the weighted nonlinear projection

Continuity of the actual finite nonlinear coefficients supplies time
integrability. A common summable second Fourier-moment envelope on a
compact time interval then makes the absolute spatial-mean projection
pairing small uniformly in the coefficient path and the output set.
The envelope is an explicit smoothness hypothesis, not an initial-energy
estimate or a construction of an arbitrary-data global solution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSmoothProjectionTimeLimit

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicVorticityEquation
open PancakeIncomingLowSourceEnergy PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge
open PancakeRetainedProjectionDefect PancakeFrequencyProjectorCommutator
open PancakeMeasurableMaterialRate PancakeEulerianAlignmentBudget PancakePhysicalWeightedTransport
open PancakePhysicalSpectralDefect PancakeMaterialDiffusionBudget PancakeTopEigenvalueDerivative
open PancakeCurlOutputTail PancakeDiscardedNonlinearLimit PancakeSummableOutputTail
open PancakeSmoothProjectionPairing
open PancakeDyadicDirectionEvolution PancakeLowDiffusionBudget

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuous_nonlinearVorticityCoeff (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (hc : ∀ k ∈ modes, ∀ i, Continuous (fun t ↦ u t k i))
    (q : Wavevector) (i : Fin 3) :
    Continuous (fun t ↦ nonlinearVorticityCoeff modes (u t) q i) := by
  have hw : ∀ k ∈ modes, ∀ j, ContinuousOn (fun t ↦ fourierCurl (u t) k j) Set.univ :=
    fun k hk j ↦ continuousOn_fourierCurl_coefficient u Set.univ k
      (fun a ↦ (hc k hk a).continuousOn) j
  have hn := continuousOn_univ.mp
    (continuousOn_incomingNonlinearCoeff modes modes (fun t ↦ fourierCurl (u t)) Set.univ hw hw q i)
  apply hn.congr
  intro t
  simp [nonlinearVorticityCoeff, incomingNonlinearCoeff, finiteUnitTorusVorticityRHS,
    finiteUnitTorusNonstretchingCoeff, unitTorusViscousVorticityCoeff, add_comm]

theorem continuous_parametric_discardedNonlinearField (modes outputs : Finset Wavevector)
    (u : ℝ → FourierVelocity) (hc : ∀ k ∈ modes, ∀ i, Continuous (fun t ↦ u t k i)) :
    Continuous (fun z : ℝ × T3 ↦ discardedNonlinearField modes outputs (u z.1) z.2) := by
  apply complexRealPartEuclideanCLM.continuous.comp
  exact continuous_parametric_reconstruction (outputs \ modes) (fun t ↦ nonlinearVorticityCoeff modes (u t))
    (fun q _ i ↦ continuous_nonlinearVorticityCoeff modes u hc q i)

def meanProjectionPairing (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ⟪physicalGapWeight chi modes u 0 x (spatialVorticity modes u x),
    discardedNonlinearField modes outputs u x⟫

theorem continuous_meanProjectionPairing (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : ℝ → FourierVelocity) (hc : ∀ k ∈ modes, ∀ i, Continuous (fun t ↦ u t k i)) :
    Continuous (fun t ↦ meanProjectionPairing chi modes outputs (u t)) := by
  have hS := continuous_parametric_strain modes chi u hc
  have hw := continuous_parametric_spatialVorticity modes u hc
  have hz := ((lipschitzWith_topEigenvalue.continuous.comp hS).smul hw).sub
    ((continuous_subtype_val.comp hS).clm_apply hw)
  have hp : Continuous (fun z : ℝ × T3 ↦
      ⟪physicalGapWeight chi modes (u z.1) 0 z.2 (spatialVorticity modes (u z.1) z.2),
        discardedNonlinearField modes outputs (u z.1) z.2⟫) := by
    simpa only [physicalGapWeight, PancakeRegularizedDiffusion.regularizedGap,
      add_zero, sub_apply, smul_apply, one_apply_eq_self, Function.comp_apply] using
      hz.inner (continuous_parametric_discardedNonlinearField modes outputs u hc)
  exact continuous_spatialMean _ hp

theorem integral_abs_meanProjectionPairing_le_tail
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (chi : Wavevector → ℂ) (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T) (hchi : ∀ k, ‖chi k‖ ≤ B)
    (modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hc : ∀ k ∈ modes, ∀ i, Continuous (fun t ↦ u t k i))
    (hzero : ∀ t ∈ Set.Icc (0 : ℝ) T, u t 0 = 0)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, fourierMoment 2 (u t) k ≤ g k) :
    (∫ t in (0 : ℝ)..T, |meanProjectionPairing chi modes outputs (u t)|) ≤
      T * projectionEnvelopeConstant B g * outputTail (velocityCurlMajorant g) modes := by
  have hi := (continuous_meanProjectionPairing chi modes outputs u hc).abs.intervalIntegrable
    (μ := volume) 0 T
  have h := intervalIntegral.integral_mono_on hT hi (intervalIntegrable_const)
    (fun t ht ↦ abs_integral_projection_le_tail g hg hSum modes outputs (u t) chi B hB hchi
      (hzero t ht) (hu t ht) (hbound t ht))
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_assoc] using h

theorem exists_uniform_integral_projection_lt
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ core : Finset Wavevector, ∀ modes : Finset Wavevector, core ⊆ modes →
      ∀ (outputs : Finset Wavevector) (u : ℝ → FourierVelocity) (chi : Wavevector → ℂ),
        (∀ k, ‖chi k‖ ≤ B) → (∀ k ∈ modes, ∀ i, Continuous (fun t ↦ u t k i)) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, u t 0 = 0) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, fourierMoment 2 (u t) k ≤ g k) →
        (∫ t in (0 : ℝ)..T, |meanProjectionPairing chi modes outputs (u t)|) < epsilon := by
  have ht : Tendsto (fun modes : Finset Wavevector ↦ T * projectionEnvelopeConstant B g *
      outputTail (velocityCurlMajorant g) modes) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_outputTail (velocityCurlMajorant g) (velocityCurlMajorant_nonneg g hg)
        (summable_velocityCurlMajorant g hg hSum))
  obtain ⟨core, hc⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hepsilon))
  exact ⟨core, fun modes hm outputs u chi hchi hu hz hi hb ↦
    (integral_abs_meanProjectionPairing_le_tail g hg hSum chi B T hB hT hchi modes outputs u hu hz hi hb).trans_lt
      (hc modes hm)⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeSmoothProjectionTimeLimit
