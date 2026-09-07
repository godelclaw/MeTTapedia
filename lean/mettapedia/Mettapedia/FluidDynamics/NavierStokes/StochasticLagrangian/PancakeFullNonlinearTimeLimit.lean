import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeParametricInfiniteCurl
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSmoothProjectionTimeLimit

/-!
# Time-integrated consistency of the complete nonlinear alignment pairing

Both missing inputs and missing outputs are included in the error against
the constructed full Fourier curl series. Its absolute space-time pairing
with the actual filtered gap weight tends to zero under one summable
smoothness envelope on the time interval. Neither the envelope nor a PDE
solution is constructed by this theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFullNonlinearTimeLimit

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeDyadicDirectionEvolution
open PancakeFrequencyProjectorCommutator PancakePhysicalSpectralDefect PancakePhysicalWeightedTransport
open PancakeMaterialDiffusionBudget PancakeTopEigenvalueDerivative PancakeMeasurableMaterialRate
open PancakeLowDiffusionBudget PancakeSmoothSpectralEnvelope PancakeSmoothProjectionPairing
open PancakeCurlOutputTail PancakeDiscardedNonlinearLimit PancakeInteractionTruncationTail
open PancakeZeroSafeInteractionTail PancakeFullNonlinearConsistency PancakeParametricInfiniteCurl

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def fullErrorPairingMass (chi : Wavevector → ℂ) (M : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, |⟪physicalGapWeight chi M u 0 x (spatialVorticity M u x), fullNonlinearError M u x⟫|

theorem abs_fullErrorPairing_le_tail (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (chi : Wavevector → ℂ) (B : ℝ) (hB : 0 ≤ B) (hchi : ∀ k, ‖chi k‖ ≤ B)
    (M : Finset Wavevector) (u : FourierVelocity) (hzero : u 0 = 0)
    (hu : ∀ k ∈ M, modeDot k (u k) = 0) (hbound : ∀ k, fourierMoment 2 u k ≤ g k) (x : T3) :
    |⟪physicalGapWeight chi M u 0 x (spatialVorticity M u x), fullNonlinearError M u x⟫| ≤
      projectionEnvelopeConstant B g * interactionTail (nonzeroMajorant (velocityCurlMajorant g)) M := by
  have hg0 : 0 ≤ ∑' k, g k := tsum_nonneg hg
  calc
    _ ≤ ‖physicalGapWeight chi M u 0 x (spatialVorticity M u x)‖ * ‖fullNonlinearError M u x‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖physicalGapWeight chi M u 0 x‖ * ‖spatialVorticity M u x‖) * ‖fullNonlinearError M u x‖ :=
      mul_le_mul_of_nonneg_right ((physicalGapWeight chi M u 0 x).le_opNorm _) (norm_nonneg _)
    _ ≤ ((18 * (2 * Real.pi) * B * ∑' k, g k) * ((2 * Real.pi) * ∑' k, g k)) *
        interactionTail (nonzeroMajorant (velocityCurlMajorant g)) M := by
      gcongr
      · exact norm_physicalGapWeight_le_envelope g hg hSum M u chi B hB hchi hbound x
      · exact norm_spatialVorticity_le_envelope g hg hSum M u hbound x
      · exact norm_fullNonlinearError_le_tail g hg hSum M u hzero hu hbound x
    _ = _ := by unfold projectionEnvelopeConstant; ring

theorem fullErrorPairingMass_le_tail (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (chi : Wavevector → ℂ) (B : ℝ) (hB : 0 ≤ B) (hchi : ∀ k, ‖chi k‖ ≤ B)
    (M : Finset Wavevector) (u : FourierVelocity) (hzero : u 0 = 0)
    (hu : ∀ k ∈ M, modeDot k (u k) = 0) (hbound : ∀ k, fourierMoment 2 u k ≤ g k) :
    fullErrorPairingMass chi M u ≤
      projectionEnvelopeConstant B g * interactionTail (nonzeroMajorant (velocityCurlMajorant g)) M := by
  have he := (continuous_fullCurlNonlinearity g hg hSum u hbound).sub (continuous_retainedCurlNonlinearity M u)
  have hp : Continuous (fun x : T3 ↦
      |⟪physicalGapWeight chi M u 0 x (spatialVorticity M u x), fullNonlinearError M u x⟫|) :=
    (((continuous_physicalGapWeight chi M u 0).clm_apply (continuous_vorticity M u)).inner he).abs
  have hi := hp.integrable_of_hasCompactSupport (μ := volume) (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ _x : T3, projectionEnvelopeConstant B g * interactionTail (nonzeroMajorant (velocityCurlMajorant g)) M :=
      integral_mono hi (integrable_const _) (abs_fullErrorPairing_le_tail g hg hSum chi B hB hchi M u hzero hu hbound)
    _ = _ := by simp

theorem continuous_parametric_fullErrorPairingMass {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [LocallyCompactSpace P]
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (chi : Wavevector → ℂ) (M : Finset Wavevector) (u : P → FourierVelocity)
    (hc : ∀ k i, Continuous (fun t ↦ u t k i))
    (hzero : ∀ t, u t 0 = 0) (hu : ∀ t k, k ∈ M → modeDot k (u t k) = 0)
    (hbound : ∀ t k, fourierMoment 2 (u t) k ≤ g k) :
    Continuous (fun t ↦ fullErrorPairingMass chi M (u t)) := by
  have hS := continuous_parametric_strain M chi u (fun k _ ↦ hc k)
  have hw := continuous_parametric_spatialVorticity M u (fun k _ ↦ hc k)
  have hz := ((lipschitzWith_topEigenvalue.continuous.comp hS).smul hw).sub
    ((continuous_subtype_val.comp hS).clm_apply hw)
  have he := continuous_parametric_fullNonlinearError g hg hSum M u hc hzero hu hbound
  have hp : Continuous (fun z : P × T3 ↦
      |⟪physicalGapWeight chi M (u z.1) 0 z.2 (spatialVorticity M (u z.1) z.2), fullNonlinearError M (u z.1) z.2⟫|) := by
    simpa only [physicalGapWeight, PancakeRegularizedDiffusion.regularizedGap,
      add_zero, sub_apply, smul_apply, one_apply_eq_self, Function.comp_apply] using (hz.inner he).abs
  have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure T3))
    (f := fun (t : P) (x : T3) ↦
      |⟪physicalGapWeight chi M (u t) 0 x (spatialVorticity M (u t) x), fullNonlinearError M (u t) x⟫|)
    hp isCompact_univ
  simpa only [fullErrorPairingMass, Measure.restrict_univ] using h

theorem integral_fullErrorPairingMass_le_tail
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (chi : Wavevector → ℂ) (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T) (hchi : ∀ k, ‖chi k‖ ≤ B)
    (M : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hc : ∀ k i, ContinuousOn (fun t ↦ u t k i) (Set.Icc (0 : ℝ) T))
    (hzero : ∀ t ∈ Set.Icc (0 : ℝ) T, u t 0 = 0)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ M, modeDot k (u t k) = 0)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, fourierMoment 2 (u t) k ≤ g k) :
    (∫ t in (0 : ℝ)..T, fullErrorPairingMass chi M (u t)) ≤
      T * projectionEnvelopeConstant B g * interactionTail (nonzeroMajorant (velocityCurlMajorant g)) M := by
  have hm : ContinuousOn (fun t ↦ fullErrorPairingMass chi M (u t)) (Set.Icc (0 : ℝ) T) := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact continuous_parametric_fullErrorPairingMass g hg hSum chi M
      (fun t : Set.Icc (0 : ℝ) T ↦ u t)
      (fun k i ↦ (hc k i).restrict) (fun t ↦ hzero t t.property)
      (fun t ↦ hu t t.property) (fun t ↦ hbound t t.property)
  have h := intervalIntegral.integral_mono_on hT (hm.intervalIntegrable_of_Icc (μ := volume) hT)
    intervalIntegrable_const (fun t ht ↦ fullErrorPairingMass_le_tail g hg hSum chi B hB hchi M (u t)
      (hzero t ht) (hu t ht) (hbound t ht))
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_assoc] using h

theorem exists_uniform_integral_fullError_erase_zero_lt
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ core : Finset Wavevector, ∀ M : Finset Wavevector, core ⊆ M →
      ∀ (u : ℝ → FourierVelocity) (chi : Wavevector → ℂ),
        (∀ k, ‖chi k‖ ≤ B) → (∀ k i, ContinuousOn (fun t ↦ u t k i) (Set.Icc (0 : ℝ) T)) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, u t 0 = 0) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ M.erase 0, modeDot k (u t k) = 0) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, fourierMoment 2 (u t) k ≤ g k) →
        (∫ t in (0 : ℝ)..T, fullErrorPairingMass chi (M.erase 0) (u t)) < epsilon := by
  have ht : Tendsto (fun M : Finset Wavevector ↦ T * projectionEnvelopeConstant B g *
      interactionTail (nonzeroMajorant (velocityCurlMajorant g)) (M.erase 0)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_interactionTail_erase_zero _ (velocityCurlMajorant_nonneg g hg)
        (summable_velocityCurlMajorant g hg hSum))
  obtain ⟨core, hc⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hepsilon))
  exact ⟨core, fun M hm u chi hchi hc' hz hu hb ↦
    (integral_fullErrorPairingMass_le_tail g hg hSum chi B T hB hT hchi (M.erase 0) u hc' hz hu hb).trans_lt
      (hc M hm)⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeFullNonlinearTimeLimit
