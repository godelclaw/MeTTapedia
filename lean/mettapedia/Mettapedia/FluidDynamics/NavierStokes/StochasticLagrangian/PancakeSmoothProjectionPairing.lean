import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSmoothSpectralEnvelope

/-!
# Vanishing of the actual strain-weighted projection pairing

One common summable second-moment envelope controls the vorticity, the
actual filtered gap weight, and the nonlinear output tail. The resulting
spatial pairing tends to zero under Fourier exhaustion. This removes an
approximation term on an enveloped smooth family; it does not establish
that envelope from arbitrary initial data or pass the full PDE to a limit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSmoothProjectionPairing

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeDyadicDirectionEvolution
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail PancakeSmoothSpectralEnvelope
open PancakeDiscardedNonlinearLimit PancakeSummableOutputTail PancakeRetainedProjectionDefect
open PancakePhysicalSpectralDefect PancakePhysicalWeightedTransport PancakeMaterialDiffusionBudget

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def projectionEnvelopeConstant (B : ℝ) (g : Wavevector → ℝ) : ℝ :=
  18 * (2 * Real.pi) ^ 2 * B * (∑' k, g k) ^ 2

theorem projectionEnvelopeConstant_nonneg (B : ℝ) (hB : 0 ≤ B) (g : Wavevector → ℝ) :
    0 ≤ projectionEnvelopeConstant B g := by unfold projectionEnvelopeConstant; positivity

theorem abs_projection_inner_le_tail (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (chi : Wavevector → ℂ) (B : ℝ) (hB : 0 ≤ B) (hchi : ∀ k, ‖chi k‖ ≤ B)
    (hzero : u 0 = 0) (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (hbound : ∀ k, fourierMoment 2 u k ≤ g k) (x : T3) :
    |⟪physicalGapWeight chi modes u 0 x (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫| ≤
      projectionEnvelopeConstant B g * outputTail (velocityCurlMajorant g) modes := by
  have hg0 : 0 ≤ ∑' k, g k := tsum_nonneg hg
  have htail := outputTail_nonneg (velocityCurlMajorant g) (velocityCurlMajorant_nonneg g hg) modes
  calc
    _ ≤ ‖physicalGapWeight chi modes u 0 x (spatialVorticity modes u x)‖ * ‖discardedNonlinearField modes outputs u x‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖physicalGapWeight chi modes u 0 x‖ * ‖spatialVorticity modes u x‖) * ‖discardedNonlinearField modes outputs u x‖ :=
      mul_le_mul_of_nonneg_right ((physicalGapWeight chi modes u 0 x).le_opNorm _) (norm_nonneg _)
    _ ≤ ((18 * (2 * Real.pi) * B * ∑' k, g k) * ((2 * Real.pi) * ∑' k, g k)) *
        outputTail (velocityCurlMajorant g) modes := by
      gcongr
      · exact norm_physicalGapWeight_le_envelope g hg hSum modes u chi B hB hchi hbound x
      · exact norm_spatialVorticity_le_envelope g hg hSum modes u hbound x
      · exact norm_discardedNonlinearField_le_tail g hg hSum modes outputs u hzero hu hbound x
    _ = _ := by unfold projectionEnvelopeConstant; ring

theorem abs_integral_projection_le_tail (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (chi : Wavevector → ℂ) (B : ℝ) (hB : 0 ≤ B) (hchi : ∀ k, ‖chi k‖ ≤ B)
    (hzero : u 0 = 0) (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (hbound : ∀ k, fourierMoment 2 u k ≤ g k) :
    |∫ x : T3, ⟪physicalGapWeight chi modes u 0 x (spatialVorticity modes u x),
      discardedNonlinearField modes outputs u x⟫| ≤
        projectionEnvelopeConstant B g * outputTail (velocityCurlMajorant g) modes := by
  have hc : Continuous (fun x : T3 ↦ ⟪physicalGapWeight chi modes u 0 x (spatialVorticity modes u x),
      discardedNonlinearField modes outputs u x⟫) :=
    ((continuous_physicalGapWeight _ _ _ _).clm_apply (continuous_vorticity _ _)).inner (continuous_discardedNonlinearField _ _ _)
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ _x : T3, projectionEnvelopeConstant B g * outputTail (velocityCurlMajorant g) modes :=
      integral_mono (hc.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (integrable_const _) (fun x ↦ abs_projection_inner_le_tail g hg hSum modes outputs u chi B hB hchi hzero hu hbound x)
    _ = _ := by simp

theorem exists_uniform_projection_pairing_lt (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (B : ℝ) (hB : 0 ≤ B) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ core : Finset Wavevector, ∀ modes : Finset Wavevector, core ⊆ modes →
      ∀ (outputs : Finset Wavevector) (u : FourierVelocity) (chi : Wavevector → ℂ),
        (∀ k, ‖chi k‖ ≤ B) → u 0 = 0 → (∀ k ∈ modes, modeDot k (u k) = 0) →
        (∀ k, fourierMoment 2 u k ≤ g k) →
        |∫ x : T3, ⟪physicalGapWeight chi modes u 0 x (spatialVorticity modes u x),
          discardedNonlinearField modes outputs u x⟫| < epsilon := by
  have ht : Tendsto (fun modes : Finset Wavevector ↦ projectionEnvelopeConstant B g *
      outputTail (velocityCurlMajorant g) modes) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_outputTail (velocityCurlMajorant g) (velocityCurlMajorant_nonneg g hg) (summable_velocityCurlMajorant g hg hSum))
  obtain ⟨core, hc⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hepsilon))
  exact ⟨core, fun modes hm outputs u chi hchi hz hu hb ↦
    (abs_integral_projection_le_tail g hg hSum modes outputs u chi B hB hchi hz hu hb).trans_lt (hc modes hm)⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeSmoothProjectionPairing
