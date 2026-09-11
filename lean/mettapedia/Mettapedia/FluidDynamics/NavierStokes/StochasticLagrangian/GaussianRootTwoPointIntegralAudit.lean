import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootTwoPointIntegral

/-! Endpoint, null-set, and genuine-integrability checks for the two-point cost. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointIntegralAudit

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail LocalLowDiffusionBudget
open GaussianRootTwoPointIntegral GaussianRootTwoPointDerivative
open Mettapedia.Analysis.GaussianPartitionEnergy Mettapedia.Analysis.BilinearTranslatedCoefficient

local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (tau : ℝ) :
    Continuous (fun p : ℝ × ℝ ↦ twoPointDistanceMoment (![-1, 1] : Fin 2 → ℝ) tau p.1 p.2) :=
  continuous_twoPointDistanceMoment _ tau

/-- The coefficient helper does not silently require nonnegative factors. -/
example (M : T6 → ℝ) (f : T3 → ℝ) (hM : Integrable M) (hf : Integrable f)
    (a b : T6 → T3) (ha : Measurable a) (hb : Measurable b) :
    Integrable (fun p : T6 × T3 ↦ -(M p.1 * f (p.2 - a p.1)))
      ((volume : Measure T6).prod (volume : Measure T3)) := by
  simpa using integrable_weighted_translate_mul_continuous M f hM hf a b ha hb
    (ContinuousMap.const (T3 × T3) (-1 : ℝ))

/-- Zero vorticity removes the entire integrated cost. -/
example (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu0 : ∀ x : T3, fullVorticity u x = 0)
    (centers : Finset T3) (tau : ℝ) (j : Fin 3) (M : T6 → ℝ) (a b : T6 → T3) :
    (∫ x : T3, ∫ q : T6, M q *
      twoPointBudget gamma chi modes u centers tau j (x - a q) (x - b q)) = 0 := by
  simp [twoPointBudget, hu0]

/-- Fixed zero temperature uses the defined constant weights; this is not a
claim about a limit as positive temperatures tend to zero. -/
example (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (centers : Finset T3) (hc : centers.Nonempty) (j : Fin 3)
    (M : T6 → ℝ) (hM : Integrable M) (a b : T6 → T3) (ha : Measurable a) (hb : Measurable b) :
    Integrable (fun p : T6 × T3 ↦ M p.1 *
      twoPointBudget gamma chi modes u centers 0 j (p.2 - a p.1) (p.2 - b p.1))
      ((volume : Measure T6).prod (volume : Measure T3)) :=
  integrable_twoPointBudget gamma hg chi modes u hu centers hc 0 j M hM a b ha hb

/-- One full-measure spatial set supports the genuine inner integrals for
both orders of the input displacements. -/
example (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (j : Fin 3)
    (M : T6 → ℝ) (hM : Integrable M) (a b : T6 → T3) (ha : Measurable a) (hb : Measurable b) :
    ∀ᵐ x : T3,
      Integrable (fun q : T6 ↦ M q * twoPointBudget gamma chi modes u centers tau j (x - a q) (x - b q)) ∧
      Integrable (fun q : T6 ↦ M q * twoPointBudget gamma chi modes u centers tau j (x - b q) (x - a q)) := by
  filter_upwards [(integrable_twoPointBudget gamma hg chi modes u hu centers hc tau j M hM a b ha hb).prod_left_ae,
    (integrable_twoPointBudget gamma hg chi modes u hu centers hc tau j M hM b a hb ha).prod_left_ae] with x hx hy
  exact ⟨hx, hy⟩

/-- The zero-output endpoint annihilates both actual normalized channel energies. -/
example (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (N : ℝ) (hN : 0 < N) (j : Fin 3) :
    let hu2 := PancakeHigherDerivativeMoments.summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
    normalizedChannelEnergy gamma hg chi modes u hu2 centers hc tau N hN 0 (.first j) = 0 ∧
      normalizedChannelEnergy gamma hg chi modes u hu2 centers hc tau N hN 0 (.second j) = 0 := by
  obtain ⟨C, _, M, h⟩ := exists_uniform_channel_sum_envelope gamma hg chi modes u hu centers hc tau
  obtain ⟨_, _, _, _, _, _, _, hb⟩ := h N hN 0 (by constructor <;> norm_num)
  obtain ⟨_, _, hfirst, hsecond⟩ := hb j
  simp only [PressureLowOutputCutoff.ratio, zero_div, zero_mul] at hfirst hsecond
  exact ⟨le_antisymm hfirst (normalizedChannelEnergy_nonneg gamma hg chi modes u _ centers hc tau N hN 0 _),
    le_antisymm hsecond (normalizedChannelEnergy_nonneg gamma hg chi modes u _ centers hc tau N hN 0 _)⟩

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointIntegralAudit

#print axioms Mettapedia.Analysis.BilinearTranslatedCoefficient.integrable_weighted_translate_mul_continuous
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.continuous_distanceMoment
#print axioms Mettapedia.Analysis.GaussianPartitionEnergy.continuous_twoPointDistanceMoment
#print axioms Mettapedia.Analysis.RootPartitionEnergy.integrable_twoPointDerivativeCost
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointIntegral.twoPointBudget_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointIntegral.integrable_rootGapDerivative_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointIntegral.integrable_projectorCoordinateDerivative_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointIntegral.integrable_twoPointBudget
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointIntegral.integral_twoPointDerivativeDensity_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointIntegral.normalizedChannelEnergy_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointIntegral.first_channel_sum_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointIntegral.second_channel_sum_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointIntegral.exists_uniform_channel_sum_envelope
