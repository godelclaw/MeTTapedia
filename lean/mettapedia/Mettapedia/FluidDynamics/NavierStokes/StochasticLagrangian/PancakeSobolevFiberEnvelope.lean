import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCoefficientLimitProperties

/-!
# Summable fixed-output convection envelopes from second-order energy

The pointwise squared coefficient decay supplied by the Sobolev energy
is sufficient for each output fiber. Incompressibility has already moved
the derivative to that output; no summable gradient envelope is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSobolevFiberEnvelope

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeLatticeDecayEnvelope
open PancakeCoefficientLimitProperties PancakeFixedOutputVelocityBound PancakeLowPressureBudget

theorem amplitude_sq_le_decay (u : FourierVelocity) (B : ℝ)
    (hB : ∀ F : Finset Wavevector, sobolevEnergy F u ≤ B) (k : Wavevector) :
    (amplitude u k)^2 ≤ B * latticeDecayWeight k := by
  have h := hB {k}
  simp only [sobolevEnergy, energy, Finset.sum_singleton, mul_pow] at h
  have hp : 0 < (1 + ‖frequencyVec k‖)^4 := by positivity
  change (amplitude u k)^2 ≤ B * (1 / (1 + ‖frequencyVec k‖)^4)
  rw [mul_one_div, le_div_iff₀ hp]
  simpa only [weight, ← pow_mul, show (2 : ℕ) * 2 = 4 from rfl, mul_comm] using h

def fiberEnvelope (B : ℝ) (q k : Wavevector) : ℝ :=
  (‖frequencyVec q‖ * B / 2) * (latticeDecayWeight k + latticeDecayWeight (q-k))

theorem fiberEnvelope_nonneg (B : ℝ) (hB : 0 ≤ B) (q k : Wavevector) :
    0 ≤ fiberEnvelope B q k := by
  unfold fiberEnvelope
  positivity [latticeDecayWeight_pos k, latticeDecayWeight_pos (q-k)]

theorem summable_fiberEnvelope (B : ℝ) (q : Wavevector) : Summable (fiberEnvelope B q) := by
  have hs : Summable (fun k ↦ latticeDecayWeight (q-k)) :=
    summable_latticeDecayWeight.comp_injective (fun _ _ h ↦ sub_right_injective h)
  exact (summable_latticeDecayWeight.add hs).mul_left (‖frequencyVec q‖ * B / 2)

/-- The fixed-output, derivative-transferred scalar interaction. -/
def outputFiber (q : Wavevector) (u : FourierVelocity) (k : Wavevector) (i : Fin 3) : ℂ :=
  modeDot q (u k) * u (q-k) i

theorem norm_outputFiber_le_envelope (u : FourierVelocity) (B : ℝ)
    (hB : ∀ F : Finset Wavevector, sobolevEnergy F u ≤ B)
    (q k : Wavevector) (i : Fin 3) :
    ‖outputFiber q u k i‖ ≤ fiberEnvelope B q k := by
  have hk := amplitude_sq_le_decay u B hB k
  have hl := amplitude_sq_le_decay u B hB (q-k)
  have hp : amplitude u k * amplitude u (q-k) ≤
      B / 2 * (latticeDecayWeight k + latticeDecayWeight (q-k)) := by
    nlinarith [sq_nonneg (amplitude u k - amplitude u (q-k))]
  calc
    _ ≤ (‖frequencyVec q‖ * amplitude u k) * amplitude u (q-k) := by
      rw [outputFiber, norm_mul]
      exact mul_le_mul (norm_modeDot_le q (u k))
        (PiLp.norm_apply_le (coefficientVec (u (q-k))) i)
        (norm_nonneg _) (by dsimp [amplitude]; positivity)
    _ = ‖frequencyVec q‖ * (amplitude u k * amplitude u (q-k)) := by ring
    _ ≤ ‖frequencyVec q‖ * (B / 2 * (latticeDecayWeight k + latticeDecayWeight (q-k))) :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = fiberEnvelope B q k := by unfold fiberEnvelope; ring

theorem summable_outputFiber (u : FourierVelocity) (B : ℝ)
    (hB : ∀ F : Finset Wavevector, sobolevEnergy F u ≤ B) (q : Wavevector) (i : Fin 3) :
    Summable (fun k ↦ outputFiber q u k i) :=
  (summable_fiberEnvelope B q).of_norm_bounded (fun k ↦ norm_outputFiber_le_envelope u B hB q k i)

end Mettapedia.FluidDynamics.NavierStokes.PancakeSobolevFiberEnvelope
