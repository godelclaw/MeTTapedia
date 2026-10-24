import Mettapedia.FluidDynamics.NavierStokes.ModeStateSobolevChartFork
import Mathlib.Analysis.PSeries

/-!
# Energy-Style Chart Fork on the Shared Mode State

The squared amplification and its compensating inverse power cancel exactly.
The resulting energy radius is independent of the amplification exponent; it
is an inverse-square coordinate observation. The uncompensated hard threshold
retains the exponent and is discontinuous at zero.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped Classical

section ModeStateEnergyChartFork

/-- Inverse power compensating squared polynomial amplification. -/
def energyCompensationWeight (m n : ℕ) : ℝ := 1 / (n + 1 : ℝ) ^ (2 * m + 2)

/-- The amplified expression, before proving its cancellation. -/
def amplifiedEnergyTerm (m : ℕ) (x : ModeState) (n : ℕ) : ℝ :=
  (sobolevAmplification m x n) ^ 2 * energyCompensationWeight m n

/-- The canonical compensated term has no amplification parameter. -/
def compensatedEnergyTerm (x : ModeState) (n : ℕ) : ℝ :=
  (x.coeff n) ^ 2 * inverseSquareModeWeights.weight n

def compensatedEnergyRadius (x : ModeState) : ℝ := ∑' n, compensatedEnergyTerm x n

def compensatedEnergyStatistic (x : ModeState) : ℝ := x.coeff 0 + compensatedEnergyRadius x

/-- A hard threshold of the amplified, uncompensated energy. -/
def hardEnergyThresholdRadius (m : ℕ) (x : ModeState) : ℝ :=
  if ∃ n, 1 ≤ (sobolevAmplification m x n) ^ 2 then 1 else 0

theorem energyCompensationWeight_nonneg (m n : ℕ) : 0 ≤ energyCompensationWeight m n := by
  unfold energyCompensationWeight
  positivity

/-- Algebraic cancellation of the independently supplied amplified expression. -/
theorem amplifiedEnergyTerm_eq_compensatedEnergyTerm (m : ℕ) (x : ModeState) (n : ℕ) :
    amplifiedEnergyTerm m x n = compensatedEnergyTerm x n := by
  unfold amplifiedEnergyTerm sobolevAmplification energyCompensationWeight
    compensatedEnergyTerm inverseSquareModeWeights
  have h1 : (n + 1 : ℝ) ^ (2 * m + 2) ≠ 0 := by positivity
  have h2 : (n + 1 : ℝ) ^ 2 ≠ 0 := by positivity
  field_simp [h1, h2]
  ring

theorem amplifiedEnergy_sum_eq_compensatedRadius (m : ℕ) (x : ModeState) :
    (∑' n, amplifiedEnergyTerm m x n) = compensatedEnergyRadius x := by
  simp only [amplifiedEnergyTerm_eq_compensatedEnergyTerm, compensatedEnergyRadius]

theorem continuous_compensatedEnergyRadius : Continuous compensatedEnergyRadius :=
  (squareModeObservable inverseSquareModeWeights).continuous_value

theorem hardEnergyThresholdRadius_tailSpikeStableAt_one (m : ℕ) :
    TailSpikeStableAt (hardEnergyThresholdRadius m) 1 := by
  intro N
  have hbase : (1 : ℝ) ≤ (N + 1 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hsq : (1 : ℝ) ≤ ((N + 1 : ℝ) ^ m) ^ 2 := one_le_pow₀ hbase
  have witness : ∃ n, 1 ≤ (sobolevAmplification m (tailSpikeMode N) n) ^ 2 :=
    ⟨N, by simpa [sobolevAmplification, tailSpikeMode] using hsq⟩
  exact if_pos witness

theorem hardEnergyThresholdRadius_modeZero (m : ℕ) :
    hardEnergyThresholdRadius m modeZero = 0 := by
  simp [hardEnergyThresholdRadius, sobolevAmplification, modeZero]

theorem not_continuousAt_hardEnergyThresholdRadius_modeZero (m : ℕ) :
    ¬ ContinuousAt (hardEnergyThresholdRadius m) modeZero := by
  refine not_continuousAt_of_tailSpikeStableAt
    (hardEnergyThresholdRadius_tailSpikeStableAt_one m) ?_
  simp [hardEnergyThresholdRadius_modeZero]

theorem not_continuousAt_hardEnergyThreshold_cutoffPotential_modeZero (m : ℕ) :
    ¬ ContinuousAt
      (cutoffPotential (fun r => r) (hardEnergyThresholdRadius m) unitStatisticMode)
      modeZero := by
  exact not_continuousAt_cutoffPotential_of_tailSpikeStableAt
    (hardEnergyThresholdRadius_tailSpikeStableAt_one m)
    tendsto_unitStatisticMode_tailSpikeMode
    (by
      unfold cutoffPotential
      rw [hardEnergyThresholdRadius_modeZero]
      norm_num [unitStatisticMode, modeZero])

theorem not_continuousAt_hardEnergyThreshold_coleHopfPhi_modeZero (m : ℕ) :
    ¬ ContinuousAt
      (coleHopfPhi 1
        (cutoffPotential (fun r => r) (hardEnergyThresholdRadius m) unitStatisticMode))
      modeZero := by
  exact not_continuousAt_coleHopfPhi_of_tailSpikeStableAt
    (hardEnergyThresholdRadius_tailSpikeStableAt_one m)
    tendsto_unitStatisticMode_tailSpikeMode
    (by norm_num)
    (by
      unfold cutoffPotential
      rw [hardEnergyThresholdRadius_modeZero]
      norm_num [unitStatisticMode, modeZero])

end ModeStateEnergyChartFork

end NavierStokes
end FluidDynamics
end Mettapedia
