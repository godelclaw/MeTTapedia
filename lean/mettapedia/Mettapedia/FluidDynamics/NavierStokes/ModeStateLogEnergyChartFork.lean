import Mettapedia.FluidDynamics.NavierStokes.ModeStateEnergyProfileFork
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Log-Energy Chart Fork on the Shared Mode State

This file tests a more manuscript-shaped radial profile on the same `ModeState`.
It replaces the raw squared Sobolev energy by the smoother quantity
`log (1 + energy)`.

* The soft log-energy radius lands on the good side: it is continuous and
  truncation-friendly because `log (1 + u) <= u`.
* The hard-side analogue asking whether `log (1 + energy) > 0` still lands on
  the bad side: it is tail-spike stable but disagrees at `modeZero`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped Classical

section ModeStateLogEnergyChartFork

/-- Soft log-energy term on the shared mode space. -/
def logEnergyTerm (m : ℕ) (x : ModeState) (n : ℕ) : ℝ :=
  Real.log (1 + (sobolevAmplification m x n) ^ (2 : ℕ)) * energyCompensationWeight m n

/-- Soft log-energy radius. -/
def logEnergyRadius (m : ℕ) (x : ModeState) : ℝ :=
  ∑' n, logEnergyTerm m x n

/-- Zeroth visible mode plus the soft log-energy radius. -/
def logEnergyStatistic (m : ℕ) (x : ModeState) : ℝ :=
  x.coeff 0 + logEnergyRadius m x

/-- Hard log-energy detector. -/
def hardLogEnergyThresholdRadius (m : ℕ) (x : ModeState) : ℝ :=
  if ∃ n, 0 < Real.log (1 + (sobolevAmplification m x n) ^ (2 : ℕ)) then 1 else 0

/-- The independent logarithmic formula agrees with the generic profile on squares. -/
theorem profiledEnergyTerm_logOnePlusMax_eq_logEnergyTerm (m : ℕ) (x : ModeState) (n : ℕ) :
    profiledEnergyTerm logOnePlusMaxEnergyProfile m x n = logEnergyTerm m x n := by
  simp [profiledEnergyTerm, logOnePlusMaxEnergyProfile, logEnergyTerm,
    max_eq_left (sq_nonneg (sobolevAmplification m x n))]

theorem profiledEnergyRadius_logOnePlusMax_eq_logEnergyRadius (m : ℕ) :
    profiledEnergyRadius logOnePlusMaxEnergyProfile m = logEnergyRadius m := by
  funext x
  simp only [profiledEnergyRadius, profiledEnergyTerm_logOnePlusMax_eq_logEnergyTerm,
    logEnergyRadius]

theorem hardProfileThresholdRadius_logOnePlusMax_eq_hardLogEnergyThresholdRadius (m : ℕ) :
    hardProfileThresholdRadius logOnePlusMaxEnergyProfile m = hardLogEnergyThresholdRadius m := by
  funext x
  simp only [hardProfileThresholdRadius, hardLogEnergyThresholdRadius,
    logOnePlusMaxEnergyProfile, max_eq_left (sq_nonneg (sobolevAmplification m x _))]

theorem continuous_logEnergyRadius (m : ℕ) : Continuous (logEnergyRadius m) := by
  rw [← profiledEnergyRadius_logOnePlusMax_eq_logEnergyRadius]
  exact continuous_profiledEnergyRadius _ m

theorem logEnergyTerm_le_compensatedEnergyTerm (m : ℕ) (x : ModeState) (n : ℕ) :
    logEnergyTerm m x n ≤ compensatedEnergyTerm x n := by
  rw [← profiledEnergyTerm_logOnePlusMax_eq_logEnergyTerm]
  exact profiledEnergyTerm_le_compensatedEnergyTerm _ m x n

theorem hardLogEnergyThresholdRadius_eq_hardSupportRadius (m : ℕ) :
    hardLogEnergyThresholdRadius m = hardSupportRadius := by
  rw [← hardProfileThresholdRadius_logOnePlusMax_eq_hardLogEnergyThresholdRadius,
    hardProfileThresholdRadius_eq_hardSobolevRadius, hardSobolevRadius_eq_hardSupportRadius]

theorem hardLogEnergyThresholdRadius_tailSpikeStableAt_one (m : ℕ) :
    TailSpikeStableAt (hardLogEnergyThresholdRadius m) 1 := by
  rw [hardLogEnergyThresholdRadius_eq_hardSupportRadius]
  exact tailPresenceRadius_tailSpikeStableAt_one

theorem hardLogEnergyThresholdRadius_modeZero (m : ℕ) :
    hardLogEnergyThresholdRadius m modeZero = 0 := by
  rw [hardLogEnergyThresholdRadius_eq_hardSupportRadius]
  exact tailPresenceRadius_modeZero

theorem not_continuousAt_hardLogEnergyThresholdRadius_modeZero (m : ℕ) :
    ¬ ContinuousAt (hardLogEnergyThresholdRadius m) modeZero := by
  rw [hardLogEnergyThresholdRadius_eq_hardSupportRadius]
  exact not_continuousAt_hardSupportRadius_modeZero

theorem not_continuousAt_hardLogEnergyThreshold_cutoffPotential_modeZero (m : ℕ) :
    ¬ ContinuousAt (cutoffPotential (fun r => r) (hardLogEnergyThresholdRadius m)
      unitStatisticMode) modeZero := by
  rw [hardLogEnergyThresholdRadius_eq_hardSupportRadius]
  exact not_continuousAt_hardSupport_cutoffPotential_modeZero

theorem not_continuousAt_hardLogEnergyThreshold_coleHopfPhi_modeZero (m : ℕ) :
    ¬ ContinuousAt (coleHopfPhi 1 (cutoffPotential (fun r => r)
      (hardLogEnergyThresholdRadius m) unitStatisticMode)) modeZero := by
  rw [hardLogEnergyThresholdRadius_eq_hardSupportRadius]
  exact not_continuousAt_hardSupport_coleHopfPhi_modeZero

end ModeStateLogEnergyChartFork

end NavierStokes
end FluidDynamics
end Mettapedia
