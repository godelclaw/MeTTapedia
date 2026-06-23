import Mettapedia.FluidDynamics.NavierStokes.ModeStateLogEnergyChartFork

/-!
# Profiled Energy Core on ModeState

This module was split out of `ModeStateEnergyProfileFork.lean` to keep the
Navier-Stokes route-audit library organized by mathematical role.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped Classical

section ModeStateEnergyProfileCore

/-- A globally continuous radial energy profile that is nonnegative,
dominated by the identity on nonnegative inputs, and strictly positive on
positive inputs. -/
structure EnergyProfile where
  profile : ℝ → ℝ
  continuous_profile : Continuous profile
  profile_nonneg : ∀ u, 0 ≤ u → 0 ≤ profile u
  profile_le : ∀ u, 0 ≤ u → profile u ≤ u
  profile_zero : profile 0 = 0
  profile_pos : ∀ u, 0 < u → 0 < profile u

/-- Soft profiled energy term. -/
def profiledEnergyTerm (P : EnergyProfile) (m : ℕ) (x : ModeState) (n : ℕ) : ℝ :=
  P.profile ((sobolevAmplification m x n) ^ (2 : ℕ)) * sobolevEnergyWeight m n

/-- Soft profiled energy radius. -/
def profiledEnergyRadius (P : EnergyProfile) (m : ℕ) (x : ModeState) : ℝ :=
  ∑' n, profiledEnergyTerm P m x n

/-- Zeroth visible mode plus the profiled energy radius. -/
def profiledEnergyStatistic (P : EnergyProfile) (m : ℕ) (x : ModeState) : ℝ :=
  x.coeff 0 + profiledEnergyRadius P m x

/-- Hard detector induced by the profile. -/
def hardProfileThresholdRadius (P : EnergyProfile) (m : ℕ) (x : ModeState) : ℝ :=
  if ∃ n, 0 < P.profile ((sobolevAmplification m x n) ^ (2 : ℕ)) then 1 else 0

theorem continuous_profiledEnergyTerm (P : EnergyProfile) (m n : ℕ) :
    Continuous fun x : ModeState => profiledEnergyTerm P m x n := by
  simpa [profiledEnergyTerm] using
    ((P.continuous_profile.comp ((continuous_sobolevAmplification m n).pow 2)).mul
      (continuous_const : Continuous fun _ : ModeState => sobolevEnergyWeight m n))

theorem profiledEnergyTerm_le_sobolevEnergyTerm
    (P : EnergyProfile) (m : ℕ) (x : ModeState) (n : ℕ) :
    profiledEnergyTerm P m x n ≤ sobolevEnergyTerm m x n := by
  have hsq_nonneg : 0 ≤ (sobolevAmplification m x n) ^ (2 : ℕ) := by positivity
  exact mul_le_mul_of_nonneg_right
    (P.profile_le _ hsq_nonneg) (sobolevEnergyWeight_nonneg m n)

theorem norm_profiledEnergyTerm_le_inverseSquare
    (P : EnergyProfile) (m : ℕ) (x : ModeState) (n : ℕ) :
    ‖profiledEnergyTerm P m x n‖ ≤ inverseSquareModeWeights.weight n := by
  have hprof_nonneg : 0 ≤ P.profile ((sobolevAmplification m x n) ^ (2 : ℕ)) := by
    have hsq_nonneg : 0 ≤ (sobolevAmplification m x n) ^ (2 : ℕ) := by positivity
    exact P.profile_nonneg _ hsq_nonneg
  have hterm_nonneg : 0 ≤ profiledEnergyTerm P m x n := by
    exact mul_nonneg hprof_nonneg (sobolevEnergyWeight_nonneg m n)
  have hsoft_nonneg : 0 ≤ sobolevEnergyTerm m x n := by
    exact mul_nonneg (by positivity) (sobolevEnergyWeight_nonneg m n)
  calc
    ‖profiledEnergyTerm P m x n‖ = profiledEnergyTerm P m x n := by
      rw [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg]
    _ ≤ sobolevEnergyTerm m x n := profiledEnergyTerm_le_sobolevEnergyTerm P m x n
    _ ≤ inverseSquareModeWeights.weight n := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hsoft_nonneg] using
        norm_sobolevEnergyTerm_le_inverseSquare m x n

theorem continuous_profiledEnergyRadius (P : EnergyProfile) (m : ℕ) :
    Continuous (profiledEnergyRadius P m) := by
  unfold profiledEnergyRadius
  refine continuous_tsum (fun n => continuous_profiledEnergyTerm P m n)
    inverseSquareModeWeights.summable_weight ?_
  intro n x
  exact norm_profiledEnergyTerm_le_inverseSquare P m x n

theorem continuous_profiledEnergyStatistic (P : EnergyProfile) (m : ℕ) :
    Continuous (profiledEnergyStatistic P m) := by
  unfold profiledEnergyStatistic
  exact (continuous_coeffObservable 0).add (continuous_profiledEnergyRadius P m)

theorem tendsto_profiledEnergyRadius_truncateModes
    (P : EnergyProfile) (m : ℕ) (x : ModeState) :
    Tendsto (fun N => profiledEnergyRadius P m (truncateModes N x))
      Filter.atTop (nhds (profiledEnergyRadius P m x)) := by
  exact (continuous_profiledEnergyRadius P m).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x)

theorem tendsto_profiledEnergyStatistic_truncateModes
    (P : EnergyProfile) (m : ℕ) (x : ModeState) :
    Tendsto (fun N => profiledEnergyStatistic P m (truncateModes N x))
      Filter.atTop (nhds (profiledEnergyStatistic P m x)) := by
  exact (continuous_profiledEnergyStatistic P m).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x)

theorem continuous_profiledEnergy_cutoffPotential
    (P : EnergyProfile) (m : ℕ) {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (cutoffPotential cutoff (profiledEnergyRadius P m) (profiledEnergyStatistic P m)) := by
  exact continuous_cutoffPotential hcutoff
    (continuous_profiledEnergyRadius P m) (continuous_profiledEnergyStatistic P m)

theorem continuous_profiledEnergy_coleHopfPhi
    (P : EnergyProfile) (m : ℕ) {ν : ℝ} {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (coleHopfPhi ν
      (cutoffPotential cutoff (profiledEnergyRadius P m) (profiledEnergyStatistic P m))) := by
  exact continuous_cutoffColeHopfPhi hcutoff
    (continuous_profiledEnergyRadius P m) (continuous_profiledEnergyStatistic P m)

theorem hardProfileThresholdRadius_tailSpikeStableAt_one
    (P : EnergyProfile) (m : ℕ) :
    TailSpikeStableAt (hardProfileThresholdRadius P m) 1 := by
  intro N
  unfold hardProfileThresholdRadius
  split_ifs with h
  · rfl
  · exfalso
    apply h
    refine ⟨N, ?_⟩
    have hsq_pos : 0 < (((N + 1 : ℝ) ^ m) ^ (2 : ℕ)) := by positivity
    have hprof_pos : 0 < P.profile ((((N + 1 : ℝ) ^ m) ^ (2 : ℕ))) :=
      P.profile_pos _ hsq_pos
    simpa [sobolevAmplification, tailSpikeMode] using hprof_pos

theorem hardProfileThresholdRadius_modeZero
    (P : EnergyProfile) (m : ℕ) :
    hardProfileThresholdRadius P m modeZero = 0 := by
  unfold hardProfileThresholdRadius
  split_ifs with h
  · rcases h with ⟨n, hn⟩
    simp [sobolevAmplification, modeZero, P.profile_zero] at hn
  · rfl

theorem not_continuousAt_hardProfileThresholdRadius_modeZero
    (P : EnergyProfile) (m : ℕ) :
    ¬ ContinuousAt (hardProfileThresholdRadius P m) modeZero := by
  refine not_continuousAt_of_tailSpikeStableAt
    (hardProfileThresholdRadius_tailSpikeStableAt_one P m) ?_
  simp [hardProfileThresholdRadius_modeZero]

theorem not_continuousAt_hardProfileThreshold_cutoffPotential_modeZero
    (P : EnergyProfile) (m : ℕ) :
    ¬ ContinuousAt
      (cutoffPotential (fun r => r) (hardProfileThresholdRadius P m) unitStatisticMode)
      modeZero := by
  exact not_continuousAt_cutoffPotential_of_tailSpikeStableAt
    (hardProfileThresholdRadius_tailSpikeStableAt_one P m)
    tendsto_unitStatisticMode_tailSpikeMode
    (by
      unfold cutoffPotential
      rw [hardProfileThresholdRadius_modeZero]
      norm_num [unitStatisticMode, modeZero])

theorem not_continuousAt_hardProfileThreshold_coleHopfPhi_modeZero
    (P : EnergyProfile) (m : ℕ) :
    ¬ ContinuousAt
      (coleHopfPhi 1
        (cutoffPotential (fun r => r) (hardProfileThresholdRadius P m) unitStatisticMode))
      modeZero := by
  exact not_continuousAt_coleHopfPhi_of_tailSpikeStableAt
    (hardProfileThresholdRadius_tailSpikeStableAt_one P m)
    tendsto_unitStatisticMode_tailSpikeMode
    (by norm_num)
    (by
      unfold cutoffPotential
      rw [hardProfileThresholdRadius_modeZero]
      norm_num [unitStatisticMode, modeZero])

theorem hardProfileThresholdRadius_eq_hardSobolevRadius
    (P : EnergyProfile) (m : ℕ) :
    hardProfileThresholdRadius P m = hardSobolevRadius m := by
  funext x
  have hiff :
      (∃ n, 0 < P.profile ((sobolevAmplification m x n) ^ (2 : ℕ))) ↔
        ∃ n, sobolevAmplification m x n ≠ 0 := by
    constructor
    · intro h
      rcases h with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      intro hzero
      have hsq_zero : (sobolevAmplification m x n) ^ (2 : ℕ) = 0 := by
        simp [hzero]
      have hprof_zero : P.profile ((sobolevAmplification m x n) ^ (2 : ℕ)) = 0 := by
        simpa [hsq_zero] using P.profile_zero
      rw [hprof_zero] at hn
      linarith
    · intro h
      rcases h with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hsq_pos : 0 < (sobolevAmplification m x n) ^ (2 : ℕ) := by
        nlinarith [sq_pos_of_ne_zero hn]
      exact P.profile_pos _ hsq_pos
  by_cases h : ∃ n, sobolevAmplification m x n ≠ 0
  · have hp :
        ∃ n, 0 < P.profile ((sobolevAmplification m x n) ^ (2 : ℕ)) := hiff.mpr h
    simp [hardProfileThresholdRadius, hardSobolevRadius, hp, h]
  · have hp :
        ¬ ∃ n, 0 < P.profile ((sobolevAmplification m x n) ^ (2 : ℕ)) := by
        intro hp
        exact h (hiff.mp hp)
    simp [hardProfileThresholdRadius, hardSobolevRadius, hp, h]

end ModeStateEnergyProfileCore

end NavierStokes
end FluidDynamics
end Mettapedia
