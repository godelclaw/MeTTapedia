import Mettapedia.FluidDynamics.NavierStokes.ModeStateEnergyChartFork
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Generic Energy-Profile Fork on the Shared Mode State

A continuous profile, nonnegative and bounded above by the identity on
nonnegative inputs, has a derived zero law. Applied to squared amplified
coordinates before compensation, it gives a summable coordinate observation.
Strict positivity identifies its hard detector with support presence.

The identity profile cancels amplification exactly. Nonlinear logarithmic,
rational, exponential, and smooth-transition profiles need not; a rational
example computes two distinct responses for different amplification levels.
The concrete logarithmic formula is interpreted by this generic theory in
`ModeStateLogEnergyChartFork`, keeping the dependency direction explicit.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped Classical

section ModeStateEnergyProfileFork

/-- A continuous radial profile dominated by the identity on nonnegative
inputs, and strictly positive on positive inputs. Its zero law is derived. -/
structure EnergyProfile where
  profile : ℝ → ℝ
  continuous_profile : Continuous profile
  profile_nonneg : ∀ u, 0 ≤ u → 0 ≤ profile u
  profile_le : ∀ u, 0 ≤ u → profile u ≤ u
  profile_pos : ∀ u, 0 < u → 0 < profile u

@[simp] theorem EnergyProfile.profile_zero (P : EnergyProfile) : P.profile 0 = 0 :=
  le_antisymm (P.profile_le 0 le_rfl) (P.profile_nonneg 0 le_rfl)

/-- Applying a nonlinear profile before compensation can retain dependence on `m`. -/
def profiledEnergyTerm (P : EnergyProfile) (m : ℕ) (x : ModeState) (n : ℕ) : ℝ :=
  P.profile ((sobolevAmplification m x n) ^ 2) * energyCompensationWeight m n

def profiledEnergyRadius (P : EnergyProfile) (m : ℕ) (x : ModeState) : ℝ :=
  ∑' n, profiledEnergyTerm P m x n

def profiledEnergyStatistic (P : EnergyProfile) (m : ℕ) (x : ModeState) : ℝ :=
  x.coeff 0 + profiledEnergyRadius P m x

def hardProfileThresholdRadius (P : EnergyProfile) (m : ℕ) (x : ModeState) : ℝ :=
  if ∃ n, 0 < P.profile ((sobolevAmplification m x n) ^ 2) then 1 else 0

theorem continuous_profiledEnergyTerm (P : EnergyProfile) (m n : ℕ) :
    Continuous fun x : ModeState => profiledEnergyTerm P m x n :=
  (P.continuous_profile.comp ((continuous_sobolevAmplification m n).pow 2)).mul continuous_const

theorem profiledEnergyTerm_le_compensatedEnergyTerm
    (P : EnergyProfile) (m : ℕ) (x : ModeState) (n : ℕ) :
    profiledEnergyTerm P m x n ≤ compensatedEnergyTerm x n := by
  rw [← amplifiedEnergyTerm_eq_compensatedEnergyTerm m]
  exact mul_le_mul_of_nonneg_right (P.profile_le _ (sq_nonneg _))
    (energyCompensationWeight_nonneg m n)

theorem norm_profiledEnergyTerm_le_inverseSquare (P : EnergyProfile) (m : ℕ)
    (x : ModeState) (n : ℕ) : ‖profiledEnergyTerm P m x n‖ ≤ inverseSquareModeWeights.weight n := by
  have nonneg : 0 ≤ profiledEnergyTerm P m x n :=
    mul_nonneg (P.profile_nonneg _ (sq_nonneg (sobolevAmplification m x n)))
    (energyCompensationWeight_nonneg m n)
  rw [Real.norm_eq_abs, abs_of_nonneg nonneg]
  exact (profiledEnergyTerm_le_compensatedEnergyTerm P m x n).trans
    (le_trans (le_abs_self _) (by
      exact (squareModeObservable inverseSquareModeWeights).norm_term_le x n))

/-- The nonlinear formula shares the inverse-square envelope with compensated energy. -/
def profiledEnergyObservable (P : EnergyProfile) (m : ℕ) : SummableCoordinateObservable where
  envelope := inverseSquareModeWeights
  response n t := P.profile (((n + 1 : ℝ) ^ m * t) ^ 2) * energyCompensationWeight m n
  continuous_response n := by
    apply Continuous.continuousOn
    apply Continuous.mul
    · apply P.continuous_profile.comp
      fun_prop
    · exact continuous_const
  norm_response_le n t ht :=
    norm_profiledEnergyTerm_le_inverseSquare P m ⟨fun _ => t, fun _ => ht⟩ n

theorem continuous_profiledEnergyRadius (P : EnergyProfile) (m : ℕ) :
    Continuous (profiledEnergyRadius P m) := (profiledEnergyObservable P m).continuous_value

/-- All strictly positive profiles have the same support detector, despite
their different quantitative observations. -/
theorem hardProfileThresholdRadius_eq_hardSobolevRadius (P : EnergyProfile) (m : ℕ) :
    hardProfileThresholdRadius P m = hardSobolevRadius m := by
  have positive (t : ℝ) : 0 < P.profile (t ^ 2) ↔ t ≠ 0 := by
    constructor
    · rintro h rfl
      simp at h
    · exact fun h => P.profile_pos _ (sq_pos_of_ne_zero h)
  funext x
  simp only [hardProfileThresholdRadius, positive, hardSobolevRadius]

theorem hardProfileThresholdRadius_tailSpikeStableAt_one (P : EnergyProfile) (m : ℕ) :
    TailSpikeStableAt (hardProfileThresholdRadius P m) 1 := by
  rw [hardProfileThresholdRadius_eq_hardSobolevRadius, hardSobolevRadius_eq_hardSupportRadius]
  exact tailPresenceRadius_tailSpikeStableAt_one

theorem hardProfileThresholdRadius_modeZero (P : EnergyProfile) (m : ℕ) :
    hardProfileThresholdRadius P m modeZero = 0 := by
  rw [hardProfileThresholdRadius_eq_hardSobolevRadius, hardSobolevRadius_eq_hardSupportRadius]
  exact tailPresenceRadius_modeZero

theorem not_continuousAt_hardProfileThresholdRadius_modeZero (P : EnergyProfile) (m : ℕ) :
    ¬ ContinuousAt (hardProfileThresholdRadius P m) modeZero := by
  rw [hardProfileThresholdRadius_eq_hardSobolevRadius]
  exact not_continuousAt_hardSobolevRadius_modeZero m

theorem not_continuousAt_hardProfileThreshold_cutoffPotential_modeZero
    (P : EnergyProfile) (m : ℕ) :
    ¬ ContinuousAt (cutoffPotential (fun r => r) (hardProfileThresholdRadius P m)
      unitStatisticMode) modeZero := by
  rw [hardProfileThresholdRadius_eq_hardSobolevRadius]
  exact not_continuousAt_hardSobolev_cutoffPotential_modeZero m

theorem not_continuousAt_hardProfileThreshold_coleHopfPhi_modeZero
    (P : EnergyProfile) (m : ℕ) :
    ¬ ContinuousAt (coleHopfPhi 1 (cutoffPotential (fun r => r)
      (hardProfileThresholdRadius P m) unitStatisticMode)) modeZero := by
  rw [hardProfileThresholdRadius_eq_hardSobolevRadius]
  exact not_continuousAt_hardSobolev_coleHopfPhi_modeZero m

/-- The identity profile recovers compensated energy. -/
def identityEnergyProfile : EnergyProfile where
  profile := id
  continuous_profile := continuous_id
  profile_nonneg _ hu := hu
  profile_le _ _ := le_rfl
  profile_pos _ hu := hu

/-- Clipped logarithm, agreeing with `log (1 + u)` on nonnegative inputs. -/
def logOnePlusMaxEnergyProfile : EnergyProfile where
  profile u := Real.log (1 + max u 0)
  continuous_profile := (continuous_const.add (continuous_id.max continuous_const)).log
    (fun u => ne_of_gt (by change 0 < 1 + max u 0; linarith [le_max_right u 0]))
  profile_nonneg u hu := by
    simp only [max_eq_left hu]
    exact Real.log_nonneg (by linarith)
  profile_le u hu := by
    simpa [max_eq_left hu] using Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + u)
  profile_pos u hu := by
    simp only [max_eq_left hu.le]
    exact Real.log_pos (by linarith)

/-- Bounded rational saturation, agreeing with `u / (1 + u)` for nonnegative `u`. -/
def rationalMaxEnergyProfile : EnergyProfile where
  profile u := max u 0 / (1 + max u 0)
  continuous_profile := (continuous_id.max continuous_const).div
    (continuous_const.add (continuous_id.max continuous_const))
    (fun u => ne_of_gt (by change 0 < 1 + max u 0; linarith [le_max_right u 0]))
  profile_nonneg u hu := by simp only [max_eq_left hu]; positivity
  profile_le u hu := by simpa [max_eq_left hu] using div_le_self hu (by linarith : 1 ≤ 1 + u)
  profile_pos u hu := by simp only [max_eq_left hu.le]; positivity

/-- Exponential saturation, agreeing with `1 - exp(-u)` for nonnegative `u`. -/
def expNegMaxEnergyProfile : EnergyProfile where
  profile u := 1 - Real.exp (-max u 0)
  continuous_profile := continuous_const.sub
    (Real.continuous_exp.comp (continuous_id.max continuous_const).neg)
  profile_nonneg u hu := by
    simp only [max_eq_left hu]
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu))
  profile_le u hu := by
    simp only [max_eq_left hu]
    linarith [Real.add_one_le_exp (-u)]
  profile_pos u hu := by
    simp only [max_eq_left hu.le]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))

/-- Smooth transition, zero on nonpositive inputs and equal to `u` above one. -/
def smoothTransitionEnergyProfile : EnergyProfile where
  profile u := u * Real.smoothTransition u
  continuous_profile := continuous_id.mul Real.smoothTransition.continuous
  profile_nonneg u hu := mul_nonneg hu (Real.smoothTransition.nonneg u)
  profile_le u hu := by simpa using mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one u) hu
  profile_pos u hu := mul_pos hu (Real.smoothTransition.pos_of_pos hu)

/-- Positive-scale smooth transition. -/
def scaledSmoothTransitionEnergyProfile (c : ℝ) (hc : 0 < c) : EnergyProfile where
  profile u := u * Real.smoothTransition (c * u)
  continuous_profile := continuous_id.mul
    (Real.smoothTransition.continuous.comp (continuous_const.mul continuous_id))
  profile_nonneg u hu := mul_nonneg hu (Real.smoothTransition.nonneg (c * u))
  profile_le u hu := by
    simpa using mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one (c * u)) hu
  profile_pos u hu := mul_pos hu (Real.smoothTransition.pos_of_pos (mul_pos hc hu))

theorem profiledEnergyTerm_identity_eq_compensatedEnergyTerm (m : ℕ) (x : ModeState) (n : ℕ) :
    profiledEnergyTerm identityEnergyProfile m x n = compensatedEnergyTerm x n :=
  amplifiedEnergyTerm_eq_compensatedEnergyTerm m x n

theorem profiledEnergyRadius_identity_eq_compensatedEnergyRadius (m : ℕ) :
    profiledEnergyRadius identityEnergyProfile m = compensatedEnergyRadius := by
  funext x
  exact amplifiedEnergy_sum_eq_compensatedRadius m x

/-- Nonlinear profiling before compensation can distinguish amplification levels. -/
theorem rationalProfile_amplification_changes_term :
    profiledEnergyTerm rationalMaxEnergyProfile 0 (tailSpikeMode 1) 1 = 1 / 8 ∧
    profiledEnergyTerm rationalMaxEnergyProfile 1 (tailSpikeMode 1) 1 = 1 / 20 := by
  norm_num [profiledEnergyTerm, rationalMaxEnergyProfile, sobolevAmplification,
    energyCompensationWeight, tailSpikeMode]

end ModeStateEnergyProfileFork

end NavierStokes
end FluidDynamics
end Mettapedia
