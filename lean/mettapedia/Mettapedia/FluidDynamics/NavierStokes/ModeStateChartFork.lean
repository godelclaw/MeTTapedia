import Mettapedia.FluidDynamics.NavierStokes.ModeStateObservableClass
import Mettapedia.FluidDynamics.NavierStokes.ModeStateTailSensitivityObstruction
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Chart Fork on the Shared Mode State

The bounded continuous scalar `|t| / (1 + |t|)` gives summable soft support
observations. Polynomial amplification can be supplied before that scalar
without changing the envelope. The hard detector asks whether any coordinate
is nonzero and is discontinuous at zero in the product topology.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section ModeStateChartFork

/-- Continuous soft support detector on one real coordinate. -/
def softSupportScalar : ℝ → ℝ :=
  fun t => |t| / (1 + |t|)

/-- Soft weighted mode contribution. -/
def softSupportTerm (W : SummableModeWeights) (x : ModeState) (n : ℕ) : ℝ :=
  softSupportScalar (x.coeff n) * W.weight n

/-- Soft support chart radius. -/
def softSupportRadius (W : SummableModeWeights) (x : ModeState) : ℝ :=
  ∑' n, softSupportTerm W x n

/-- Zeroth visible mode plus the soft support radius. -/
def softSupportStatistic (W : SummableModeWeights) (x : ModeState) : ℝ :=
  x.coeff 0 + softSupportRadius W x

/-- Hard support chart radius: any nonzero mode is counted as present. -/
def hardSupportRadius : ModeState → ℝ :=
  tailPresenceRadius

theorem continuous_softSupportScalar :
    Continuous softSupportScalar := by
  have hden : ∀ t : ℝ, 1 + |t| ≠ 0 := by
    intro t
    positivity
  exact continuous_abs.div (continuous_const.add continuous_abs) hden

theorem softSupportScalar_nonneg (t : ℝ) :
    0 ≤ softSupportScalar t := by
  unfold softSupportScalar
  positivity

theorem softSupportScalar_le_one (t : ℝ) : softSupportScalar t ≤ 1 := by
  exact (div_le_one (by positivity : 0 < 1 + |t|)).mpr (by linarith [abs_nonneg t])

/-- Bounded soft support after an arbitrary coordinate amplification. -/
def softSupportObservable (W : SummableModeWeights) (amplification : ℕ → ℝ) :
    SummableCoordinateObservable where
  envelope := W
  response n t := softSupportScalar (amplification n * t) * W.weight n
  continuous_response n := ((continuous_softSupportScalar.comp
    (continuous_const.mul continuous_id)).mul continuous_const).continuousOn
  norm_response_le n t _ := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (softSupportScalar_nonneg _) (W.weight_nonneg n))]
    exact mul_le_of_le_one_left (W.weight_nonneg n) (softSupportScalar_le_one _)

theorem continuous_softSupportRadius (W : SummableModeWeights) :
    Continuous (softSupportRadius W) := by
  convert (softSupportObservable W (fun _ => 1)).continuous_value using 1
  ext x
  simp [SummableCoordinateObservable.value, SummableCoordinateObservable.term,
    softSupportObservable, softSupportRadius, softSupportTerm]

theorem not_continuousAt_hardSupportRadius_modeZero :
    ¬ ContinuousAt hardSupportRadius modeZero := by
  exact not_continuousAt_tailPresenceRadius_modeZero

theorem not_continuousAt_hardSupport_cutoffPotential_modeZero :
    ¬ ContinuousAt
      (cutoffPotential (fun r => r) hardSupportRadius unitStatisticMode)
      modeZero := by
  exact not_continuousAt_cutoffPotential_of_tailSpikeStableAt
    tailPresenceRadius_tailSpikeStableAt_one
    tendsto_unitStatisticMode_tailSpikeMode
    (by
      unfold hardSupportRadius cutoffPotential
      rw [tailPresenceRadius_modeZero]
      norm_num [unitStatisticMode, modeZero])

theorem not_continuousAt_hardSupport_coleHopfPhi_modeZero :
    ¬ ContinuousAt
      (coleHopfPhi 1 (cutoffPotential (fun r => r) hardSupportRadius unitStatisticMode))
      modeZero := by
  exact not_continuousAt_coleHopfPhi_of_tailSpikeStableAt
    tailPresenceRadius_tailSpikeStableAt_one
    tendsto_unitStatisticMode_tailSpikeMode
    (by norm_num)
    (by
      unfold hardSupportRadius cutoffPotential
      rw [tailPresenceRadius_modeZero]
      norm_num [unitStatisticMode, modeZero])

end ModeStateChartFork

end NavierStokes
end FluidDynamics
end Mettapedia
