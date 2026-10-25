import Mettapedia.FluidDynamics.NavierStokes.ModeStateLogEnergyChartFork

/-!
# Profiled energy: continuity and mode truncation

Extends the profiled-energy theory of `ModeStateEnergyProfileFork`. The statistic is
continuous; the radius and the statistic converge along mode truncation; and the
cutoff potential built from them, and its Cole-Hopf transform, are continuous.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped Classical

section ModeStateEnergyProfileCore

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

end ModeStateEnergyProfileCore

end NavierStokes
end FluidDynamics
end Mettapedia
