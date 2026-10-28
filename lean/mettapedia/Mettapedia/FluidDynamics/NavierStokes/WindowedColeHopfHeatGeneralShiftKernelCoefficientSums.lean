import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatShiftKernelFrontierCore

/-!
# Finite Shift-Kernel Coefficient Sums

Definitions for seeded and live coefficient mass at a chosen translation anchor.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatGeneralShiftKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X] [DecidableEq X]

namespace SeedLiveShiftKernel

/-- Total seeded mass sitting at a chosen anchor. -/
def seedCoeffSumAt (K : SeedLiveShiftKernel κ X) (u : X) : ℝ :=
  ∑ i, if K.seedShift i = u then K.seedCoeff i else 0

/-- Total live mass sitting at a chosen anchor. -/
def liveCoeffSumAt (K : SeedLiveShiftKernel κ X) (u : X) : ℝ :=
  ∑ i, if K.liveShift i = u then K.liveCoeff i else 0

end SeedLiveShiftKernel

end WindowedColeHopfHeatGeneralShiftKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
