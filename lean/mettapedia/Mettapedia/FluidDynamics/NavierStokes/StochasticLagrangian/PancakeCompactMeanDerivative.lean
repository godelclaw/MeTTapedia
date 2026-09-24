import Mettapedia.Analysis.CompactMeanDerivative
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMaterialSpatialEstimate

/-!
# Compact-mean differentiation interface for periodic material balances

The reusable differentiation and Lipschitz estimates live in the analysis
library. These names retain the interface used by the one-point balances.
-/

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeCompactMeanDerivative

export Mettapedia.Analysis.CompactMeanDerivative
  (parameterRate measurable_parameterRate integrable_slice
    hasDerivAt_mean_of_uniform_lipschitz lipschitzOnWith_mean)

end Mettapedia.FluidDynamics.NavierStokes.PancakeCompactMeanDerivative
