import Mettapedia.FluidDynamics.NavierStokes.ContinuationRegressionCounterexamplesBasic
import Mettapedia.FluidDynamics.NavierStokes.ContinuationRegressionCounterexamplesAffineShear
import Mettapedia.FluidDynamics.NavierStokes.ContinuationRegressionCounterexamplesHeatShearCore
import Mettapedia.FluidDynamics.NavierStokes.ContinuationRegressionCounterexamplesHeatShearDrifts
import Mettapedia.FluidDynamics.NavierStokes.ContinuationRegressionCounterexamplesHeatShearTransport

/-!
# False-target, non-finite-energy, shear, heat-shear, and transported-shear counterexample regressions

Compatibility umbrella for continuation counterexample regressions. The
implementation is split into basic target/domain failures, affine-shear
families, undrifted heat-shear, drift heat-shear, and transported heat-shear
regressions.
-/
