import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportProfiles
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportDerivatives
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportLaplacian
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportMomentum
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportVorticity

/-!
# Vector Calculus R3: Transport

Compatibility umbrella for transported heat-shear identities. The
implementation is split into profile/smoothness, derivative/divergence,
Laplacian, momentum, and vorticity-obstruction layers.
-/
