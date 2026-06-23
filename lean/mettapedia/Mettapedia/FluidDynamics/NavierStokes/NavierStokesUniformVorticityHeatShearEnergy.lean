import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearEnergyCore
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearFullDriftEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearStreamwiseDriftEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearVerticalDriftEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearEnergyTransport

/-!
# Heat-Shear Energy Obstructions for Uniform-Vorticity Continuation

Compatibility umbrella for the heat-shear kinetic-energy identities and
finite-energy obstructions. The implementation is split into core, drift, and
transport modules so downstream rebuilds can depend on the smaller layer they
actually need.
-/
