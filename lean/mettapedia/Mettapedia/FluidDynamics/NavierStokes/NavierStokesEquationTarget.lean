import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationCore
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationKits
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationProblemData
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationFiniteEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationComponentBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationEquivalences
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationKitIff

/-!
# Concrete Navier-Stokes Equation Target

Compatibility umbrella for the concrete Navier-Stokes theorem surface. The
implementation is split into equation core, differential kits, problem data and
clauses, finite-energy target lemmas, component bridge, target equivalences, and
kit projection lemmas.
-/
