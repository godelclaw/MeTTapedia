import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphFaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# Genuine spherical presentations for the Four-Colour headline

The legacy `Mettapedia.GraphTheory.IsPlanar` predicate stores only twice-used
edge sets and is satisfied by every finite simple graph.  The compositional
route already uses a stronger and mathematically standard representation:
a cyclic rotation at every graph vertex together with connectedness and the
spherical Euler equation on the resulting face orbits.

This file packages that representation without changing the shared legacy
API.  The connected presentation is the input consumed by Tait's reduction.
The componentwise predicate treats components with at most two vertices
separately, exactly as the ordinary proof does.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SphericalGraphPresentation

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24SimpleGraphFaceDualConnectedness

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A connected simple graph presented as a cellular map on the sphere.
The cyclicity field rules out a rotation permutation with several local
cycles at one graph vertex; the Euler field fixes the surface to the sphere. -/
structure ConnectedSphericalGraphPresentation (G : SimpleGraph V)
    [DecidableRel G.Adj] where
  graphData : SimpleGraphDartRotation.Data G
  connected : G.Connected
  vertexRotationCyclic : VertexRotationCyclic graphData.toRotationSystem
  euler :
    (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace graphData.toRotationSystem) = 2

namespace ConnectedSphericalGraphPresentation

variable (presentation : ConnectedSphericalGraphPresentation G)

/-- The presentation's primal rotation graph is the original simple graph. -/
theorem primalConnected :
    (rotationPrimalGraph presentation.graphData.toRotationSystem).Connected := by
  rw [rotationPrimalGraph_toRotationSystem_eq]
  exact presentation.connected

end ConnectedSphericalGraphPresentation

/-- The repaired connected source-facing Four-Colour statement.  Unlike the
legacy `IsPlanar` formulation, its premise is a genuine spherical
rotation-system presentation.  The componentwise wrapper is kept separate:
components with at most two vertices require no dart presentation. -/
def ConnectedSphericalFourColorStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj],
    3 ≤ Fintype.card V →
      Nonempty (ConnectedSphericalGraphPresentation G) →
        G.Colorable 4

end GoertzelV24SphericalGraphPresentation

end Mettapedia.GraphTheory.FourColor
