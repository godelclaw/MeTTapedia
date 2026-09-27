import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
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

noncomputable local instance connectedComponentVertexFintype
    (component : G.ConnectedComponent) : Fintype component :=
  Fintype.ofFinite component

noncomputable local instance connectedComponentAdjDecidable
    (component : G.ConnectedComponent) :
    DecidableRel component.toSimpleGraph.Adj :=
  Classical.decRel _

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

/-- A finite graph is presented componentwise on the sphere when every
connected component with at least three vertices carries the genuine
connected spherical presentation above.  Components with at most two
vertices need no rotation-system witness for four-colourability. -/
def ComponentwiseSphericalGraphPresentable (G : SimpleGraph V) : Prop :=
  ∀ component : G.ConnectedComponent,
    3 ≤ Fintype.card component →
      Nonempty (ConnectedSphericalGraphPresentation component.toSimpleGraph)

/-- The sound combinatorial notion of planarity used by the formal headline.
A finite simple graph is combinatorially planar when every nontrivial
connected component carries a cellular spherical rotation presentation.

This is the standard finite-map representation of planarity.  Equivalence
with a topological crossing-free drawing is a separate representation theorem;
unlike the legacy `Mettapedia.GraphTheory.IsPlanar`, this predicate records the
cyclic orders and spherical Euler equation actually consumed by Tait's
reduction. -/
abbrev CombinatoriallyPlanar (G : SimpleGraph V) : Prop :=
  ComponentwiseSphericalGraphPresentable G

/-- The componentwise spherical form of the Four-Colour statement. -/
def SphericalFourColorStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj],
    ComponentwiseSphericalGraphPresentable G → G.Colorable 4

/-- The Four-Colour statement in the finite combinatorial-map convention:
every finite simple graph carrying a cellular spherical presentation is
four-colourable. -/
def CombinatorialFourColorStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj],
    CombinatoriallyPlanar G → G.Colorable 4

/-- The explicit combinatorial-planarity headline is definitionally the
componentwise spherical headline used by the route. -/
theorem combinatorialFourColorStatement_iff_spherical :
    CombinatorialFourColorStatement.{u} ↔ SphericalFourColorStatement.{u} :=
  Iff.rfl

/-- Colouring every genuinely presented connected component colours the
whole graph.  Small components are coloured injectively; all other
components are passed to the connected spherical statement. -/
theorem sphericalFourColorStatement_of_connected
    (hconnected : ConnectedSphericalFourColorStatement.{u}) :
    SphericalFourColorStatement.{u} := by
  intro V _ _ G _ hpresentation
  rw [G.colorable_iff_forall_connectedComponents]
  intro component
  by_cases hcard : 3 ≤ Fintype.card component
  · exact hconnected component.toSimpleGraph hcard
      (hpresentation component hcard)
  · exact (component.toSimpleGraph.colorable_of_fintype).mono (by omega)

end GoertzelV24SphericalGraphPresentation

end Mettapedia.GraphTheory.FourColor
