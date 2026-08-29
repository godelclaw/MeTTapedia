import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedBranchDecompositionAdapter
import Mettapedia.GraphTheory.FourColor.GoertzelV24SphericalMinimalCounterexampleSelection

/-!
# Sound spherical assembly of the reductive/compositional route

This module joins the three checked consumer layers of the repaired route:

* a complete connected edge-leaf decomposition bounds the size of a
  graph-backed vertex-minimal Tait counterexample;
* the route-native finite base rules out every counterexample below that
  bound;
* absence of a graph-backed vertex-minimal Tait counterexample implies the
  genuine spherical Four-Colour statement.

The two remaining inputs are deliberately visible.  `ConnectedDecompositionSupply`
is M1: it must come from the source corridor, or from fixed-wall exclusion
together with a connected branch-decomposition theorem.  `TaitBaseVerifiedAt`
is M3: it is the route-native bounded-size verification.  Neither input is
encoded as an axiom, and neither the legacy vacuous `IsPlanar` predicate nor
the refuted closed-web headline is imported here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SphericalReductiveAssembly

open GoertzelV24ConnectedBranchDecompositionForest
open GoertzelV24ConnectedBranchDecompositionAdapter
open GoertzelV24SphericalMinimalCounterexampleSelection
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

universe u

/-- The raw vertex threshold delivered by the checked connected-decomposition
consumer.  This is a logical bound, not the size of a minimized reachable
profile closure. -/
def rawVertexBound (k w : Nat) : Nat :=
  4 * (2 ^ ((6 * w + 1) *
    (∑ j : Fin (k + 1),
      Nat.factorial (j : Nat) * 2 ^ (3 ^ (j : Nat)))) - 1) + 6

/-- M1 in its exact consumer-facing form: every graph-backed vertex-minimal
counterexample carries a complete rooted connected edge-leaf decomposition
of the fixed interface bounds `k,w`.

Fixed-wall exclusion and the external connected branch-decomposition theorem
are one intended way to construct this function; they are not hidden inside
the definition. -/
def ConnectedDecompositionSupply (k w : Nat) : Type (u + 1) :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (rotation : Data G),
    GraphBackedVertexMinimalTaitCounterexample rotation →
      RootedConnectedBranchDecomposition (G := G) k w

/-- The branchwidth/wall part of M1, before connectedization: every minimal
counterexample has some rooted branch decomposition of width at most `w`.
This is deliberately separate from the Fomin--Fraigniaud--Thilikos
width-preserving connectedization proposition. -/
def RawBranchDecompositionSupply (w : Nat) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (rotation : Data G),
    GraphBackedVertexMinimalTaitCounterexample rotation →
      ∃ decomposition : RootedBranchDecomposition (G := G),
        decomposition.WidthAtMost w

/-- The two honest M1 inputs produce the exact checked literal-shore supply:
a raw width bound supplies a branch tree, and width-preserving
connectedization supplies the connected shores.  Connectedness and absence
of bridges in the minimal map discharge the external theorem's
2-edge-connected hypothesis. -/
noncomputable def connectedDecompositionSupply_of_raw_and_connectedization
    (w : Nat)
    (raw : RawBranchDecompositionSupply.{u} w)
    (connectedize : WidthPreservingConnectedization.{u}) :
    ConnectedDecompositionSupply.{u} w w := by
  intro V _ _ G _ rotation minimal
  let decomposition : RootedBranchDecomposition (G := G) :=
    Classical.choose (raw rotation minimal)
  have hwidth : decomposition.WidthAtMost w :=
    Classical.choose_spec (raw rotation minimal)
  have hgraphConnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G rotation]
    exact minimal.primalConnected
  have hnoBridge : ∀ edge ∈ G.edgeSet, ¬ G.IsBridge edge := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ left right =>
        have hadj : G.Adj left right := G.mem_edgeSet.mp hedge
        let dart : G.Dart := ⟨(left, right), hadj⟩
        have hfree :=
          (GoertzelV24RotationEdgeBridge.edgeBridgeFree_toRotationSystem_iff
            rotation).1 minimal.edgeBridgeFree dart
        simpa [dart, SimpleGraph.Dart.edge] using hfree
  have htwo : G.IsEdgeConnected 2 :=
    isEdgeConnected_two_of_connected_no_bridges
      hgraphConnected hnoBridge
  let connected : RootedBranchDecomposition (G := G) :=
    Classical.choose (connectedize htwo w decomposition hwidth)
  have hconnectedSpec :
      connected.Connected ∧ connected.WidthAtMost w :=
    Classical.choose_spec (connectedize htwo w decomposition hwidth)
  have hconnected : connected.Connected := hconnectedSpec.1
  have hconnectedWidth : connected.WidthAtMost w := hconnectedSpec.2
  exact connected.toConsumerAtWidth w hconnected hconnectedWidth

/-- M3 in its exact logical form: every graph-backed member of the cap-stable
spherical cubic class up to `bound` is Tait colourable.  A certificate
enumeration may prove this proposition, but enumeration is not built into
the statement. -/
def TaitBaseVerifiedAt (bound : Nat) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (rotation : Data G),
    BridgelessSphericalCubicMapData rotation.toRotationSystem →
    Fintype.card V ≤ bound →
    RotationSystemTaitColorable rotation.toRotationSystem

/-- The checked decomposition bound and the bounded base exclude every
graph-backed vertex-minimal Tait counterexample. -/
theorem noGraphBackedVertexMinimalTaitCounterexample_of_supply_and_base
    (k w : Nat)
    (supply : ConnectedDecompositionSupply.{u} k w)
    (base : TaitBaseVerifiedAt.{u} (rawVertexBound k w)) :
    NoGraphBackedVertexMinimalTaitCounterexample.{u} := by
  intro V _ _ G _ rotation minimal
  have hbound : Fintype.card V ≤ rawVertexBound k w := by
    simpa [rawVertexBound] using
      vertexCount_le_of_rootedConnectedBranchDecomposition
        rotation minimal k w (supply rotation minimal)
  exact minimal.notColorable
    (base rotation minimal.toBridgelessSphericalCubicMapData hbound)

/-- **Sound connected-spherical headline.**  M1 plus the route-native finite
base imply the genuine connected spherical Four-Colour statement. -/
theorem connectedSphericalFourColorStatement_of_supply_and_base
    (k w : Nat)
    (supply : ConnectedDecompositionSupply.{u} k w)
    (base : TaitBaseVerifiedAt.{u} (rawVertexBound k w)) :
    GoertzelV24SphericalGraphPresentation.ConnectedSphericalFourColorStatement.{u} :=
  connectedSphericalFourColorStatement_of_no_minimal
    (noGraphBackedVertexMinimalTaitCounterexample_of_supply_and_base
      k w supply base)

/-- **Sound componentwise spherical headline.**  This is the endpoint of the
formal compositional route before the separate classical representation
theorem from an abstract planar graph to a spherical rotation presentation. -/
theorem sphericalFourColorStatement_of_supply_and_base
    (k w : Nat)
    (supply : ConnectedDecompositionSupply.{u} k w)
    (base : TaitBaseVerifiedAt.{u} (rawVertexBound k w)) :
    GoertzelV24SphericalGraphPresentation.SphericalFourColorStatement.{u} :=
  sphericalFourColorStatement_of_no_minimal
    (noGraphBackedVertexMinimalTaitCounterexample_of_supply_and_base
      k w supply base)

/-- **Combinatorial Four-Colour headline.**  M1 plus the route-native finite
base imply four-colourability of every finite simple graph equipped
componentwise with a cellular spherical rotation presentation. -/
theorem combinatorialFourColorStatement_of_supply_and_base
    (k w : Nat)
    (supply : ConnectedDecompositionSupply.{u} k w)
    (base : TaitBaseVerifiedAt.{u} (rawVertexBound k w)) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  (GoertzelV24SphericalGraphPresentation.combinatorialFourColorStatement_iff_spherical.{u}).2
    (sphericalFourColorStatement_of_supply_and_base k w supply base)

/-- **Combinatorial headline with M1 factored at its real boundary.**  The
raw bounded-width decomposition, the generic width-preserving connectedizer,
and the route-native finite base imply the combinatorial Four-Colour
statement.  In particular, the connectedizer is not conflated with the open
wall-exclusion/branchwidth input. -/
theorem combinatorialFourColorStatement_of_raw_connectedization_and_base
    (w : Nat)
    (raw : RawBranchDecompositionSupply.{u} w)
    (connectedize : WidthPreservingConnectedization.{u})
    (base : TaitBaseVerifiedAt.{u} (rawVertexBound w w)) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  combinatorialFourColorStatement_of_supply_and_base w w
    (connectedDecompositionSupply_of_raw_and_connectedization
      w raw connectedize)
    base

end

end GoertzelV24SphericalReductiveAssembly

end Mettapedia.GraphTheory.FourColor
