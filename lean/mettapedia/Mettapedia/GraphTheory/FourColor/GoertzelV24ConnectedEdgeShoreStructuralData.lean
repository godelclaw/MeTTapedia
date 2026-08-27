import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedEdgeShoreMajority
import Mettapedia.GraphTheory.FourColor.GoertzelV24ComplementaryShoreBoundaryOrder

/-!
# Structural seam data from a connected edge shore

The branch-decomposition supplier speaks about edge shores.  The physical
splice consumes complementary connected vertex shores.  In a cubic graph the
majority construction converts the former to the latter without increasing
the interface width.

This file feeds that conversion directly into the canonical planar-bond seam
constructor.  The result is the complete bridgeless spherical cubic map data
for the literal composite.  Existence of a connected branch decomposition and
the target-specific Count replacement are deliberately outside this module.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ConnectedEdgeShoreStructuralData

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24RotationSpliceConstructor
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24VertexSideOpenTangle

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Delete exactly the vertices which do not follow the majority of the
chosen edge shore. -/
def majorityDeletedVertices (G : SimpleGraph V) [Fintype G.edgeSet]
    (shore : Finset G.edgeSet) : Finset V := by
  classical
  exact Finset.univ.filter fun vertex =>
    ¬ majorityVertexSide G shore vertex

/-- The retained predicate arising from `majorityDeletedVertices`. -/
abbrev majorityRetainedKeep (G : SimpleGraph V) [Fintype G.edgeSet]
    (shore : Finset G.edgeSet) : V → Prop :=
  deletedRegionKeep (majorityDeletedVertices G shore)

/-- The complementary deleted-side predicate. -/
abbrev majorityDeletedKeep (G : SimpleGraph V) [Fintype G.edgeSet]
    (shore : Finset G.edgeSet) : V → Prop :=
  deletedSideKeep (majorityDeletedVertices G shore)

omit [G.LocallyFinite] in
@[simp]
theorem majorityRetainedKeep_iff (shore : Finset G.edgeSet) (vertex : V) :
    majorityRetainedKeep G shore vertex ↔
      majorityVertexSide G shore vertex := by
  simp [majorityRetainedKeep, majorityDeletedVertices,
    deletedRegionKeep]

omit [G.LocallyFinite] in
@[simp]
theorem majorityDeletedKeep_iff (shore : Finset G.edgeSet) (vertex : V) :
    majorityDeletedKeep G shore vertex ↔
      ¬ majorityVertexSide G shore vertex := by
  simp [majorityDeletedKeep, deletedSideKeep,
    majorityRetainedKeep_iff]

/-- Connected complementary edge shores canonically supply the complete D3
structural package on their majority vertex shores.  All cap orders, cap Euler
equalities, and seam orientation facts are consequences of the ambient
spherical planar bond; they are not caller-supplied choices. -/
def bridgelessSphericalCubicMapData_of_majorityEdgeShore
    (rotation : SimpleGraphDartRotation.Data G)
    (shore : Finset G.edgeSet)
    (hshoreConnected : EdgeShoreConnected G shore)
    (hcomplementConnected :
      EdgeShoreConnected G (Finset.univ \ shore))
    (hmajorityNonempty :
      ∃ vertex, majorityVertexSide G shore vertex)
    (hcomplementNonempty :
      ∃ vertex, ¬ majorityVertexSide G shore vertex)
    (outerRetained : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G shore))
    (outerDeleted : RetainedDart rotation.toRotationSystem
      (majorityDeletedKeep G shore))
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hbridgeless :
      (toMultigraph rotation.toRotationSystem).Bridgeless)
    (first second : BoundaryDart rotation.toRotationSystem
      (majorityRetainedKeep G shore))
    (hne : first ≠ second) :
    BridgelessSphericalCubicMapData
      ((ofVertexSide rotation.toRotationSystem
          (majorityRetainedKeep G shore) outerRetained).composeRotationSystem
        (ofVertexSide rotation.toRotationSystem
          (majorityDeletedKeep G shore) outerDeleted)
        (complementBoundaryAlphaEquiv rotation.toRotationSystem
          (majorityDeletedVertices G shore))) := by
  have hcubicEdges :
      ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      rotation hsphere.cubic
  have hshores := connected_majority_shores_and_width
    hcubicEdges shore hshoreConnected hcomplementConnected
      hmajorityNonempty hcomplementNonempty
  have hretainedConnected :
      (G.induce {vertex | majorityRetainedKeep G shore vertex}).Connected := by
    have hset :
        {vertex | majorityRetainedKeep G shore vertex} =
          {vertex | majorityVertexSide G shore vertex} := by
      ext vertex
      exact majorityRetainedKeep_iff shore vertex
    rw [hset]
    exact hshores.1
  have hdeletedConnected :
      (G.induce {vertex | majorityDeletedKeep G shore vertex}).Connected := by
    have hset :
        {vertex | majorityDeletedKeep G shore vertex} =
          {vertex | ¬ majorityVertexSide G shore vertex} := by
      ext vertex
      exact majorityDeletedKeep_iff shore vertex
    rw [hset]
    exact hshores.2.1
  exact bridgelessSphericalCubicMapData_of_planarBond_canonical
    rotation (majorityDeletedVertices G shore)
      outerRetained outerDeleted hsphere htwoSided hconnected hrotation
      hretainedConnected hdeletedConnected hbridgeless first second hne

end

end GoertzelV24ConnectedEdgeShoreStructuralData

end Mettapedia.GraphTheory.FourColor
