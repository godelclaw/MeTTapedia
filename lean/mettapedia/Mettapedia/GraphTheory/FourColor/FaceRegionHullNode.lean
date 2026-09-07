import Mettapedia.GraphTheory.FourColor.FaceRegionHull
import Mettapedia.GraphTheory.FourColor.SphericalContourNodeChain

/-!
# Face-region hulls as exact Count nodes

A connected region in the actual face dual and a vertex-disjoint outside
face construct both cyclic connected shores. The complete original edge
boundary bounds the exposed ports and hence the incident-shore middle set.
The result uses the existing exact Count node, not a new notion of width.

No uniform bound or long sequence of such regions is assumed or concluded.
Those are the remaining geometric tasks in the mesh branch.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceRegionHull

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24OrbitFaceTwoSided GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24ConnectedShoreLiteralNode GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24CubicSmallBoundaryCycle GoertzelV24SimpleGraphTaitBridge
open GoertzelV24RotationCutDartDecomposition
open SphericalContourSeparators VertexSeparatorBond

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

noncomputable section

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- The node is constructed from face geometry, with width charged to the
complete edge boundary before filling. Neither shore connectivity nor a
middle-set bound is an input. -/
def toConnectedNode (data : Data G) (hc : data.toRotationSystem.IsCubic)
    (ht : OrbitFacesTwoSided data.toRotationSystem) (hG : G.Connected)
    {R : Set (OrbitFace data.toRotationSystem)}
    (hR : ((orbitFaceDualGraph data).induce R).Connected)
    {f : OrbitFace data.toRotationSystem}
    (hf : Disjoint (faceVertices data f) (closedVertices data R))
    {b : V} (hb : b ∈ faceVertices data f) :
    ConnectedShoreNode (G := G) (edgeBoundary G (closedVertices data R)).card
      (edgeBoundary G (closedVertices data R)).card := by
  classical
  have hRN : R.Nonempty := by
    obtain ⟨g⟩ := hR.nonempty
    exact ⟨g.val, g.property⟩
  have hbn : b ∉ closedVertices data R := Set.disjoint_left.mp hf hb
  have hconn := hull_connected_sides data hc ht hG hR hbn
  have hcycles := hull_hasCycles data hc ht hRN hf hb
  have hg := connected_edgeShores_and_nonempty_majoritySides_of_cycles
    (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic data hc)
    (· ∈ hull data R b) hconn.1 hconn.2 hcycles.1 hcycles.2
  have hwidth : (edgeShoreMiddleVertices G (incidentEdgeShore G (· ∈ hull data R b))).card ≤
      (edgeBoundary G (closedVertices data R)).card := by
    calc
      _ ≤ Fintype.card (CrossingSideDart G (· ∈ hull data R b)) :=
        card_middle_incidentEdgeShore_le_crossingSideDart _
      _ = Fintype.card (BoundaryDart data.toRotationSystem (· ∈ hull data R b)) :=
        Fintype.card_congr (crossingEquivBoundary data _)
      _ ≤ (edgeBoundary G (hull data R b)).card := card_boundaryDart_le_edgeBoundary data _
      _ ≤ _ := Finset.card_le_card (hull_boundary_subset data R b)
  exact ⟨incidentEdgeShore G (· ∈ hull data R b), hg.1, hg.2.1,
    hg.2.2.1, hg.2.2.2, hwidth, hwidth⟩

@[simp] theorem toConnectedNode_shore (data : Data G) (hc ht hG)
    {R : Set (OrbitFace data.toRotationSystem)}
    (hR : ((orbitFaceDualGraph data).induce R).Connected)
    {f : OrbitFace data.toRotationSystem}
    (hf : Disjoint (faceVertices data f) (closedVertices data R))
    {b : V} (hb : b ∈ faceVertices data f) :
    (toConnectedNode data hc ht hG hR hf hb).shore = incidentEdgeShore G (· ∈ hull data R b) := rfl

/-- The barrier cell and its connectedness are computed from the ambient
dual. Only a disjoint outside face and its anchor remain as terminal data. -/
def cellNode (data : Data G) (hc : data.toRotationSystem.IsCubic)
    (ht : OrbitFacesTwoSided data.toRotationSystem) (hG : G.Connected)
    (B : Finset G.edgeSet) (root : OrbitFace data.toRotationSystem)
    {f : OrbitFace data.toRotationSystem}
    (hf : Disjoint (faceVertices data f) (closedVertices data (cell data B root)))
    {b : V} (hb : b ∈ faceVertices data f) :
    ConnectedShoreNode (G := G) (edgeBoundary G (closedVertices data (cell data B root))).card
      (edgeBoundary G (closedVertices data (cell data B root))).card :=
  toConnectedNode data hc ht hG (cell_dual_connected data B root) hf hb

end
end Mettapedia.GraphTheory.FourColor.FaceRegionHull
