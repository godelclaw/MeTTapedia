import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualPathTransversalDeletionComponent
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationCutDartDecomposition
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationVertexCutProfile

/-!
# Ordered splice boundary from a selected transversal pair

This is the selected-edge replacement for the historical annular-crosscut
boundary package.  Its component, retained vertex side, ordered ports, and
port orientations are constructed from the exact deletion boundary.  The
crossed edge at each source step is the literal selected edge carried by that
step; no global face-intersection uniqueness is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SelectedDualPathTransversal

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SelectedDualCycleSeparator
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SeparatedAlignedSelectedDualTransversals

local instance selectedSpliceBoundaryEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The finite vertex side of a constructed deletion component. -/
noncomputable def componentSide
    {data : Data G}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent) :
    Finset V := by
  classical
  exact Finset.univ.filter fun vertex => vertex ∈ component.supp

@[simp] theorem mem_componentSide_iff
    {data : Data G}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent)
    (vertex : V) :
    vertex ∈ pair.componentSide component ↔ vertex ∈ component.supp := by
  simp [componentSide]

/-- The ordered image of a selected transversal is exactly its finite
selected crossing support. -/
theorem orderedCut_crossingEdge_eq_crossingEdges
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (transversal : SelectedDualPathTransversal
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish) :
    orderedCut transversal.crossingEdge = transversal.crossingEdges := by
  ext edge
  simp [orderedCut, SelectedDualPathTransversal.mem_crossingEdges_iff]

/-- Exact deletion boundary equality transported to the rotation-system
vertex-side crossing carrier. -/
theorem vertexSetCrossingEdges_componentSide_eq_primalCutEdges
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent)
    (hboundary : componentCrossingEdges (pair.primalCutEdges data) component =
      pair.primalCutEdges data) :
    vertexSetCrossingEdges data.toRotationSystem
      (pair.componentSide component) = pair.primalCutEdges data := by
  ext edge
  calc
    edge ∈ vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide component) ↔
        EdgeCrossesVertexSide G
          (fun vertex => vertex ∈ pair.componentSide component) edge :=
      mem_simpleGraph_vertexSetCrossingEdges_iff
        data (pair.componentSide component) edge
    _ ↔ EdgeCrossesVertexSide G
          (fun vertex => vertex ∈ component.supp) edge := by
      simp only [pair.mem_componentSide_iff]
    _ ↔ edge ∈ componentCrossingEdges
          (pair.primalCutEdges data) component :=
      (mem_componentCrossingEdges_iff
        (pair.primalCutEdges data) component edge).symm
    _ ↔ edge ∈ pair.primalCutEdges data := by rw [hboundary]

/-- Every exact-boundary edge has a dart oriented out of the retained
component. -/
theorem exists_oriented_componentSide_crossingDart
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent)
    (hboundary : componentCrossingEdges (pair.primalCutEdges data) component =
      pair.primalCutEdges data)
    (edge : G.edgeSet) (hedge : edge ∈ pair.primalCutEdges data) :
    ∃ dart : data.toRotationSystem.D,
      data.toRotationSystem.edgeOf dart = edge ∧
      data.toRotationSystem.vertOf dart ∈ pair.componentSide component ∧
      data.toRotationSystem.vertOf (data.toRotationSystem.alpha dart) ∉
        pair.componentSide component := by
  have hcross : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ pair.componentSide component) edge := by
    apply (mem_simpleGraph_vertexSetCrossingEdges_iff data
      (pair.componentSide component) edge).1
    rw [pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
      data component hboundary]
    exact hedge
  rcases hcross with ⟨inside, outside, hinsideEdge, houtsideEdge,
    hinside, houtside⟩
  have hne : inside ≠ outside := by
    intro heq
    exact houtside (heq ▸ hinside)
  have hedgeValue : edge.1 = s(inside, outside) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hinsideEdge houtsideEdge hne
  have hadj : G.Adj inside outside := by
    rw [← SimpleGraph.mem_edgeSet, ← hedgeValue]
    exact edge.property
  let dart : G.Dart := ⟨(inside, outside), hadj⟩
  refine ⟨dart, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simpa [dart] using hedgeValue.symm
  · simpa [dart] using hinside
  · simpa [dart] using houtside

/-- An exposed retained dart is an edge of the corresponding finite vertex
boundary. -/
theorem boundaryDart_edge_mem_vertexSetCrossingEdges
    (RS : RotationSystem V G.edgeSet) (side : Finset V)
    (boundary : BoundaryDart RS (fun vertex => vertex ∈ side)) :
    RS.edgeOf boundary.1.1 ∈ vertexSetCrossingEdges RS side := by
  rw [mem_vertexSetCrossingEdges_iff]
  refine ⟨RS.vertOf boundary.1.1, ?_, boundary.1.2,
    RS.vertOf (RS.alpha boundary.1.1), ?_, boundary.2⟩
  · rw [RS.mem_endpoints_iff]
    exact ⟨boundary.1.1, by simp, rfl⟩
  · rw [RS.mem_endpoints_iff]
    refine ⟨RS.alpha boundary.1.1, ?_, rfl⟩
    rw [RS.mem_dartsOn]
    exact RS.edge_alpha boundary.1.1

/-- A vertex separated from another vertex in a connected graph carries a
literal graph dart. -/
theorem exists_dartAt_of_connected_of_ne
    (data : Data G) (hconnected : G.Connected) {vertex other : V}
    (hne : vertex ≠ other) :
    ∃ dart : data.toRotationSystem.D,
      data.toRotationSystem.vertOf dart = vertex := by
  rcases (hconnected vertex other).nonempty_neighborSet_left hne with
    ⟨neighbor, hadjacent⟩
  exact ⟨⟨(vertex, neighbor), hadjacent⟩, rfl⟩

/-- Complete geometry for the ordered selected boundary used by the splice
and Count-profile layers. -/
structure SourceSelectedBoundaryData
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish) where
  component : (G.deleteEdges
    (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent
  component_boundary : componentCrossingEdges (pair.primalCutEdges data)
    component = pair.primalCutEdges data
  outer_kept : data.toRotationSystem.vertOf data.toRotationSystem.outer ∈
    pair.componentSide component
  removed : V
  removed_not_kept : removed ∉ pair.componentSide component
  removedDart : data.toRotationSystem.D
  removedDart_vertOf : data.toRotationSystem.vertOf removedDart = removed
  leftCrosses : ∀ step, ∃ dart : data.toRotationSystem.D,
    data.toRotationSystem.edgeOf dart = pair.left.crossingEdge step ∧
    data.toRotationSystem.vertOf dart ∈ pair.componentSide component ∧
    data.toRotationSystem.vertOf (data.toRotationSystem.alpha dart) ∉
      pair.componentSide component
  rightCrosses : ∀ step, ∃ dart : data.toRotationSystem.D,
    data.toRotationSystem.edgeOf dart = pair.right.crossingEdge step ∧
    data.toRotationSystem.vertOf dart ∈ pair.componentSide component ∧
    data.toRotationSystem.vertOf (data.toRotationSystem.alpha dart) ∉
      pair.componentSide component
  leftInjective : Function.Injective pair.left.crossingEdge
  rightInjective : Function.Injective pair.right.crossingEdge
  cover : ∀ boundary : BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide component),
    data.toRotationSystem.edgeOf boundary.1.1 ∈
        orderedCut pair.left.crossingEdge ∨
      data.toRotationSystem.edgeOf boundary.1.1 ∈
        orderedCut pair.right.crossingEdge
  disjoint : Disjoint (orderedCut pair.left.crossingEdge)
    (orderedCut pair.right.crossingEdge)

/-- The selected pair constructs every field of its ordered splice boundary
from the graph and its locally two-sided dual loop. -/
theorem exists_sourceSelectedBoundaryData_of_euler
    (data : Data G)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (hsupportTwoSided : ∀ face,
      face ∈ pair.selectedDualCycle.walk.support → ∀ dart,
        dartOrbitFace data.toRotationSystem dart = face.1 →
          dartOrbitFace data.toRotationSystem dart ≠
            dartOrbitFace data.toRotationSystem
              (data.toRotationSystem.alpha dart)) :
    Nonempty (SourceSelectedBoundaryData data pair) := by
  rcases pair.exists_outer_primalCutComponent_exactBoundary_and_removed_of_euler
      data hdual hconnected heuler hsupportTwoSided with
    ⟨component, removed, houter, hremoved, hboundary⟩
  have hremovedNeOuter :
      removed ≠ data.toRotationSystem.vertOf data.toRotationSystem.outer := by
    intro heq
    exact hremoved (heq ▸ houter)
  let removedDart := Classical.choose
    (exists_dartAt_of_connected_of_ne data hconnected hremovedNeOuter)
  have hremovedDart : data.toRotationSystem.vertOf removedDart = removed :=
    Classical.choose_spec
      (exists_dartAt_of_connected_of_ne data hconnected hremovedNeOuter)
  exact ⟨{
    component := component
    component_boundary := hboundary
    outer_kept := (pair.mem_componentSide_iff component _).2 houter
    removed := removed
    removed_not_kept := by
      intro hkept
      exact hremoved ((pair.mem_componentSide_iff component removed).1 hkept)
    removedDart := removedDart
    removedDart_vertOf := hremovedDart
    leftCrosses := by
      intro step
      apply pair.exists_oriented_componentSide_crossingDart
        data component hboundary
      exact Finset.mem_union_left _
        ((pair.left.mem_crossingEdges_iff _).2 ⟨step, rfl⟩)
    rightCrosses := by
      intro step
      apply pair.exists_oriented_componentSide_crossingDart
        data component hboundary
      exact Finset.mem_union_right _
        ((pair.right.mem_crossingEdges_iff _).2 ⟨step, rfl⟩)
    leftInjective := pair.left.crossingEdge_injective
      (orbitFace_incidence_le_two data.toRotationSystem)
    rightInjective := pair.right.crossingEdge_injective
      (orbitFace_incidence_le_two data.toRotationSystem)
    cover := by
      intro exposed
      have hcut : data.toRotationSystem.edgeOf exposed.1.1 ∈
          pair.primalCutEdges data := by
        rw [← pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
          data component hboundary]
        exact boundaryDart_edge_mem_vertexSetCrossingEdges
          data.toRotationSystem (pair.componentSide component) exposed
      rcases Finset.mem_union.1 hcut with hleft | hright
      · left
        rw [orderedCut_crossingEdge_eq_crossingEdges pair.left]
        exact hleft
      · right
        rw [orderedCut_crossingEdge_eq_crossingEdges pair.right]
        exact hright
    disjoint := by
      rw [orderedCut_crossingEdge_eq_crossingEdges pair.left,
        orderedCut_crossingEdge_eq_crossingEdges pair.right]
      exact pair.crossing_disjoint
    }⟩

end SeparatedAlignedSelectedDualTransversals

end

end GoertzelV24SelectedDualPathTransversal

end Mettapedia.GraphTheory.FourColor
