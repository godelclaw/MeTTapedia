import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComponentProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationCutDartDecomposition

/-!
# Concrete splice boundary from paired annular crosscuts

The source splice operates on two simple, equal-width transversals.  This
file connects those actual source objects to the retained-side boundary
interface used by the rotation-system splice.  In particular, the retained
side, every outward boundary dart, its full coverage, and the two-cut
partition are constructed from the paired dual loop; none is an ambient
assumption.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteEdgeDeletion
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The ordered image of a simple dual crosscut is exactly its finite primal
crossing support.  This keeps the source's transversal order while exposing
the ordinary `Finset` needed by the splice implementation. -/
theorem orderedCut_crossingEdge_eq_crossingEdges
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))) :
    orderedCut (crosscut.crossingEdge hunique) = crosscut.crossingEdges hunique := by
  ext edge
  constructor
  · intro hmem
    change edge ∈ Finset.univ.image (crosscut.crossingEdge hunique) at hmem
    rcases Finset.mem_image.1 hmem with ⟨step, _, hstep⟩
    exact (crosscut.mem_crossingEdges_iff hunique edge).2 ⟨step, hstep⟩
  · intro hmem
    rcases (crosscut.mem_crossingEdges_iff hunique edge).1 hmem with
      ⟨step, hstep⟩
    change edge ∈ Finset.univ.image (crosscut.crossingEdge hunique)
    exact Finset.mem_image.2 ⟨step, Finset.mem_univ _, hstep⟩

/-- An exposed retained dart is an actual crossing edge of its finite vertex
side.  This is the small rotation-system bridge needed to prove that the two
source crosscuts cover every boundary port of the selected component. -/
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

/-- The complete, source-derived boundary data of the paired annular
transversals.  It intentionally records only geometry: the later semantic
profile layer must still prove its own preservation claims against this real
boundary rather than acquire them from this package. -/
structure SourceCrosscutBoundaryData
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) where
  component : (G.deleteEdges
    (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent
  component_boundary : componentCrossingEdges (pair.primalCutEdges data)
    component = pair.primalCutEdges data
  outer_kept : data.toRotationSystem.vertOf data.toRotationSystem.outer ∈
    pair.componentSide component
  removed : V
  removed_not_kept : removed ∉ pair.componentSide component
  leftCrosses : ∀ step, ∃ dart : data.toRotationSystem.D,
    data.toRotationSystem.edgeOf dart = pair.left.crossingEdge hunique step ∧
    data.toRotationSystem.vertOf dart ∈ pair.componentSide component ∧
    data.toRotationSystem.vertOf (data.toRotationSystem.alpha dart) ∉
      pair.componentSide component
  rightCrosses : ∀ step, ∃ dart : data.toRotationSystem.D,
    data.toRotationSystem.edgeOf dart = pair.right.crossingEdge hunique step ∧
    data.toRotationSystem.vertOf dart ∈ pair.componentSide component ∧
    data.toRotationSystem.vertOf (data.toRotationSystem.alpha dart) ∉
      pair.componentSide component
  leftInjective : Function.Injective (pair.left.crossingEdge hunique)
  rightInjective : Function.Injective (pair.right.crossingEdge hunique)
  cover : ∀ boundary : BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide component),
    data.toRotationSystem.edgeOf boundary.1.1 ∈
        orderedCut (pair.left.crossingEdge hunique) ∨
      data.toRotationSystem.edgeOf boundary.1.1 ∈
        orderedCut (pair.right.crossingEdge hunique)
  disjoint : Disjoint (orderedCut (pair.left.crossingEdge hunique))
    (orderedCut (pair.right.crossingEdge hunique))

/-- The paired simple source transversals construct all geometric boundary
fields required by the splice.  The proof selects the outer deletion
component, obtains every port orientation from its exact boundary, and then
uses the dual-loop decomposition to establish coverage and disjointness. -/
theorem exists_sourceCrosscutBoundaryData
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    Nonempty (SourceCrosscutBoundaryData data pair) := by
  rcases pair.exists_outer_primalCutComponent_exactBoundary_and_removed data
      htwoSided hdual hconnected hsphere with
    ⟨component, removed, houter, hremoved, hboundary⟩
  exact ⟨{
    component := component
    component_boundary := hboundary
    outer_kept := (pair.mem_componentSide_iff component
      (data.toRotationSystem.vertOf data.toRotationSystem.outer)).2 houter
    removed := removed
    removed_not_kept := by
      intro hkept
      exact hremoved ((pair.mem_componentSide_iff component removed).1 hkept)
    leftCrosses := by
      intro step
      apply pair.exists_oriented_componentSide_crossingDart data component hboundary
      rw [pair.primalCutEdges_eq_sourceCrossingSupport data]
      exact Finset.mem_union_left _
        ((pair.left.mem_crossingEdges_iff hunique _).2 ⟨step, rfl⟩)
    rightCrosses := by
      intro step
      apply pair.exists_oriented_componentSide_crossingDart data component hboundary
      rw [pair.primalCutEdges_eq_sourceCrossingSupport data]
      exact Finset.mem_union_right _
        ((pair.right.mem_crossingEdges_iff hunique _).2 ⟨step, rfl⟩)
    leftInjective := pair.left.crossingEdge_injective
      (orbitFace_incidence_le_two data.toRotationSystem) hunique
    rightInjective := pair.right.crossingEdge_injective
      (orbitFace_incidence_le_two data.toRotationSystem) hunique
    cover := by
      intro exposed
      have hcut : data.toRotationSystem.edgeOf exposed.1.1 ∈
          pair.primalCutEdges data := by
        rw [← pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
          data component hboundary]
        exact boundaryDart_edge_mem_vertexSetCrossingEdges
          data.toRotationSystem (pair.componentSide component) exposed
      rw [pair.primalCutEdges_eq_sourceCrossingSupport data] at hcut
      rcases Finset.mem_union.1 hcut with hleft | hright
      · left
        rw [orderedCut_crossingEdge_eq_crossingEdges pair.left hunique]
        exact hleft
      · right
        rw [orderedCut_crossingEdge_eq_crossingEdges pair.right hunique]
        exact hright
    disjoint := by
      rw [orderedCut_crossingEdge_eq_crossingEdges pair.left hunique,
        orderedCut_crossingEdge_eq_crossingEdges pair.right hunique]
      exact pair.crossing_disjoint
    }⟩

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
