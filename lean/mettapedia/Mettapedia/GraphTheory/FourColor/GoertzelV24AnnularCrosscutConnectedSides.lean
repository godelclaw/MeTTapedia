import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSpliceBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteDeletionCyclicCut

/-!
# Connected sides of a source annular crosscut

A paired simple dual crosscut gives an exact primal boundary for every
deletion component.  This module turns that saturation fact into the missing
two-side statement: the selected outer component and its complement are both
connected.  The argument is finite graph theory, not an added topological
assumption: one removed edge cannot cross three distinct saturated
components.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FaceOrbitIncidence
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FiniteEdgeDeletion
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SpliceUnification
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The selected component of a paired source crosscut remains connected in
the original graph.  Together with the complement result below, this gives
the two connected pieces required by the planar splice construction. -/
theorem SourceCrosscutBoundaryData.componentSide_connected
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    (G.induce (fun vertex => vertex ∈ pair.componentSide boundary.component)).Connected := by
  have hcomponent : (G.induce boundary.component.supp).Connected :=
    pair.connected_induce_primalCutComponent data boundary.component
  have hsideEq :
      (fun vertex => vertex ∈ pair.componentSide boundary.component) =
        boundary.component.supp := by
    funext vertex
    apply propext
    exact pair.mem_componentSide_iff boundary.component vertex
  rw [hsideEq]
  exact hcomponent

/-- The complement of the component selected by a paired source crosscut is
connected.  Exact boundary saturation propagates from the simple dual loop
to every deletion component; the generic finite-component lemma then gives
the genuine second side of the separator. -/
theorem SourceCrosscutBoundaryData.componentSide_complement_connected
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    (G.induce (fun vertex => vertex ∉ pair.componentSide boundary.component)).Connected := by
  let other : (G.deleteEdges
      (GoertzelV24FiniteEdgeDeletion.edgeFinsetValueSet
        (pair.primalCutEdges data))).ConnectedComponent :=
    (G.deleteEdges (GoertzelV24FiniteEdgeDeletion.edgeFinsetValueSet
      (pair.primalCutEdges data))).connectedComponentMk
      boundary.removed
  have hremovedOther : boundary.removed ∈ other.supp := by
    dsimp [other]
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hotherNe : other ≠ boundary.component := by
    intro heq
    apply boundary.removed_not_kept
    rw [pair.mem_componentSide_iff]
    exact heq ▸ hremovedOther
  have hcutNonempty : (pair.primalCutEdges data).Nonempty := by
    have hboundaryNonempty := pair.componentCrossingEdges_nonempty_of_distinct
      data hconnected boundary.component other hotherNe.symm
    rw [boundary.component_boundary] at hboundaryNonempty
    exact hboundaryNonempty
  have hsaturation : ∀ component :
      (G.deleteEdges
        (GoertzelV24FiniteEdgeDeletion.edgeFinsetValueSet
          (pair.primalCutEdges data))).ConnectedComponent,
      componentCrossingEdges (pair.primalCutEdges data) component =
        pair.primalCutEdges data := by
    intro component
    by_cases hcomponent : component = boundary.component
    · simpa [hcomponent] using boundary.component_boundary
    · exact pair.componentCrossingEdges_eq_primalCutEdges_of_distinct
        data htwoSided hconnected component boundary.component hcomponent
  have hcomplement :
      (G.induce (fun vertex => vertex ∉ boundary.component.supp)).Connected := by
    exact _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteDeletionCyclicCut.induce_complement_connected_of_component_boundary_saturation
      (G := G) (removed := pair.primalCutEdges data)
      boundary.component hcutNonempty hsaturation
  have hsideEq :
      (fun vertex => vertex ∉ pair.componentSide boundary.component) =
        (fun vertex => vertex ∉ boundary.component.supp) := by
    funext vertex
    apply propext
    simp only [pair.mem_componentSide_iff]
  rw [hsideEq]
  exact hcomplement

/-- The source crosscut removes precisely the finite complement of the
selected component side. -/
noncomputable def SourceCrosscutBoundaryData.deletedVertices
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) : Finset V :=
  (pair.componentSide boundary.component)ᶜ

/-- The generic deleted-region convention keeps exactly the component side
selected by the source crosscut. -/
theorem SourceCrosscutBoundaryData.deletedRegionKeep_eq_componentSide
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    deletedRegionKeep (boundary.deletedVertices data pair) =
      (fun vertex => vertex ∈ pair.componentSide boundary.component) := by
  funext vertex
  simp [SourceCrosscutBoundaryData.deletedVertices, deletedRegionKeep]

/-- With that deleted-region convention, the two source crossing lists are
the exact graph boundary of the region, not merely a cover of it. -/
theorem SourceCrosscutBoundaryData.orderedCut_boundary_eq
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    orderedCut (pair.left.crossingEdge hunique) ∪
        orderedCut (fun step : Fin pair.left.walk.length =>
          pair.right.crossingEdge hunique (Fin.cast pair.length_eq step)) =
      vertexSetCrossingEdges data.toRotationSystem
        (boundary.deletedVertices data pair) := by
  rw [SourceCrosscutBoundaryData.deletedVertices,
    vertexSetCrossingEdges_compl,
    pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
      data boundary.component boundary.component_boundary,
    pair.primalCutEdges_eq_sourceCrossingSupport data,
    orderedCut_crossingEdge_eq_crossingEdges pair.left hunique,
    pair.orderedCut_sourceCrosscutRight_eq data,
    orderedCut_crossingEdge_eq_crossingEdges pair.right hunique]

/-- The distinguished outer dart remains in the retained side of the source
crosscut deletion. -/
theorem SourceCrosscutBoundaryData.outer_not_mem_deletedVertices
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    data.toRotationSystem.vertOf data.toRotationSystem.outer ∉
      boundary.deletedVertices data pair := by
  simpa [SourceCrosscutBoundaryData.deletedVertices] using boundary.outer_kept

/-- Both graph sides needed by the planar-bond splice are now source-derived
facts about the paired simple crosscut. -/
theorem SourceCrosscutBoundaryData.deletedRegion_sides_connected
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    (G.induce {vertex |
        deletedRegionKeep (boundary.deletedVertices data pair) vertex}).Connected ∧
      (G.induce {vertex |
        Not (deletedRegionKeep (boundary.deletedVertices data pair) vertex)}).Connected := by
  constructor
  · have hside := SourceCrosscutBoundaryData.componentSide_connected
      data pair boundary
    rw [SourceCrosscutBoundaryData.deletedRegionKeep_eq_componentSide
      data pair boundary]
    exact hside
  · have hside := SourceCrosscutBoundaryData.componentSide_complement_connected
      data htwoSided hconnected pair boundary
    rw [SourceCrosscutBoundaryData.deletedRegionKeep_eq_componentSide
      data pair boundary]
    exact hside

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
