import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedLocalLayerPair
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebInteriorFaceGeometry
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedAnnularFaceParityCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualPathTransversalSpliceBoundary

/-!
# Exact ordered boundary of a colouring-free literal Cell layer

The two pointwise-selected source rails visit only annular-interior faces.
Their closed selected cycle therefore satisfies the local two-sidedness
premise of the selected bond, and hence constructs the complete ordered
splice boundary without a colouring or global face-intersection uniqueness.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FramedAnnularExcess
open GoertzelV24FramedLocalDualCycleBond
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24SelectedDualCycleBond
open GoertzelV24SelectedDualPathTransversal
open GoertzelV24SelectedDualPathTransversal.SeparatedAlignedSelectedDualTransversals
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace Formation.LocalLayerPair

/-- Every face visited by the closed selected Cell loop is an annular-interior
face. -/
theorem pointwiseSelectedLocalLayerPair_walk_support_internal
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (face : AmbientFace
      (Finset.univ : Finset (OrbitFace formation.annular.RS)))
    (hface : face ∈
      (layers.pointwiseSelectedLocalLayerPair hinterior).selectedDualCycle.walk.support) :
    face.1 ∈ formation.annular.cellulation.interiorFaces := by
  change face ∈ (layers.firstWalk.append layers.secondWalk.reverse).support at hface
  rw [SimpleGraph.Walk.support_append,
    SimpleGraph.Walk.support_reverse] at hface
  rcases List.mem_append.1 hface with hfirst | hsecond
  · rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hfirst with
      ⟨index, hindex, hle⟩
    have hinternal := layers.firstWalk_getVert_internal
      ⟨index, by omega⟩
    rw [hindex] at hinternal
    exact hinternal
  · have hsecond' : face ∈ layers.secondWalk.support := by
      have : face ∈ layers.secondWalk.support.reverse :=
        List.mem_of_mem_tail hsecond
      simpa using this
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hsecond' with
      ⟨index, hindex, hle⟩
    have hinternal := layers.secondWalk_getVert_internal
      ⟨index, by omega⟩
    rw [hindex] at hinternal
    exact hinternal

/-- Local interior-face geometry supplies exactly the two-sidedness premise
required by the selected-cycle bond. -/
theorem pointwiseSelectedLocalLayerPair_supportTwoSided
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    ∀ face,
      face ∈ (layers.pointwiseSelectedLocalLayerPair hinterior).selectedDualCycle.walk.support →
      ∀ dart,
        dartOrbitFace formation.annular.RS dart = face.1 →
          dartOrbitFace formation.annular.RS dart ≠
            dartOrbitFace formation.annular.RS
              (formation.annular.RS.alpha dart) := by
  intro face hface dart hdart
  apply Formation.InteriorFace.dartOrbitFace_ne_alpha formation dart
  rw [hdart]
  exact layers.pointwiseSelectedLocalLayerPair_walk_support_internal
    hinterior face hface

/-- A colouring-free literal Cell constructs its full selected ordered
boundary.  This is the source-facing discharge of the selected separator,
bond, and port-orientation stack. -/
theorem exists_pointwiseSelectedSourceBoundaryData
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    Nonempty
      (SourceSelectedBoundaryData formation.annular.cellulation.rotation
        (layers.pointwiseSelectedLocalLayerPair hinterior)) := by
  apply exists_sourceSelectedBoundaryData_of_euler
    formation.annular.cellulation.rotation
  · exact formation.annular.cellulation.fullOrbitFaceInteriorDual_connected
  · exact formation.annular.cellulation.connected
  · exact formation.annular.cellulation.euler
  · exact layers.pointwiseSelectedLocalLayerPair_supportTwoSided hinterior

/-- The literal selected Cell boundary avoids the inner pentagonal cap.  The
selected primal edges are used directly, so no global shared-edge choice is
hidden in this statement. -/
theorem pointwiseSelectedLocalLayerPair_primalCutEdges_disjoint_innerHoleBoundary
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    Disjoint
      ((layers.pointwiseSelectedLocalLayerPair hinterior).primalCutEdges
        formation.annular.cellulation.rotation)
      (orbitFaceBoundary formation.annular.RS
        formation.annular.cellulation.innerHole) := by
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  rw [← pair.selectedDualCycle_crossingEdges_eq_primalCutEdges
    formation.annular.cellulation.rotation]
  exact pair.selectedDualCycle.crossingEdges_disjoint_faceBoundary_of_support
    formation.annular.cellulation.interiorFaces
    (layers.pointwiseSelectedLocalLayerPair_walk_support_internal hinterior)
    formation.annular.cellulation.innerHole
    (by
      simp [FramedAnnularCellulation.interiorFaces,
        FramedAnnularCellulation.holeFaces])

/-- The same literal boundary avoids the outer pentagonal cap. -/
theorem pointwiseSelectedLocalLayerPair_primalCutEdges_disjoint_outerHoleBoundary
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext) :
    Disjoint
      ((layers.pointwiseSelectedLocalLayerPair hinterior).primalCutEdges
        formation.annular.cellulation.rotation)
      (orbitFaceBoundary formation.annular.RS
        formation.annular.cellulation.outerHole) := by
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  rw [← pair.selectedDualCycle_crossingEdges_eq_primalCutEdges
    formation.annular.cellulation.rotation]
  exact pair.selectedDualCycle.crossingEdges_disjoint_faceBoundary_of_support
    formation.annular.cellulation.interiorFaces
    (layers.pointwiseSelectedLocalLayerPair_walk_support_internal hinterior)
    formation.annular.cellulation.outerHole
    (by
      simp [FramedAnnularCellulation.interiorFaces,
        FramedAnnularCellulation.holeFaces])

/-- Every component of the selected Cell-edge deletion sees the entire
four-edge selected boundary.  This is the exact two-side input needed by the
finite deletion complement theorem.  It uses only local two-sidedness on the
selected dual loop. -/
theorem pointwiseSelectedLocalLayerPair_component_boundary_saturation
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (boundary : SourceSelectedBoundaryData
      formation.annular.cellulation.rotation
      (layers.pointwiseSelectedLocalLayerPair hinterior))
    (other : (G.deleteEdges (edgeFinsetValueSet
      ((layers.pointwiseSelectedLocalLayerPair hinterior).primalCutEdges
        formation.annular.cellulation.rotation))).ConnectedComponent) :
    componentCrossingEdges
        ((layers.pointwiseSelectedLocalLayerPair hinterior).primalCutEdges
          formation.annular.cellulation.rotation) other =
      (layers.pointwiseSelectedLocalLayerPair hinterior).primalCutEdges
        formation.annular.cellulation.rotation := by
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let rotationData := formation.annular.cellulation.rotation
  by_cases hother : other = boundary.component
  · simpa [pair, rotationData, hother] using
      boundary.component_boundary
  · have hnonempty :
        (componentCrossingEdges (pair.primalCutEdges rotationData) other).Nonempty :=
      componentCrossingEdges_nonempty_of_distinct formation.connected
        (pair.primalCutEdges rotationData) other boundary.component hother
    let side : V → Prop := fun vertex => vertex ∈ other.supp
    have hlocal :
        componentCrossingEdges (pair.primalCutEdges rotationData) other =
          localCrossingEdgeFinset G side := by
      exact pair.componentCrossingEdges_eq_localCrossingEdgeFinset
        rotationData other
    have hsubset : localCrossingEdgeFinset G side ⊆
        pair.selectedDualCycle.crossingEdges := by
      rw [← hlocal,
        pair.selectedDualCycle_crossingEdges_eq_primalCutEdges rotationData]
      exact componentCrossingEdges_subset_removed
        (pair.primalCutEdges rotationData) other
    have hlocalNonempty : (localCrossingEdgeFinset G side).Nonempty := by
      rw [← hlocal]
      exact hnonempty
    have hsaturated :=
      crossingEdgeFinset_eq_crossingEdges_of_isCycle_of_subset_of_supportTwoSided
        rotationData pair.selectedDualCycle side hsubset hlocalNonempty
          (layers.pointwiseSelectedLocalLayerPair_supportTwoSided hinterior)
    calc
      componentCrossingEdges (pair.primalCutEdges rotationData) other =
          localCrossingEdgeFinset G side := hlocal
      _ = pair.selectedDualCycle.crossingEdges := hsaturated
      _ = pair.primalCutEdges rotationData :=
        pair.selectedDualCycle_crossingEdges_eq_primalCutEdges rotationData

/-- The literal selected Cell side opposite the retained component is
connected.  In particular, the selected dual loop has exactly two primal
sides; this conclusion does not use the historical global shared-edge
uniqueness receipt. -/
theorem pointwiseSelectedLocalLayerPair_complement_connected
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (boundary : SourceSelectedBoundaryData
      formation.annular.cellulation.rotation
      (layers.pointwiseSelectedLocalLayerPair hinterior)) :
    (G.induce (fun vertex => vertex ∉ boundary.component.supp)).Connected := by
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let rotationData := formation.annular.cellulation.rotation
  have hcard : (pair.primalCutEdges rotationData).card = 4 := by
    change pair.crossingSupport.card = 4
    rw [pair.card_crossingSupport
      (orbitFace_incidence_le_two formation.annular.RS)]
    norm_num [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
      Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
      Formation.LocalLayerPair.firstLayer,
      Formation.LocalLayerPair.secondLayer,
      Formation.LocalLayerPair.firstWalk,
      Formation.LocalLayerPair.secondWalk]
  apply induce_complement_connected_of_component_boundary_saturation
    (removed := pair.primalCutEdges rotationData) boundary.component
  · exact Finset.card_pos.mp (by omega)
  · intro other
    exact layers.pointwiseSelectedLocalLayerPair_component_boundary_saturation
      hinterior boundary other

end Formation.LocalLayerPair

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
