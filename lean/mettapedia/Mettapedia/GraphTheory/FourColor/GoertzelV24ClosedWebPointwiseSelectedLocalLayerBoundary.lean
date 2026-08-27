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
open GoertzelV24FramedAnnularExcess
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
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

end Formation.LocalLayerPair

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
