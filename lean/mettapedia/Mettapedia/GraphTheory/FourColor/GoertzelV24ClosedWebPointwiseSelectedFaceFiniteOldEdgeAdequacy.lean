import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceFinitePredecessorDisjoint
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphThreeFactorSelectedAnchor

/-!
# Adequacy of the finite old-prefix face support

The finite source-Cell decoder names only predecessor components meeting its
twenty-four-dart transition carrier.  This file proves the corresponding
coverage fact for literal old-prefix edges: whenever an old edge belongs to a
chosen outgoing face component, its old regional component has an anchor on
that carrier.

The proof is the source-specific instance of three-factor selected anchoring.
The other two factors, the literal Cell and the residual facial seam, are
already proved to have support inside the finite carrier.  Singleton old
components are retained through explicit old-region membership rather than
graph support.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOldEdgeAdequacy

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteClosure
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteEdgeState
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteNewEdgeAdequacy
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputCap
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputFragment
open GoertzelV24ClosedWebPointwiseSelectedFaceFinitePredecessorDisjoint
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24SimpleGraphThreeFactorSelectedAnchor
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceFiniteOldEdgeAdequacyEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Every literal old-prefix dart in a chosen output component has an
old-component anchor on the finite transition carrier.  The returned finite
closure is the exact graph-free certificate that the anchor contributes to
the selected output fragment. -/
theorem exists_pointwiseSelectedSourceLocalLayerSerialFaceOldFactorAnchor
    {data : AnnularBoundaryData G 5} (formation : Formation data) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset)
    (dart : formation.annular.RS.D)
    (hdartOld : formation.annular.RS.edgeOf dart ∈
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior offset)
    (hreachable :
      (faceRegionalDartGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset)
        ).Reachable
          (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior offset fragment).1 dart) :
    let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor hinterior offset
    let coordinate := carrierCoordinate carrier
    let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior
      offset hcell
    let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor hinterior offset hcell
    let output := coordinate
      (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
        offset fragment)
    ∃ anchor : {dart // dart ∈ carrier},
      (faceRegionalDartGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior offset)
        ).Reachable anchor.1 dart ∧
      Relation.ReflTransGen
        (SourceLocalLayerSerialFaceFiniteComponentStep state code)
        output (coordinate anchor) := by
  dsimp only
  let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor hinterior
    offset
  let coordinate := carrierCoordinate carrier
  let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior offset
    hcell
  let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor hinterior offset hcell
  let oldRegion := pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior
    offset
  let outputRegion := pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset
  let oldGraph := faceRegionalDartGraph formation.annular.RS oldRegion
  let cellGraph := faceRegionalDartGraph formation.annular.RS
    (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset)
  let seamGraph := pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt formation corridor hinterior
    offset
  let outputDart := pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
    formation corridor hinterior offset fragment
  have hreachableUnion : ((oldGraph ⊔ cellGraph) ⊔ seamGraph).Reachable
      outputDart.1 dart := by
    rw [← pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor formation corridor hinterior offset]
    exact hreachable
  rcases exists_selected_firstFactor_anchor_of_present oldGraph cellGraph
      seamGraph
      (fun current => formation.annular.RS.edgeOf current ∈ oldRegion)
      (fun current => current ∈ carrier) outputDart.1 dart outputDart.2 hdartOld
      (by
        intro left right hright hreach
        by_cases heq : left = right
        · simpa [heq] using hright
        · have hsupport : left ∈ oldGraph.support :=
            SimpleGraph.mem_support_of_reachable heq hreach
          rw [SimpleGraph.mem_support] at hsupport
          rcases hsupport with ⟨neighbor, hadjacent⟩
          exact hadjacent.2.2.1)
      (by
        intro middle right _hmiddleOld hne hcellReachable
        apply pointwiseSelectedSourceLocalLayerCellFaceDartGraph_support_subset_transitionCarrier
          formation corridor hinterior offset
        exact SimpleGraph.mem_support_of_reachable hne hcellReachable)
      (by
        intro middle right _hmiddleOld hne hseamReachable
        apply pointwiseSelectedSourceLocalLayerFaceDartSeam_support_subset_transitionCarrier
          formation corridor hinterior offset
        exact SimpleGraph.mem_support_of_reachable hne hseamReachable)
      hreachableUnion with ⟨anchor, hanchor, holdAnchor⟩
  let selectedAnchor : {dart // dart ∈ carrier} := ⟨anchor, hanchor⟩
  have hanchorOutput :
      (faceRegionalDartGraph formation.annular.RS outputRegion).Reachable
        outputDart.1 anchor := by
    have holdOutput :
        (faceRegionalDartGraph formation.annular.RS outputRegion).Reachable
          anchor dart := by
      rw [pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor formation corridor hinterior offset]
      exact holdAnchor.mono (le_trans le_sup_left le_sup_left)
    exact hreachable.trans holdOutput.symm
  refine ⟨selectedAnchor, holdAnchor, ?_⟩
  exact
    (pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure formation corridor hinterior offset hcell outputDart selectedAnchor).1 hanchorOutput

/-- Literal old-prefix part of one complete outgoing face component. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceOldOutputComponentEdgesAt
    {data : AnnularBoundaryData G 5} (formation : Formation data) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) : Finset G.edgeSet :=
  (sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset)
    (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
      offset fragment).1).filter fun edge =>
        edge ∈ pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior
          offset

@[simp]
theorem mem_pointwiseSelectedSourceLocalLayerSerialFaceOldOutputComponentEdgesAt_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) (edge : G.edgeSet) :
    edge ∈ pointwiseSelectedSourceLocalLayerSerialFaceOldOutputComponentEdgesAt formation corridor hinterior
        offset fragment ↔
      edge ∈ sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset)
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior offset fragment).1 ∧
      edge ∈ pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior
        offset := by
  classical
  simp [pointwiseSelectedSourceLocalLayerSerialFaceOldOutputComponentEdgesAt]

/-- The canonical predecessor union is exactly the old-region part of the
complete outgoing component.  Thus the finite selector misses neither an
old component nor an isolated old occurrence. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt_eq_oldOutput
    {data : AnnularBoundaryData G 5} (formation : Formation data) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) :
    pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt formation corridor hinterior offset hcell
        fragment =
      pointwiseSelectedSourceLocalLayerSerialFaceOldOutputComponentEdgesAt formation corridor hinterior
        offset fragment := by
  classical
  let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor hinterior
    offset
  let coordinate := carrierCoordinate carrier
  let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior offset
    hcell
  let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor hinterior offset hcell
  let semantic := pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessorSemanticAt formation corridor hinterior offset hcell
  let outputDart := pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
    formation corridor hinterior offset fragment
  let output := coordinate outputDart
  let oldRegion := pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior
    offset
  let outputRegion := pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset
  let oldGraph := faceRegionalDartGraph formation.annular.RS oldRegion
  have holdSubset : oldRegion ⊆ outputRegion := by
    intro edge hedge
    change edge ∈ pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset
    rw [← pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_union_cell formation corridor hinterior offset]
    exact Finset.mem_union_left _ (by simpa [oldRegion] using hedge)
  have holdGraphLe : oldGraph ≤
      faceRegionalDartGraph formation.annular.RS outputRegion := by
    intro left right hadjacent
    exact ⟨hadjacent.1, hadjacent.2.1,
      holdSubset hadjacent.2.2.1, holdSubset hadjacent.2.2.2⟩
  have hcomponentStep :
      SourceLocalLayerSerialFaceFiniteComponentStep state code =
        PointwiseSelectedSourceLocalLayerSerialFaceFiniteComponentStep state
          code := by
    rfl
  ext edge
  rw [mem_pointwiseSelectedSourceLocalLayerSerialFaceOldOutputComponentEdgesAt_iff]
  constructor
  · intro hedge
    unfold pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt at hedge
    rw [Finset.mem_biUnion] at hedge
    rcases hedge with ⟨representative, hrepresentative, hedgeRepresentative⟩
    have hclosure := (Finset.mem_filter.mp hrepresentative).2
    rw [hcomponentStep] at hclosure
    have houtputRepresentative :
        (faceRegionalDartGraph formation.annular.RS outputRegion).Reachable
          outputDart.1 (coordinate.symm representative).1 :=
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
        formation corridor hinterior offset hcell outputDart
          (coordinate.symm representative)).2 (by
            simpa [outputDart, output, coordinate, carrier] using hclosure)
    rcases (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      formation.annular.RS oldRegion (coordinate.symm representative).1 edge).1
        hedgeRepresentative with ⟨hedgeOld, dart, hdart⟩
    refine ⟨?_, hedgeOld⟩
    apply (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      formation.annular.RS outputRegion outputDart.1 edge).2
    exact ⟨holdSubset hedgeOld, dart,
      houtputRepresentative.trans (hdart.mono holdGraphLe)⟩
  · rintro ⟨hedgeOutput, hedgeOld⟩
    rcases (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      formation.annular.RS outputRegion outputDart.1 edge).1 hedgeOutput with
      ⟨_hedgeRegion, dart, hdart⟩
    have hdartOld : formation.annular.RS.edgeOf dart.1 ∈ oldRegion := by
      rw [(formation.annular.RS.mem_dartsOn).1 dart.2]
      exact hedgeOld
    rcases exists_pointwiseSelectedSourceLocalLayerSerialFaceOldFactorAnchor formation corridor hinterior
        offset hcell fragment dart.1 hdartOld hdart with
      ⟨anchor, hanchorDart, houtputAnchor⟩
    let anchorIndex := coordinate anchor
    let representative :=
      sourceLocalLayerSerialFaceFinitePredecessorRepresentative state code
        semantic anchorIndex
    have hanchorOld : formation.annular.RS.edgeOf anchor.1 ∈ oldRegion := by
      by_cases heq : anchor.1 = dart.1
      · simpa [heq] using hdartOld
      · have hsupport : anchor.1 ∈ oldGraph.support :=
          SimpleGraph.mem_support_of_reachable heq hanchorDart
        rw [SimpleGraph.mem_support] at hsupport
        rcases hsupport with ⟨neighbor, hadjacent⟩
        exact hadjacent.2.2.1
    have hslotAnchor :
        sourceLocalLayerSerialFaceFiniteStableSlot code anchorIndex =
          pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation corridor hinterior offset
            hcell anchor := by
      rfl
    have hanchorPresent :
        state.interfacePresent
            (sourceLocalLayerSerialFaceFiniteStableSlot code anchorIndex) =
          true := by
      rw [hslotAnchor]
      rw [pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt_interfacePresent]
      simpa [oldRegion] using hanchorOld
    have hrepresentativeConnected :
        SourceLocalLayerSerialFaceFinitePredecessorConnected state code
          anchorIndex representative :=
      (mem_sourceLocalLayerSerialFaceFinitePredecessorPartition_part_iff state
        code semantic anchorIndex representative).1
        (sourceLocalLayerSerialFaceFinitePredecessorRepresentative_mem_part
          state code semantic anchorIndex)
    have hrepresentativePresent :
        state.interfacePresent
            (sourceLocalLayerSerialFaceFiniteStableSlot code representative) =
          true := by
      rw [← semantic.present_constant hrepresentativeConnected]
      exact hanchorPresent
    have hrepresentativeFixed :
        sourceLocalLayerSerialFaceFinitePredecessorRepresentative state code
            semantic representative = representative := by
      have hfixed :=
        (sourceLocalLayerSerialFaceFinitePredecessorRepresentative_eq_iff state
          code semantic anchorIndex representative).2
          hrepresentativeConnected
      simpa [representative] using hfixed
    have hrepresentativeBase : representative ∈
        sourceLocalLayerSerialFaceFinitePredecessorRepresentatives state code
          semantic :=
      (mem_sourceLocalLayerSerialFaceFinitePredecessorRepresentatives_iff state
        code semantic representative).2
        ⟨hrepresentativePresent, hrepresentativeFixed⟩
    have hrepresentativeContributes : representative ∈
        sourceLocalLayerSerialFaceFiniteContributingPredecessors state code
          semantic output := by
      apply Finset.mem_filter.mpr
      refine ⟨hrepresentativeBase, ?_⟩
      exact houtputAnchor.trans
        (Relation.ReflTransGen.single (Or.inl hrepresentativeConnected))
    have hslotRepresentative :
        sourceLocalLayerSerialFaceFiniteStableSlot code representative =
          pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation corridor hinterior offset
            hcell (coordinate.symm representative) := by
      have hslotDart (current : {dart // dart ∈ carrier}) :
          sourceLocalLayerSerialFaceFiniteStableSlot code
              (coordinate current) =
            pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation corridor hinterior offset
              hcell current := by
        rfl
      rw [← hslotDart (coordinate.symm representative)]
      simp
    have hanchorRepresentative : oldGraph.Reachable anchor.1
        (coordinate.symm representative).1 := by
      unfold SourceLocalLayerSerialFaceFinitePredecessorConnected at hrepresentativeConnected
      rw [hslotAnchor, hslotRepresentative] at hrepresentativeConnected
      exact
        (pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt_factoredReachability_iff
          formation corridor hinterior offset hcell anchor
            (coordinate.symm representative)).1 hrepresentativeConnected
    unfold pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt
    rw [Finset.mem_biUnion]
    refine ⟨representative, hrepresentativeContributes, ?_⟩
    apply (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      formation.annular.RS oldRegion (coordinate.symm representative).1 edge).2
    exact ⟨hedgeOld, dart,
      hanchorRepresentative.symm.trans hanchorDart⟩

/-- The complete outgoing face support is the disjoint union of its canonical
old predecessor components and the genuinely new Cell edges. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceComponentEdges_eq_old_union_new
    {data : AnnularBoundaryData G 5} (formation : Formation data) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) :
    sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset)
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior offset fragment).1 =
      pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt formation corridor hinterior offset
          hcell fragment ∪
        pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt formation corridor hinterior offset
          fragment := by
  classical
  rw [pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt_eq_oldOutput formation corridor hinterior offset hcell fragment]
  ext edge
  rw [Finset.mem_union,
    mem_pointwiseSelectedSourceLocalLayerSerialFaceOldOutputComponentEdgesAt_iff,
    mem_pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt_iff]
  constructor
  · intro hedgeOutput
    have hedgeRegion :=
      (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset)
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior offset fragment).1 edge).1 hedgeOutput |>.1
    rw [← pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_union_cell formation corridor hinterior offset] at hedgeRegion
    rcases Finset.mem_union.mp hedgeRegion with hedgeOld | hedgeCell
    · exact Or.inl ⟨hedgeOutput, hedgeOld⟩
    · by_cases hedgeOld : edge ∈
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior offset
      · exact Or.inl ⟨hedgeOutput, hedgeOld⟩
      · exact Or.inr ⟨hedgeOutput, hedgeCell, hedgeOld⟩
  · rintro (⟨hedgeOutput, _hedgeOld⟩ |
      ⟨hedgeOutput, _hedgeCell, _hedgeNotOld⟩)
    · exact hedgeOutput
    · exact hedgeOutput

/-- The old predecessor support and genuinely new Cell support cannot overlap:
new edges are selected only after predecessor membership is excluded. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt_disjoint_new
    {data : AnnularBoundaryData G 5} (formation : Formation data) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) :
    Disjoint
      (pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt formation corridor hinterior offset
        hcell fragment)
      (pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt formation corridor hinterior offset
        fragment) := by
  classical
  rw [pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt_eq_oldOutput formation corridor hinterior offset hcell fragment]
  rw [Finset.disjoint_left]
  intro edge hedgeOld hedgeNew
  have hedgeOldRegion :=
    (mem_pointwiseSelectedSourceLocalLayerSerialFaceOldOutputComponentEdgesAt_iff formation corridor hinterior offset fragment edge).1 hedgeOld |>.2
  have hedgeNotOld :=
    (mem_pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt_iff formation corridor hinterior
      offset fragment edge).1 hedgeNew |>.2.2
  exact hedgeNotOld hedgeOldRegion

/-- Cardinality form of the exact old/new support split. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceComponentEdges_card_eq_old_add_new
    {data : AnnularBoundaryData G 5} (formation : Formation data) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) :
    (sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset)
      (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
        offset fragment).1).card =
      (pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt formation corridor hinterior offset
        hcell fragment).card +
      (pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt formation corridor hinterior offset
        fragment).card := by
  rw [pointwiseSelectedSourceLocalLayerSerialFaceComponentEdges_eq_old_union_new formation corridor hinterior
    offset hcell fragment]
  exact Finset.card_union_of_disjoint
    (pointwiseSelectedSourceLocalLayerSerialFaceOldComponentEdgesAt_disjoint_new formation corridor hinterior
      offset hcell fragment)

/-- Graph-free cap-at-five decoder for one finite facial transition.  It adds
the canonical predecessor-component cap sum to the number of distinct new
Cell-edge representatives and saturates only at the manuscript threshold. -/
noncomputable def PointwiseSelectedSourceLocalLayerSerialFaceFiniteOutputCap
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (predecessorSemantic :
      SourceLocalLayerSerialFaceFinitePredecessorSemantic state code)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output : Fin code.vertexCount.val)
    (newEdgeSemantic : SourceLocalLayerSerialFaceFiniteNewEdgeSemantic state
      code edgeState output) : Fin 6 :=
  ⟨min
      (sourceLocalLayerSerialFaceFinitePredecessorCapSum state code
          predecessorSemantic output +
        (sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives state code
          edgeState output newEdgeSemantic).card)
      5,
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- Actual-source specialization of the graph-free cap decoder. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceFiniteOutputCapAt
    {data : AnnularBoundaryData G 5} (formation : Formation data) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) : Fin 6 := by
  classical
  let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor hinterior
    offset
  let coordinate := carrierCoordinate carrier
  let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior offset
    hcell
  let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor hinterior offset hcell
  let predecessorSemantic :=
    pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessorSemanticAt formation corridor hinterior offset
      hcell
  let edgeState := pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt formation corridor hinterior
    offset hcell
  let output := coordinate
    (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
      offset fragment)
  let newEdgeSemantic := pointwiseSelectedSourceLocalLayerSerialFaceFiniteNewEdgeSemanticAt
    formation corridor hinterior offset hcell output
  exact PointwiseSelectedSourceLocalLayerSerialFaceFiniteOutputCap state code
    predecessorSemantic edgeState output newEdgeSemantic

/-- The finite decoder computes exactly the capped cardinality of the complete
literal outgoing face component. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceFiniteOutputCapAt_val
    {data : AnnularBoundaryData G 5} (formation : Formation data) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) :
    (pointwiseSelectedSourceLocalLayerSerialFaceFiniteOutputCapAt formation corridor hinterior offset hcell
      fragment).val =
      min
        (sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset)
          (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior offset fragment).1).card
        5 := by
  classical
  unfold pointwiseSelectedSourceLocalLayerSerialFaceFiniteOutputCapAt
  unfold PointwiseSelectedSourceLocalLayerSerialFaceFiniteOutputCap
  dsimp only
  rw [pointwiseSelectedSourceLocalLayerSerialFaceFinitePredecessorCapSum_eq_oldComponentEdges
    formation corridor hinterior offset hcell fragment]
  rw [card_pointwiseSelectedSourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives_eq formation corridor hinterior offset hcell fragment]
  rw [pointwiseSelectedSourceLocalLayerSerialFaceComponentEdges_card_eq_old_add_new formation corridor hinterior offset hcell fragment]
  omega

/-- On every actual output fragment, the graph-free finite decoder is exactly
the manuscript's capped regional-fragment edge count.  This is the semantic
quantity stored in the `faceLengthCap` field of the five-field profile. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceFiniteOutputCapAt_eq_fragmentCap
    {data : AnnularBoundaryData G 5} (formation : Formation data) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) :
    pointwiseSelectedSourceLocalLayerSerialFaceFiniteOutputCapAt formation corridor hinterior offset hcell
        fragment =
      ⟨min
        (boundaryRegionalFragmentEdges formation.annular.RS
          (indexedCrossingEdgeSet
            (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor hinterior offset))
          (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset)
          fragment).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ := by
  apply Fin.ext
  rw [pointwiseSelectedSourceLocalLayerSerialFaceFiniteOutputCapAt_val]
  exact congrArg (fun edges : Finset G.edgeSet => min edges.card 5)
    (boundaryRegionalFragmentEdges_eq_componentEdges formation.annular.RS
      (indexedCrossingEdgeSet
        (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor hinterior offset))
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset)
      fragment).symm

end

end GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOldEdgeAdequacy

end Mettapedia.GraphTheory.FourColor
