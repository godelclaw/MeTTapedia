import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorDisjoint
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

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOldEdgeAdequacy

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeAdequacy
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorDisjoint
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

local instance closedWebLocalLayerSerialCellFaceFiniteOldEdgeAdequacyEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Every literal old-prefix dart in a chosen output component has an
old-component anchor on the finite transition carrier.  The returned finite
closure is the exact graph-free certificate that the anchor contributes to
the selected output fragment. -/
theorem exists_sourceLocalLayerSerialFaceOldFactorAnchor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset)
    (dart : web.annular.RS.D)
    (hdartOld : web.annular.RS.edgeOf dart ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
    (hreachable :
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        ).Reachable
          (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
            hunique offset fragment).1 dart) :
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let coordinate := carrierCoordinate carrier
    let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
      offset hcell
    let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
      hunique offset hcell
    let output := coordinate
      (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
        offset fragment)
    ∃ anchor : {dart // dart ∈ carrier},
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        ).Reachable anchor.1 dart ∧
      Relation.ReflTransGen
        (SourceLocalLayerSerialFaceFiniteComponentStep state code)
        output (coordinate anchor) := by
  dsimp only
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let coordinate := carrierCoordinate carrier
  let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
    hcell
  let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcell
  let oldRegion := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
    offset
  let outputRegion := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor
    hunique offset
  let oldGraph := faceRegionalDartGraph web.annular.RS oldRegion
  let cellGraph := faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerCellRegionAt corridor hunique offset)
  let seamGraph := sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique
    offset
  let outputDart := sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
    corridor hunique offset fragment
  have hreachableUnion : ((oldGraph ⊔ cellGraph) ⊔ seamGraph).Reachable
      outputDart.1 dart := by
    rw [← sourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor corridor
      hunique offset]
    exact hreachable
  rcases exists_selected_firstFactor_anchor_of_present oldGraph cellGraph
      seamGraph
      (fun current => web.annular.RS.edgeOf current ∈ oldRegion)
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
        apply sourceLocalLayerCellFaceDartGraph_support_subset_transitionCarrier
          corridor hunique offset
        exact SimpleGraph.mem_support_of_reachable hne hcellReachable)
      (by
        intro middle right _hmiddleOld hne hseamReachable
        apply sourceLocalLayerFaceDartSeam_support_subset_transitionCarrier
          corridor hunique offset
        exact SimpleGraph.mem_support_of_reachable hne hseamReachable)
      hreachableUnion with ⟨anchor, hanchor, holdAnchor⟩
  let selectedAnchor : {dart // dart ∈ carrier} := ⟨anchor, hanchor⟩
  have hanchorOutput :
      (faceRegionalDartGraph web.annular.RS outputRegion).Reachable
        outputDart.1 anchor := by
    have holdOutput :
        (faceRegionalDartGraph web.annular.RS outputRegion).Reachable
          anchor dart := by
      rw [sourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor corridor
        hunique offset]
      exact holdAnchor.mono (le_trans le_sup_left le_sup_left)
    exact hreachable.trans holdOutput.symm
  refine ⟨selectedAnchor, holdAnchor, ?_⟩
  exact
    (sourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure corridor
      hunique offset hcell outputDart selectedAnchor).1 hanchorOutput

/-- Literal old-prefix part of one complete outgoing face component. -/
noncomputable def sourceLocalLayerSerialFaceOldOutputComponentEdgesAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) : Finset G.edgeSet :=
  (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
      offset fragment).1).filter fun edge =>
        edge ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          offset

@[simp]
theorem mem_sourceLocalLayerSerialFaceOldOutputComponentEdgesAt_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) (edge : G.edgeSet) :
    edge ∈ sourceLocalLayerSerialFaceOldOutputComponentEdgesAt corridor hunique
        offset fragment ↔
      edge ∈ sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
          hunique offset fragment).1 ∧
      edge ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        offset := by
  classical
  simp [sourceLocalLayerSerialFaceOldOutputComponentEdgesAt]

/-- The canonical predecessor union is exactly the old-region part of the
complete outgoing component.  Thus the finite selector misses neither an
old component nor an isolated old occurrence. -/
theorem sourceLocalLayerSerialFaceOldComponentEdgesAt_eq_oldOutput
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    sourceLocalLayerSerialFaceOldComponentEdgesAt corridor hunique offset hcell
        fragment =
      sourceLocalLayerSerialFaceOldOutputComponentEdgesAt corridor hunique
        offset fragment := by
  classical
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let coordinate := carrierCoordinate carrier
  let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
    hcell
  let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcell
  let semantic := sourceLocalLayerSerialFaceFinitePredecessorSemanticAt corridor
    hunique offset hcell
  let outputDart := sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
    corridor hunique offset fragment
  let output := coordinate outputDart
  let oldRegion := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
    offset
  let outputRegion := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor
    hunique offset
  let oldGraph := faceRegionalDartGraph web.annular.RS oldRegion
  have holdSubset : oldRegion ⊆ outputRegion := by
    intro edge hedge
    change edge ∈ sourceLocalLayerSerialPreRebaseOutputRegionAt corridor
      hunique offset
    rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor
      hunique offset]
    exact Finset.mem_union_left _ (by simpa [oldRegion] using hedge)
  have holdGraphLe : oldGraph ≤
      faceRegionalDartGraph web.annular.RS outputRegion := by
    intro left right hadjacent
    exact ⟨hadjacent.1, hadjacent.2.1,
      holdSubset hadjacent.2.2.1, holdSubset hadjacent.2.2.2⟩
  ext edge
  rw [mem_sourceLocalLayerSerialFaceOldOutputComponentEdgesAt_iff]
  constructor
  · intro hedge
    unfold sourceLocalLayerSerialFaceOldComponentEdgesAt at hedge
    rw [Finset.mem_biUnion] at hedge
    rcases hedge with ⟨representative, hrepresentative, hedgeRepresentative⟩
    have hclosure := (Finset.mem_filter.mp hrepresentative).2
    have houtputRepresentative :
        (faceRegionalDartGraph web.annular.RS outputRegion).Reachable
          outputDart.1 (coordinate.symm representative).1 :=
      (sourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
        corridor hunique offset hcell outputDart
          (coordinate.symm representative)).2 (by
            simpa [outputDart, output, coordinate, carrier] using hclosure)
    rcases (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      web.annular.RS oldRegion (coordinate.symm representative).1 edge).1
        hedgeRepresentative with ⟨hedgeOld, dart, hdart⟩
    refine ⟨?_, hedgeOld⟩
    apply (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      web.annular.RS outputRegion outputDart.1 edge).2
    exact ⟨holdSubset hedgeOld, dart,
      houtputRepresentative.trans (hdart.mono holdGraphLe)⟩
  · rintro ⟨hedgeOutput, hedgeOld⟩
    rcases (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      web.annular.RS outputRegion outputDart.1 edge).1 hedgeOutput with
      ⟨_hedgeRegion, dart, hdart⟩
    have hdartOld : web.annular.RS.edgeOf dart.1 ∈ oldRegion := by
      rw [(web.annular.RS.mem_dartsOn).1 dart.2]
      exact hedgeOld
    rcases exists_sourceLocalLayerSerialFaceOldFactorAnchor corridor hunique
        offset hcell fragment dart.1 hdartOld hdart with
      ⟨anchor, hanchorDart, houtputAnchor⟩
    let anchorIndex := coordinate anchor
    let representative :=
      sourceLocalLayerSerialFaceFinitePredecessorRepresentative state code
        semantic anchorIndex
    have hanchorOld : web.annular.RS.edgeOf anchor.1 ∈ oldRegion := by
      by_cases heq : anchor.1 = dart.1
      · simpa [heq] using hdartOld
      · have hsupport : anchor.1 ∈ oldGraph.support :=
          SimpleGraph.mem_support_of_reachable heq hanchorDart
        rw [SimpleGraph.mem_support] at hsupport
        rcases hsupport with ⟨neighbor, hadjacent⟩
        exact hadjacent.2.2.1
    have hslotAnchor :
        sourceLocalLayerSerialFaceFiniteStableSlot code anchorIndex =
          sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
            hcell anchor := by
      rfl
    have hanchorPresent :
        state.interfacePresent
            (sourceLocalLayerSerialFaceFiniteStableSlot code anchorIndex) =
          true := by
      rw [hslotAnchor]
      rw [sourceLocalLayerSerialFacePrefixAttachmentStateAt_interfacePresent]
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
          sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
            hcell (coordinate.symm representative) := by
      have hslotDart (current : {dart // dart ∈ carrier}) :
          sourceLocalLayerSerialFaceFiniteStableSlot code
              (coordinate current) =
            sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
              hcell current := by
        rfl
      rw [← hslotDart (coordinate.symm representative)]
      simp
    have hanchorRepresentative : oldGraph.Reachable anchor.1
        (coordinate.symm representative).1 := by
      unfold SourceLocalLayerSerialFaceFinitePredecessorConnected at hrepresentativeConnected
      rw [hslotAnchor, hslotRepresentative] at hrepresentativeConnected
      exact
        (sourceLocalLayerSerialFacePrefixAttachmentStateAt_factoredReachability_iff
          corridor hunique offset hcell anchor
            (coordinate.symm representative)).1 hrepresentativeConnected
    unfold sourceLocalLayerSerialFaceOldComponentEdgesAt
    rw [Finset.mem_biUnion]
    refine ⟨representative, hrepresentativeContributes, ?_⟩
    apply (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      web.annular.RS oldRegion (coordinate.symm representative).1 edge).2
    exact ⟨hedgeOld, dart,
      hanchorRepresentative.symm.trans hanchorDart⟩

/-- The complete outgoing face support is the disjoint union of its canonical
old predecessor components and the genuinely new Cell edges. -/
theorem sourceLocalLayerSerialFaceComponentEdges_eq_old_union_new
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
          hunique offset fragment).1 =
      sourceLocalLayerSerialFaceOldComponentEdgesAt corridor hunique offset
          hcell fragment ∪
        sourceLocalLayerSerialFaceNewComponentEdgesAt corridor hunique offset
          fragment := by
  classical
  rw [sourceLocalLayerSerialFaceOldComponentEdgesAt_eq_oldOutput corridor
    hunique offset hcell fragment]
  ext edge
  rw [Finset.mem_union,
    mem_sourceLocalLayerSerialFaceOldOutputComponentEdgesAt_iff,
    mem_sourceLocalLayerSerialFaceNewComponentEdgesAt_iff]
  constructor
  · intro hedgeOutput
    have hedgeRegion :=
      (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
          hunique offset fragment).1 edge).1 hedgeOutput |>.1
    rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor
      hunique offset] at hedgeRegion
    rcases Finset.mem_union.mp hedgeRegion with hedgeOld | hedgeCell
    · exact Or.inl ⟨hedgeOutput, hedgeOld⟩
    · by_cases hedgeOld : edge ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset
      · exact Or.inl ⟨hedgeOutput, hedgeOld⟩
      · exact Or.inr ⟨hedgeOutput, hedgeCell, hedgeOld⟩
  · rintro (⟨hedgeOutput, _hedgeOld⟩ |
      ⟨hedgeOutput, _hedgeCell, _hedgeNotOld⟩)
    · exact hedgeOutput
    · exact hedgeOutput

/-- The old predecessor support and genuinely new Cell support cannot overlap:
new edges are selected only after predecessor membership is excluded. -/
theorem sourceLocalLayerSerialFaceOldComponentEdgesAt_disjoint_new
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    Disjoint
      (sourceLocalLayerSerialFaceOldComponentEdgesAt corridor hunique offset
        hcell fragment)
      (sourceLocalLayerSerialFaceNewComponentEdgesAt corridor hunique offset
        fragment) := by
  classical
  rw [sourceLocalLayerSerialFaceOldComponentEdgesAt_eq_oldOutput corridor
    hunique offset hcell fragment]
  rw [Finset.disjoint_left]
  intro edge hedgeOld hedgeNew
  have hedgeOldRegion :=
    (mem_sourceLocalLayerSerialFaceOldOutputComponentEdgesAt_iff corridor
      hunique offset fragment edge).1 hedgeOld |>.2
  have hedgeNotOld :=
    (mem_sourceLocalLayerSerialFaceNewComponentEdgesAt_iff corridor hunique
      offset fragment edge).1 hedgeNew |>.2.2
  exact hedgeNotOld hedgeOldRegion

/-- Cardinality form of the exact old/new support split. -/
theorem sourceLocalLayerSerialFaceComponentEdges_card_eq_old_add_new
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
        offset fragment).1).card =
      (sourceLocalLayerSerialFaceOldComponentEdgesAt corridor hunique offset
        hcell fragment).card +
      (sourceLocalLayerSerialFaceNewComponentEdgesAt corridor hunique offset
        fragment).card := by
  rw [sourceLocalLayerSerialFaceComponentEdges_eq_old_union_new corridor hunique
    offset hcell fragment]
  exact Finset.card_union_of_disjoint
    (sourceLocalLayerSerialFaceOldComponentEdgesAt_disjoint_new corridor hunique
      offset hcell fragment)

/-- Graph-free cap-at-five decoder for one finite facial transition.  It adds
the canonical predecessor-component cap sum to the number of distinct new
Cell-edge representatives and saturates only at the manuscript threshold. -/
noncomputable def SourceLocalLayerSerialFaceFiniteOutputCap
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
noncomputable def sourceLocalLayerSerialFaceFiniteOutputCapAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) : Fin 6 := by
  classical
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let coordinate := carrierCoordinate carrier
  let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
    hcell
  let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcell
  let predecessorSemantic :=
    sourceLocalLayerSerialFaceFinitePredecessorSemanticAt corridor hunique offset
      hcell
  let edgeState := sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique
    offset hcell
  let output := coordinate
    (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
      offset fragment)
  let newEdgeSemantic := sourceLocalLayerSerialFaceFiniteNewEdgeSemanticAt
    corridor hunique offset hcell output
  exact SourceLocalLayerSerialFaceFiniteOutputCap state code
    predecessorSemantic edgeState output newEdgeSemantic

/-- The finite decoder computes exactly the capped cardinality of the complete
literal outgoing face component. -/
theorem sourceLocalLayerSerialFaceFiniteOutputCapAt_val
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    (sourceLocalLayerSerialFaceFiniteOutputCapAt corridor hunique offset hcell
      fragment).val =
      min
        (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
            hunique offset fragment).1).card
        5 := by
  classical
  unfold sourceLocalLayerSerialFaceFiniteOutputCapAt
  unfold SourceLocalLayerSerialFaceFiniteOutputCap
  dsimp only
  rw [sourceLocalLayerSerialFaceFinitePredecessorCapSum_eq_oldComponentEdges
    corridor hunique offset hcell fragment]
  rw [card_sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives_eq corridor
    hunique offset hcell fragment]
  rw [sourceLocalLayerSerialFaceComponentEdges_card_eq_old_add_new corridor
    hunique offset hcell fragment]
  omega

/-- On every actual output fragment, the graph-free finite decoder is exactly
the manuscript's capped regional-fragment edge count.  This is the semantic
quantity stored in the `faceLengthCap` field of the five-field profile. -/
theorem sourceLocalLayerSerialFaceFiniteOutputCapAt_eq_fragmentCap
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    sourceLocalLayerSerialFaceFiniteOutputCapAt corridor hunique offset hcell
        fragment =
      ⟨min
        (boundaryRegionalFragmentEdges web.annular.RS
          (indexedCrossingEdgeSet
            (sourceLocalLayerRightCrossingAt corridor hunique offset))
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          fragment).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ := by
  apply Fin.ext
  rw [sourceLocalLayerSerialFaceFiniteOutputCapAt_val]
  exact congrArg (fun edges : Finset G.edgeSet => min edges.card 5)
    (boundaryRegionalFragmentEdges_eq_componentEdges web.annular.RS
      (indexedCrossingEdgeSet
        (sourceLocalLayerRightCrossingAt corridor hunique offset))
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      fragment).symm

end

end GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOldEdgeAdequacy

end Mettapedia.GraphTheory.FourColor
