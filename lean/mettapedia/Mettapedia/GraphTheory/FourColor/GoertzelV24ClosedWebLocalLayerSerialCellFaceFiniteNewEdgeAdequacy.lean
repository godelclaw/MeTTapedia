import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeRepresentatives

/-!
# Adequacy of the finite new-Cell edge selector

For a chosen outgoing regional face fragment, the finite selector retains
exactly the distinct Cell edges in its complete pre-rebase component which
were not already present in the accumulated predecessor.  This file proves
that statement by an explicit equivalence: canonical finite representatives
are in bijection with the literal new primal-edge support.

The result is the overlap-free local summand of the cap-at-five decoder.  The
other summand is the canonical predecessor-component sum.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeAdequacy

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellFaceFiniteNewEdgeAdequacyEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Literal distinct edges of one output component contributed by the Cell
but absent from the predecessor region. -/
noncomputable def sourceLocalLayerSerialFaceNewComponentEdgesAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) : Finset G.edgeSet := by
  classical
  let oldRegion := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
    offset
  let cellRegion := sourceLocalLayerCellRegionAt corridor hunique offset
  let outputRegion := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor
    hunique offset
  let start := (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
    corridor hunique offset fragment).1
  exact (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
    outputRegion start).filter fun edge =>
      edge ∈ cellRegion ∧ edge ∉ oldRegion

@[simp]
theorem mem_sourceLocalLayerSerialFaceNewComponentEdgesAt_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) (edge : G.edgeSet) :
    edge ∈ sourceLocalLayerSerialFaceNewComponentEdgesAt corridor hunique offset
        fragment ↔
      edge ∈ sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
            hunique offset fragment).1 ∧
        edge ∈ sourceLocalLayerCellRegionAt corridor hunique offset ∧
        edge ∉ sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          offset := by
  classical
  simp [sourceLocalLayerSerialFaceNewComponentEdgesAt]

/-- On an actual source Cell, the finite new-edge predicate is exactly literal
Cell membership, predecessor absence, and complete output-component
reachability. -/
theorem sourceLocalLayerSerialFaceFiniteNewEdgeContributesAt_iff
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
    (coordinateIndex : Fin
      (sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset hcell
        ).vertexCount.val) :
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let coordinate := carrierCoordinate carrier
    let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
      offset hcell
    let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
      hunique offset hcell
    let edgeState := sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique
      offset hcell
    let output := coordinate
      (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
        offset fragment)
    SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
        output coordinateIndex ↔
      web.annular.RS.edgeOf (coordinate.symm coordinateIndex).1 ∈
          sourceLocalLayerCellRegionAt corridor hunique offset ∧
        web.annular.RS.edgeOf (coordinate.symm coordinateIndex).1 ∉
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∧
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          ).Reachable
            (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
              hunique offset fragment).1
            (coordinate.symm coordinateIndex).1 := by
  dsimp only
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let coordinate := carrierCoordinate carrier
  let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
    hcell
  let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcell
  let edgeState := sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique
    offset hcell
  change Fin carrier.card at coordinateIndex
  let output := coordinate
    (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
      offset fragment)
  change SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
      output coordinateIndex ↔
    web.annular.RS.edgeOf (coordinate.symm coordinateIndex).1 ∈
        sourceLocalLayerCellRegionAt corridor hunique offset ∧
      web.annular.RS.edgeOf (coordinate.symm coordinateIndex).1 ∉
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∧
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        ).Reachable
          (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
            hunique offset fragment).1
          (coordinate.symm coordinateIndex).1
  have hslotDart (dart : {dart // dart ∈ carrier}) :
      sourceLocalLayerSerialFaceFiniteStableSlot code (coordinate dart) =
        sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell dart := by
    rfl
  have hslot :
      sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex =
        sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell (coordinate.symm coordinateIndex) := by
    rw [← hslotDart (coordinate.symm coordinateIndex)]
    simp
  unfold SourceLocalLayerSerialFaceFiniteNewEdgeContributes
  rw [hslot]
  rw [sourceLocalLayerSerialFaceFiniteEdgeStateAt_cellPresent_iff]
  rw [Bool.eq_false_iff]
  rw [sourceLocalLayerSerialFacePrefixAttachmentStateAt_interfacePresent]
  have hnotOld :
      (decide
          (web.annular.RS.edgeOf (coordinate.symm coordinateIndex).1 ∈
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset) ≠
          true) ↔
        web.annular.RS.edgeOf (coordinate.symm coordinateIndex).1 ∉
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset := by
    simp
  rw [hnotOld]
  constructor
  · rintro ⟨hcellEdge, hnotOldEdge, hfinite⟩
    refine ⟨hcellEdge, hnotOldEdge, ?_⟩
    apply (sourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
      corridor hunique offset hcell
        (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
          hunique offset fragment)
        (coordinate.symm coordinateIndex)).2
    simpa [state, code, output, coordinate, carrier] using hfinite
  · rintro ⟨hcellEdge, hnotOldEdge, hreachable⟩
    refine ⟨hcellEdge, hnotOldEdge, ?_⟩
    have hfinite :=
      (sourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
        corridor hunique offset hcell
          (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
            hunique offset fragment)
          (coordinate.symm coordinateIndex)).1 hreachable
    simpa [state, code, output, coordinate, carrier] using hfinite

/-- Canonical finite new-edge representatives are in explicit bijection with
the literal distinct new Cell edges of one output component. -/
noncomputable def sourceLocalLayerSerialFaceFiniteNewEdgeRepresentativeEquiv
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
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let coordinate := carrierCoordinate carrier
    let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
      offset hcell
    let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
      hunique offset hcell
    let edgeState := sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique
      offset hcell
    let output := coordinate
      (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
        offset fragment)
    let semantic := sourceLocalLayerSerialFaceFiniteNewEdgeSemanticAt corridor
      hunique offset hcell output
    {coordinateIndex // coordinateIndex ∈
      sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives state code
        edgeState output semantic} ≃
      {edge // edge ∈ sourceLocalLayerSerialFaceNewComponentEdgesAt corridor
        hunique offset fragment} := by
  classical
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let coordinate := carrierCoordinate carrier
  let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset
    hcell
  let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
    hunique offset hcell
  let edgeState := sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique
    offset hcell
  let output := coordinate
    (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
      offset fragment)
  let semantic := sourceLocalLayerSerialFaceFiniteNewEdgeSemanticAt corridor
    hunique offset hcell output
  let representatives :=
    sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives state code edgeState
      output semantic
  let newEdges := sourceLocalLayerSerialFaceNewComponentEdgesAt corridor hunique
    offset fragment
  have hslotDart (dart : {dart // dart ∈ carrier}) :
      sourceLocalLayerSerialFaceFiniteStableSlot code (coordinate dart) =
        sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell dart := by
    rfl
  have hslot (coordinateIndex : Fin code.vertexCount.val) :
      sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex =
        sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell (coordinate.symm coordinateIndex) := by
    rw [← hslotDart (coordinate.symm coordinateIndex)]
    simp
  have hsame (left right : Fin code.vertexCount.val) :
      edgeState.samePrimalEdge
          (sourceLocalLayerSerialFaceFiniteStableSlot code left)
          (sourceLocalLayerSerialFaceFiniteStableSlot code right) = true ↔
        web.annular.RS.edgeOf (coordinate.symm left).1 =
          web.annular.RS.edgeOf (coordinate.symm right).1 := by
    rw [hslot left, hslot right]
    exact sourceLocalLayerSerialFaceFiniteEdgeStateAt_samePrimalEdge_iff
      corridor hunique offset hcell (coordinate.symm left)
        (coordinate.symm right)
  let toNewEdge : {coordinateIndex // coordinateIndex ∈ representatives} →
      {edge // edge ∈ newEdges} := fun representative => by
    let dart := coordinate.symm representative.1
    refine ⟨web.annular.RS.edgeOf dart.1, ?_⟩
    have hrepresentative :=
      (mem_sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives_iff state code
        edgeState output semantic representative.1).1 representative.2
    rcases hrepresentative with ⟨hcontributes, _hfixed⟩
    have hliteral :=
      (sourceLocalLayerSerialFaceFiniteNewEdgeContributesAt_iff corridor hunique
        offset hcell fragment representative.1).1 hcontributes
    rw [mem_sourceLocalLayerSerialFaceNewComponentEdgesAt_iff]
    refine ⟨?_, hliteral.1, hliteral.2.1⟩
    apply (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
        offset fragment).1 _).2
    refine ⟨?_, ⟨⟨dart.1, (web.annular.RS.mem_dartsOn).2 rfl⟩,
      hliteral.2.2⟩⟩
    rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor
      hunique offset]
    exact Finset.mem_union_right _ hliteral.1
  refine Equiv.ofBijective toNewEdge ⟨?_, ?_⟩
  · intro left right heq
    apply Subtype.ext
    have hleft :=
      (mem_sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives_iff state code
        edgeState output semantic left.1).1 left.2
    have hright :=
      (mem_sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives_iff state code
        edgeState output semantic right.1).1 right.2
    rcases hleft with ⟨hleftContributes, hleftFixed⟩
    rcases hright with ⟨hrightContributes, hrightFixed⟩
    have hedge : web.annular.RS.edgeOf (coordinate.symm left.1).1 =
        web.annular.RS.edgeOf (coordinate.symm right.1).1 := by
      exact congrArg Subtype.val heq
    have hrepresentatives :=
      (sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative_eq_iff state code
        edgeState output semantic left.1 right.1 hleftContributes
          hrightContributes).2 ((hsame left.1 right.1).2 hedge)
    rw [hleftFixed, hrightFixed] at hrepresentatives
    exact hrepresentatives.symm
  · intro edge
    have hedge :=
      (mem_sourceLocalLayerSerialFaceNewComponentEdgesAt_iff corridor hunique
        offset fragment edge.1).1 edge.2
    rcases (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
        offset fragment).1 edge.1).1 hedge.1 with
      ⟨_hedgeOutput, dart, hreachable⟩
    have hdartCell : web.annular.RS.edgeOf dart.1 ∈
        sourceLocalLayerCellRegionAt corridor hunique offset := by
      rw [(web.annular.RS.mem_dartsOn).1 dart.2]
      exact hedge.2.1
    let carrierDart : {dart // dart ∈ carrier} :=
      ⟨dart.1, Finset.mem_union_left _
        ((GoertzelV24RotationFaceRegionalDartCarrier.mem_dartsOnEdges_iff
          web.annular.RS _ dart.1).2 hdartCell)⟩
    let coordinateIndex := coordinate carrierDart
    have hcontributes :
        SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
          output coordinateIndex := by
      apply (sourceLocalLayerSerialFaceFiniteNewEdgeContributesAt_iff corridor
        hunique offset hcell fragment coordinateIndex).2
      constructor
      · change web.annular.RS.edgeOf
            (coordinate.symm (coordinate carrierDart)).1 ∈
          sourceLocalLayerCellRegionAt corridor hunique offset
        rw [coordinate.symm_apply_apply]
        exact hdartCell
      constructor
      · change web.annular.RS.edgeOf
            (coordinate.symm (coordinate carrierDart)).1 ∉
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset
        rw [coordinate.symm_apply_apply]
        change web.annular.RS.edgeOf dart.1 ∉ _
        rw [(web.annular.RS.mem_dartsOn).1 dart.2]
        exact hedge.2.2
      · change (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset)).Reachable
          (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
            hunique offset fragment).1
          (coordinate.symm (coordinate carrierDart)).1
        rw [coordinate.symm_apply_apply]
        exact hreachable
    let representative :=
      sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative state code edgeState
        output semantic coordinateIndex hcontributes
    have hrepresentativeClass :=
      sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative_mem_class state code
        edgeState output semantic coordinateIndex hcontributes
    have hrepresentativeData :=
      (mem_sourceLocalLayerSerialFaceFiniteNewEdgeClass_iff state code edgeState
        output coordinateIndex representative).1 hrepresentativeClass
    have hrepresentativeFixed :
        sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative state code edgeState
          output semantic representative hrepresentativeData.1 = representative := by
      have hidempotent :=
        (sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative_eq_iff state code
          edgeState output semantic representative coordinateIndex
            hrepresentativeData.1 hcontributes).2 hrepresentativeData.2
      exact hidempotent.symm
    have hrepresentativeMem : representative ∈ representatives :=
      (mem_sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives_iff state code
        edgeState output semantic representative).2
        ⟨hrepresentativeData.1, hrepresentativeFixed⟩
    refine ⟨⟨representative, hrepresentativeMem⟩, ?_⟩
    apply Subtype.ext
    dsimp only [toNewEdge]
    have hsameEdge := (hsame representative coordinateIndex).1
      hrepresentativeData.2
    have hedgeOf : web.annular.RS.edgeOf dart.1 = edge.1 :=
      (web.annular.RS.mem_dartsOn).1 dart.2
    exact hsameEdge.trans (by
      simpa [coordinateIndex, carrierDart] using hedgeOf)

/-- The finite representative count is exactly the number of literal distinct
new Cell edges in the selected output component. -/
theorem card_sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives_eq
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
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let coordinate := carrierCoordinate carrier
    let code := sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique
      offset hcell
    let state := sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor
      hunique offset hcell
    let edgeState := sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique
      offset hcell
    let output := coordinate
      (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
        offset fragment)
    let semantic := sourceLocalLayerSerialFaceFiniteNewEdgeSemanticAt corridor
      hunique offset hcell output
    (sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives state code edgeState
      output semantic).card =
      (sourceLocalLayerSerialFaceNewComponentEdgesAt corridor hunique offset
        fragment).card := by
  classical
  let representatives := sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives
    (sourceLocalLayerSerialFacePrefixAttachmentStateAt corridor hunique offset
      hcell)
    (sourceLocalLayerSerialFaceTransitionCodeAt corridor hunique offset hcell)
    (sourceLocalLayerSerialFaceFiniteEdgeStateAt corridor hunique offset hcell)
    ((carrierCoordinate
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset))
      (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor hunique
        offset fragment))
    (sourceLocalLayerSerialFaceFiniteNewEdgeSemanticAt corridor hunique offset
      hcell ((carrierCoordinate
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset))
        (sourceLocalLayerSerialFaceOutputFragmentTransitionDartAt corridor
          hunique offset fragment)))
  let newEdges := sourceLocalLayerSerialFaceNewComponentEdgesAt corridor hunique
    offset fragment
  calc
    representatives.card = Fintype.card {x // x ∈ representatives} :=
      (Fintype.card_coe representatives).symm
    _ = Fintype.card {edge // edge ∈ newEdges} :=
      Fintype.card_congr
        (sourceLocalLayerSerialFaceFiniteNewEdgeRepresentativeEquiv corridor
          hunique offset hcell fragment)
    _ = newEdges.card := Fintype.card_coe newEdges

end

end GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeAdequacy

end Mettapedia.GraphTheory.FourColor
