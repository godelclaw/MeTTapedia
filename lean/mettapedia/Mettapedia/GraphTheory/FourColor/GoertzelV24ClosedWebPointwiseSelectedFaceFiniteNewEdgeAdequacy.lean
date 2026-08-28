import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceFiniteRepresentatives

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

namespace GoertzelV24ClosedWebPointwiseSelectedFaceFiniteNewEdgeAdequacy

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
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteClosure
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteEdgeState
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputFragment
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteRepresentatives
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceFiniteNewEdgeAdequacyEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Literal distinct edges of one output component contributed by the Cell
but absent from the predecessor region. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) : Finset G.edgeSet := by
  classical
  let oldRegion := pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior
    offset
  let cellRegion := pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset
  let outputRegion := pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor
    hinterior offset
  let start := (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt
    formation corridor hinterior offset fragment).1
  exact (sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS
    outputRegion start).filter fun edge =>
      edge ∈ cellRegion ∧ edge ∉ oldRegion

@[simp]
theorem mem_pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) (edge : G.edgeSet) :
    edge ∈ pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt formation corridor hinterior offset
        fragment ↔
      edge ∈ sourceLocalLayerBoundaryRebaseFaceComponentEdges formation.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset)
          (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor
            hinterior offset fragment).1 ∧
        edge ∈ pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset ∧
        edge ∉ pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior
          offset := by
  classical
  simp [pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt]

/-- On an actual source Cell, the finite new-edge predicate is exactly literal
Cell membership, predecessor absence, and complete output-component
reachability. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceFiniteNewEdgeContributesAt_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset)
    (coordinateIndex : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior offset hcell
        ).vertexCount.val) :
    let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor
      hinterior offset
    let coordinate := carrierCoordinate carrier
    let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior
      offset hcell
    let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
      hinterior offset hcell
    let edgeState := pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt formation corridor hinterior
      offset hcell
    let output := coordinate
      (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
        offset fragment)
    SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
        output coordinateIndex ↔
      formation.annular.RS.edgeOf (coordinate.symm coordinateIndex).1 ∈
          pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset ∧
        formation.annular.RS.edgeOf (coordinate.symm coordinateIndex).1 ∉
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior offset ∧
        (faceRegionalDartGraph formation.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset)
          ).Reachable
            (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor
              hinterior offset fragment).1
            (coordinate.symm coordinateIndex).1 := by
  dsimp only
  let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor hinterior
    offset
  let coordinate := carrierCoordinate carrier
  let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior offset
    hcell
  let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
    hinterior offset hcell
  let edgeState := pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt formation corridor hinterior
    offset hcell
  change Fin carrier.card at coordinateIndex
  let output := coordinate
    (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
      offset fragment)
  change SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
      output coordinateIndex ↔
    formation.annular.RS.edgeOf (coordinate.symm coordinateIndex).1 ∈
        pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset ∧
      formation.annular.RS.edgeOf (coordinate.symm coordinateIndex).1 ∉
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior offset ∧
      (faceRegionalDartGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset)
        ).Reachable
          (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor
            hinterior offset fragment).1
          (coordinate.symm coordinateIndex).1
  have hslotDart (dart : {dart // dart ∈ carrier}) :
      sourceLocalLayerSerialFaceFiniteStableSlot code (coordinate dart) =
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation corridor hinterior offset
          hcell dart := by
    rfl
  have hslot :
      sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex =
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation corridor hinterior offset
          hcell (coordinate.symm coordinateIndex) := by
    rw [← hslotDart (coordinate.symm coordinateIndex)]
    simp
  unfold SourceLocalLayerSerialFaceFiniteNewEdgeContributes
  rw [hslot]
  rw [pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt_cellPresent_iff]
  rw [Bool.eq_false_iff]
  rw [pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt_interfacePresent]
  have hnotOld :
      (decide
          (formation.annular.RS.edgeOf (coordinate.symm coordinateIndex).1 ∈
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior offset) ≠
          true) ↔
        formation.annular.RS.edgeOf (coordinate.symm coordinateIndex).1 ∉
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior offset := by
    simp
  rw [hnotOld]
  have hstep :
      SourceLocalLayerSerialFaceFiniteComponentStep state code =
        PointwiseSelectedSourceLocalLayerSerialFaceFiniteComponentStep state
          code := by
    rfl
  constructor
  · rintro ⟨hcellEdge, hnotOldEdge, hfinite⟩
    refine ⟨hcellEdge, hnotOldEdge, ?_⟩
    apply (pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
      formation corridor hinterior offset hcell
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor
          hinterior offset fragment)
        (coordinate.symm coordinateIndex)).2
    rw [hstep] at hfinite
    simpa [state, code, output, coordinate, carrier] using hfinite
  · rintro ⟨hcellEdge, hnotOldEdge, hreachable⟩
    refine ⟨hcellEdge, hnotOldEdge, ?_⟩
    have hfinite :=
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartReachable_iff_finiteClosure
        formation corridor hinterior offset hcell
          (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor
            hinterior offset fragment)
          (coordinate.symm coordinateIndex)).1 hreachable
    rw [← hstep] at hfinite
    simpa [state, code, output, coordinate, carrier] using hfinite

/-- Canonical finite new-edge representatives are in explicit bijection with
the literal distinct new Cell edges of one output component. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceFiniteNewEdgeRepresentativeEquiv
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) :
    let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor
      hinterior offset
    let coordinate := carrierCoordinate carrier
    let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior
      offset hcell
    let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
      hinterior offset hcell
    let edgeState := pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt formation corridor hinterior
      offset hcell
    let output := coordinate
      (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
        offset fragment)
    let semantic := pointwiseSelectedSourceLocalLayerSerialFaceFiniteNewEdgeSemanticAt formation corridor
      hinterior offset hcell output
    {coordinateIndex // coordinateIndex ∈
      sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives state code
        edgeState output semantic} ≃
      {edge // edge ∈ pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt formation corridor
        hinterior offset fragment} := by
  classical
  let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor hinterior
    offset
  let coordinate := carrierCoordinate carrier
  let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior offset
    hcell
  let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
    hinterior offset hcell
  let edgeState := pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt formation corridor hinterior
    offset hcell
  let output := coordinate
    (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
      offset fragment)
  let semantic := pointwiseSelectedSourceLocalLayerSerialFaceFiniteNewEdgeSemanticAt formation corridor
    hinterior offset hcell output
  let representatives :=
    sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives state code edgeState
      output semantic
  let newEdges := pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt formation corridor hinterior
    offset fragment
  have hslotDart (dart : {dart // dart ∈ carrier}) :
      sourceLocalLayerSerialFaceFiniteStableSlot code (coordinate dart) =
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation corridor hinterior offset
          hcell dart := by
    rfl
  have hslot (coordinateIndex : Fin code.vertexCount.val) :
      sourceLocalLayerSerialFaceFiniteStableSlot code coordinateIndex =
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt formation corridor hinterior offset
          hcell (coordinate.symm coordinateIndex) := by
    rw [← hslotDart (coordinate.symm coordinateIndex)]
    simp
  have hsame (left right : Fin code.vertexCount.val) :
      edgeState.samePrimalEdge
          (sourceLocalLayerSerialFaceFiniteStableSlot code left)
          (sourceLocalLayerSerialFaceFiniteStableSlot code right) = true ↔
        formation.annular.RS.edgeOf (coordinate.symm left).1 =
          formation.annular.RS.edgeOf (coordinate.symm right).1 := by
    rw [hslot left, hslot right]
    exact pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt_samePrimalEdge_iff
      formation corridor hinterior offset hcell (coordinate.symm left)
        (coordinate.symm right)
  let toNewEdge : {coordinateIndex // coordinateIndex ∈ representatives} →
      {edge // edge ∈ newEdges} := fun representative => by
    let dart := coordinate.symm representative.1
    refine ⟨formation.annular.RS.edgeOf dart.1, ?_⟩
    have hrepresentative :=
      (mem_sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives_iff state code
        edgeState output semantic representative.1).1 representative.2
    rcases hrepresentative with ⟨hcontributes, _hfixed⟩
    have hliteral :=
      (pointwiseSelectedSourceLocalLayerSerialFaceFiniteNewEdgeContributesAt_iff formation corridor hinterior
        offset hcell fragment representative.1).1 hcontributes
    rw [mem_pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt_iff]
    refine ⟨?_, hliteral.1, hliteral.2.1⟩
    apply (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      formation.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset)
      (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
        offset fragment).1 _).2
    refine ⟨?_, ⟨⟨dart.1, (formation.annular.RS.mem_dartsOn).2 rfl⟩,
      hliteral.2.2⟩⟩
    rw [← pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_union_cell formation corridor
      hinterior offset]
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
    have hedge : formation.annular.RS.edgeOf (coordinate.symm left.1).1 =
        formation.annular.RS.edgeOf (coordinate.symm right.1).1 := by
      exact congrArg Subtype.val heq
    have hrepresentatives :=
      (sourceLocalLayerSerialFaceFiniteNewEdgeRepresentative_eq_iff state code
        edgeState output semantic left.1 right.1 hleftContributes
          hrightContributes).2 ((hsame left.1 right.1).2 hedge)
    rw [hleftFixed, hrightFixed] at hrepresentatives
    exact hrepresentatives.symm
  · intro edge
    have hedge :=
      (mem_pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt_iff formation corridor hinterior
        offset fragment edge.1).1 edge.2
    rcases (mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
      formation.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior offset)
      (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
        offset fragment).1 edge.1).1 hedge.1 with
      ⟨_hedgeOutput, dart, hreachable⟩
    have hdartCell : formation.annular.RS.edgeOf dart.1 ∈
        pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset := by
      rw [(formation.annular.RS.mem_dartsOn).1 dart.2]
      exact hedge.2.1
    let carrierDart : {dart // dart ∈ carrier} :=
      ⟨dart.1, Finset.mem_union_left _
        ((GoertzelV24RotationFaceRegionalDartCarrier.mem_dartsOnEdges_iff
          formation.annular.RS _ dart.1).2 hdartCell)⟩
    let coordinateIndex := coordinate carrierDart
    have hcontributes :
        SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
          output coordinateIndex := by
      apply (pointwiseSelectedSourceLocalLayerSerialFaceFiniteNewEdgeContributesAt_iff formation corridor
        hinterior offset hcell fragment coordinateIndex).2
      constructor
      · change formation.annular.RS.edgeOf
            (coordinate.symm (coordinate carrierDart)).1 ∈
          pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset
        rw [coordinate.symm_apply_apply]
        exact hdartCell
      constructor
      · change formation.annular.RS.edgeOf
            (coordinate.symm (coordinate carrierDart)).1 ∉
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation corridor hinterior offset
        rw [coordinate.symm_apply_apply]
        change formation.annular.RS.edgeOf dart.1 ∉ _
        rw [(formation.annular.RS.mem_dartsOn).1 dart.2]
        exact hedge.2.2
      · change (faceRegionalDartGraph formation.annular.RS
            (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation corridor hinterior
              offset)).Reachable
          (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor
            hinterior offset fragment).1
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
    have hedgeOf : formation.annular.RS.edgeOf dart.1 = edge.1 :=
      (formation.annular.RS.mem_dartsOn).1 dart.2
    exact hsameEdge.trans (by
      simpa [coordinateIndex, carrierDart] using hedgeOf)

/-- The finite representative count is exactly the number of literal distinct
new Cell edges in the selected output component. -/
theorem card_pointwiseSelectedSourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives_eq
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor hinterior offset).card ≤ 6)
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation corridor hinterior
      offset) :
    let carrier := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor
      hinterior offset
    let coordinate := carrierCoordinate carrier
    let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior
      offset hcell
    let state := pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor
      hinterior offset hcell
    let edgeState := pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt formation corridor hinterior
      offset hcell
    let output := coordinate
      (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
        offset fragment)
    let semantic := pointwiseSelectedSourceLocalLayerSerialFaceFiniteNewEdgeSemanticAt formation corridor
      hinterior offset hcell output
    (sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives state code edgeState
      output semantic).card =
      (pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt formation corridor hinterior offset
        fragment).card := by
  classical
  let representatives := sourceLocalLayerSerialFaceFiniteNewEdgeRepresentatives
    (pointwiseSelectedSourceLocalLayerSerialFacePrefixAttachmentStateAt formation corridor hinterior offset
      hcell)
    (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation corridor hinterior offset hcell)
    (pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt formation corridor hinterior offset hcell)
    ((carrierCoordinate
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor hinterior offset))
      (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor hinterior
        offset fragment))
    (pointwiseSelectedSourceLocalLayerSerialFaceFiniteNewEdgeSemanticAt formation corridor hinterior offset
      hcell ((carrierCoordinate
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation corridor hinterior offset))
        (pointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentTransitionDartAt formation corridor
          hinterior offset fragment)))
  let newEdges := pointwiseSelectedSourceLocalLayerSerialFaceNewComponentEdgesAt formation corridor hinterior
    offset fragment
  calc
    representatives.card = Fintype.card {x // x ∈ representatives} :=
      (Fintype.card_coe representatives).symm
    _ = Fintype.card {edge // edge ∈ newEdges} :=
      Fintype.card_congr
        (pointwiseSelectedSourceLocalLayerSerialFaceFiniteNewEdgeRepresentativeEquiv formation corridor
          hinterior offset hcell fragment)
    _ = newEdges.card := Fintype.card_coe newEdges

end

end GoertzelV24ClosedWebPointwiseSelectedFaceFiniteNewEdgeAdequacy

end Mettapedia.GraphTheory.FourColor
