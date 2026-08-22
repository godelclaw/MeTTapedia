import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFaceResidualState

/-!
# The finite facial collar of an actual Cell boundary rebase

The regional edge sets change on at most four primal edges.  Facial adjacency
is a step of the face permutation, so a sound update carrier must also retain
the immediate predecessor and successor dart of every changed occurrence.
This file constructs that one-step collar and proves its uniform bound of
twenty-four darts.

It also proves the exact locality statement needed by the next recurrence:
outside the collar, the old and new regional face graphs have identical
adjacency.  Thus the eight changed occurrences are the observed coordinates,
while the twenty-four-dart collar is the finite computation support.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseFaceCollarEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The literal dart occurrences over the at most four changed primal edges. -/
noncomputable def sourceLocalLayerBoundaryRebaseChangedFaceDartsAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) : Finset web.annular.RS.D :=
  Finset.univ.filter fun dart =>
    web.annular.RS.edgeOf dart ∈
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext

@[simp]
theorem mem_sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (dart : web.annular.RS.D) :
    dart ∈ sourceLocalLayerBoundaryRebaseChangedFaceDartsAt corridor hunique
        offset hnext ↔
      web.annular.RS.edgeOf dart ∈
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext := by
  simp [sourceLocalLayerBoundaryRebaseChangedFaceDartsAt]

/-- There are at most two darts over each of the four changed edges. -/
theorem card_sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_le_eight
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerBoundaryRebaseChangedFaceDartsAt corridor hunique offset
      hnext).card ≤ 8 := by
  simpa [sourceLocalLayerBoundaryRebaseChangedFaceDartsAt,
    Fintype.card_subtype] using
      (sourceLocalLayerBoundaryRebaseFaceOccurrenceAt_card_le_eight
        corridor hunique offset hnext)

/-- One-step facial collar: every changed occurrence and its two neighbors in
the face permutation. -/
noncomputable def sourceLocalLayerBoundaryRebaseFaceCollarAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) : Finset web.annular.RS.D :=
  (sourceLocalLayerBoundaryRebaseChangedFaceDartsAt corridor hunique offset
    hnext).biUnion fun dart =>
      {dart, web.annular.RS.phi dart, web.annular.RS.phi.symm dart}

/-- The finite computation support has at most twenty-four dart occurrences. -/
theorem card_sourceLocalLayerBoundaryRebaseFaceCollarAt_le_twentyFour
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext
      ).card ≤ 24 := by
  let changed := sourceLocalLayerBoundaryRebaseChangedFaceDartsAt corridor
    hunique offset hnext
  calc
    (sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext
      ).card ≤ changed.card * 3 := by
        apply Finset.card_biUnion_le_card_mul
        intro dart hdart
        exact (Finset.card_insert_le _ _).trans
          (Nat.succ_le_succ <| (Finset.card_insert_le _ _).trans_eq <| by
            rw [Finset.card_singleton])
    _ ≤ 8 * 3 := Nat.mul_le_mul_right 3
      (card_sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_le_eight
        corridor hunique offset hnext)
    _ = 24 := by omega

theorem sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    sourceLocalLayerBoundaryRebaseChangedFaceDartsAt corridor hunique offset
        hnext ⊆
      sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset
        hnext := by
  intro dart hdart
  rw [sourceLocalLayerBoundaryRebaseFaceCollarAt, Finset.mem_biUnion]
  exact ⟨dart, hdart, by simp⟩

theorem sourceLocalLayerBoundaryRebaseFaceCollarAt_phi_mem
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    {dart : web.annular.RS.D}
    (hdart : dart ∈ sourceLocalLayerBoundaryRebaseChangedFaceDartsAt
      corridor hunique offset hnext) :
    web.annular.RS.phi dart ∈
      sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset
        hnext := by
  rw [sourceLocalLayerBoundaryRebaseFaceCollarAt, Finset.mem_biUnion]
  exact ⟨dart, hdart, by simp⟩

theorem sourceLocalLayerBoundaryRebaseFaceCollarAt_phi_symm_mem
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    {dart : web.annular.RS.D}
    (hdart : dart ∈ sourceLocalLayerBoundaryRebaseChangedFaceDartsAt
      corridor hunique offset hnext) :
    web.annular.RS.phi.symm dart ∈
      sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset
        hnext := by
  rw [sourceLocalLayerBoundaryRebaseFaceCollarAt, Finset.mem_biUnion]
  exact ⟨dart, hdart, by simp⟩

/-- The common old/new region after removing the finite changed support. -/
noncomputable def sourceLocalLayerBoundaryRebaseFaceCoreRegionAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) : Finset G.edgeSet :=
  sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset \
    sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext

theorem sourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    sourceLocalLayerBoundaryRebaseFaceCoreRegionAt corridor hunique offset hnext =
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext) \
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext := by
  ext edge
  simp only [sourceLocalLayerBoundaryRebaseFaceCoreRegionAt,
    Finset.mem_sdiff]
  by_cases hswitch : edge ∈
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext
  · simp [hswitch]
  · simp only [hswitch, not_false_eq_true, and_true]
    exact
      sourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
        corridor hunique offset hnext edge hswitch

/-- If one endpoint of a regional facial adjacency lies over a changed edge,
both dart endpoints lie in the one-step facial collar. -/
theorem sourceLocalLayerBoundaryRebaseFaceCollarAt_of_adj_of_changed
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (region : Finset G.edgeSet) {left right : web.annular.RS.D}
    (hadj : (faceRegionalDartGraph web.annular.RS region).Adj left right)
    (hchanged : web.annular.RS.edgeOf left ∈
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext) :
    left ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset
        hnext ∧
      right ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique
        offset hnext := by
  have hleftChanged : left ∈
      sourceLocalLayerBoundaryRebaseChangedFaceDartsAt corridor hunique offset
        hnext := by
    simpa using hchanged
  have hleftCollar :=
    sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar corridor
      hunique offset hnext hleftChanged
  rcases (faceRegionalDartGraph_adj web.annular.RS region left right).1 hadj with
    ⟨_hne, hstep, _hleftRegion, _hrightRegion⟩
  refine ⟨hleftCollar, ?_⟩
  rcases hstep with hforward | hbackward
  · subst right
    exact sourceLocalLayerBoundaryRebaseFaceCollarAt_phi_mem corridor hunique
      offset hnext hleftChanged
  · have hsymm : web.annular.RS.phi.symm left = right := by
      apply web.annular.RS.phi.injective
      simp [hbackward]
    rw [← hsymm]
    exact sourceLocalLayerBoundaryRebaseFaceCollarAt_phi_symm_mem corridor
      hunique offset hnext hleftChanged

/-- Outside the finite facial collar, predecessor and successor facial
adjacency are definitionally the same local turn with the same two regional
membership facts. -/
theorem sourceLocalLayerBoundaryRebase_faceAdj_iff_next_of_outside_collar
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : web.annular.RS.D)
    (hleftOutside : left ∉
      sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext)
    (hrightOutside : right ∉
      sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext) :
    (faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      ).Adj left right ↔
    (faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext))).Adj left right := by
  have hleftSwitch : web.annular.RS.edgeOf left ∉
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext := by
    intro hswitch
    apply hleftOutside
    apply sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar
      corridor hunique offset hnext
    simpa using hswitch
  have hrightSwitch : web.annular.RS.edgeOf right ∉
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext := by
    intro hswitch
    apply hrightOutside
    apply sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar
      corridor hunique offset hnext
    simpa using hswitch
  have hleftRegion :=
    sourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
      corridor hunique offset hnext (web.annular.RS.edgeOf left) hleftSwitch
  have hrightRegion :=
    sourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
      corridor hunique offset hnext (web.annular.RS.edgeOf right) hrightSwitch
  simp only [faceRegionalDartGraph_adj]
  constructor
  · rintro ⟨hne, hstep, hl, hr⟩
    exact ⟨hne, hstep, hleftRegion.mp hl, hrightRegion.mp hr⟩
  · rintro ⟨hne, hstep, hl, hr⟩
    exact ⟨hne, hstep, hleftRegion.mpr hl, hrightRegion.mpr hr⟩

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
