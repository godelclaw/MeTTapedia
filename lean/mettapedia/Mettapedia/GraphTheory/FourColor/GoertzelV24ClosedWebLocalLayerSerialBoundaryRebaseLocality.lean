import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalFaceBoundaryAdjacency
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebase

/-!
# Source-local historical crossing locality at one Cell rebase

The opened closed-web carrier has degree-one boundary stubs, so the older
serial-rebase locality theorem cannot be reused with its global cubicity and
two-sidedness assumptions.  The corridor crossings themselves lie on named
interior faces, however, and adjacency of two distinct primal edges is locally
cubic at their common vertex.  This file reruns the geodesic argument through
that local theorem.

The result is deliberately only about the four literal crossing portals.  It
does not yet claim that every edge shared by a strict historical Cell and the
successor transition carrier is one of those portals; that is the next overlap
localization theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseLocality

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalFaceBoundaryAdjacency
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Every incoming crossing of a literal source Cell lies on that Cell's
named corridor-centre face. -/
theorem sourceLocalLayerLeftCrossingAt_mem_centerFaceBoundary
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    sourceLocalLayerLeftCrossingAt corridor hunique offset step ∈
      orbitFaceBoundary web.annular.RS
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt (sourceLocalLayerInteriorAt offset).center).1 := by
  let layers := sourceLocalLayerPairAt corridor hunique offset
  let cutStep : Fin layers.firstLayer.walk.length :=
    ⟨step.val, by
      simpa [LocalLayerPair.firstLayer, LocalLayerPair.firstWalk] using
        step.isLt⟩
  have hcases : cutStep.val = 0 ∨ cutStep.val = 1 := by
    change step.val = 0 ∨ step.val = 1
    omega
  change dualWalkCrossingEdge
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
    layers.firstLayer.walk cutStep ∈ _
  rcases hcases with hzero | hone
  · have hstep : cutStep = ⟨0, by
        simp [layers, sourceLocalLayerPairAt, LocalLayerPair.firstLayer,
          LocalLayerPair.firstWalk]⟩ := by
      apply Fin.ext
      exact hzero
    rw [hstep]
    simpa [layers, sourceLocalLayerPairAt, LocalLayerPair.firstLayer,
      LocalLayerPair.firstWalk] using
      (dualWalkCrossingEdge_mem_rightFace
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        layers.firstLayer.walk
        ⟨0, by
          simp [layers, sourceLocalLayerPairAt, LocalLayerPair.firstLayer,
            LocalLayerPair.firstWalk]⟩)
  · have hstep : cutStep = ⟨1, by
        simp [layers, sourceLocalLayerPairAt, LocalLayerPair.firstLayer,
          LocalLayerPair.firstWalk]⟩ := by
      apply Fin.ext
      exact hone
    rw [hstep]
    simpa [layers, sourceLocalLayerPairAt, LocalLayerPair.firstLayer,
      LocalLayerPair.firstWalk] using
      (dualWalkCrossingEdge_mem_leftFace
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        layers.firstLayer.walk
        ⟨1, by
          simp [layers, sourceLocalLayerPairAt, LocalLayerPair.firstLayer,
            LocalLayerPair.firstWalk]⟩)

/-- Every outgoing crossing of a literal source Cell lies on the successor
corridor-centre face of that Cell. -/
theorem sourceLocalLayerRightCrossingAt_mem_nextCenterFaceBoundary
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    sourceLocalLayerRightCrossingAt corridor hunique offset step ∈
      orbitFaceBoundary web.annular.RS
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt
            (nextCorridorInterior (sourceLocalLayerInteriorAt offset)
              (sourceLocalLayerInteriorAt_hasNext offset)).center).1 := by
  let layers := sourceLocalLayerPairAt corridor hunique offset
  let cutStep : Fin layers.secondLayer.walk.length :=
    ⟨step.val, by
      simpa [LocalLayerPair.secondLayer, LocalLayerPair.secondWalk] using
        step.isLt⟩
  have hcases : cutStep.val = 0 ∨ cutStep.val = 1 := by
    change step.val = 0 ∨ step.val = 1
    omega
  change dualWalkCrossingEdge
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
    layers.secondLayer.walk cutStep ∈ _
  rcases hcases with hzero | hone
  · have hstep : cutStep = ⟨0, by
        simp [layers, sourceLocalLayerPairAt, LocalLayerPair.secondLayer,
          LocalLayerPair.secondWalk]⟩ := by
      apply Fin.ext
      exact hzero
    rw [hstep]
    simpa [layers, sourceLocalLayerPairAt, LocalLayerPair.secondLayer,
      LocalLayerPair.secondWalk] using
      (dualWalkCrossingEdge_mem_rightFace
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        layers.secondLayer.walk
        ⟨0, by
          simp [layers, sourceLocalLayerPairAt, LocalLayerPair.secondLayer,
            LocalLayerPair.secondWalk]⟩)
  · have hstep : cutStep = ⟨1, by
        simp [layers, sourceLocalLayerPairAt, LocalLayerPair.secondLayer,
          LocalLayerPair.secondWalk]⟩ := by
      apply Fin.ext
      exact hone
    rw [hstep]
    simpa [layers, sourceLocalLayerPairAt, LocalLayerPair.secondLayer,
      LocalLayerPair.secondWalk] using
      (dualWalkCrossingEdge_mem_leftFace
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        layers.secondLayer.walk
        ⟨1, by
          simp [layers, sourceLocalLayerPairAt, LocalLayerPair.secondLayer,
            LocalLayerPair.secondWalk]⟩)

/-- A strict historical incoming crossing adjacent to the successor incoming
presentation must be the current Cell's incoming crossing. -/
theorem sourceLocalLayerLeftCrossingAt_index_eq_of_lt_of_adj_nextLeftCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset historical : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hhistorical : historical.val < offset.val + 1)
    (oldStep newStep : Fin 2)
    (hadj : web.annular.RS.edgeAdjacencyGraph.Adj
      (sourceLocalLayerLeftCrossingAt corridor hunique historical oldStep)
      (sourceLocalLayerLeftCrossingAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) newStep)) :
    historical.val = offset.val := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let oldFace := skeleton.faceAt (sourceLocalLayerInteriorAt historical).center
  let newOffset := sourceLocalLayerNextOffset offset hnext
  let newFace := skeleton.faceAt (sourceLocalLayerInteriorAt newOffset).center
  have hold : sourceLocalLayerLeftCrossingAt corridor hunique historical oldStep
      ∈ orbitFaceBoundary web.annular.RS oldFace.1 := by
    simpa [oldFace, skeleton] using
      sourceLocalLayerLeftCrossingAt_mem_centerFaceBoundary corridor hunique
        historical oldStep
  have hnew : sourceLocalLayerLeftCrossingAt corridor hunique newOffset newStep
      ∈ orbitFaceBoundary web.annular.RS newFace.1 := by
    simpa [newFace, skeleton] using
      sourceLocalLayerLeftCrossingAt_mem_centerFaceBoundary corridor hunique
        newOffset newStep
  have hfacesNe : oldFace.1 ≠ newFace.1 := by
    intro hfaces
    have hindices : (sourceLocalLayerInteriorAt historical).center =
        (sourceLocalLayerInteriorAt newOffset).center :=
      skeleton.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change historical.val + 1 = newOffset.val + 1 at hvalues
    have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
    rw [hnewOffsetVal] at hvalues
    omega
  have hfaceAdj := interiorDualGraph_adj_of_edgeAdjacencyGraph_adj web
    hfacesNe hold hnew hadj
  by_contra hne
  have hseparated :
      (sourceLocalLayerInteriorAt historical).center.val + 1 <
        (sourceLocalLayerInteriorAt newOffset).center.val := by
    change historical.val + 1 + 1 < newOffset.val + 1
    have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
    rw [hnewOffsetVal]
    omega
  exact (skeleton.separated_not_adjacent _ _ hseparated) hfaceAdj

/-- A strict historical outgoing crossing adjacent to the successor incoming
presentation belongs to the current Cell or its immediate predecessor. -/
theorem sourceLocalLayerRightCrossingAt_index_eq_or_succ_eq_of_lt_of_adj_nextLeftCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset historical : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hhistorical : historical.val < offset.val + 1)
    (oldStep newStep : Fin 2)
    (hadj : web.annular.RS.edgeAdjacencyGraph.Adj
      (sourceLocalLayerRightCrossingAt corridor hunique historical oldStep)
      (sourceLocalLayerLeftCrossingAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) newStep)) :
    historical.val = offset.val ∨ historical.val + 1 = offset.val := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let oldFace := skeleton.faceAt
    (nextCorridorInterior (sourceLocalLayerInteriorAt historical)
      (sourceLocalLayerInteriorAt_hasNext historical)).center
  let newOffset := sourceLocalLayerNextOffset offset hnext
  let newFace := skeleton.faceAt (sourceLocalLayerInteriorAt newOffset).center
  have hold : sourceLocalLayerRightCrossingAt corridor hunique historical oldStep
      ∈ orbitFaceBoundary web.annular.RS oldFace.1 := by
    simpa [oldFace, skeleton] using
      sourceLocalLayerRightCrossingAt_mem_nextCenterFaceBoundary corridor
        hunique historical oldStep
  have hnew : sourceLocalLayerLeftCrossingAt corridor hunique newOffset newStep
      ∈ orbitFaceBoundary web.annular.RS newFace.1 := by
    simpa [newFace, skeleton] using
      sourceLocalLayerLeftCrossingAt_mem_centerFaceBoundary corridor hunique
        newOffset newStep
  by_cases hfaces : oldFace.1 = newFace.1
  · left
    have hindices :
        (nextCorridorInterior (sourceLocalLayerInteriorAt historical)
          (sourceLocalLayerInteriorAt_hasNext historical)).center =
        (sourceLocalLayerInteriorAt newOffset).center :=
      skeleton.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change historical.val + 2 = newOffset.val + 1 at hvalues
    have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
    rw [hnewOffsetVal] at hvalues
    omega
  · have hfaceAdj := interiorDualGraph_adj_of_edgeAdjacencyGraph_adj web
      hfaces hold hnew hadj
    by_cases hnear : historical.val + 1 = offset.val
    · exact Or.inr hnear
    · have hcurrentNe : historical.val ≠ offset.val := by
        intro hcurrent
        apply hfaces
        have hindices :
            (nextCorridorInterior (sourceLocalLayerInteriorAt historical)
              (sourceLocalLayerInteriorAt_hasNext historical)).center =
            (sourceLocalLayerInteriorAt newOffset).center := by
          apply Fin.ext
          change historical.val + 2 = newOffset.val + 1
          have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
          rw [hnewOffsetVal, hcurrent]
        exact congrArg Subtype.val (congrArg skeleton.faceAt hindices)
      have hseparated :
          (nextCorridorInterior (sourceLocalLayerInteriorAt historical)
              (sourceLocalLayerInteriorAt_hasNext historical)).center.val + 1 <
            (sourceLocalLayerInteriorAt newOffset).center.val := by
        change historical.val + 2 + 1 < newOffset.val + 1
        have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
        rw [hnewOffsetVal]
        omega
      exact False.elim
        ((skeleton.separated_not_adjacent _ _ hseparated) hfaceAdj)

/-- Two named faces containing related primal edges are adjacent in the
interior dual.  Equality of the primal edges uses the two-face incidence
bound; adjacency uses local cubicity at their common vertex. -/
private theorem interiorDualGraph_adj_of_eq_or_edgeAdjacencyGraph_adj
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    {oldFace newFace : OrbitFace web.annular.RS}
    {oldEdge newEdge : G.edgeSet}
    (hfaces : oldFace ≠ newFace)
    (hold : oldEdge ∈ orbitFaceBoundary web.annular.RS oldFace)
    (hnew : newEdge ∈ orbitFaceBoundary web.annular.RS newFace)
    (hrel : oldEdge = newEdge ∨
      web.annular.RS.edgeAdjacencyGraph.Adj oldEdge newEdge) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        ⟨oldFace, Finset.mem_univ _⟩ ⟨newFace, Finset.mem_univ _⟩ := by
  rcases hrel with heq | hadj
  · subst newEdge
    exact
      interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (orbitFace_incidence_le_two web.annular.RS) hfaces hold hnew
  · exact interiorDualGraph_adj_of_edgeAdjacencyGraph_adj web hfaces
      hold hnew hadj

/-- A historical incoming crossing that is equal or adjacent to the successor
incoming presentation belongs to the current Cell.  This is the exact
same-edge-or-adjacent-edge relation emitted by the expanded collar decoder. -/
theorem sourceLocalLayerLeftCrossingAt_index_eq_of_lt_of_eq_or_adj_nextLeftCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset historical : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hhistorical : historical.val < offset.val + 1)
    (oldStep newStep : Fin 2)
    (hrel :
      sourceLocalLayerLeftCrossingAt corridor hunique historical oldStep =
          sourceLocalLayerLeftCrossingAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext) newStep ∨
        web.annular.RS.edgeAdjacencyGraph.Adj
          (sourceLocalLayerLeftCrossingAt corridor hunique historical oldStep)
          (sourceLocalLayerLeftCrossingAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext) newStep)) :
    historical.val = offset.val := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let oldFace := skeleton.faceAt (sourceLocalLayerInteriorAt historical).center
  let newOffset := sourceLocalLayerNextOffset offset hnext
  let newFace := skeleton.faceAt (sourceLocalLayerInteriorAt newOffset).center
  have hold : sourceLocalLayerLeftCrossingAt corridor hunique historical oldStep
      ∈ orbitFaceBoundary web.annular.RS oldFace.1 := by
    simpa [oldFace, skeleton] using
      sourceLocalLayerLeftCrossingAt_mem_centerFaceBoundary corridor hunique
        historical oldStep
  have hnew : sourceLocalLayerLeftCrossingAt corridor hunique newOffset newStep
      ∈ orbitFaceBoundary web.annular.RS newFace.1 := by
    simpa [newFace, skeleton] using
      sourceLocalLayerLeftCrossingAt_mem_centerFaceBoundary corridor hunique
        newOffset newStep
  have hfacesNe : oldFace.1 ≠ newFace.1 := by
    intro hfaces
    have hindices : (sourceLocalLayerInteriorAt historical).center =
        (sourceLocalLayerInteriorAt newOffset).center :=
      skeleton.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change historical.val + 1 = newOffset.val + 1 at hvalues
    have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
    rw [hnewOffsetVal] at hvalues
    omega
  have hfaceAdj := interiorDualGraph_adj_of_eq_or_edgeAdjacencyGraph_adj web
    hfacesNe hold hnew hrel
  by_contra hne
  have hseparated :
      (sourceLocalLayerInteriorAt historical).center.val + 1 <
        (sourceLocalLayerInteriorAt newOffset).center.val := by
    change historical.val + 1 + 1 < newOffset.val + 1
    have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
    rw [hnewOffsetVal]
    omega
  exact (skeleton.separated_not_adjacent _ _ hseparated) hfaceAdj

/-- A historical outgoing crossing that is equal or adjacent to the successor
incoming presentation belongs to the current Cell or its immediate
predecessor. -/
theorem sourceLocalLayerRightCrossingAt_index_eq_or_succ_eq_of_lt_of_eq_or_adj_nextLeftCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset historical : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hhistorical : historical.val < offset.val + 1)
    (oldStep newStep : Fin 2)
    (hrel :
      sourceLocalLayerRightCrossingAt corridor hunique historical oldStep =
          sourceLocalLayerLeftCrossingAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext) newStep ∨
        web.annular.RS.edgeAdjacencyGraph.Adj
          (sourceLocalLayerRightCrossingAt corridor hunique historical oldStep)
          (sourceLocalLayerLeftCrossingAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext) newStep)) :
    historical.val = offset.val ∨ historical.val + 1 = offset.val := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let oldFace := skeleton.faceAt
    (nextCorridorInterior (sourceLocalLayerInteriorAt historical)
      (sourceLocalLayerInteriorAt_hasNext historical)).center
  let newOffset := sourceLocalLayerNextOffset offset hnext
  let newFace := skeleton.faceAt (sourceLocalLayerInteriorAt newOffset).center
  have hold : sourceLocalLayerRightCrossingAt corridor hunique historical oldStep
      ∈ orbitFaceBoundary web.annular.RS oldFace.1 := by
    simpa [oldFace, skeleton] using
      sourceLocalLayerRightCrossingAt_mem_nextCenterFaceBoundary corridor
        hunique historical oldStep
  have hnew : sourceLocalLayerLeftCrossingAt corridor hunique newOffset newStep
      ∈ orbitFaceBoundary web.annular.RS newFace.1 := by
    simpa [newFace, skeleton] using
      sourceLocalLayerLeftCrossingAt_mem_centerFaceBoundary corridor hunique
        newOffset newStep
  by_cases hfaces : oldFace.1 = newFace.1
  · left
    have hindices :
        (nextCorridorInterior (sourceLocalLayerInteriorAt historical)
          (sourceLocalLayerInteriorAt_hasNext historical)).center =
        (sourceLocalLayerInteriorAt newOffset).center :=
      skeleton.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change historical.val + 2 = newOffset.val + 1 at hvalues
    have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
    rw [hnewOffsetVal] at hvalues
    omega
  · have hfaceAdj :=
      interiorDualGraph_adj_of_eq_or_edgeAdjacencyGraph_adj web hfaces
        hold hnew hrel
    by_cases hnear : historical.val + 1 = offset.val
    · exact Or.inr hnear
    · have hcurrentNe : historical.val ≠ offset.val := by
        intro hcurrent
        apply hfaces
        have hindices :
            (nextCorridorInterior (sourceLocalLayerInteriorAt historical)
              (sourceLocalLayerInteriorAt_hasNext historical)).center =
            (sourceLocalLayerInteriorAt newOffset).center := by
          apply Fin.ext
          change historical.val + 2 = newOffset.val + 1
          have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
          rw [hnewOffsetVal, hcurrent]
        exact congrArg Subtype.val (congrArg skeleton.faceAt hindices)
      have hseparated :
          (nextCorridorInterior (sourceLocalLayerInteriorAt historical)
              (sourceLocalLayerInteriorAt_hasNext historical)).center.val + 1 <
            (sourceLocalLayerInteriorAt newOffset).center.val := by
        change historical.val + 2 + 1 < newOffset.val + 1
        have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
        rw [hnewOffsetVal]
        omega
      exact False.elim
        ((skeleton.separated_not_adjacent _ _ hseparated) hfaceAdj)

/-- No strict historical incoming crossing is equal or adjacent to the
successor incoming presentation. -/
theorem not_sourceLocalLayerLeftCrossingAt_eq_or_adj_nextLeftCrossing_of_lt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset historical : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hhistorical : historical.val < offset.val)
    (oldStep newStep : Fin 2)
    (hrel :
      sourceLocalLayerLeftCrossingAt corridor hunique historical oldStep =
          sourceLocalLayerLeftCrossingAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext) newStep ∨
        web.annular.RS.edgeAdjacencyGraph.Adj
          (sourceLocalLayerLeftCrossingAt corridor hunique historical oldStep)
          (sourceLocalLayerLeftCrossingAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext) newStep)) : False := by
  have hindex :=
    sourceLocalLayerLeftCrossingAt_index_eq_of_lt_of_eq_or_adj_nextLeftCrossing
      web corridor hunique offset historical hnext (by omega) oldStep newStep
        hrel
  omega

/-- A strict historical outgoing crossing equal or adjacent to the successor
incoming presentation is the immediate predecessor's outgoing crossing. -/
theorem sourceLocalLayerRightCrossingAt_succ_eq_of_lt_of_eq_or_adj_nextLeftCrossing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset historical : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hhistorical : historical.val < offset.val)
    (oldStep newStep : Fin 2)
    (hrel :
      sourceLocalLayerRightCrossingAt corridor hunique historical oldStep =
          sourceLocalLayerLeftCrossingAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext) newStep ∨
        web.annular.RS.edgeAdjacencyGraph.Adj
          (sourceLocalLayerRightCrossingAt corridor hunique historical oldStep)
          (sourceLocalLayerLeftCrossingAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext) newStep)) :
    historical.val + 1 = offset.val := by
  rcases
      sourceLocalLayerRightCrossingAt_index_eq_or_succ_eq_of_lt_of_eq_or_adj_nextLeftCrossing
        web corridor hunique offset historical hnext (by omega) oldStep newStep
          hrel with hcurrent | himmediate
  · omega
  · exact himmediate

end

end GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseLocality

end Mettapedia.GraphTheory.FourColor
