import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceBoundaryAdjacency
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseTrackedEscape

/-!
# Bounded historical locality of a tracked serial rebase

The true old-prefix frontier is a union of literal historical Cell
interfaces.  A priori, the parity escape theorem may return any one of those
interfaces.  The retained source geodesic makes the relevant history bounded:
an edge of the successor input presentation can be adjacent only to an input
edge of the current Cell, or to an output edge of the current or immediately
preceding Cell.

The proof is local.  Each displayed crossing lies on its named corridor
centre face.  Adjacent primal edges in a cubic cyclic two-sided rotation
system force those centre faces to be equal or adjacent in the facial dual,
while the source corridor excludes adjacency beyond one geodesic step.

This is a locality theorem for the rebase letter.  It does not yet identify
the remaining three bounded interface cases with the two current profile
ports, and it does not assert full one-Cell semantic factorization.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CubicFaceBoundaryAdjacency
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseTrackedLocalityEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- Every input crossing of a literal Cell lies on that Cell's centre face. -/
theorem localLayerPrefixCrossing_mem_centerLayerFaceBoundary
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    interface.localLayerPrefixCrossing step ∈ orbitFaceBoundary
      embedded.cellulation.rotation.toRotationSystem
      interface.centerLayerFace.1 := by
  let cutStep : Fin interface.localLayer.walk.length :=
    Fin.cast interface.localLayer_walk_length_eq_two.symm step
  have hcases : cutStep.val = 0 ∨ cutStep.val = 1 := by
    change step.val = 0 ∨ step.val = 1
    omega
  change dualWalkCrossingEdge
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    interface.localLayer.walk cutStep ∈ _
  rcases hcases with hzero | hone
  · have hstep : cutStep = ⟨0, by
        rw [interface.localLayer_walk_length_eq_two]
        omega⟩ := by
      apply Fin.ext
      exact hzero
    rw [hstep]
    simpa [localLayer, localLayerWalk] using
      (dualWalkCrossingEdge_mem_rightFace
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        interface.localLayer.walk
        ⟨0, by rw [interface.localLayer_walk_length_eq_two]; omega⟩)
  · have hstep : cutStep = ⟨1, by
        rw [interface.localLayer_walk_length_eq_two]
        omega⟩ := by
      apply Fin.ext
      exact hone
    rw [hstep]
    simpa [localLayer, localLayerWalk] using
      (dualWalkCrossingEdge_mem_leftFace
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        interface.localLayer.walk
        ⟨1, by rw [interface.localLayer_walk_length_eq_two]; omega⟩)

/-- Every output crossing of a literal Cell lies on the successor centre
face of that Cell. -/
theorem nextLocalLayerPrefixCrossing_mem_nextCenterLayerFaceBoundary
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    interface.nextLocalLayerPrefixCrossing step ∈ orbitFaceBoundary
      embedded.cellulation.rotation.toRotationSystem
      interface.nextCenterLayerFace.1 := by
  let cutStep : Fin interface.nextLocalLayer.walk.length :=
    Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm step
  have hcases : cutStep.val = 0 ∨ cutStep.val = 1 := by
    change step.val = 0 ∨ step.val = 1
    omega
  change dualWalkCrossingEdge
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    interface.nextLocalLayer.walk cutStep ∈ _
  rcases hcases with hzero | hone
  · have hstep : cutStep = ⟨0, by
        rw [interface.nextLocalLayer_walk_length_eq_two]
        omega⟩ := by
      apply Fin.ext
      exact hzero
    rw [hstep]
    simpa [nextLocalLayer, nextLocalLayerWalk] using
      (dualWalkCrossingEdge_mem_rightFace
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        interface.nextLocalLayer.walk
        ⟨0, by rw [interface.nextLocalLayer_walk_length_eq_two]; omega⟩)
  · have hstep : cutStep = ⟨1, by
        rw [interface.nextLocalLayer_walk_length_eq_two]
        omega⟩ := by
      apply Fin.ext
      exact hone
    rw [hstep]
    simpa [nextLocalLayer, nextLocalLayerWalk] using
      (dualWalkCrossingEdge_mem_leftFace
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        interface.nextLocalLayer.walk
        ⟨1, by rw [interface.nextLocalLayer_walk_length_eq_two]; omega⟩)

end SourceConsecutiveSlabInterface

/-- A historical input crossing adjacent to the successor rebase presentation
must belong to the current Cell. -/
theorem sourceSlabInputCrossing_index_eq_of_lt_cut_of_adj_rebaseCrossing
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset historical : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hhistorical : historical.val < offset.val + 1)
    (oldStep newStep : Fin 2)
    (hadj : embedded.cellulation.rotation.toRotationSystem.edgeAdjacencyGraph.Adj
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        historical).localLayerPrefixCrossing oldStep)
      (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
        hrotation htwoSided hunique offset hnext newStep)) :
    historical.val = offset.val := by
  let corridor := realization.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton
  let oldFace := corridor.faceAt (sourceSlabLeftInterior historical).center
  let newOffset := sourceCorridorSerialNextOffset offset hnext
  let newFace := corridor.faceAt (sourceSlabLeftInterior newOffset).center
  have hold :
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        historical).localLayerPrefixCrossing oldStep ∈
        orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
          oldFace.1 := by
    simpa [oldFace, corridor, SourceConsecutiveSlabInterface.centerLayerFace]
      using (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique historical).localLayerPrefixCrossing_mem_centerLayerFaceBoundary
          oldStep
  have hnew :
      sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
          hrotation htwoSided hunique offset hnext newStep ∈
        orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
          newFace.1 := by
    simpa [sourceCorridorSerialBoundaryRebaseCrossingAt, newFace, newOffset,
      corridor, SourceConsecutiveSlabInterface.centerLayerFace] using
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        newOffset).localLayerPrefixCrossing_mem_centerLayerFaceBoundary newStep
  have hfacesNe : oldFace.1 ≠ newFace.1 := by
    intro hfaces
    have hindices : (sourceSlabLeftInterior historical).center =
        (sourceSlabLeftInterior newOffset).center :=
      corridor.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change historical.val + 1 = newOffset.val + 1 at hvalues
    have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
    rw [hnewOffsetVal] at hvalues
    omega
  have hfaceAdj := interiorDualGraph_adj_of_edgeAdjacencyGraph_adj
    embedded.cellulation.rotation.toRotationSystem hcubic hrotation htwoSided
      hfacesNe hold hnew hadj
  by_contra hne
  have hseparated :
      (sourceSlabLeftInterior historical).center.val + 1 <
        (sourceSlabLeftInterior newOffset).center.val := by
    change historical.val + 1 + 1 < newOffset.val + 1
    have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
    rw [hnewOffsetVal]
    omega
  exact (corridor.separated_not_adjacent _ _ hseparated) hfaceAdj

/-- A historical output crossing adjacent to the successor rebase
presentation belongs either to the current Cell or to its immediate
predecessor. -/
theorem sourceSlabOutputCrossing_index_eq_or_succ_eq_of_lt_cut_of_adj_rebaseCrossing
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset historical : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hhistorical : historical.val < offset.val + 1)
    (oldStep newStep : Fin 2)
    (hadj : embedded.cellulation.rotation.toRotationSystem.edgeAdjacencyGraph.Adj
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        historical).nextLocalLayerPrefixCrossing oldStep)
      (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
        hrotation htwoSided hunique offset hnext newStep)) :
    historical.val = offset.val ∨ historical.val + 1 = offset.val := by
  let corridor := realization.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton
  let oldFace := corridor.faceAt
    (nextCorridorInterior (sourceSlabLeftInterior historical)
      (sourceSlabLeftInterior_hasNext historical)).center
  let newOffset := sourceCorridorSerialNextOffset offset hnext
  let newFace := corridor.faceAt (sourceSlabLeftInterior newOffset).center
  have hold :
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        historical).nextLocalLayerPrefixCrossing oldStep ∈
        orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
          oldFace.1 := by
    simpa [oldFace, corridor,
      SourceConsecutiveSlabInterface.nextCenterLayerFace] using
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        historical).nextLocalLayerPrefixCrossing_mem_nextCenterLayerFaceBoundary
          oldStep
  have hnew :
      sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
          hrotation htwoSided hunique offset hnext newStep ∈
        orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
          newFace.1 := by
    simpa [sourceCorridorSerialBoundaryRebaseCrossingAt, newFace, newOffset,
      corridor, SourceConsecutiveSlabInterface.centerLayerFace] using
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        newOffset).localLayerPrefixCrossing_mem_centerLayerFaceBoundary newStep
  by_cases hfaces : oldFace.1 = newFace.1
  · left
    have hindices :
        (nextCorridorInterior (sourceSlabLeftInterior historical)
          (sourceSlabLeftInterior_hasNext historical)).center =
        (sourceSlabLeftInterior newOffset).center :=
      corridor.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change historical.val + 2 = newOffset.val + 1 at hvalues
    have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
    rw [hnewOffsetVal] at hvalues
    omega
  · have hfaceAdj := interiorDualGraph_adj_of_edgeAdjacencyGraph_adj
      embedded.cellulation.rotation.toRotationSystem hcubic hrotation htwoSided
        hfaces hold hnew hadj
    by_cases hnear : historical.val + 1 = offset.val
    · exact Or.inr hnear
    · have hcurrentNe : historical.val ≠ offset.val := by
        intro hcurrent
        apply hfaces
        have hindices :
            (nextCorridorInterior (sourceSlabLeftInterior historical)
              (sourceSlabLeftInterior_hasNext historical)).center =
            (sourceSlabLeftInterior newOffset).center := by
          apply Fin.ext
          change historical.val + 2 = newOffset.val + 1
          have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
          rw [hnewOffsetVal, hcurrent]
        exact congrArg Subtype.val (congrArg corridor.faceAt hindices)
      have hseparated :
        (nextCorridorInterior (sourceSlabLeftInterior historical)
            (sourceSlabLeftInterior_hasNext historical)).center.val + 1 <
          (sourceSlabLeftInterior newOffset).center.val := by
        have holdCenterVal :
            (nextCorridorInterior (sourceSlabLeftInterior historical)
              (sourceSlabLeftInterior_hasNext historical)).center.val =
                historical.val + 2 := rfl
        have hnewCenterVal :
            (sourceSlabLeftInterior newOffset).center.val =
              newOffset.val + 1 := rfl
        rw [holdCenterVal, hnewCenterVal]
        have hnewOffsetVal : newOffset.val = offset.val + 1 := rfl
        rw [hnewOffsetVal]
        omega
      exact False.elim
        ((corridor.separated_not_adjacent _ _ hseparated) hfaceAdj)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
