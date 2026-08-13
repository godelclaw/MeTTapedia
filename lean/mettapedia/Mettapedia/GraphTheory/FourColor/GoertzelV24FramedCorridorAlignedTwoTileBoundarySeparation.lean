import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileBoundary

/-!
# Remote separation of literal aligned two-tile boundary windows

The six-edge boundary at one source offset is a local window, not itself a
source radial crosscut.  Nevertheless, the finite-state repeat uses offsets
far enough apart that their literal windows must not collide.  This file
proves exactly that noncollision from the clean corridor's geodesic
separation.  It deliberately does not claim that either window is a global
annular cut or that the region between two such windows has already been
realized as a serial open tangle.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

/- Keep the finite boundary-edge carrier aligned with the source geometry. -/
local instance alignedTwoTileBoundarySeparationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Every face of one literal aligned two-tile boundary is a full-dual
neighbor of one of its two consecutive corridor centres.  The two centre
faces themselves use the corridor rung between them; the rail faces use their
checked source provenance. -/
theorem sourceTwoTileAlignedBoundaryWalkAt_support_adjacent_to_centers
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
    (offset : Fin (blockLength - 4))
    (face : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hface : face ∈
      (sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation
        htwoSided hunique offset).support) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
          hunique offset).toInterface.centerLayerFace face ∨
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
          hunique offset).toInterface.centerLayerFace face := by
  let first := sourceTwoTileFirstInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let second := sourceTwoTileSecondInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let rails := sourceTwoTileRailPairAt realization hcubic hrotation
    htwoSided hunique offset
  let corridor :=
    realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  have hcenters :
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        first.toInterface.centerLayerFace second.toInterface.centerLayerFace := by
    simpa [corridor, first, second, SourceConsecutiveSlabInterface.centerLayerFace,
      sourceTwoTileLeftInterior, nextCorridorInterior] using
      (corridor.consecutive_adjacent
        (sourceTwoTileLeftInterior offset).center
        (nextCorridorInterior (sourceTwoTileLeftInterior offset)
          (sourceTwoTileLeftInterior_hasNext offset)).center (by rfl))
  simp only [sourceTwoTileAlignedBoundaryWalkAt,
    SimpleGraph.Walk.mem_support_append_iff] at hface
  rcases hface with hleft | hrailsFirst
  · rcases hleft with hleft | hsecond
    · rcases hleft with hfirst | hrailsSecond
      · change face ∈ first.toInterface.localLayerWalk.support at hfirst
        simp only [SourceConsecutiveSlabInterface.localLayerWalk,
          SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons] at hfirst
        rcases hfirst with rfl | rfl | hnone
        · exact Or.inl first.toInterface.firstLayerFace_adjacent_centerLayerFace.symm
        · exact Or.inr hcenters.symm
        · rcases hnone with rfl | hnone
          · exact Or.inl first.toInterface.centerLayerFace_adjacent_secondLayerFace
          · simp at hnone
      · change face ∈ rails.secondRail.support at hrailsSecond
        rcases rails.secondRail_support_adjacent_to_source face hrailsSecond with hfirst | hsecond
        · exact Or.inl (by simpa [first] using hfirst)
        · exact Or.inr (by simpa [second] using hsecond)
    · change face ∈ second.toInterface.localLayerWalk.reverse.support at hsecond
      rw [SimpleGraph.Walk.support_reverse] at hsecond
      simp only [SourceConsecutiveSlabInterface.localLayerWalk,
        SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_reverse, List.mem_cons] at hsecond
      rcases hsecond with rfl | rfl | hnone
      · exact Or.inr second.toInterface.firstLayerFace_adjacent_centerLayerFace.symm
      · exact Or.inl hcenters
      · rcases hnone with rfl | hnone
        · exact Or.inr second.toInterface.centerLayerFace_adjacent_secondLayerFace
        · simp at hnone
  · change face ∈ rails.firstRail.reverse.support at hrailsFirst
    rw [SimpleGraph.Walk.support_reverse] at hrailsFirst
    have hrailsFirst' : face ∈ rails.firstRail.support := by
      simpa only [List.mem_reverse] using hrailsFirst
    rcases rails.firstRail_support_adjacent_to_source face hrailsFirst' with hfirst | hsecond
    · exact Or.inl (by simpa [first] using hfirst)
    · exact Or.inr (by simpa [second] using hsecond)

/-- Source windows whose starts differ by at least four positions are
disjoint in the full facial dual.  This is a remote-window noncollision fact,
not an assertion that these local cycles are the separated radial cuts used
by the eventual annular splice. -/
theorem sourceTwoTileAlignedBoundaryWalks_support_disjoint_of_add_three_lt
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
    (first second : Fin (blockLength - 4))
    (hseparated : first.val + 3 < second.val) :
    (sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation
      htwoSided hunique first).support.Disjoint
      (sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation
        htwoSided hunique second).support := by
  apply realization.walkSupports_disjoint_of_two_source_anchor_pairs_of_add_three_lt
    (sourceTwoTileLeftInterior_hasNext first)
    (sourceTwoTileLeftInterior_hasNext second)
  · intro face hface
    exact sourceTwoTileAlignedBoundaryWalkAt_support_adjacent_to_centers
      realization hcubic hrotation htwoSided hunique first face hface
  · intro face hface
    exact sourceTwoTileAlignedBoundaryWalkAt_support_adjacent_to_centers
      realization hcubic hrotation htwoSided hunique second face hface
  · change first.val + 1 + 3 < second.val + 1
    omega

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
