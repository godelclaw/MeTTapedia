import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorTwoTileProfileWord

/-!
# Primal support of the source intercell rails

Successive literal corridor Cells do not expose definitionally identical
ambient cuts.  The source construction supplies two short facial-dual rails
across the shared hexagon.  This file retains the primal edges crossed by
those rails as an explicit bounded support, so a later open-tangle
realization can include the intercell transport rather than gluing two
abstract `Fin 2` interfaces directly.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorIntercellRailSupportEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The primal support traversed by the two concrete rails between adjacent
source interfaces.  Both tracks are retained: in the bent cases one is a
zero-step rail and the other has length two, while in the straight case both
have length one. -/
noncomputable def sourceTwoTileRailCrossingEdgesAt
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
    (offset : Fin (blockLength - 4)) : Finset G.edgeSet :=
  let pair := sourceTwoTileRailPairAt realization hcubic hrotation htwoSided
    hunique offset
  dualWalkCrossingEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      pair.firstRail ∪
    dualWalkCrossingEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      pair.secondRail

/-- The two source rails cross at most four primal edges in total.  This is
the uniform finite carrier needed by an intercell transfer: the estimate is
derived from the checked path lengths, not from a corridor-state bound. -/
theorem sourceTwoTileRailCrossingEdgesAt_card_le_four
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
    (offset : Fin (blockLength - 4)) :
    (sourceTwoTileRailCrossingEdgesAt realization hcubic hrotation htwoSided
      hunique offset).card ≤ 4 := by
  let pair := sourceTwoTileRailPairAt realization hcubic hrotation htwoSided
    hunique offset
  let firstEdges := dualWalkCrossingEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    pair.firstRail
  let secondEdges := dualWalkCrossingEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    pair.secondRail
  have hfirstCard : firstEdges.card = pair.firstRail.length := by
    dsimp [firstEdges]
    exact card_dualWalkCrossingEdges_eq_length_of_isPath
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      (orbitFace_incidence_le_two
        embedded.cellulation.rotation.toRotationSystem)
      hunique pair.firstRail pair.firstRail_isPath
  have hsecondCard : secondEdges.card = pair.secondRail.length := by
    dsimp [secondEdges]
    exact card_dualWalkCrossingEdges_eq_length_of_isPath
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      (orbitFace_incidence_le_two
        embedded.cellulation.rotation.toRotationSystem)
      hunique pair.secondRail pair.secondRail_isPath
  change (firstEdges ∪ secondEdges).card ≤ 4
  calc
    (firstEdges ∪ secondEdges).card ≤
        firstEdges.card + secondEdges.card := Finset.card_union_le _ _
    _ = pair.firstRail.length + pair.secondRail.length := by
      rw [hfirstCard, hsecondCard]
    _ ≤ 2 + 2 := Nat.add_le_add pair.firstRail_length_le_two
      pair.secondRail_length_le_two
    _ = 4 := rfl

/-- The bounded intercell support avoids every named hole boundary outside
the annular interior.  This is inherited from both concrete rails and is
preserved by their union. -/
theorem sourceTwoTileRailCrossingEdgesAt_disjoint_holeBoundary
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
    (hole : OrbitFace embedded.cellulation.rotation.toRotationSystem)
    (hhole : hole ∉ embedded.cellulation.interiorFaces) :
    Disjoint
      (sourceTwoTileRailCrossingEdgesAt realization hcubic hrotation
        htwoSided hunique offset)
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        hole) := by
  let pair := sourceTwoTileRailPairAt realization hcubic hrotation htwoSided
    hunique offset
  have hfirst := pair.firstRail_crossingEdges_disjoint_holeBoundary hole hhole
  have hsecond := pair.secondRail_crossingEdges_disjoint_holeBoundary hole hhole
  rw [Finset.disjoint_left]
  intro edge hedge hboundary
  change edge ∈
      dualWalkCrossingEdges
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
          pair.firstRail ∪
        dualWalkCrossingEdges
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
          pair.secondRail at hedge
  rcases Finset.mem_union.1 hedge with hfirstEdge | hsecondEdge
  · exact (Finset.disjoint_left.1 hfirst hfirstEdge hboundary).elim
  · exact (Finset.disjoint_left.1 hsecond hsecondEdge hboundary).elim

/-- The concrete intercell rails avoid the inner-hole boundary. -/
theorem sourceTwoTileRailCrossingEdgesAt_disjoint_innerHoleBoundary
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
    (offset : Fin (blockLength - 4)) :
    Disjoint
      (sourceTwoTileRailCrossingEdgesAt realization hcubic hrotation
        htwoSided hunique offset)
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        embedded.cellulation.innerHole) := by
  apply sourceTwoTileRailCrossingEdgesAt_disjoint_holeBoundary
    realization hcubic hrotation htwoSided hunique offset
  intro hinner
  exact Finset.disjoint_left.1
    embedded.cellulation.interiorFaces_disjoint_holeFaces hinner (by
      simp [GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.holeFaces])

/-- The concrete intercell rails avoid the outer-hole boundary. -/
theorem sourceTwoTileRailCrossingEdgesAt_disjoint_outerHoleBoundary
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
    (offset : Fin (blockLength - 4)) :
    Disjoint
      (sourceTwoTileRailCrossingEdgesAt realization hcubic hrotation
        htwoSided hunique offset)
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        embedded.cellulation.outerHole) := by
  apply sourceTwoTileRailCrossingEdgesAt_disjoint_holeBoundary
    realization hcubic hrotation htwoSided hunique offset
  intro houter
  exact Finset.disjoint_left.1
    embedded.cellulation.interiorFaces_disjoint_holeFaces houter (by
      simp [GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.holeFaces])

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
