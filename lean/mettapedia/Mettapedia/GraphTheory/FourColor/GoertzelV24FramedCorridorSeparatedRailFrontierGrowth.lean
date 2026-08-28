import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorIntercellRailSupport

/-!
# Growth of the lateral frontier in the local two-tile construction

The two rail ports of a source-aligned two-tile window are genuine lateral
boundary crossings, not a second copy of the transverse interface shared with
the successor window.  Windows whose start positions differ by at least four
have disjoint rail supports.  Consequently the union of the displayed rail
carriers for any correspondingly spaced family has exactly two edges per
member.

This is an obstruction theorem for one proposed pumping supplier: the local
profile coordinates do not telescope merely by being reindexed at consecutive
positions.  It does not assert that every displayed rail edge remains in the
true frontier of a union of enclosed sides; proving absorption there would be
additional geometry.  Nor does it rule out a different nested-cut construction
forced by the zero-Count target.
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

local instance framedCorridorSeparatedRailFrontierGrowthEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Source-aligned two-tile windows separated by at least three intervening
start positions cross disjoint sets of primal rail edges. -/
theorem sourceTwoTileRailCrossingEdgesAt_disjoint_of_add_three_lt
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
    Disjoint
      (sourceTwoTileRailCrossingEdgesAt realization hcubic hrotation
        htwoSided hunique first)
      (sourceTwoTileRailCrossingEdgesAt realization hcubic hrotation
        htwoSided hunique second) := by
  let firstPair := sourceTwoTileRailPairAt realization hcubic hrotation
    htwoSided hunique first
  let secondPair := sourceTwoTileRailPairAt realization hcubic hrotation
    htwoSided hunique second
  have hsupports := sourceTwoTileRailPairSupports_disjoint_of_add_three_lt
    realization hcubic hrotation htwoSided hunique first second hseparated
  have hfirstFirst := dualWalkCrossingEdges_disjoint_of_support_disjoint
    hunique firstPair.firstRail secondPair.firstRail hsupports.1
  have hsecondSecond := dualWalkCrossingEdges_disjoint_of_support_disjoint
    hunique firstPair.secondRail secondPair.secondRail hsupports.2.1
  have hfirstSecond := dualWalkCrossingEdges_disjoint_of_support_disjoint
    hunique firstPair.firstRail secondPair.secondRail hsupports.2.2.1
  have hsecondFirst := dualWalkCrossingEdges_disjoint_of_support_disjoint
    hunique firstPair.secondRail secondPair.firstRail hsupports.2.2.2
  rw [Finset.disjoint_left]
  intro edge hfirst hsecond
  change edge ∈
      dualWalkCrossingEdges
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
          firstPair.firstRail ∪
        dualWalkCrossingEdges
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
          firstPair.secondRail at hfirst
  change edge ∈
      dualWalkCrossingEdges
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
          secondPair.firstRail ∪
        dualWalkCrossingEdges
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
          secondPair.secondRail at hsecond
  rcases Finset.mem_union.1 hfirst with hfirstRail | hsecondRail
  · rcases Finset.mem_union.1 hsecond with hfirstRail' | hsecondRail'
    · exact Finset.disjoint_left.1 hfirstFirst hfirstRail hfirstRail'
    · exact Finset.disjoint_left.1 hfirstSecond hfirstRail hsecondRail'
  · rcases Finset.mem_union.1 hsecond with hfirstRail' | hsecondRail'
    · exact Finset.disjoint_left.1 hsecondFirst hsecondRail hfirstRail'
    · exact Finset.disjoint_left.1 hsecondSecond hsecondRail hsecondRail'

/-- The union of the displayed lateral rail supports of a pairwise four-spaced
family has exactly two distinct crossing edges per window.  Thus these local
profile coordinates grow linearly unless a separate union-absorption theorem
removes them from the true ambient frontier. -/
theorem card_biUnion_sourceTwoTileRailCrossingEdgesAt_eq_two_mul_card
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
    (offsets : Finset (Fin (blockLength - 4)))
    (hseparated : ∀ first ∈ offsets, ∀ second ∈ offsets,
      first ≠ second →
        first.val + 3 < second.val ∨ second.val + 3 < first.val) :
    (offsets.biUnion fun offset =>
      sourceTwoTileRailCrossingEdgesAt realization hcubic hrotation
        htwoSided hunique offset).card = 2 * offsets.card := by
  rw [Finset.card_biUnion]
  · simp_rw [sourceTwoTileRailCrossingEdgesAt_card_eq_two]
    simp [Nat.mul_comm]
  · rintro first hfirst second hsecond hne
    rcases hseparated first hfirst second hsecond hne with hlt | hgt
    · exact sourceTwoTileRailCrossingEdgesAt_disjoint_of_add_three_lt
        realization hcubic hrotation htwoSided hunique first second hlt
    · exact (sourceTwoTileRailCrossingEdgesAt_disjoint_of_add_three_lt
        realization hcubic hrotation htwoSided hunique second first hgt).symm

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
