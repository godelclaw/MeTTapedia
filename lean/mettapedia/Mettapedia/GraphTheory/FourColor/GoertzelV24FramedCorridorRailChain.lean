import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorRailPair

/-!
# Composing concrete rails along a source corridor

One source slab step supplies two short rails between consecutive interfaces.
This file proves the first genuinely nonlocal piece of the construction: two
such steps compose into two simple facial-dual paths when their checked
supports meet only at their joining interface.  The support condition is kept
visible because global simplicity is a geometric theorem about the realized
corridor, not a consequence of merely having two local paths.

No profile, catalogue, or covering-style data is introduced here.  This is
only the path-composition part of the source's simple layer-boundary
construction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/- Keep the edge carrier's equality instance aligned with the source-corridor
   geometry, whose finite facial boundaries use the ordinary subtype instance. -/
local instance corridorRailChainGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Appending two simple walks is simple when the second walk has no new
intersection with the first one.  The common joining face is omitted from the
second support tail, exactly as it is in the definition of walk append. -/
private theorem walk_append_isPath_of_support_disjoint
    {F : Type*} {H : SimpleGraph F}
    {start middle finish : F}
    (left : H.Walk start middle) (right : H.Walk middle finish)
    (hleft : left.IsPath) (hright : right.IsPath)
    (hdisjoint : left.support.Disjoint right.support.tail) :
    (left.append right).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    List.nodup_append']
  exact ⟨hleft.support_nodup, hright.support_nodup.tail, hdisjoint⟩

/-- The source anchor of a face is preserved when two local rail walks are
appended: it comes from the first cell, the shared cell, or the last cell.
The theorem only records provenance; simplicity remains the separately
checked geometric obligation. -/
private theorem walk_append_support_adjacent_three
    {F : Type*} {H : SimpleGraph F}
    {start middle finish : F}
    (left : H.Walk start middle) (right : H.Walk middle finish)
    (firstAnchor sharedAnchor lastAnchor : F)
    (hleft : ∀ face ∈ left.support,
      H.Adj firstAnchor face ∨ H.Adj sharedAnchor face)
    (hright : ∀ face ∈ right.support,
      H.Adj sharedAnchor face ∨ H.Adj lastAnchor face)
    {face : F} (hface : face ∈ (left.append right).support) :
    H.Adj firstAnchor face ∨ H.Adj sharedAnchor face ∨ H.Adj lastAnchor face := by
  rw [SimpleGraph.Walk.support_append] at hface
  rcases List.mem_append.mp hface with hleftFace | hrightFace
  · rcases hleft face hleftFace with hfirst | hshared
    · exact Or.inl hfirst
    · exact Or.inr (Or.inl hshared)
  · rcases hright face (List.mem_of_mem_tail hrightFace) with hshared | hlast
    · exact Or.inr (Or.inl hshared)
    · exact Or.inr (Or.inr hlast)

/-- Two consecutive local rail pairs composed into the two actual source
rails across a three-interface corridor segment.  Individual rail simplicity
is retained here; mutual rail disjointness is the next, separate geometric
obligation required before closing the segment into a layer boundary. -/
structure SourceCornerAlignedRailChain
    {source : SourceTrail G}
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
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {hnextThird :
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center.val + 2 < blockLength}
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (last : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext) hnextThird) where
  firstRail :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      first.toInterface.firstLayerFace last.toInterface.firstLayerFace
  secondRail :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      first.toInterface.secondLayerFace last.toInterface.secondLayerFace
  firstRail_isPath : firstRail.IsPath
  secondRail_isPath : secondRail.IsPath
  firstRail_length_le_four : firstRail.length ≤ 4
  secondRail_length_le_four : secondRail.length ≤ 4

/-- Compose two checked local rail pairs.  The two explicit support
disjointness hypotheses are the exact remaining simplicity checks for this
three-interface segment; they are not replaced by a profile equality or by a
choice of an abstract separator. -/
def sourceCornerAlignedRailChain_of_pairs
    {source : SourceTrail G}
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
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {hnextThird :
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center.val + 2 < blockLength}
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (middle : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (last : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext) hnextThird)
    (leftPair : SourceCornerAlignedRailPair first middle)
    (rightPair : SourceCornerAlignedRailPair middle last)
    (hfirst : leftPair.firstRail.support.Disjoint rightPair.firstRail.support.tail)
    (hsecond : leftPair.secondRail.support.Disjoint rightPair.secondRail.support.tail) :
    SourceCornerAlignedRailChain first last where
  firstRail := leftPair.firstRail.append rightPair.firstRail
  secondRail := leftPair.secondRail.append rightPair.secondRail
  firstRail_isPath :=
    walk_append_isPath_of_support_disjoint leftPair.firstRail rightPair.firstRail
      leftPair.firstRail_isPath rightPair.firstRail_isPath hfirst
  secondRail_isPath :=
    walk_append_isPath_of_support_disjoint leftPair.secondRail rightPair.secondRail
      leftPair.secondRail_isPath rightPair.secondRail_isPath hsecond
  firstRail_length_le_four := by
    simp only [SimpleGraph.Walk.length_append]
    have hleft := leftPair.firstRail_length_le_two
    have hright := rightPair.firstRail_length_le_two
    omega
  secondRail_length_le_four := by
    simp only [SimpleGraph.Walk.length_append]
    have hleft := leftPair.secondRail_length_le_two
    have hright := rightPair.secondRail_length_le_two
    omega

/-- The composed first rail is definitionally the append of the two local
rails.  Exposing this equality lets the next layer prove global rail
disjointness from the individual source cells without unfolding the chain
record. -/
@[simp]
theorem sourceCornerAlignedRailChain_of_pairs_firstRail
    {source : SourceTrail G}
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
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {hnextThird :
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center.val + 2 < blockLength}
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (middle : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (last : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext) hnextThird)
    (leftPair : SourceCornerAlignedRailPair first middle)
    (rightPair : SourceCornerAlignedRailPair middle last)
    (hfirst : leftPair.firstRail.support.Disjoint rightPair.firstRail.support.tail)
    (hsecond : leftPair.secondRail.support.Disjoint rightPair.secondRail.support.tail) :
    (sourceCornerAlignedRailChain_of_pairs first middle last
      leftPair rightPair hfirst hsecond).firstRail =
      leftPair.firstRail.append rightPair.firstRail :=
  rfl

/-- The analogous literal append equation for the second source rail. -/
@[simp]
theorem sourceCornerAlignedRailChain_of_pairs_secondRail
    {source : SourceTrail G}
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
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {hnextThird :
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center.val + 2 < blockLength}
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (middle : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (last : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext) hnextThird)
    (leftPair : SourceCornerAlignedRailPair first middle)
    (rightPair : SourceCornerAlignedRailPair middle last)
    (hfirst : leftPair.firstRail.support.Disjoint rightPair.firstRail.support.tail)
    (hsecond : leftPair.secondRail.support.Disjoint rightPair.secondRail.support.tail) :
    (sourceCornerAlignedRailChain_of_pairs first middle last
      leftPair rightPair hfirst hsecond).secondRail =
      leftPair.secondRail.append rightPair.secondRail :=
  rfl

/-- Every face on the composed first rail remains anchored at one of the
three source cells crossed by the two local steps. -/
theorem sourceCornerAlignedRailChain_of_pairs_firstRail_support_adjacent_to_source
    {source : SourceTrail G}
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
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {hnextThird :
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center.val + 2 < blockLength}
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (middle : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (last : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext) hnextThird)
    (leftPair : SourceCornerAlignedRailPair first middle)
    (rightPair : SourceCornerAlignedRailPair middle last)
    (hfirst : leftPair.firstRail.support.Disjoint rightPair.firstRail.support.tail)
    (hsecond : leftPair.secondRail.support.Disjoint rightPair.secondRail.support.tail)
    {face : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    (hface : face ∈
      (sourceCornerAlignedRailChain_of_pairs first middle last
        leftPair rightPair hfirst hsecond).firstRail.support) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        first.toInterface.centerLayerFace face ∨
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        middle.toInterface.centerLayerFace face ∨
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        last.toInterface.centerLayerFace face := by
  rw [sourceCornerAlignedRailChain_of_pairs_firstRail] at hface
  exact walk_append_support_adjacent_three leftPair.firstRail rightPair.firstRail
    first.toInterface.centerLayerFace middle.toInterface.centerLayerFace
    last.toInterface.centerLayerFace
    leftPair.firstRail_support_adjacent_to_source
    rightPair.firstRail_support_adjacent_to_source hface

/-- The analogous source-anchor statement for the composed second rail. -/
theorem sourceCornerAlignedRailChain_of_pairs_secondRail_support_adjacent_to_source
    {source : SourceTrail G}
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
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {hnextThird :
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center.val + 2 < blockLength}
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (middle : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (last : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext) hnextThird)
    (leftPair : SourceCornerAlignedRailPair first middle)
    (rightPair : SourceCornerAlignedRailPair middle last)
    (hfirst : leftPair.firstRail.support.Disjoint rightPair.firstRail.support.tail)
    (hsecond : leftPair.secondRail.support.Disjoint rightPair.secondRail.support.tail)
    {face : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    (hface : face ∈
      (sourceCornerAlignedRailChain_of_pairs first middle last
        leftPair rightPair hfirst hsecond).secondRail.support) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        first.toInterface.centerLayerFace face ∨
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        middle.toInterface.centerLayerFace face ∨
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        last.toInterface.centerLayerFace face := by
  rw [sourceCornerAlignedRailChain_of_pairs_secondRail] at hface
  exact walk_append_support_adjacent_three leftPair.secondRail rightPair.secondRail
    first.toInterface.centerLayerFace middle.toInterface.centerLayerFace
    last.toInterface.centerLayerFace
    leftPair.secondRail_support_adjacent_to_source
    rightPair.secondRail_support_adjacent_to_source hface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
