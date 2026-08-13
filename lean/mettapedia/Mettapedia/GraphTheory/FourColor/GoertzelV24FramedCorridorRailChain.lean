import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorRailPair
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathTransversalAppend

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
open GoertzelV24DualPathTransversal
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

/-- A full-dual neighbor of one of the realized clean-axis faces is still an
internal annular face.  This exposes the boundary-clean consequence in the
form used by composed rails. -/
private theorem face_internal_of_adjacent_to_cleanAxis
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (offset : Fin blockLength)
    (face : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hadj : (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        (realization.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton.faceAt offset) face) :
    face.1 ∈ embedded.cellulation.interiorFaces := by
  have hpositive : 0 < blockLength :=
    Nat.pos_of_ne_zero (by
      intro hzero
      subst blockLength
      exact Fin.elim0 offset)
  apply realization.coreWalk_neighbor_internal hpositive offset face
  rw [realization.coreWalk_getVert hpositive offset,
    ← realization.toCleanOrbitHexCorridorSkeleton_faceAt]
  exact hadj

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
    GoertzelV24DualPathTransversal.walk_append_isPath_of_support_disjoint
      leftPair.firstRail rightPair.firstRail
      leftPair.firstRail_isPath rightPair.firstRail_isPath hfirst
  secondRail_isPath :=
    GoertzelV24DualPathTransversal.walk_append_isPath_of_support_disjoint
      leftPair.secondRail rightPair.secondRail
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

/-- The composed first rail remains wholly in the annular interior.  The
source's boundary-clean corridor supplies this fact for all three anchors of
the two-step chain, so composition cannot introduce a hidden visit to either
container hole. -/
theorem sourceCornerAlignedRailChain_of_pairs_firstRail_support_internal
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
    (face : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hface : face ∈
      (sourceCornerAlignedRailChain_of_pairs first middle last
        leftPair rightPair hfirst hsecond).firstRail.support) :
    face.1 ∈ embedded.cellulation.interiorFaces := by
  rcases sourceCornerAlignedRailChain_of_pairs_firstRail_support_adjacent_to_source
      first middle last leftPair rightPair hfirst hsecond hface with
    hfirstFace | hmiddleFace | hlastFace
  · exact face_internal_of_adjacent_to_cleanAxis realization
      leftInterior.center face (by
        simpa [SourceConsecutiveSlabInterface.centerLayerFace] using hfirstFace)
  · exact face_internal_of_adjacent_to_cleanAxis realization
      (nextCorridorInterior leftInterior hnext).center face (by
        simpa [SourceConsecutiveSlabInterface.centerLayerFace] using hmiddleFace)
  · exact face_internal_of_adjacent_to_cleanAxis realization
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center face (by
        simpa [SourceConsecutiveSlabInterface.centerLayerFace] using hlastFace)

/-- The composed second rail satisfies the same internal-face invariant. -/
theorem sourceCornerAlignedRailChain_of_pairs_secondRail_support_internal
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
    (face : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hface : face ∈
      (sourceCornerAlignedRailChain_of_pairs first middle last
        leftPair rightPair hfirst hsecond).secondRail.support) :
    face.1 ∈ embedded.cellulation.interiorFaces := by
  rcases sourceCornerAlignedRailChain_of_pairs_secondRail_support_adjacent_to_source
      first middle last leftPair rightPair hfirst hsecond hface with
    hfirstFace | hmiddleFace | hlastFace
  · exact face_internal_of_adjacent_to_cleanAxis realization
      leftInterior.center face (by
        simpa [SourceConsecutiveSlabInterface.centerLayerFace] using hfirstFace)
  · exact face_internal_of_adjacent_to_cleanAxis realization
      (nextCorridorInterior leftInterior hnext).center face (by
        simpa [SourceConsecutiveSlabInterface.centerLayerFace] using hmiddleFace)
  · exact face_internal_of_adjacent_to_cleanAxis realization
      (nextCorridorInterior
        (nextCorridorInterior leftInterior hnext) hnextNext).center face (by
        simpa [SourceConsecutiveSlabInterface.centerLayerFace] using hlastFace)

/-- Composing two first rails preserves the graph-level fact that their crossed
edges avoid every non-interior container boundary.  This is a safety invariant
for the later global layer assembly; it does not by itself choose a deletion
side or assert a completed separator. -/
theorem sourceCornerAlignedRailChain_of_pairs_firstRail_crossingEdges_disjoint_holeBoundary
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
    (hole : OrbitFace embedded.cellulation.rotation.toRotationSystem)
    (hhole : hole ∉ embedded.cellulation.interiorFaces) :
    Disjoint
      (dualWalkCrossingEdges
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        (sourceCornerAlignedRailChain_of_pairs first middle last
          leftPair rightPair hfirst hsecond).firstRail)
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem hole) := by
  exact dualWalkCrossingEdges_disjoint_holeBoundary_of_support_internal
    (hunique := hunique) embedded
    (sourceCornerAlignedRailChain_of_pairs first middle last
      leftPair rightPair hfirst hsecond).firstRail
    (fun face hface =>
      sourceCornerAlignedRailChain_of_pairs_firstRail_support_internal
        first middle last leftPair rightPair hfirst hsecond face hface)
    hole hhole

/-- The same boundary-safety invariant for the composed second rail. -/
theorem sourceCornerAlignedRailChain_of_pairs_secondRail_crossingEdges_disjoint_holeBoundary
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
    (hole : OrbitFace embedded.cellulation.rotation.toRotationSystem)
    (hhole : hole ∉ embedded.cellulation.interiorFaces) :
    Disjoint
      (dualWalkCrossingEdges
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
        (sourceCornerAlignedRailChain_of_pairs first middle last
          leftPair rightPair hfirst hsecond).secondRail)
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem hole) := by
  exact dualWalkCrossingEdges_disjoint_holeBoundary_of_support_internal
    (hunique := hunique) embedded
    (sourceCornerAlignedRailChain_of_pairs first middle last
      leftPair rightPair hfirst hsecond).secondRail
    (fun face hface =>
      sourceCornerAlignedRailChain_of_pairs_secondRail_support_internal
        first middle last leftPair rightPair hfirst hsecond face hface)
    hole hhole

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
