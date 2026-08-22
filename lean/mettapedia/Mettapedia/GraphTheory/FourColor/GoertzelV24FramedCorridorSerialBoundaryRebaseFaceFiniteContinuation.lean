import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceFinitePortPositions
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixProfileCompression

/-!
# Finite successor face continuation

The successor cut of one literal serial boundary rebase has at most four
boundary-face fragments.  On a graph-derived profile, `faceContinues` is not
an arbitrary Boolean matrix: it is the equivalence relation induced by
equality of ambient orbit faces.

This file applies the existing lossless face-equivalence codec to the actual
successor profile.  The resulting code has at most fifteen values at the
four-fragment bound, and its graph-free decoder recovers every literal
successor continuation bit exactly.

This is one field of the finite heterogeneous rebase receipt.  It does not
yet combine continuation, port positions, capped lengths, and tracked-strand
updates into the complete one-Cell support relation, measure its reachable
closure, or derive a threshold.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24WidthTwoFaceEquivalenceCompression
open GoertzelV24WidthTwoPortIncidenceCompression
open SimpleGraph
open SimpleGraphDartRotation

/-- Up to four fragments admit at most the fifteen equivalence relations on
four labels. -/
theorem card_faceEquivalenceCode_le_fifteen
    {faceFragmentCount : Nat} (hcount : faceFragmentCount ≤ 4) :
    Fintype.card (FaceEquivalenceCode faceFragmentCount) ≤ 15 := by
  interval_cases faceFragmentCount <;>
    norm_num [card_faceEquivalenceCode_zero, card_faceEquivalenceCode_one,
      card_faceEquivalenceCode_two, card_faceEquivalenceCode_three,
      card_faceEquivalenceCode_four]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceFiniteContinuationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The canonical finite equivalence code of the actual successor
face-continuation relation after one literal serial rebase. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceContinuationCodeAt
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
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext))
        |>.localLayerPrefixCrossing step) ≠ 0) :
    FaceEquivalenceCode
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).faceFragmentCount.val :=
  let profile := sourceCorridorSerialInputBoundedProfileAt realization hcubic
    hrotation htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
    color hcolor
  let semantic :=
    sourceCorridorSerialInputBoundedProfileAt_isPortIncidenceSemantic
      realization hcubic hrotation htwoSided hunique
      (sourceCorridorSerialNextOffset offset hnext) color hcolor
  (compressFaceEquivalence profile.profile
    semantic.toIsFaceEquivalenceSemantic).face

/-- The finite equivalence code reconstructs every literal successor
`faceContinues` bit exactly. -/
theorem sourceCorridorSerialInputBoundedProfileAt_next_faceContinues_eq_finiteCode
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
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext))
        |>.localLayerPrefixCrossing step) ≠ 0)
    (left right : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt
      realization hcubic hrotation htwoSided hunique offset hnext) :
    faceRelation
        (sourceCorridorSerialBoundaryRebaseFaceContinuationCodeAt realization
          hcubic hrotation htwoSided hunique offset hnext color hcolor).1
        left right =
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.faceContinues left right := by
  let profile := sourceCorridorSerialInputBoundedProfileAt realization hcubic
    hrotation htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
    color hcolor
  let semantic :=
    sourceCorridorSerialInputBoundedProfileAt_isPortIncidenceSemantic
      realization hcubic hrotation htwoSided hunique
      (sourceCorridorSerialNextOffset offset hnext) color hcolor
  change faceRelation
      (fun pair => profile.profile.faceContinues pair.1.1 pair.1.2)
      left right = profile.profile.faceContinues left right
  exact faceRelation_compress_eq profile.profile
    semantic.toIsFaceEquivalenceSemantic left right

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
