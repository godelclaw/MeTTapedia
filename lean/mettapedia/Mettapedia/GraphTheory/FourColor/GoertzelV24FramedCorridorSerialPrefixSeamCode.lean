import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedSupportGraphCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixSeamRelation

/-!
# Finite codes for a source serial-prefix residual seam

The residual tracked and facial seam graphs of one literal source Cell are
presented on ambient carriers, but their actual supports have cardinality at
most fourteen.  This module removes those ambient carriers by transporting
each induced support graph to a graph on its canonical finite coordinate.

These codes retain the exact residual adjacency and reachability relations.
They do not assert that an input profile determines the residual code, that
two independently realized seams have equal codes, or that the residual is
already the completed corridor transfer morphism.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedSupportGraphCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialPrefixSeamCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The tracked residual seam, stripped of isolated ambient edges and coded
on at most fourteen vertices. -/
noncomputable def sourceCorridorSerialInputTrackedSeamCodeAt
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
    (color : G.edgeSet → Color) (first second : Color) :
    BoundedSupportGraphCode 14 :=
  boundedSupportCode
    (sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic hrotation
      htwoSided hunique offset color first second)
    14
    (sourceCorridorSerialInputTrackedSeamGraphAt_support_card_le_fourteen
      realization hcubic hrotation htwoSided hunique offset color first second)

/-- The tracked residual graph on its participating ambient edges is
isomorphic to its finite code. -/
noncomputable def sourceCorridorSerialInputTrackedSeamCodeIsoAt
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
    (color : G.edgeSet → Color) (first second : Color) :
    let seam := sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic
      hrotation htwoSided hunique offset color first second
    seam.induce seam.support ≃g
      (sourceCorridorSerialInputTrackedSeamCodeAt realization hcubic hrotation
        htwoSided hunique offset color first second).graph := by
  dsimp only
  exact boundedSupportCodeIso
    (sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic hrotation
      htwoSided hunique offset color first second)
    14
    (sourceCorridorSerialInputTrackedSeamGraphAt_support_card_le_fourteen
      realization hcubic hrotation htwoSided hunique offset color first second)

/-- The occurrence-sensitive facial residual seam, stripped of isolated face
positions and coded on at most fourteen vertices. -/
noncomputable def sourceCorridorSerialInputFaceSeamCodeAt
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
    (root : embedded.cellulation.rotation.toRotationSystem.D) :
    BoundedSupportGraphCode 14 :=
  boundedSupportCode
    (sourceCorridorSerialInputFaceSeamGraphAt realization hcubic hrotation
      htwoSided hunique offset root)
    14
    (sourceCorridorSerialInputFaceSeamGraphAt_support_card_le_fourteen
      realization hcubic hrotation htwoSided hunique offset root)

/-- The facial residual graph on its participating face occurrences is
isomorphic to its finite code. -/
noncomputable def sourceCorridorSerialInputFaceSeamCodeIsoAt
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
    (root : embedded.cellulation.rotation.toRotationSystem.D) :
    let seam := sourceCorridorSerialInputFaceSeamGraphAt realization hcubic
      hrotation htwoSided hunique offset root
    seam.induce seam.support ≃g
      (sourceCorridorSerialInputFaceSeamCodeAt realization hcubic hrotation
        htwoSided hunique offset root).graph := by
  dsimp only
  exact boundedSupportCodeIso
    (sourceCorridorSerialInputFaceSeamGraphAt realization hcubic hrotation
      htwoSided hunique offset root)
    14
    (sourceCorridorSerialInputFaceSeamGraphAt_support_card_le_fourteen
      realization hcubic hrotation htwoSided hunique offset root)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
