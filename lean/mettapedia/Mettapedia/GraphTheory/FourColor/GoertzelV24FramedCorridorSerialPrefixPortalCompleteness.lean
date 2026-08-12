import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixSeamSupport

/-!
# Portal completeness of the literal source-prefix seam

The compositional interface is the residual seam between the cumulative
literal prefix and the next source Cell.  Its already-proved adjacency
classification is stronger than a global “container walls are inert” claim:
every actual residual adjacency touches one of the two outgoing crossings.

Consequently every non-isolated tracked seam component reaches a named
moving-cut portal.  The occurrence-sensitive facial seam satisfies the same
statement using the same literal geometry.  No assertion is made that rail
edges are uncolored or that every boundary of every larger auxiliary region
has only two members.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialPrefixPortalCompletenessEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Every non-isolated tracked edge of the literal prefix/Cell residual seam
lies in a component containing one of the two named outgoing crossings. -/
theorem sourceCorridorSerialInputTrackedSeamGraphAt_support_reaches_outputCrossing
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
    (color : G.edgeSet → Color) (first second : Color)
    (edge : G.edgeSet)
    (hedge : edge ∈
      (sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic
        hrotation htwoSided hunique offset color first second).support) :
    ∃ step : Fin 2,
      (sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic
        hrotation htwoSided hunique offset color first second).Reachable edge
        ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
          offset).nextLocalLayerPrefixCrossing step) := by
  let seam := sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic
    hrotation htwoSided hunique offset color first second
  rcases (SimpleGraph.mem_support seam).1 hedge with ⟨neighbor, hadj⟩
  rcases sourceCorridorSerialInputTrackedSeamGraphAt_adj_touches_outputCrossing
      realization hcubic hrotation htwoSided hunique offset color first second
      hadj with ⟨step, hedgeOutput | hneighborOutput⟩
  · refine ⟨step, ?_⟩
    simp [hedgeOutput]
  · refine ⟨step, ?_⟩
    simpa [seam, hneighborOutput] using hadj.reachable

/-- Every non-isolated occurrence of the facial prefix/Cell residual seam
lies in a component containing an occurrence of a named outgoing crossing. -/
theorem sourceCorridorSerialInputFaceSeamGraphAt_support_reaches_outputCrossing
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
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (position : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card)
    (hposition : position ∈
      (sourceCorridorSerialInputFaceSeamGraphAt realization hcubic hrotation
        htwoSided hunique offset root).support) :
    ∃ (step : Fin 2)
        (outputPosition : Fin
          (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card),
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
          outputPosition =
        (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
          offset).nextLocalLayerPrefixCrossing step ∧
      (sourceCorridorSerialInputFaceSeamGraphAt realization hcubic hrotation
        htwoSided hunique offset root).Reachable position outputPosition := by
  let seam := sourceCorridorSerialInputFaceSeamGraphAt realization hcubic
    hrotation htwoSided hunique offset root
  rcases (SimpleGraph.mem_support seam).1 hposition with ⟨neighbor, hadj⟩
  rcases sourceCorridorSerialInputFaceSeamGraphAt_adj_touches_outputCrossing
      realization hcubic hrotation htwoSided hunique offset root hadj with
      ⟨step, hpositionOutput | hneighborOutput⟩
  · exact ⟨step, position, hpositionOutput, SimpleGraph.Reachable.rfl⟩
  · exact ⟨step, neighbor, hneighborOutput, hadj.reachable⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
