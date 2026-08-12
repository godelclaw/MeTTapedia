import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryDartOpposite
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileSuccessorInterface

/-!
# Boundary darts at a consecutive aligned-slab interface

The source coordinates already show that the output transverse edge of one
aligned slab is the input transverse edge of the following slab.  To turn
that coordinate fact into physical gluing, the two exposed boundary darts
must be alpha-opposites.  This file records the two literal boundary darts
and reduces that orientation statement to a single source-side membership
fact.  It deliberately does not assume the membership fact, region
disjointness, or a serial composite.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/- Keep the edge equality instance aligned with the source-aligned boundary
   modules, whose physical crossing carriers use the ordinary subtype
   instance. -/
local instance framedCorridorAlignedTwoTileSuccessorBoundaryDartEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The literal outgoing boundary dart of the left aligned slab at the
transverse interface it shares physically with its successor. -/
noncomputable def sourceTwoTileAlignedEnclosedOutputBoundaryDartAt
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
    (offset : Fin (blockLength - 5)) (step : Fin 2) :
    BoundaryDart embedded.cellulation.rotation.toRotationSystem
      (deletedRegionKeep
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique (sourceTwoTileSuccessorStartOffset offset)).componentSide) :=
  sourceTwoTileAlignedTerminalPortBoundaryDartEquiv realization hcubic
    hrotation htwoSided hunique (sourceTwoTileSuccessorStartOffset offset)
      (.inl (sourceTwoTileAlignedSecondTerminalCrossingIndex step))

/-- The literal incoming boundary dart of the successor aligned slab at its
shared transverse interface. -/
noncomputable def sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt
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
    (offset : Fin (blockLength - 5)) (step : Fin 2) :
    BoundaryDart embedded.cellulation.rotation.toRotationSystem
      (deletedRegionKeep
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique (sourceTwoTileSuccessorNextOffset offset)).componentSide) :=
  sourceTwoTileAlignedTerminalPortBoundaryDartEquiv realization hcubic
    hrotation htwoSided hunique (sourceTwoTileSuccessorNextOffset offset)
      (.inl (sourceTwoTileAlignedFirstTerminalCrossingIndex step))

/-- The two named boundary darts lie on the same physical source edge.  This
is only the coordinate part of gluing; the orientation is isolated below. -/
theorem sourceTwoTileAlignedEnclosedOutputBoundaryDartAt_edgeOf_eq_successorInput
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
    (offset : Fin (blockLength - 5)) (step : Fin 2) :
    embedded.cellulation.rotation.toRotationSystem.edgeOf
        (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
          hrotation htwoSided hunique offset step).1.1 =
    embedded.cellulation.rotation.toRotationSystem.edgeOf
        (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt realization
          hcubic hrotation htwoSided hunique offset step).1.1 := by
  calc
    embedded.cellulation.rotation.toRotationSystem.edgeOf
        (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
          hrotation htwoSided hunique offset step).1.1 =
        (sourceTwoTileAlignedEnclosedSecondTerminalProfileDataAt realization
          hcubic hrotation htwoSided hunique
          (sourceTwoTileSuccessorStartOffset offset)).crossingEdge step := by
      unfold sourceTwoTileAlignedEnclosedOutputBoundaryDartAt
      rw [sourceTwoTileAlignedTerminalPortBoundaryDartEquiv_edgeOf]
      rw [← sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portEdge]
      rfl
    _ =
        (sourceTwoTileAlignedEnclosedFirstTerminalProfileDataAt realization
          hcubic hrotation htwoSided hunique
          (sourceTwoTileSuccessorNextOffset offset)).crossingEdge step :=
      sourceTwoTileAlignedEnclosedOutputCrossing_eq_successorInputCrossing realization
        hcubic hrotation htwoSided hunique offset step
    _ = embedded.cellulation.rotation.toRotationSystem.edgeOf
        (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt realization
          hcubic hrotation htwoSided hunique offset step).1.1 := by
      unfold sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt
      rw [sourceTwoTileAlignedTerminalPortBoundaryDartEquiv_edgeOf]
      rw [← sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portEdge]
      rfl

/-- The remaining orientation condition for physical serial gluing is exactly
that the outgoing base vertex lies outside the successor's enclosed side.
Once that source-side fact is proved, the common transverse edge is exposed
by alpha-opposite darts. -/
theorem sourceTwoTileAlignedEnclosedOutputBoundaryDartAt_eq_alpha_successorInput_of_not_keep
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
    (offset : Fin (blockLength - 5)) (step : Fin 2)
    (hnotKeep : ¬ deletedRegionKeep
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique (sourceTwoTileSuccessorNextOffset offset)).componentSide
      (embedded.cellulation.rotation.toRotationSystem.vertOf
        (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
          hrotation htwoSided hunique offset step).1.1)) :
    embedded.cellulation.rotation.toRotationSystem.alpha
        (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
          hrotation htwoSided hunique offset step).1.1 =
      (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt realization
        hcubic hrotation htwoSided hunique offset step).1.1 := by
  apply alpha_eq_of_boundaryDart_edgeOf_eq_of_not_keep_vert
    embedded.cellulation.rotation.toRotationSystem
    (deletedRegionKeep
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique (sourceTwoTileSuccessorStartOffset offset)).componentSide)
    (deletedRegionKeep
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique (sourceTwoTileSuccessorNextOffset offset)).componentSide)
  · exact sourceTwoTileAlignedEnclosedOutputBoundaryDartAt_edgeOf_eq_successorInput
      realization hcubic hrotation htwoSided hunique offset step
  · exact hnotKeep

/-- The remaining source-side orientation fact is not merely sufficient: on
the already matched transverse edge it is exactly equivalent to alpha-opposite
boundary darts.  Thus physical serial gluing has one concrete endpoint-side
obligation before any ambient-carrier or union argument is attempted. -/
theorem sourceTwoTileAlignedEnclosedOutputBoundaryDartAt_eq_alpha_successorInput_iff_not_keep
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
    (offset : Fin (blockLength - 5)) (step : Fin 2) :
    embedded.cellulation.rotation.toRotationSystem.alpha
        (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
          hrotation htwoSided hunique offset step).1.1 =
      (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt realization
        hcubic hrotation htwoSided hunique offset step).1.1 ↔
    ¬ deletedRegionKeep
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique (sourceTwoTileSuccessorNextOffset offset)).componentSide
      (embedded.cellulation.rotation.toRotationSystem.vertOf
        (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
          hrotation htwoSided hunique offset step).1.1) := by
  exact alpha_eq_boundaryDart_iff_not_keep_vert_of_edgeOf_eq
    embedded.cellulation.rotation.toRotationSystem
    (deletedRegionKeep
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique (sourceTwoTileSuccessorStartOffset offset)).componentSide)
    (deletedRegionKeep
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique (sourceTwoTileSuccessorNextOffset offset)).componentSide)
    (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
      hrotation htwoSided hunique offset step)
    (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt realization
      hcubic hrotation htwoSided hunique offset step)
    (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt_edgeOf_eq_successorInput
      realization hcubic hrotation htwoSided hunique offset step)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
