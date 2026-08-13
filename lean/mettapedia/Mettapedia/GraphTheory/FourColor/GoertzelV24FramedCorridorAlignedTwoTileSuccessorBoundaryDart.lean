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

/-- On the matched transverse edge, the two literal exposed darts have only
the two genuine possibilities: they are alpha-opposite, or they are the same
ambient dart.  The latter alternative is not a serial seam; it records a
shared enclosed endpoint and is kept explicit below. -/
theorem sourceTwoTileAlignedEnclosedOutputBoundaryDartAt_eq_or_alpha_successorInput
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
    (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
        hrotation htwoSided hunique offset step).1.1 =
      (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt realization
        hcubic hrotation htwoSided hunique offset step).1.1 ∨
    embedded.cellulation.rotation.toRotationSystem.alpha
        (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
          hrotation htwoSided hunique offset step).1.1 =
      (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt realization
        hcubic hrotation htwoSided hunique offset step).1.1 := by
  let left := (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization
    hcubic hrotation htwoSided hunique offset step).1.1
  let right := (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt
    realization hcubic hrotation htwoSided hunique offset step).1.1
  have hedge : embedded.cellulation.rotation.toRotationSystem.edgeOf left =
      embedded.cellulation.rotation.toRotationSystem.edgeOf right := by
    simpa [left, right] using
      sourceTwoTileAlignedEnclosedOutputBoundaryDartAt_edgeOf_eq_successorInput
        realization hcubic hrotation htwoSided hunique offset step
  rcases embedded.cellulation.rotation.toRotationSystem.edge_fiber_two_cases
      (e := embedded.cellulation.rotation.toRotationSystem.edgeOf left)
      (d := left) (y := right) rfl hedge.symm with hsame | hopposite
  · exact Or.inl hsame.symm
  · exact Or.inr hopposite.symm

/-- If the matched transverse darts are the same rather than alpha-opposite,
then the two enclosed slab carriers literally share that dart's base vertex.
This is an obstruction to treating the two vertex-side tangles as a disjoint
serial composite. -/
theorem sourceTwoTileAlignedEnclosed_vertexOverlap_of_outputBoundaryDart_eq_successorInput
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
    (hsame :
      (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
          hrotation htwoSided hunique offset step).1.1 =
        (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt realization
          hcubic hrotation htwoSided hunique offset step).1.1) :
    ∃ vertex,
      deletedRegionKeep
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique (sourceTwoTileSuccessorStartOffset offset)).componentSide
        vertex ∧
      deletedRegionKeep
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique (sourceTwoTileSuccessorNextOffset offset)).componentSide
        vertex := by
  refine ⟨embedded.cellulation.rotation.toRotationSystem.vertOf
    (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
      hrotation htwoSided hunique offset step).1.1, ?_, ?_⟩
  · exact (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
      hrotation htwoSided hunique offset step).1.2
  · rw [hsame]
    exact (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt realization
      hcubic hrotation htwoSided hunique offset step).1.2

/-- Every named consecutive transverse edge is now classified without any
unproved geometry: it is either a correctly oriented serial seam, or it
exhibits a concrete shared vertex of the two enclosed carriers.  This does
not decide which branch the source realization occupies. -/
theorem sourceTwoTileAlignedEnclosed_alphaSeam_or_vertexOverlap
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
        hcubic hrotation htwoSided hunique offset step).1.1 ∨
    ∃ vertex,
      deletedRegionKeep
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique (sourceTwoTileSuccessorStartOffset offset)).componentSide
        vertex ∧
      deletedRegionKeep
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique (sourceTwoTileSuccessorNextOffset offset)).componentSide
        vertex := by
  rcases sourceTwoTileAlignedEnclosedOutputBoundaryDartAt_eq_or_alpha_successorInput
      realization hcubic hrotation htwoSided hunique offset step with hsame | halpha
  · exact Or.inr
      (sourceTwoTileAlignedEnclosed_vertexOverlap_of_outputBoundaryDart_eq_successorInput
        realization hcubic hrotation htwoSided hunique offset step hsame)
  · exact Or.inl halpha

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

/-- Disjoint enclosed vertex carriers force the common transverse edge to be
exposed by opposite darts.  This is the exact local orientation consequence
of the global geometry still needed for a literal serial composite; it does
not assert that the source's sliding two-tile carriers are disjoint. -/
theorem sourceTwoTileAlignedEnclosedOutputBoundaryDartAt_eq_alpha_successorInput_of_disjoint
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
    (hdisjoint : Disjoint
      {vertex | deletedRegionKeep
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique (sourceTwoTileSuccessorStartOffset offset)).componentSide
        vertex}
      {vertex | deletedRegionKeep
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique (sourceTwoTileSuccessorNextOffset offset)).componentSide
        vertex}) :
    embedded.cellulation.rotation.toRotationSystem.alpha
        (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
          hrotation htwoSided hunique offset step).1.1 =
      (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt realization
        hcubic hrotation htwoSided hunique offset step).1.1 := by
  apply sourceTwoTileAlignedEnclosedOutputBoundaryDartAt_eq_alpha_successorInput_of_not_keep
    realization hcubic hrotation htwoSided hunique offset step
  exact Set.disjoint_left.mp hdisjoint
    (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
      hrotation htwoSided hunique offset step).1.2

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
