import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixUpdate
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileVertexSideSeam

/-!
# Finite support of a source serial-prefix seam

The residual seam between an open corridor prefix and its next literal Cell
cannot occur at an arbitrary ambient edge.  The Cell is a vertex-side region,
so its exclusive endpoint crosses the Cell cut.  That cut consists of the two
incoming and two outgoing source crossings.  Since the incoming crossings
already belong to the open prefix, a genuinely residual adjacency must touch
one of the two outgoing crossings.

Both tracked connectivity and occurrence-sensitive face progress use this
same geometric localization.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TerminalProfileVertexSideSeam
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialPrefixSeamSupportEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The literal Cell carrier is definitionally the regional edge set induced
by the complementary source-crosscut vertex side. -/
theorem sourceSlabLiteralCellRegionAt_eq_vertexSetRegionEdges_compl
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
    (offset : Fin (blockLength - 3)) :
    sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
        hunique offset =
      vertexSetRegionEdges embedded.cellulation.rotation.toRotationSystem
        ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
            offset).separatedLocalLayerPair.componentSide
          ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
              hunique offset).localLayerPairSourceCrosscutBoundaryData
            hcubic).component)ᶜ := by
  rfl

/-- Every edge crossing the literal Cell's vertex cut is one of its two
incoming or two outgoing source crossings. -/
theorem sourceSlabLiteralCellCrossing_eq_input_or_output
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
    (offset : Fin (blockLength - 3)) {edge : G.edgeSet}
    (hedge : edge ∈
      vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
            offset).separatedLocalLayerPair.componentSide
          ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
              hunique offset).localLayerPairSourceCrosscutBoundaryData
            hcubic).component)ᶜ) :
    (∃ step : Fin 2,
      edge = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step) ∨
      ∃ step : Fin 2,
        edge = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
          hunique offset).nextLocalLayerPrefixCrossing step := by
  let interface :=
    sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  let crossing : VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem
      (pair.componentSide boundary.component)ᶜ := ⟨edge, hedge⟩
  let sourceIndex :=
    (pair.sourceCrosscutComplementPort embedded.cellulation.rotation boundary).symm
      crossing
  have hsource :
      pair.sourceCrosscutComplementPort embedded.cellulation.rotation boundary
          sourceIndex = crossing :=
    (pair.sourceCrosscutComplementPort embedded.cellulation.rotation boundary)
      |>.apply_symm_apply crossing
  rcases sourceIndex with leftStep | rightStep
  · apply Or.inl
    let step : Fin 2 :=
      Fin.cast interface.localLayer_walk_length_eq_two leftStep
    refine ⟨step, ?_⟩
    have hedgeEq := congrArg Subtype.val hsource
    rw [pair.sourceCrosscutComplementPort_left
      embedded.cellulation.rotation boundary] at hedgeEq
    simpa [interface, pair, crossing, step,
      SourceConsecutiveSlabInterface.separatedLocalLayerPair,
      SourceConsecutiveSlabInterface.localLayerPrefixCrossing] using hedgeEq.symm
  · apply Or.inr
    let step : Fin 2 :=
      Fin.cast interface.nextLocalLayer_walk_length_eq_two rightStep
    refine ⟨step, ?_⟩
    have hedgeEq := congrArg Subtype.val hsource
    rw [pair.sourceCrosscutComplementPort_right
      embedded.cellulation.rotation boundary] at hedgeEq
    simpa [interface, pair, crossing, step,
      SourceConsecutiveSlabInterface.separatedLocalLayerPair,
      SourceConsecutiveSlabInterface.nextLocalLayerPrefixCrossing] using
        hedgeEq.symm

/-- Every tracked residual adjacency in the source serial update touches one
of the two outgoing source crossings. -/
theorem sourceCorridorSerialInputTrackedSeamGraphAt_adj_touches_outputCrossing
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
    (color : G.edgeSet → Color) (first second : Color) {x y : G.edgeSet}
    (hadj : (sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic
      hrotation htwoSided hunique offset color first second).Adj x y) :
    ∃ step : Fin 2,
      x = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
          offset).nextLocalLayerPrefixCrossing step ∨
        y = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
          hunique offset).nextLocalLayerPrefixCrossing step := by
  let interface :=
    sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset
  let inside :=
    (interface.separatedLocalLayerPair.componentSide
      (interface.localLayerPairSourceCrosscutBoundaryData hcubic).component)ᶜ
  have hlocalized :=
    regionalTrackedSeamGraph_adj_localizes_to_vertexCut
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
        hunique offset) inside color first second
      (by
        simpa [sourceCorridorSerialInputTrackedSeamGraphAt, inside,
          sourceSlabLiteralCellRegionAt_eq_vertexSetRegionEdges_compl]
          using hadj)
  rcases hlocalized with
    ⟨_hxLeft, _hxNotCell, _hyCell, hyNotLeft, hyCut⟩ |
      ⟨_hxCell, hxNotLeft, hxCut, _hyLeft, _hyNotCell⟩
  · rcases sourceSlabLiteralCellCrossing_eq_input_or_output realization hcubic
      hrotation htwoSided hunique offset hyCut with
      ⟨step, hyInput⟩ | ⟨step, hyOutput⟩
    · have hyMem : y ∈ sourceCorridorSerialCutRegionAt realization hcubic
          hrotation htwoSided hunique offset := by
        simpa [hyInput] using
          sourceCorridorSerialCutRegionAt_inputCrossing realization hcubic
            hrotation htwoSided hunique offset step
      exact (hyNotLeft hyMem).elim
    · exact ⟨step, Or.inr hyOutput⟩
  · rcases sourceSlabLiteralCellCrossing_eq_input_or_output realization hcubic
      hrotation htwoSided hunique offset hxCut with
      ⟨step, hxInput⟩ | ⟨step, hxOutput⟩
    · have hxMem : x ∈ sourceCorridorSerialCutRegionAt realization hcubic
          hrotation htwoSided hunique offset := by
        simpa [hxInput] using
          sourceCorridorSerialCutRegionAt_inputCrossing realization hcubic
            hrotation htwoSided hunique offset step
      exact (hxNotLeft hxMem).elim
    · exact ⟨step, Or.inl hxOutput⟩

/-- Every occurrence-sensitive facial residual has the same outgoing-crossing
support after projecting its positions to ambient edges. -/
theorem sourceCorridorSerialInputFaceSeamGraphAt_adj_touches_outputCrossing
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
    {x y : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card}
    (hadj : (sourceCorridorSerialInputFaceSeamGraphAt realization hcubic
      hrotation htwoSided hunique offset root).Adj x y) :
    ∃ step : Fin 2,
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root x =
          (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
            offset).nextLocalLayerPrefixCrossing step ∨
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root y =
          (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
            offset).nextLocalLayerPrefixCrossing step := by
  let interface :=
    sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset
  let inside :=
    (interface.separatedLocalLayerPair.componentSide
      (interface.localLayerPairSourceCrosscutBoundaryData hcubic).component)ᶜ
  have hlocalized :=
    faceRegionalSeamGraph_adj_localizes_to_vertexCut
      embedded.cellulation.rotation.toRotationSystem hcubic hrotation root
      (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
        hunique offset) inside
      (by
        simpa [sourceCorridorSerialInputFaceSeamGraphAt, inside,
          sourceSlabLiteralCellRegionAt_eq_vertexSetRegionEdges_compl]
          using hadj)
  rcases hlocalized with
    ⟨_hxLeft, _hxNotCell, _hyCell, hyNotLeft, hyCut⟩ |
      ⟨_hxCell, hxNotLeft, hxCut, _hyLeft, _hyNotCell⟩
  · rcases sourceSlabLiteralCellCrossing_eq_input_or_output realization hcubic
      hrotation htwoSided hunique offset hyCut with
      ⟨step, hyInput⟩ | ⟨step, hyOutput⟩
    · have hyMem : faceCycleEdge
          embedded.cellulation.rotation.toRotationSystem root y ∈
          sourceCorridorSerialCutRegionAt realization hcubic hrotation
            htwoSided hunique offset := by
        simpa [hyInput] using
          sourceCorridorSerialCutRegionAt_inputCrossing realization hcubic
            hrotation htwoSided hunique offset step
      exact (hyNotLeft hyMem).elim
    · exact ⟨step, Or.inr hyOutput⟩
  · rcases sourceSlabLiteralCellCrossing_eq_input_or_output realization hcubic
      hrotation htwoSided hunique offset hxCut with
      ⟨step, hxInput⟩ | ⟨step, hxOutput⟩
    · have hxMem : faceCycleEdge
          embedded.cellulation.rotation.toRotationSystem root x ∈
          sourceCorridorSerialCutRegionAt realization hcubic hrotation
            htwoSided hunique offset := by
        simpa [hxInput] using
          sourceCorridorSerialCutRegionAt_inputCrossing realization hcubic
            hrotation htwoSided hunique offset step
      exact (hxNotLeft hxMem).elim
    · exact ⟨step, Or.inl hxOutput⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
