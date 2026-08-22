import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseTrackedLocality

/-!
# Local attachment classes of a tracked serial rebase

The old endpoint of a tracked boundary-rebase seam was already known to lie
on a historical literal-Cell interface.  Geodesic locality now makes that
classification finite at the actual rebase: the endpoint is an input or
output crossing of the current Cell, or an output crossing of the immediately
preceding Cell.

This is the local attachment theorem needed by a finite rebase decoder.  It
does not claim that the parity escape's other endpoint is local, reconstruct
the complete successor profile, or identify the true cumulative frontier with
the two displayed old ports.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CubicFaceBoundaryAdjacency
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileRegionalCoverage
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseTrackedAttachmentEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Every tracked seam attachment to a successor rebase comes from one of
three bounded historical interface classes: the current Cell's input, its
output, or the immediately preceding Cell's output.  The newly displayed
endpoint is retained explicitly in the two-edge rebase region. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedSeamAt_adj_has_local_old_attachment
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
    (color : G.edgeSet → Color) (first second : Color) {x y : G.edgeSet}
    (hadj : (sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization
      hcubic hrotation htwoSided hunique offset hnext color first second).Adj
        x y) :
    ∃ old new : G.edgeSet,
      (embedded.cellulation.rotation.toRotationSystem.trackedEdgeGraph
        color first second).Adj old new ∧
      old ∈ (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges ∧
      new ∈ sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
        hrotation htwoSided hunique offset hnext ∧
      new ∉ (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges ∧
      ((∃ step : Fin 2,
          old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).localLayerPrefixCrossing step) ∨
        (∃ step : Fin 2,
          old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).nextLocalLayerPrefixCrossing step) ∨
        ∃ historical : Fin (blockLength - 3), ∃ step : Fin 2,
          historical.val + 1 = offset.val ∧
          old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique historical).nextLocalLayerPrefixCrossing step) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let newRegion := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization
    hcubic hrotation htwoSided hunique offset hnext
  have hraw := (regionalTrackedSeamGraph_adj_iff RS oldRegion newRegion
    color first second x y).1 hadj
  have holdBoundary :=
    sourceCorridorSerialBoundaryRebaseTrackedSeamAt_adj_oldEndpoint_mem_truePrefixCrossing
      realization hcubic hrotation htwoSided hunique offset hnext color first
        second hadj
  have classify {old new : G.edgeSet}
      (hadjAmbient : (RS.trackedEdgeGraph color first second).Adj old new)
      (hold : old ∈ oldRegion) (hnewRegion : new ∈ newRegion)
      (hnewOld : new ∉ oldRegion)
      (holdBoundary : old ∈
        sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1)) :
      ((∃ step : Fin 2,
          old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).localLayerPrefixCrossing step) ∨
        (∃ step : Fin 2,
          old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).nextLocalLayerPrefixCrossing step) ∨
        ∃ historical : Fin (blockLength - 3), ∃ step : Fin 2,
          historical.val + 1 = offset.val ∧
          old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique historical).nextLocalLayerPrefixCrossing step) := by
    rcases (mem_indexedCrossingEdgeSet_iff _ _).1 hnewRegion with
      ⟨newStep, hnew⟩
    rcases sourceCorridorSerialPrefixTrueCrossingEdge_eq_cell_input_or_output
        realization hcubic hrotation htwoSided hunique (offset.val + 1)
          holdBoundary with ⟨historical, hhistorical, hinput | houtput⟩
    · rcases hinput with ⟨oldStep, holdEq⟩
      have hindex :=
        sourceSlabInputCrossing_index_eq_of_lt_cut_of_adj_rebaseCrossing
          realization hcubic hrotation htwoSided hunique offset historical
            hnext hhistorical oldStep newStep (by
              simpa [RS, oldRegion, newRegion, holdEq, hnew] using
                hadjAmbient.1)
      have heq : historical = offset := Fin.ext hindex
      subst historical
      exact Or.inl ⟨oldStep, holdEq⟩
    · rcases houtput with ⟨oldStep, holdEq⟩
      have hindex :=
        sourceSlabOutputCrossing_index_eq_or_succ_eq_of_lt_cut_of_adj_rebaseCrossing
          realization hcubic hrotation htwoSided hunique offset historical
            hnext hhistorical oldStep newStep (by
              simpa [RS, oldRegion, newRegion, holdEq, hnew] using
                hadjAmbient.1)
      rcases hindex with hcurrent | hprevious
      · have heq : historical = offset := Fin.ext hcurrent
        subst historical
        exact Or.inr (Or.inl ⟨oldStep, holdEq⟩)
      · exact Or.inr (Or.inr ⟨historical, oldStep, hprevious, holdEq⟩)
  rcases hraw.2 with hforward | hbackward
  · have hxBoundary : x ∈
        sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1) := by
      rcases holdBoundary with hx | hy
      · exact hx.2
      · exact False.elim (hforward.2.2.2 hy.1)
    refine ⟨x, y, hraw.1, hforward.1, hforward.2.2.1,
      hforward.2.2.2, ?_⟩
    exact classify hraw.1 hforward.1 hforward.2.2.1 hforward.2.2.2
      hxBoundary
  · have hyBoundary : y ∈
        sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1) := by
      rcases holdBoundary with hx | hy
      · exact False.elim (hbackward.2.1 hx.1)
      · exact hy.2
    refine ⟨y, x, hraw.1.symm, hbackward.2.2.1, hbackward.1,
      hbackward.2.1, ?_⟩
    exact classify hraw.1.symm hbackward.2.2.1 hbackward.1 hbackward.2.1
      hyBoundary

/-- An oriented ambient tracked adjacency from the old prefix to one of the
two newly displayed rebase edges has its old endpoint in one of the three
bounded historical interface classes.  This is the endpoint-oriented form of
the classification used above; it is useful when retaining the literal
vertices of a seam rather than merely an existential old/new pair. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedOldEndpoint_has_local_attachment
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
    (color : G.edgeSet → Color) (first second : Color) {old new : G.edgeSet}
    (hadjAmbient :
      (embedded.cellulation.rotation.toRotationSystem.trackedEdgeGraph
        color first second).Adj old new)
    (hnewRegion : new ∈
      sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
        htwoSided hunique offset hnext)
    (holdBoundary : old ∈
      sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
        hrotation htwoSided hunique (offset.val + 1)) :
    ((∃ step : Fin 2,
        old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
          hunique offset).localLayerPrefixCrossing step) ∨
      (∃ step : Fin 2,
        old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
          hunique offset).nextLocalLayerPrefixCrossing step) ∨
      ∃ historical : Fin (blockLength - 3), ∃ step : Fin 2,
        historical.val + 1 = offset.val ∧
        old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
          hunique historical).nextLocalLayerPrefixCrossing step) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let newRegion := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization
    hcubic hrotation htwoSided hunique offset hnext
  rcases (mem_indexedCrossingEdgeSet_iff _ _).1 hnewRegion with
    ⟨newStep, hnew⟩
  rcases sourceCorridorSerialPrefixTrueCrossingEdge_eq_cell_input_or_output
      realization hcubic hrotation htwoSided hunique (offset.val + 1)
        holdBoundary with ⟨historical, hhistorical, hinput | houtput⟩
  · rcases hinput with ⟨oldStep, holdEq⟩
    have hindex :=
      sourceSlabInputCrossing_index_eq_of_lt_cut_of_adj_rebaseCrossing
        realization hcubic hrotation htwoSided hunique offset historical
          hnext hhistorical oldStep newStep (by
            simpa [RS, newRegion, holdEq, hnew] using hadjAmbient.1)
    have heq : historical = offset := Fin.ext hindex
    subst historical
    exact Or.inl ⟨oldStep, holdEq⟩
  · rcases houtput with ⟨oldStep, holdEq⟩
    have hindex :=
      sourceSlabOutputCrossing_index_eq_or_succ_eq_of_lt_cut_of_adj_rebaseCrossing
        realization hcubic hrotation htwoSided hunique offset historical
          hnext hhistorical oldStep newStep (by
            simpa [RS, newRegion, holdEq, hnew] using hadjAmbient.1)
    rcases hindex with hcurrent | hprevious
    · have heq : historical = offset := Fin.ext hcurrent
      subst historical
      exact Or.inr (Or.inl ⟨oldStep, holdEq⟩)
    · exact Or.inr (Or.inr ⟨historical, oldStep, hprevious, holdEq⟩)

/-- The occurrence-sensitive facial seam has the same three local attachment
classes after projecting its positions to ambient primal edges.  Keeping this
separate from the tracked theorem ensures that the finite rebase alphabet
respects the source's capped face-progress coordinate as well as its two-color
connectivity coordinate. -/
theorem sourceCorridorSerialBoundaryRebaseFaceSeamAt_adj_has_local_old_attachment
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
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    {x y : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card}
    (hadj : (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
      hrotation htwoSided hunique offset hnext root).Adj x y) :
    ∃ old new : Fin
        (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card,
      (faceCyclePositionGraph embedded.cellulation.rotation.toRotationSystem
        root).Adj old new ∧
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root old ∈
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges ∧
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root new ∈
        sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
          hrotation htwoSided hunique offset hnext ∧
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root new ∉
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges ∧
      ((∃ step : Fin 2,
          faceCycleEdge embedded.cellulation.rotation.toRotationSystem root old =
            (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
              hunique offset).localLayerPrefixCrossing step) ∨
        (∃ step : Fin 2,
          faceCycleEdge embedded.cellulation.rotation.toRotationSystem root old =
            (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
              hunique offset).nextLocalLayerPrefixCrossing step) ∨
        ∃ historical : Fin (blockLength - 3), ∃ step : Fin 2,
          historical.val + 1 = offset.val ∧
          faceCycleEdge embedded.cellulation.rotation.toRotationSystem root old =
            (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
              hunique historical).nextLocalLayerPrefixCrossing step) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let newRegion := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization
    hcubic hrotation htwoSided hunique offset hnext
  have hraw := (faceRegionalSeamGraph_adj_iff RS root oldRegion newRegion
    x y).1 hadj
  have hedgeAdj := edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj
    RS hcubic hrotation root hraw.1
  have holdBoundary :=
    sourceCorridorSerialBoundaryRebaseFaceSeamAt_adj_oldEndpoint_mem_truePrefixCrossing
      realization hcubic hrotation htwoSided hunique offset hnext root hadj
  have classify {old new : G.edgeSet}
      (hadjAmbient : RS.edgeAdjacencyGraph.Adj old new)
      (hnewRegion : new ∈ newRegion)
      (holdBoundary : old ∈
        sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1)) :
      ((∃ step : Fin 2,
          old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).localLayerPrefixCrossing step) ∨
        (∃ step : Fin 2,
          old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).nextLocalLayerPrefixCrossing step) ∨
        ∃ historical : Fin (blockLength - 3), ∃ step : Fin 2,
          historical.val + 1 = offset.val ∧
          old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique historical).nextLocalLayerPrefixCrossing step) := by
    rcases (mem_indexedCrossingEdgeSet_iff _ _).1 hnewRegion with
      ⟨newStep, hnew⟩
    rcases sourceCorridorSerialPrefixTrueCrossingEdge_eq_cell_input_or_output
        realization hcubic hrotation htwoSided hunique (offset.val + 1)
          holdBoundary with ⟨historical, hhistorical, hinput | houtput⟩
    · rcases hinput with ⟨oldStep, holdEq⟩
      have hindex :=
        sourceSlabInputCrossing_index_eq_of_lt_cut_of_adj_rebaseCrossing
          realization hcubic hrotation htwoSided hunique offset historical
            hnext hhistorical oldStep newStep (by
              simpa [RS, newRegion, holdEq, hnew] using hadjAmbient)
      have heq : historical = offset := Fin.ext hindex
      subst historical
      exact Or.inl ⟨oldStep, holdEq⟩
    · rcases houtput with ⟨oldStep, holdEq⟩
      have hindex :=
        sourceSlabOutputCrossing_index_eq_or_succ_eq_of_lt_cut_of_adj_rebaseCrossing
          realization hcubic hrotation htwoSided hunique offset historical
            hnext hhistorical oldStep newStep (by
              simpa [RS, newRegion, holdEq, hnew] using hadjAmbient)
      rcases hindex with hcurrent | hprevious
      · have heq : historical = offset := Fin.ext hcurrent
        subst historical
        exact Or.inr (Or.inl ⟨oldStep, holdEq⟩)
      · exact Or.inr (Or.inr ⟨historical, oldStep, hprevious, holdEq⟩)
  rcases hraw.2 with hforward | hbackward
  · have hxBoundary : faceCycleEdge RS root x ∈
        sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1) := by
      rcases holdBoundary with hx | hy
      · exact hx.2
      · exact False.elim (hforward.2.2.2 hy.1)
    refine ⟨x, y, hraw.1, hforward.1, hforward.2.2.1,
      hforward.2.2.2, ?_⟩
    exact classify hedgeAdj hforward.2.2.1 hxBoundary
  · have hyBoundary : faceCycleEdge RS root y ∈
        sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1) := by
      rcases holdBoundary with hx | hy
      · exact False.elim (hbackward.2.1 hx.1)
      · exact hy.2
    refine ⟨y, x, hraw.1.symm, hbackward.2.2.1, hbackward.1,
      hbackward.2.1, ?_⟩
    exact classify hedgeAdj.symm hbackward.1 hyBoundary

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
