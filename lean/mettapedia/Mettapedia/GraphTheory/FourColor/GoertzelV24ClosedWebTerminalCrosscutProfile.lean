import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSpliceBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAtGoodWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedTerminalProfile

/-!
# Terminal-aware profiles on source crosscuts

The five inner-boundary edges are the fixed cap feet whose ancestry must
survive the Cell-3 splice.  This file attaches them to the two actual source
crosscuts, rather than to the small Cell region between those crosscuts.

The construction is deliberately conditional on the already-defined
`ProtectedInnerInterface.InnerBoundaryKept` certificate.  That certificate
is concrete geometry: every dart of every cap-foot edge lies on the retained
side.  From it we prove that all five terminal edges genuinely belong to the
graph-derived profile region.  No terminal membership or connectivity datum
is supplied as a free profile field.

These retained-side profiles are splice-boundary data.  They are not the
local Cell generator and are not yet the cumulative Cell update law.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24GraphDerivedTerminalProfile
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SpliceUnification
open GoertzelV24SpliceUnification.OrderedCutSidesData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebTerminalCrosscutEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

/-- The retained inner-interface certificate puts every cap-foot edge in the
literal vertex-side region used by both source crosscut profiles. -/
theorem innerBoundaryEdge_mem_sourceCrosscutRegion
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation)
    (hinner : ProtectedInnerInterface.InnerBoundaryKept
      (pair.sourceCrosscutLayerSpliceData
        web.annular.cellulation.rotation boundary hseparated))
    (terminal : Fin 5) :
    data.innerBoundaryEdge terminal ∈
      vertexSetRegionEdges web.annular.RS
        (pair.componentSide boundary.component) := by
  let interface := ProtectedInnerInterface.of_innerBoundaryKept hinner
  let dart : web.annular.RS.D := (interface.dart terminal).1.1
  rw [mem_vertexSetRegionEdges_iff]
  refine ⟨web.annular.RS.vertOf dart, ?_, ?_⟩
  · rw [web.annular.RS.mem_endpoints_iff]
    refine ⟨dart, ?_, rfl⟩
    apply (web.annular.RS.mem_dartsOn).2
    exact interface.edge_eq terminal
  · exact (interface.dart terminal).1.2

/-- The left source transversal with the five actual cap-foot terminals. -/
noncomputable def sourceCrosscutLeftCutDataWithInnerTerminals
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair) :
    GraphCorridorCutData web.annular.RS pair.left.walk.length 5
      (pair.sourceCrosscutFaceFragmentCount
        web.annular.cellulation.rotation boundary) :=
  withInnerBoundaryTerminals data
    (pair.sourceCrosscutLeftCutData
      web.annular.cellulation.rotation boundary)

/-- The aligned right source transversal with the same five cap-foot
terminals. -/
noncomputable def sourceCrosscutRightCutDataWithInnerTerminals
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair) :
    GraphCorridorCutData web.annular.RS pair.left.walk.length 5
      (pair.sourceCrosscutFaceFragmentCount
        web.annular.cellulation.rotation boundary) :=
  withInnerBoundaryTerminals data
    (pair.sourceCrosscutRightCutData
      web.annular.cellulation.rotation boundary)

/-- The two source crosscuts as one concrete splice boundary carrying the
five cap-foot terminals.  All geometric splice fields are inherited from
the existing source construction; only the profile terminal coordinate is
enriched. -/
noncomputable def sourceCrosscutTerminalOrderedCutSidesData
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair) :
    OrderedCutSidesData web.annular.RS pair.left.walk.length 5
      (pair.sourceCrosscutFaceFragmentCount
        web.annular.cellulation.rotation boundary) := by
  let base := pair.sourceCrosscutOrderedCutSidesData
    web.annular.cellulation.rotation boundary
  exact {
    keep := base.keep
    left := sourceCrosscutLeftCutDataWithInnerTerminals web pair boundary
    right := sourceCrosscutRightCutDataWithInnerTerminals web pair boundary
    leftCrosses := base.leftCrosses
    rightCrosses := base.rightCrosses
    leftInjective := base.leftInjective
    rightInjective := base.rightInjective
    cover := base.cover
    disjoint := base.disjoint
    outer_kept := base.outer_kept
    removed := base.removed
    removed_not_kept := base.removed_not_kept }

/-- Install the already-constructed source seam on the terminal-aware pair.
Terminal coordinates do not alter the cut edges or their seam pairing. -/
noncomputable def sourceCrosscutTerminalLayerSpliceData
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation) :
    OrderedCutSpliceData web.annular.RS pair.left.walk.length 5
      (pair.sourceCrosscutFaceFragmentCount
        web.annular.cellulation.rotation boundary) :=
  (sourceCrosscutTerminalOrderedCutSidesData web pair boundary).splice
    (fun step =>
      pair.sourceCrosscutSeamEndpoints_of_matchedCrossingsVertexDisjoint
        web.annular.cellulation.rotation boundary hseparated step)

@[simp] theorem sourceCrosscutTerminalLayerSpliceData_keep
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation)
    (vertex : V) :
    (sourceCrosscutTerminalLayerSpliceData web pair boundary hseparated).keep vertex <->
      vertex ∈ pair.componentSide boundary.component := by
  rfl

/-- The previously constructed retained-inner-boundary certificate transports
definitionally to the terminal-aware splice, since the retained side is
unchanged. -/
theorem sourceCrosscutTerminalLayerSpliceData_innerBoundaryKept
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation)
    (hinner : ProtectedInnerInterface.InnerBoundaryKept
      (pair.sourceCrosscutLayerSpliceData
        web.annular.cellulation.rotation boundary hseparated)) :
    ProtectedInnerInterface.InnerBoundaryKept
      (sourceCrosscutTerminalLayerSpliceData web pair boundary hseparated) := by
  intro terminal dart hdart
  exact hinner terminal dart hdart

/-- Every crossing and terminal port of the terminal-aware left source
profile is a literal edge of its retained-side region. -/
theorem sourceCrosscutLeftCutDataWithInnerTerminals_portsInRegion
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation)
    (hinner : ProtectedInnerInterface.InnerBoundaryKept
      (pair.sourceCrosscutLayerSpliceData
        web.annular.cellulation.rotation boundary hseparated)) :
    (sourceCrosscutLeftCutDataWithInnerTerminals web pair boundary).PortsInRegion := by
  rw [sourceCrosscutLeftCutDataWithInnerTerminals,
    withInnerBoundaryTerminals_portsInRegion_iff]
  refine ⟨pair.sourceCrosscutLeftCutData_portsInRegion
    web.annular.cellulation.rotation boundary, ?_⟩
  exact fun terminal =>
    innerBoundaryEdge_mem_sourceCrosscutRegion pair boundary hseparated hinner terminal

/-- Every crossing and terminal port of the terminal-aware right source
profile is a literal edge of the same retained-side region. -/
theorem sourceCrosscutRightCutDataWithInnerTerminals_portsInRegion
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation)
    (hinner : ProtectedInnerInterface.InnerBoundaryKept
      (pair.sourceCrosscutLayerSpliceData
        web.annular.cellulation.rotation boundary hseparated)) :
    (sourceCrosscutRightCutDataWithInnerTerminals web pair boundary).PortsInRegion := by
  rw [sourceCrosscutRightCutDataWithInnerTerminals,
    withInnerBoundaryTerminals_portsInRegion_iff]
  refine ⟨pair.sourceCrosscutRightCutData_portsInRegion
    web.annular.cellulation.rotation boundary, ?_⟩
  exact fun terminal =>
    innerBoundaryEdge_mem_sourceCrosscutRegion pair boundary hseparated hinner terminal

/-- A left-transversal crossing edge cannot be one of the five retained cap
feet: its outward dart has an endpoint outside, while every dart of a cap
foot is retained. -/
theorem sourceCrosscutLeft_crossingEdge_ne_innerBoundaryEdge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation)
    (hinner : ProtectedInnerInterface.InnerBoundaryKept
      (pair.sourceCrosscutLayerSpliceData
        web.annular.cellulation.rotation boundary hseparated))
    (crossing : Fin pair.left.walk.length) (terminal : Fin 5) :
    pair.left.crossingEdge hunique crossing ≠
      data.innerBoundaryEdge terminal := by
  intro hedge
  rcases boundary.leftCrosses crossing with
    ⟨dart, hdartEdge, _hinside, houtside⟩
  apply houtside
  apply hinner terminal (web.annular.RS.alpha dart)
  apply (web.annular.RS.mem_dartsOn).2
  rw [web.annular.RS.edge_alpha, hdartEdge, hedge]

/-- The corresponding disjointness statement for the aligned right source
transversal. -/
theorem sourceCrosscutRight_crossingEdge_ne_innerBoundaryEdge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation)
    (hinner : ProtectedInnerInterface.InnerBoundaryKept
      (pair.sourceCrosscutLayerSpliceData
        web.annular.cellulation.rotation boundary hseparated))
    (crossing : Fin pair.left.walk.length) (terminal : Fin 5) :
    pair.right.crossingEdge hunique (Fin.cast pair.length_eq crossing) ≠
      data.innerBoundaryEdge terminal := by
  intro hedge
  rcases boundary.rightCrosses (Fin.cast pair.length_eq crossing) with
    ⟨dart, hdartEdge, _hinside, houtside⟩
  apply houtside
  apply hinner terminal (web.annular.RS.alpha dart)
  apply (web.annular.RS.mem_dartsOn).2
  rw [web.annular.RS.edge_alpha, hdartEdge, hedge]

/-- Crossing ports and cap-foot terminals form one duplicate-free left
profile interface. -/
theorem sourceCrosscutLeftCutDataWithInnerTerminals_portsInjective
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation)
    (hinner : ProtectedInnerInterface.InnerBoundaryKept
      (pair.sourceCrosscutLayerSpliceData
        web.annular.cellulation.rotation boundary hseparated)) :
    (sourceCrosscutLeftCutDataWithInnerTerminals web pair boundary).PortsInjective := by
  rw [sourceCrosscutLeftCutDataWithInnerTerminals,
    withInnerBoundaryTerminals, withTerminalEdges_portsInjective_iff]
  exact ⟨boundary.leftInjective, data.innerBoundaryEdge.injective,
    sourceCrosscutLeft_crossingEdge_ne_innerBoundaryEdge
      pair boundary hseparated hinner⟩

/-- Crossing ports and cap-foot terminals form one duplicate-free aligned
right profile interface. -/
theorem sourceCrosscutRightCutDataWithInnerTerminals_portsInjective
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation)
    (hinner : ProtectedInnerInterface.InnerBoundaryKept
      (pair.sourceCrosscutLayerSpliceData
        web.annular.cellulation.rotation boundary hseparated)) :
    (sourceCrosscutRightCutDataWithInnerTerminals web pair boundary).PortsInjective := by
  rw [sourceCrosscutRightCutDataWithInnerTerminals,
    withInnerBoundaryTerminals, withTerminalEdges_portsInjective_iff]
  refine ⟨?_, data.innerBoundaryEdge.injective,
    sourceCrosscutRight_crossingEdge_ne_innerBoundaryEdge
      pair boundary hseparated hinner⟩
  intro first second heq
  have hcast := boundary.rightInjective heq
  exact Fin.cast_injective pair.length_eq hcast

/-- Terminal augmentation leaves the left source cut's literal face
fragments unchanged. -/
theorem sourceCrosscutLeftCutDataWithInnerTerminals_fragmentsOnFaceInRegion
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair) :
    (sourceCrosscutLeftCutDataWithInnerTerminals web pair boundary).FragmentsOnFaceInRegion := by
  rw [sourceCrosscutLeftCutDataWithInnerTerminals,
    withInnerBoundaryTerminals, withTerminalEdges_fragmentsOnFaceInRegion_iff]
  exact pair.sourceCrosscutCutData_fragmentsOnFaceInRegion
    web.annular.cellulation.rotation boundary (pair.left.crossingEdge hunique)

/-- Terminal augmentation likewise leaves the aligned right source cut's
literal face fragments unchanged. -/
theorem sourceCrosscutRightCutDataWithInnerTerminals_fragmentsOnFaceInRegion
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData
      web.annular.cellulation.rotation pair) :
    (sourceCrosscutRightCutDataWithInnerTerminals web pair boundary).FragmentsOnFaceInRegion := by
  rw [sourceCrosscutRightCutDataWithInnerTerminals,
    withInnerBoundaryTerminals, withTerminalEdges_fragmentsOnFaceInRegion_iff]
  exact pair.sourceCrosscutCutData_fragmentsOnFaceInRegion
    web.annular.cellulation.rotation boundary
      (fun step => pair.right.crossingEdge hunique (Fin.cast pair.length_eq step))

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
