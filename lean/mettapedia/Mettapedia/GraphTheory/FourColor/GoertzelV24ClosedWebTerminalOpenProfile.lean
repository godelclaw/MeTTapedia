import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebTerminalCrosscutProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLiteralProfileMatrix
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileRestriction

/-!
# Terminal-aware profiles from literal source open colorings

The five cap-foot terminals have already been attached geometrically to both
source crosscuts.  This file reads those enriched profiles from an actual Tait
coloring of the retained open region.  Thus the terminal-aware states used by
the Cell-3 transfer are populated without assuming a coloring of the closed
ambient counterexample.

Forgetting the five terminal rows and columns recovers the existing literal
source-interface profiles exactly.  The established zero-terminal `Count`
semantics is therefore a projection of this refinement, rather than a
separate interpretation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24GraphDerivedTerminalProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SpliceUnification
open GoertzelV24SpliceUnification.OrderedCutSidesData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebTerminalOpenProfileEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

/-- Read the left source crosscut, including all five fixed cap-foot
terminals, from a genuine coloring of the retained literal open region. -/
noncomputable def sourceCrosscutLiteralOpenLeftTerminalProfile
    {data : AnnularBoundaryData G 5} {ambient : G.EdgeColoring Color}
    (web : Instance data ambient)
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
    (coloring : (pair.sourceCrosscutOpenRegion
      web.annular.cellulation.rotation boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutOpenRegion
      web.annular.cellulation.rotation boundary).IsTaitEdgeColoring coloring) :
    CorridorCutProfile pair.left.walk.length 5
      (pair.sourceCrosscutFaceFragmentCount
        web.annular.cellulation.rotation boundary) := by
  let cut := sourceCrosscutLeftCutDataWithInnerTerminals web pair boundary
  let hports := sourceCrosscutLeftCutDataWithInnerTerminals_portsInRegion
    pair boundary hseparated hinner
  exact cut.regionalProfile
    (pair.sourceCrosscutLiteralColorOnVertexSide
      web.annular.cellulation.rotation boundary coloring)
    (fun crossing =>
      pair.sourceCrosscutLiteralColorOnVertexSide_ne_zero
        web.annular.cellulation.rotation boundary coloring hcoloring
        (hports (.inl crossing)))

/-- Read the aligned right source crosscut from the same literal open
coloring, with the same five fixed terminals and source crossing order. -/
noncomputable def sourceCrosscutLiteralOpenRightTerminalProfile
    {data : AnnularBoundaryData G 5} {ambient : G.EdgeColoring Color}
    (web : Instance data ambient)
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
    (coloring : (pair.sourceCrosscutOpenRegion
      web.annular.cellulation.rotation boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutOpenRegion
      web.annular.cellulation.rotation boundary).IsTaitEdgeColoring coloring) :
    CorridorCutProfile pair.left.walk.length 5
      (pair.sourceCrosscutFaceFragmentCount
        web.annular.cellulation.rotation boundary) := by
  let cut := sourceCrosscutRightCutDataWithInnerTerminals web pair boundary
  let hports := sourceCrosscutRightCutDataWithInnerTerminals_portsInRegion
    pair boundary hseparated hinner
  exact cut.regionalProfile
    (pair.sourceCrosscutLiteralColorOnVertexSide
      web.annular.cellulation.rotation boundary coloring)
    (fun crossing =>
      pair.sourceCrosscutLiteralColorOnVertexSide_ne_zero
        web.annular.cellulation.rotation boundary coloring hcoloring
        (hports (.inl crossing)))

/-- Forgetting terminal observations on the enriched left state recovers the
existing literal left source-interface profile. -/
@[simp] theorem forgetTerminals_sourceCrosscutLiteralOpenLeftTerminalProfile
    {data : AnnularBoundaryData G 5} {ambient : G.EdgeColoring Color}
    (web : Instance data ambient)
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
    (coloring : (pair.sourceCrosscutOpenRegion
      web.annular.cellulation.rotation boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutOpenRegion
      web.annular.cellulation.rotation boundary).IsTaitEdgeColoring coloring) :
    forgetTerminals
        (sourceCrosscutLiteralOpenLeftTerminalProfile web pair boundary
          hseparated hinner coloring hcoloring) =
      pair.sourceCrosscutLiteralOpenLeftProfile
        web.annular.cellulation.rotation boundary coloring hcoloring := by
  simp [sourceCrosscutLiteralOpenLeftTerminalProfile,
    sourceCrosscutLeftCutDataWithInnerTerminals,
    withInnerBoundaryTerminals,
    SeparatedAlignedSimpleDualCrosscuts.sourceCrosscutLiteralOpenLeftProfile]

/-- Forgetting terminal observations on the enriched right state likewise
recovers the existing aligned right source-interface profile. -/
@[simp] theorem forgetTerminals_sourceCrosscutLiteralOpenRightTerminalProfile
    {data : AnnularBoundaryData G 5} {ambient : G.EdgeColoring Color}
    (web : Instance data ambient)
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
    (coloring : (pair.sourceCrosscutOpenRegion
      web.annular.cellulation.rotation boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutOpenRegion
      web.annular.cellulation.rotation boundary).IsTaitEdgeColoring coloring) :
    forgetTerminals
        (sourceCrosscutLiteralOpenRightTerminalProfile web pair boundary
          hseparated hinner coloring hcoloring) =
      pair.sourceCrosscutLiteralOpenRightProfile
        web.annular.cellulation.rotation boundary coloring hcoloring := by
  simp [sourceCrosscutLiteralOpenRightTerminalProfile,
    sourceCrosscutRightCutDataWithInnerTerminals,
    withInnerBoundaryTerminals,
    SeparatedAlignedSimpleDualCrosscuts.sourceCrosscutLiteralOpenRightProfile]

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
