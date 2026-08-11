import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebTerminalOpenProfile

/-!
# Terminal-aware `Count` support on a literal source crosscut

The existing literal source matrix records complete zero-terminal interface
profiles.  Cell 3 also needs the five fixed cap-foot terminals.  This file
counts the same genuine retained-open-region Tait colorings by their enriched
five-terminal profiles and proves that forgetting terminal observations gives
exactly the existing full-profile matrix support.

Thus the boundary-color audit and the older zero-terminal matrix are honest
projections of a finite relation on the manuscript's joint profile data.  No
terminal value is invented, and no deterministic profile update is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24CorridorTransferMatrix
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedTerminalProfile

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebTerminalProfileCountEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

/-- The exact terminal-aware interface carrier at the two source crosscuts.
It has the same graph-computed fragment coordinate as the existing literal
retained-open profile, with five additional fixed cap-foot ports. -/
abbrev SourceCrosscutTerminalInterfaceProfile
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
      web.annular.cellulation.rotation pair) :=
  CorridorCutProfile pair.left.walk.length 5
    (pair.sourceCrosscutFaceFragmentCount
      web.annular.cellulation.rotation boundary)

/-- The finite fiber of literal retained-open Tait colorings realizing one
pair of terminal-aware source-interface profiles. -/
noncomputable def sourceCrosscutLiteralOpenTerminalProfilePairFiber
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
    (left right : SourceCrosscutTerminalInterfaceProfile web pair boundary) :
    Finset (pair.SourceCrosscutLiteralOpenTaitColoring
      web.annular.cellulation.rotation boundary) := by
  classical
  exact Finset.univ.filter fun coloring =>
    sourceCrosscutLiteralOpenLeftTerminalProfile web pair boundary
        hseparated hinner coloring.1 coloring.2 = left ∧
      sourceCrosscutLiteralOpenRightTerminalProfile web pair boundary
        hseparated hinner coloring.1 coloring.2 = right

/-- The terminal-aware retained-open `Count` matrix.  Its entries count actual
colorings; the five profile coordinates are computed from those colorings. -/
noncomputable def sourceCrosscutLiteralOpenTerminalProfileCount
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
        web.annular.cellulation.rotation boundary hseparated)) :
    TransferMatrix (SourceCrosscutTerminalInterfaceProfile web pair boundary) :=
  fun left right =>
    (sourceCrosscutLiteralOpenTerminalProfilePairFiber web pair boundary
      hseparated hinner left right).card

@[simp]
theorem sourceCrosscutLiteralOpenTerminalProfileCount_apply
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
    (left right : SourceCrosscutTerminalInterfaceProfile web pair boundary) :
    sourceCrosscutLiteralOpenTerminalProfileCount web pair boundary
        hseparated hinner left right =
      (sourceCrosscutLiteralOpenTerminalProfilePairFiber web pair boundary
        hseparated hinner left right).card :=
  rfl

/-- Fiber membership is exactly simultaneous realization of the two enriched
profiles by one literal retained-open coloring. -/
theorem mem_sourceCrosscutLiteralOpenTerminalProfilePairFiber_iff
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
    (left right : SourceCrosscutTerminalInterfaceProfile web pair boundary)
    (coloring : pair.SourceCrosscutLiteralOpenTaitColoring
      web.annular.cellulation.rotation boundary) :
    coloring ∈ sourceCrosscutLiteralOpenTerminalProfilePairFiber web pair
        boundary hseparated hinner left right ↔
      sourceCrosscutLiteralOpenLeftTerminalProfile web pair boundary
          hseparated hinner coloring.1 coloring.2 = left ∧
        sourceCrosscutLiteralOpenRightTerminalProfile web pair boundary
          hseparated hinner coloring.1 coloring.2 = right := by
  classical
  simp [sourceCrosscutLiteralOpenTerminalProfilePairFiber]

/-- Positivity of one terminal-aware matrix entry has its exact existential
coloring semantics. -/
theorem sourceCrosscutLiteralOpenTerminalProfileCount_pos_iff
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
    (left right : SourceCrosscutTerminalInterfaceProfile web pair boundary) :
    0 < sourceCrosscutLiteralOpenTerminalProfileCount web pair boundary
        hseparated hinner left right ↔
      ∃ coloring : pair.SourceCrosscutLiteralOpenTaitColoring
          web.annular.cellulation.rotation boundary,
        sourceCrosscutLiteralOpenLeftTerminalProfile web pair boundary
            hseparated hinner coloring.1 coloring.2 = left ∧
          sourceCrosscutLiteralOpenRightTerminalProfile web pair boundary
            hseparated hinner coloring.1 coloring.2 = right := by
  rw [sourceCrosscutLiteralOpenTerminalProfileCount_apply]
  constructor
  · intro hpositive
    rcases Finset.card_pos.mp hpositive with ⟨coloring, hmember⟩
    exact ⟨coloring,
      (mem_sourceCrosscutLiteralOpenTerminalProfilePairFiber_iff web pair
        boundary hseparated hinner left right coloring).1 hmember⟩
  · rintro ⟨coloring, hleft, hright⟩
    apply Finset.card_pos.mpr
    refine ⟨coloring, ?_⟩
    exact (mem_sourceCrosscutLiteralOpenTerminalProfilePairFiber_iff web pair
      boundary hseparated hinner left right coloring).2 ⟨hleft, hright⟩

/-- The existing zero-terminal complete-profile support is exactly the
existential projection of the terminal-aware support.  This is a projection
of all five profile fields, not merely of the boundary color word. -/
theorem sourceCrosscutLiteralOpenProfileCount_pos_iff_exists_terminalProfilePair
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
    (left right : pair.SourceCrosscutInterfaceProfile
      web.annular.cellulation.rotation boundary) :
    0 < pair.sourceCrosscutLiteralOpenProfileCount
        web.annular.cellulation.rotation boundary left right ↔
      ∃ leftTerminal rightTerminal :
          SourceCrosscutTerminalInterfaceProfile web pair boundary,
        forgetTerminals leftTerminal = left ∧
          forgetTerminals rightTerminal = right ∧
            0 < sourceCrosscutLiteralOpenTerminalProfileCount web pair boundary
              hseparated hinner leftTerminal rightTerminal := by
  rw [pair.sourceCrosscutLiteralOpenProfileCount_pos_iff]
  constructor
  · rintro ⟨coloring, hleft, hright⟩
    let leftTerminal := sourceCrosscutLiteralOpenLeftTerminalProfile web pair
      boundary hseparated hinner coloring.1 coloring.2
    let rightTerminal := sourceCrosscutLiteralOpenRightTerminalProfile web pair
      boundary hseparated hinner coloring.1 coloring.2
    refine ⟨leftTerminal, rightTerminal, ?_, ?_, ?_⟩
    · calc
        forgetTerminals leftTerminal =
            pair.sourceCrosscutLiteralOpenLeftProfile
              web.annular.cellulation.rotation boundary coloring.1 coloring.2 :=
          forgetTerminals_sourceCrosscutLiteralOpenLeftTerminalProfile
            web pair boundary hseparated hinner coloring.1 coloring.2
        _ = left := hleft
    · calc
        forgetTerminals rightTerminal =
            pair.sourceCrosscutLiteralOpenRightProfile
              web.annular.cellulation.rotation boundary coloring.1 coloring.2 :=
          forgetTerminals_sourceCrosscutLiteralOpenRightTerminalProfile
            web pair boundary hseparated hinner coloring.1 coloring.2
        _ = right := hright
    · rw [sourceCrosscutLiteralOpenTerminalProfileCount_pos_iff]
      exact ⟨coloring, rfl, rfl⟩
  · rintro ⟨leftTerminal, rightTerminal, hleft, hright, hpositive⟩
    rcases (sourceCrosscutLiteralOpenTerminalProfileCount_pos_iff web pair
      boundary hseparated hinner leftTerminal rightTerminal).1 hpositive with
      ⟨coloring, hleftTerminal, hrightTerminal⟩
    refine ⟨coloring, ?_, ?_⟩
    · calc
        pair.sourceCrosscutLiteralOpenLeftProfile
            web.annular.cellulation.rotation boundary coloring.1 coloring.2 =
            forgetTerminals
              (sourceCrosscutLiteralOpenLeftTerminalProfile web pair boundary
                hseparated hinner coloring.1 coloring.2) :=
          (forgetTerminals_sourceCrosscutLiteralOpenLeftTerminalProfile
            web pair boundary hseparated hinner coloring.1 coloring.2).symm
        _ = forgetTerminals leftTerminal := congrArg forgetTerminals hleftTerminal
        _ = left := hleft
    · calc
        pair.sourceCrosscutLiteralOpenRightProfile
            web.annular.cellulation.rotation boundary coloring.1 coloring.2 =
            forgetTerminals
              (sourceCrosscutLiteralOpenRightTerminalProfile web pair boundary
                hseparated hinner coloring.1 coloring.2) :=
          (forgetTerminals_sourceCrosscutLiteralOpenRightTerminalProfile
            web pair boundary hseparated hinner coloring.1 coloring.2).symm
        _ = forgetTerminals rightTerminal := congrArg forgetTerminals hrightTerminal
        _ = right := hright

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
