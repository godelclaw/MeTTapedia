import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebTerminalProfileCount

/-!
# Bounded support of the terminal-aware source `Count`

A width-two source crosscut has five fixed terminals and at most eight
boundary-local face fragments.  This file transports the exact terminal-aware
retained-open `Count` support to the common finite carrier
`BoundedCorridorCutProfile 2 5 8`.

The encoding is injective and the transported relation contains only encoded
profiles realized by literal open Tait colorings.  States outside a source
profile's exact dependent fragment coordinate acquire no transitions.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedTerminalProfile

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebTerminalBoundedCountEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

/-- Faithfully package one exact source terminal profile in the common
width-two, five-terminal, eight-fragment carrier. -/
noncomputable def sourceCrosscutTerminalProfileCode
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
    (hwidth : pair.left.walk.length = 2)
    (profile : SourceCrosscutTerminalInterfaceProfile web pair boundary) :
    Cell3TerminalAwareProfile := by
  refine {
    faceFragmentCount := ⟨_, Nat.lt_succ_of_le
      (sourceCrosscutTerminal_faceFragmentCount_le_eight
        pair boundary hwidth)⟩
    profile := ?_ }
  rw [← hwidth]
  exact profile

/-- The common-carrier encoding cannot merge two distinct complete terminal
profiles. -/
theorem sourceCrosscutTerminalProfileCode_injective
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
    (hwidth : pair.left.walk.length = 2) :
    Function.Injective
      (sourceCrosscutTerminalProfileCode web pair boundary hwidth) := by
  intro left right heq
  dsimp only [sourceCrosscutTerminalProfileCode] at heq
  injection heq with hcount hprofile
  simpa using hprofile

/-- The exact positive support relation of the terminal-aware retained-open
matrix, transported to the common finite carrier. -/
noncomputable def sourceCrosscutTerminalBoundedProfileTransfer
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
    (hwidth : pair.left.walk.length = 2)
    (hseparated : pair.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation)
    (hinner : ProtectedInnerInterface.InnerBoundaryKept
      (pair.sourceCrosscutLayerSpliceData
        web.annular.cellulation.rotation boundary hseparated))
    (left right : Cell3TerminalAwareProfile) : Prop :=
  ∃ leftRaw rightRaw : SourceCrosscutTerminalInterfaceProfile web pair boundary,
    sourceCrosscutTerminalProfileCode web pair boundary hwidth leftRaw = left ∧
      sourceCrosscutTerminalProfileCode web pair boundary hwidth rightRaw = right ∧
        0 < sourceCrosscutLiteralOpenTerminalProfileCount web pair boundary
          hseparated hinner leftRaw rightRaw

/-- The transported finite relation remains decidable. -/
noncomputable instance instDecidableRelSourceCrosscutTerminalBoundedProfileTransfer
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
    (hwidth : pair.left.walk.length = 2)
    (hseparated : pair.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation)
    (hinner : ProtectedInnerInterface.InnerBoundaryKept
      (pair.sourceCrosscutLayerSpliceData
        web.annular.cellulation.rotation boundary hseparated)) :
    DecidableRel (sourceCrosscutTerminalBoundedProfileTransfer web pair boundary
      hwidth hseparated hinner) := by
  classical
  intro left right
  unfold sourceCrosscutTerminalBoundedProfileTransfer
  infer_instance

/-- On encoded source states, the common-carrier relation is exactly
positivity of the underlying terminal-aware `Count` entry. -/
theorem sourceCrosscutTerminalBoundedProfileTransfer_code_iff
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
    (hwidth : pair.left.walk.length = 2)
    (hseparated : pair.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation)
    (hinner : ProtectedInnerInterface.InnerBoundaryKept
      (pair.sourceCrosscutLayerSpliceData
        web.annular.cellulation.rotation boundary hseparated))
    (left right : SourceCrosscutTerminalInterfaceProfile web pair boundary) :
    sourceCrosscutTerminalBoundedProfileTransfer web pair boundary hwidth
        hseparated hinner
        (sourceCrosscutTerminalProfileCode web pair boundary hwidth left)
        (sourceCrosscutTerminalProfileCode web pair boundary hwidth right) ↔
      0 < sourceCrosscutLiteralOpenTerminalProfileCount web pair boundary
        hseparated hinner left right := by
  constructor
  · rintro ⟨leftRaw, rightRaw, hleft, hright, hpositive⟩
    have hleftRaw : leftRaw = left :=
      sourceCrosscutTerminalProfileCode_injective web pair boundary hwidth hleft
    have hrightRaw : rightRaw = right :=
      sourceCrosscutTerminalProfileCode_injective web pair boundary hwidth hright
    simpa only [hleftRaw, hrightRaw] using hpositive
  · intro hpositive
    exact ⟨left, right, rfl, rfl, hpositive⟩

/-- Concrete semantics of the common-carrier relation: it holds between two
encoded states exactly when one literal retained-open Tait coloring realizes
their complete terminal profiles. -/
theorem sourceCrosscutTerminalBoundedProfileTransfer_code_iff_exists_coloring
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
    (hwidth : pair.left.walk.length = 2)
    (hseparated : pair.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation)
    (hinner : ProtectedInnerInterface.InnerBoundaryKept
      (pair.sourceCrosscutLayerSpliceData
        web.annular.cellulation.rotation boundary hseparated))
    (left right : SourceCrosscutTerminalInterfaceProfile web pair boundary) :
    sourceCrosscutTerminalBoundedProfileTransfer web pair boundary hwidth
        hseparated hinner
        (sourceCrosscutTerminalProfileCode web pair boundary hwidth left)
        (sourceCrosscutTerminalProfileCode web pair boundary hwidth right) ↔
      ∃ coloring : pair.SourceCrosscutLiteralOpenTaitColoring
          web.annular.cellulation.rotation boundary,
        sourceCrosscutLiteralOpenLeftTerminalProfile web pair boundary
            hseparated hinner coloring.1 coloring.2 = left ∧
          sourceCrosscutLiteralOpenRightTerminalProfile web pair boundary
            hseparated hinner coloring.1 coloring.2 = right := by
  rw [sourceCrosscutTerminalBoundedProfileTransfer_code_iff]
  exact sourceCrosscutLiteralOpenTerminalProfileCount_pos_iff web pair boundary
    hseparated hinner left right

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
