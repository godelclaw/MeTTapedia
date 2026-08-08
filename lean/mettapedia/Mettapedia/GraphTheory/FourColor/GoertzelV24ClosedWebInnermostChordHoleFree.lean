import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebChordHoleSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialPathChordDiagram

/-!
# An innermost closed-web chord with a derived hole-free side

The source's Sector-Alternation step begins by choosing an innermost
same-path chord and then considering the disk on its hole-free side.  The two
ingredients are independent: finiteness of the actual third-color chord
diagram supplies a minimum-span chord, while exact facial separation supplies
one side containing neither annular hole.

This module joins those proved ingredients.  It does not assume that chords
on opposite sectors are pairwise noncrossing.  Minimum span already excludes
every strictly nested same-path chord; the remaining interleaving case is the
genuine cross-sector drainage seam.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebInnermostChordHoleFree

open SimpleGraph
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebChordHoleSeparation
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChordDiagram
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24ClosedWebSelectedEdgeStructure

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- A nonempty actual same-path chord diagram contains a minimum-span chord
whose chord cycle has a genuinely hole-free facial side. -/
theorem exists_innermost_majorityChord_with_holeFreeSide
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second)
    (hnonempty :
      (majorityChordDiagram C majority first second
        pair.firstPath).Nonempty) :
    ∃ (position : OrderedPathChord (pair.firstPath.path.length + 1))
        (hpositionData : IsMajorityChordAt
          C majority first second pair.firstPath position),
      position ∈ majorityChordDiagram C majority first second
          pair.firstPath ∧
        InnermostIn position
          (majorityChordDiagram C majority first second pair.firstPath) ∧
        (∀ other ∈ majorityChordDiagram C majority first second
              pair.firstPath,
          other ≠ position → other.HasEndpointInside position →
            other.Crosses position) ∧
        ∃ side : Bool,
          HoleFreeChordSide embedded.cellulation
            ((majorityChordOfPosition position hpositionData).boundary
              htriple) side := by
  obtain ⟨position, hposition, hinnermost⟩ :=
    exists_innermost_majorityChord hnonempty
  have hpositionData : IsMajorityChordAt
      C majority first second pair.firstPath position :=
    (mem_majorityChordDiagram_iff).1 hposition
  let chord := majorityChordOfPosition position hpositionData
  obtain ⟨side, hside⟩ :=
    exists_holeFreeChordSide embedded hdata pair chord htriple
  refine ⟨position, hpositionData, hposition, hinnermost, ?_, side, ?_⟩
  · intro other hother hne htouches
    exact other_chord_crosses_of_hasEndpointInside_innermost
      hinnermost hposition hother hne htouches
  simpa [chord, hpositionData] using hside

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- No distinct actual chord can have both endpoints strictly inside the
chosen innermost chord's open path interval.  Unlike the stronger
no-endpoint-inside statement, this needs no global noncrossing premise. -/
theorem not_nestedIn_innermost_majorityChord
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    {outer inner : OrderedPathChord (radial.path.length + 1)}
    (hinnermost : InnermostIn outer
      (majorityChordDiagram C majority first second radial))
    (hinner : inner ∈
      majorityChordDiagram C majority first second radial)
    (hne : inner ≠ outer) :
    ¬ inner.NestedIn outer :=
  hinnermost inner hinner hne

end

end GoertzelV24ClosedWebInnermostChordHoleFree

end Mettapedia.GraphTheory.FourColor
