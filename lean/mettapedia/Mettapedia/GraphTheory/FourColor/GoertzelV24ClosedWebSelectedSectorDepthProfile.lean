import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebComputedDepthProfile

/-!
# Selected-sector depth-profile handoff

The curvature-free L6 theorem returns one cut and one rotation sector whose
spanning chords form a large laminar family.  L7 therefore does not need a
transversal or cyclic-cut assignment for every cut and both sectors.  It needs
that geometry only for the chords in the single selected family.

This module records that exact locality.  A family of genuine cyclic cut
realizations on one selected sector mechanically supplies the existing
`ChordSectorSideAssignment`, after which the proved finite-state pigeonhole
returns nested equal graph-derived profiles.

This is an **L6/L7 interface reduction**, not the missing geometry.  It does
not manufacture the cyclic cuts, simple layer boundaries, or deletion
transversals, and it does not claim a strict splice.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebSelectedSectorDepthProfile

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebChordRotationSector
open GoertzelV24ClosedWebChordRotationNoncrossing
open GoertzelV24ClosedWebComputedDepthProfile
open GoertzelV24ClosedWebLaminarDepth
open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathSectorAnchors
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- Genuine cyclic cuts indexed only by the chords in one selected rotation
sector.  This is the local geometric datum actually consumed by the depth
profile pigeonhole. -/
structure SelectedSectorCyclicCutAssignment
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second)
    (widthBound : Nat)
    (cut : Fin pair.firstPath.path.length) (side : Bool) where
  edgeCut : SectorChord pair embedded hdata htriple cut side → Finset G.edgeSet
  realization : ∀ chord,
    CyclicEdgeCutRealization G (edgeCut chord)
  width : ∀ chord, (edgeCut chord).card ≤ widthBound

namespace SelectedSectorCyclicCutAssignment

/-- Convert the selected-sector cut family to the exact side interface used
by the graph-derived L7 profile.  Exact cut equality supplies the crossing
width; it is not assumed independently. -/
noncomputable def toSideAssignment
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    {embedded : ClosedWebAnnularEmbedding data}
    {hdata : data.WellFormed}
    {htriple : IsTaitColorTriple majority first second}
    {widthBound : Nat}
    {cut : Fin pair.firstPath.path.length} {side : Bool}
    (cuts : SelectedSectorCyclicCutAssignment pair embedded hdata htriple
      widthBound cut side) :
    ChordSectorSideAssignment pair embedded hdata htriple
      widthBound cut side where
  inside := fun chord => sideFinset (cuts.realization chord).side
  crossingWidth := by
    intro chord
    rw [card_vertexSetCrossingEdge_eq_of_cyclicEdgeCutRealization
      embedded.cellulation.rotation (cuts.realization chord)]
    exact cuts.width chord

end SelectedSectorCyclicCutAssignment

/-- **L7, selected-sector form.** A large laminar sector plus genuine bounded
cyclic cuts on that sector yields two distinct nested chords with equal
graph-derived profiles.  No geometry outside the returned sector is needed. -/
theorem exists_nested_equal_computed_depthProfile_of_selectedSectorCyclicCuts
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second)
    (hC : IsTaitEdgeColoring G C)
    (widthBound : Nat)
    (cut : Fin pair.firstPath.path.length) (side : Bool)
    (hlarge : closedWebCutProfileCount widthBound <
      (sectorSpanningChords C majority first second pair.firstPath
        (positionRotationSector embedded hdata pair.firstPath htriple)
        side cut).card)
    (hlaminar : PairwiseLaminar
      (sectorSpanningChords C majority first second pair.firstPath
        (positionRotationSector embedded hdata pair.firstPath htriple)
        side cut))
    (cuts : SelectedSectorCyclicCutAssignment pair embedded hdata htriple
      widthBound cut side) :
    ∃ (inner outer : SectorChord pair embedded hdata htriple cut side),
      inner ≠ outer ∧ inner.1.NestedIn outer.1 ∧
        cuts.toSideAssignment.profile hC inner =
          cuts.toSideAssignment.profile hC outer := by
  exact exists_nested_equal_computed_depthProfile_of_largeLaminarSector
    embedded hdata pair htriple hC widthBound cut side hlarge hlaminar
      cuts.toSideAssignment

end

end GoertzelV24ClosedWebSelectedSectorDepthProfile

end Mettapedia.GraphTheory.FourColor
