import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLaminarProfileRepeat

/-!
# Graph-derived depth profiles for closed-web chords

The finite repetition theorem deliberately accepts a profile assignment as
data: that exposed, rather than hid, the missing chord-side construction.  This
module supplies the next interface without pretending to prove the geometry.
For each sector chord it takes an actual finite vertex side, a width bound for
its crossing ports, and the hole-free face-side certificate.  The profile is
then computed by the occurrence-sensitive graph-derived constructor, not
chosen arbitrarily.  Equal profiles returned below are therefore genuine L7
states of the supplied sides; the properness and splice theorem remain
separate obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebComputedDepthProfile

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebChordRotationSector
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebLaminarDepth
open GoertzelV24ClosedWebLaminarProfileRepeat
open GoertzelV24ClosedWebLengthDepthDichotomy
open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24ClosedWebRadialPathChordDiagram
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24RotationVertexCutProfile

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

local instance computedDepthProfileGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/- The embedding stores a rotation system whose edge-adjacency graph is not
definitionally equal to the ordinary line graph.  Keep
this transport in one small helper, so the profile below is genuinely driven
by the graph coloring used by the radial chord data. -/
def rotationColoringOfGraph
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (C : G.EdgeColoring Color) : embedded.RS.EdgeColoring Color := by
  have hgraph : embedded.RS.edgeAdjacencyGraph = G.lineGraph :=
    GoertzelV24SimpleGraphTaitBridge.toRotationSystem_edgeAdjacencyGraph_eq_lineGraph
      embedded.cellulation.rotation
  refine SimpleGraph.Coloring.mk (fun edge => C edge) ?_
  intro first second hadj
  apply C.valid
  rw [← hgraph]
  exact hadj

theorem rotationColoringOfGraph_isTait
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C) :
    embedded.RS.IsTaitEdgeColoring (rotationColoringOfGraph embedded C) := by
  intro edge
  exact hC edge

/-- The actual chord subtype used by one cut and one intrinsic sector side. -/
abbrev SectorChord
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second)
    (cut : Fin pair.firstPath.path.length) (side : Bool) :=
  { chord // chord ∈
    sectorSpanningChords C majority first second pair.firstPath
      (positionRotationSector embedded hdata pair.firstPath htriple)
      side cut }

/-- Recover the face-tracing wall carried by a sector chord.  Membership in
the sector supplies the majority-chord certificate needed to materialize the
radial-path chord object. -/
noncomputable def chordBoundary
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    {embedded : ClosedWebAnnularEmbedding data}
    {hdata : data.WellFormed}
    {htriple : IsTaitColorTriple majority first second}
    {cut : Fin pair.firstPath.path.length} {side : Bool}
    (chord : SectorChord pair embedded hdata htriple cut side) :
    SamePathChordBoundary G :=
  (majorityChordOfPosition chord.1
    (mem_majorityChordDiagram_iff.mp
      ((mem_sectorSpanningChords_iff).mp chord.2).1)).boundary htriple

/-- The materialized radial-path chord underlying a sector-diagram member. -/
noncomputable def materializedChord
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    {embedded : ClosedWebAnnularEmbedding data}
    {hdata : data.WellFormed}
    {htriple : IsTaitColorTriple majority first second}
    {cut : Fin pair.firstPath.path.length} {side : Bool}
    (chord : SectorChord pair embedded hdata htriple cut side) :
    MajorityChordOnRadialPath C majority first second pair.firstPath :=
  majorityChordOfPosition chord.1
    (mem_majorityChordDiagram_iff.mp
      ((mem_sectorSpanningChords_iff).mp chord.2).1)

@[simp] theorem chordBoundary_eq_materializedChord_boundary
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    {embedded : ClosedWebAnnularEmbedding data}
    {hdata : data.WellFormed}
    {htriple : IsTaitColorTriple majority first second}
    {cut : Fin pair.firstPath.path.length} {side : Bool}
    (chord : SectorChord pair embedded hdata htriple cut side) :
    chordBoundary chord = (materializedChord chord).boundary htriple :=
  rfl

/-- The hole-free facial side canonically selected by the exact binary cut
theorem.  This Boolean is independent of the radial sector bit. -/
noncomputable def canonicalFaceSide
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second)
    {cut : Fin pair.firstPath.path.length} {side : Bool}
    (chord : SectorChord pair embedded hdata htriple cut side) : Bool :=
  Classical.choose <|
    GoertzelV24ClosedWebChordHoleSeparation.exists_holeFreeChordSide
      embedded hdata pair (materializedChord chord) htriple

theorem canonicalFaceSide_holeFree
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second)
    {cut : Fin pair.firstPath.path.length} {side : Bool}
    (chord : SectorChord pair embedded hdata htriple cut side) :
      HoleFreeChordSide embedded.cellulation (chordBoundary chord)
      (canonicalFaceSide embedded hdata htriple chord) := by
  unfold canonicalFaceSide
  simpa [chordBoundary_eq_materializedChord_boundary] using
    Classical.choose_spec
      (GoertzelV24ClosedWebChordHoleSeparation.exists_holeFreeChordSide
        embedded hdata pair (materializedChord chord) htriple)

/-- A side assignment for every candidate chord, with the exact finite-state
data needed to turn it into a depth profile.  The side itself is supplied by
the pending embedded/Jordan argument; this structure does not assert it. -/
structure ChordSideAssignment
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second)
    (widthBound : Nat) where
  inside : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool),
    SectorChord pair embedded hdata htriple cut side → Finset V
  crossingWidth : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
    (chord : SectorChord pair embedded hdata htriple cut side),
    Fintype.card (VertexSetCrossingEdge embedded.RS
      (inside cut side chord)) ≤ widthBound

/-- Once an actual side assignment is available, compute its L7 depth state.
The use of `vertexSetClosedWebCutProfileOfDartOccurrences` is important for
framed graphs: repeated bridge-stub dart occurrences are counted correctly. -/
def ChordSideAssignment.profile
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    {embedded : ClosedWebAnnularEmbedding data}
    {hdata : data.WellFormed}
    {htriple : IsTaitColorTriple majority first second}
    {widthBound : Nat}
    (assignment : ChordSideAssignment pair embedded hdata htriple widthBound)
    (hC : IsTaitEdgeColoring G C)
    (cut : Fin pair.firstPath.path.length) (side : Bool)
    (chord : SectorChord pair embedded hdata htriple cut side) :
    ClosedWebDepthProfile widthBound :=
  vertexSetClosedWebCutProfileOfDartOccurrences widthBound embedded.RS
    (assignment.inside cut side chord)
    (rotationColoringOfGraph embedded C)
    (rotationColoringOfGraph_isTait embedded C hC)
    (assignment.crossingWidth cut side chord)

/-- The abstract depth-repeat theorem instantiated with actual graph-derived
profiles.  This is the concrete side/profile interface needed before a splice
can be attempted: no arbitrary profile function remains. -/
theorem exists_nested_equal_computed_depthProfile_of_hasDeepChordTransversal
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second)
    (hC : IsTaitEdgeColoring G C)
    (widthBound : Nat)
    (hdeep : HasDeepChordTransversal C majority first second
      pair.firstPath (2 * closedWebCutProfileCount widthBound))
    (assignment : ChordSideAssignment pair embedded hdata htriple widthBound) :
    ∃ (cut : Fin pair.firstPath.path.length) (side : Bool)
        (inner outer : SectorChord pair embedded hdata htriple cut side),
      (inner ≠ outer) ∧ (inner.1.NestedIn outer.1) ∧
        ((assignment.profile hC cut side inner =
          assignment.profile hC cut side outer) ∧
        (HoleFreeChordSide embedded.cellulation
            (chordBoundary inner)
            (canonicalFaceSide embedded hdata htriple inner) ∧
          HoleFreeChordSide embedded.cellulation
            (chordBoundary outer)
            (canonicalFaceSide embedded hdata htriple outer))) := by
  let profile : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool),
      SectorChord pair embedded hdata htriple cut side →
        ClosedWebDepthProfile widthBound :=
    fun cut side chord => assignment.profile hC cut side chord
  rcases exists_nested_equal_depthProfile_of_hasDeepChordTransversal
      embedded hdata pair htriple widthBound hdeep profile with
    ⟨cut, side, inner, outer, hne, hnested, hequal⟩
  exact ⟨cut, side, inner, outer, hne, hnested, hequal,
    ⟨canonicalFaceSide_holeFree embedded hdata htriple inner,
      canonicalFaceSide_holeFree embedded hdata htriple outer⟩⟩

end

end GoertzelV24ClosedWebComputedDepthProfile

end Mettapedia.GraphTheory.FourColor
