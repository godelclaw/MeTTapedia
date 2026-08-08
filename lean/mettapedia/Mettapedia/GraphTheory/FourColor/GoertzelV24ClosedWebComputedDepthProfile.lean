import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLaminarProfileRepeat
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebChordRotationNoncrossing

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
open GoertzelV24ClosedWebChordHoleSideCutWitness
open GoertzelV24ClosedWebChordRotationNoncrossing
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

/-- Turn a finite graph-side predicate into the finite carrier consumed by
the rotation-system profile engine. -/
noncomputable def sideFinset (side : V → Prop) : Finset V := by
  classical
  exact Finset.univ.filter side

omit [DecidableEq V] in
@[simp] theorem mem_sideFinset_iff
    (side : V → Prop) (vertex : V) :
    vertex ∈ sideFinset side ↔ side vertex := by
  simp [sideFinset]

/-- A cyclic-cut realization has exactly the crossing-port support computed
from its finite vertex side.  This is the finite graph bridge; it does not
construct the realization from a chord or invoke planarity. -/
theorem vertexSetCrossingEdges_eq_of_cyclicEdgeCutRealization
    (data : SimpleGraphDartRotation.Data G)
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut) :
    vertexSetCrossingEdges data.toRotationSystem
        (sideFinset realization.side) = edgeCut := by
  ext edge
  rw [mem_vertexSetCrossingEdges_iff,
    simpleGraph_edgeCrossesVertexSet_iff_edgeCrossesVertexSide]
  simpa [sideFinset] using (realization.hcut_eq edge).symm

theorem card_vertexSetCrossingEdge_eq_of_cyclicEdgeCutRealization
    (data : SimpleGraphDartRotation.Data G)
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut) :
    Fintype.card (VertexSetCrossingEdge data.toRotationSystem
        (sideFinset realization.side)) = edgeCut.card := by
  rw [card_vertexSetCrossingEdge,
    vertexSetCrossingEdges_eq_of_cyclicEdgeCutRealization data realization]

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

/-- The hole-free facial side canonically selected by the exact binary-cut
theorem.  Retaining the exact-label witness makes the later sector alignment
theorem transparent; this definition still selects only a face side. -/
noncomputable def canonicalFaceSide
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second)
    {cut : Fin pair.firstPath.path.length} {side : Bool}
    (chord : SectorChord pair embedded hdata htriple cut side) : Bool :=
  Classical.choose
    (Classical.choose_spec
      (exists_exact_chordCycle_faceCut_with_holeFreeSide
        embedded hdata pair (materializedChord chord) htriple))

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
    (Classical.choose_spec
      (Classical.choose_spec
        (exists_exact_chordCycle_faceCut_with_holeFreeSide
          embedded hdata pair (materializedChord chord) htriple))).2.2.2.2

/-- The exact-label witness also identifies the selected hole-free facial side
with the intrinsic rotation sector of the materialized chord.  This is a
face-side/rotation-bit identification only; it does not yet construct the
primal vertex side needed by the computed-profile interface. -/
theorem canonicalFaceSide_eq_rotationSector
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second)
    {cut : Fin pair.firstPath.path.length} {side : Bool}
    (chord : SectorChord pair embedded hdata htriple cut side) :
    canonicalFaceSide embedded hdata htriple chord =
      MajorityChordOnRadialPath.rotationSector
        embedded (materializedChord chord) hdata htriple := by
  unfold canonicalFaceSide
  let hwitness :=
    exists_exact_chordCycle_faceCut_with_holeFreeSide
      embedded hdata pair (materializedChord chord) htriple
  have hspec := Classical.choose_spec (Classical.choose_spec hwitness)
  exact side_eq_rotationSector_of_label_ne_innerHole
    embedded hdata (materializedChord chord) htriple
      (Classical.choose hwitness) hspec.2.1
      (Classical.choose (Classical.choose_spec hwitness)) hspec.2.2.2.1

/-- A sector chord's canonical hole-free face side is the same Boolean used
by the finite sector partition.  This closes the bookkeeping between the
ordered-path sector carrier and the exact facial cut; it still makes no claim
about the corresponding primal vertex side. -/
theorem canonicalFaceSide_eq_sectorSide
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second)
    {cut : Fin pair.firstPath.path.length} {side : Bool}
    (chord : SectorChord pair embedded hdata htriple cut side) :
    canonicalFaceSide embedded hdata htriple chord = side := by
  have hmem := (mem_sectorSpanningChords_iff).mp chord.2
  have hposition := positionRotationSector_eq_rotationSector
    embedded hdata pair.firstPath htriple chord.1 hmem.1
  calc
    canonicalFaceSide embedded hdata htriple chord =
        MajorityChordOnRadialPath.rotationSector
          embedded (materializedChord chord) hdata htriple :=
      canonicalFaceSide_eq_rotationSector embedded hdata htriple chord
    _ = positionRotationSector embedded hdata pair.firstPath htriple chord.1 :=
      hposition.symm
    _ = side := hmem.2.2

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

/-- The exact geometric input that is sufficient to build a side assignment:
each chord receives a cyclic edge-cut realization, together with a uniform
finite cut bound.  Constructing this family is the remaining Jordan/sector
lemma; the conversion to profile data is mechanical and proved below. -/
structure ChordCyclicCutAssignment
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second)
    (widthBound : Nat) where
  edgeCut : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
    (_chord : SectorChord pair embedded hdata htriple cut side), Finset G.edgeSet
  realization : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
    (chord : SectorChord pair embedded hdata htriple cut side),
    CyclicEdgeCutRealization G (edgeCut cut side chord)
  width : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
    (chord : SectorChord pair embedded hdata htriple cut side),
    (edgeCut cut side chord).card ≤ widthBound

/-- A chord-side assignment exposes the exact side-transport interface needed
by a radial/Jordan argument.  The geometric caller supplies a local dart
certificate saying that the proposed cut is absent at every vertex visited by
the walk; the generic cut layer then turns that certificate into equality of
the endpoint side bits.  This keeps the construction obligation (producing
the certificate from the embedded chord wall) separate from the finite
profile machinery. -/
theorem ChordCyclicCutAssignment.side_iff_of_walk_darts_avoid_edgeCut
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    {embedded : ClosedWebAnnularEmbedding data}
    {hdata : data.WellFormed}
    {htriple : IsTaitColorTriple majority first second}
    {widthBound : Nat}
    (cuts : ChordCyclicCutAssignment pair embedded hdata htriple widthBound)
    (cut : Fin pair.firstPath.path.length) (side : Bool)
    (chord : SectorChord pair embedded hdata htriple cut side)
    {u v : V} (walk : G.Walk u v)
    (havoid : ∀ based ∈ walk.darts, ∀ incident : G.Dart,
      incident.fst = based.fst →
        (⟨incident.edge, incident.edge_mem⟩ : G.edgeSet) ∉
          cuts.edgeCut cut side chord) :
    (cuts.realization cut side chord).side u ↔
      (cuts.realization cut side chord).side v := by
  exact (cuts.realization cut side chord).side_iff_of_walk_darts_avoid_edgeCut
    walk havoid

/-- Convert exact cyclic cut realizations into the finite vertex-side profile
interface.  The crossing-width proof is obtained from exact cut equality,
not supplied as a second classification. -/
def ChordCyclicCutAssignment.toSideAssignment
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    {embedded : ClosedWebAnnularEmbedding data}
    {hdata : data.WellFormed}
    {htriple : IsTaitColorTriple majority first second}
    {widthBound : Nat}
    (cuts : ChordCyclicCutAssignment pair embedded hdata htriple widthBound) :
    ChordSideAssignment pair embedded hdata htriple widthBound where
  inside := fun cut side chord =>
    sideFinset (cuts.realization cut side chord).side
  crossingWidth := by
    intro cut side chord
    rw [card_vertexSetCrossingEdge_eq_of_cyclicEdgeCutRealization
      embedded.cellulation.rotation (cuts.realization cut side chord)]
    exact cuts.width cut side chord

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

/--
The geometric premise can be supplied in its most economical form: a cyclic
edge-cut realization for each chord.  Once those realizations exist, the
conversion to vertex sides and the occurrence-sensitive L7 profile is wholly
mechanical.  Keeping this theorem separate makes the remaining Jordan/sector
lemma a single named input rather than an implicit assumption.
 -/
theorem exists_nested_equal_computed_depthProfile_of_hasDeepChordTransversal_of_cyclicCuts
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
    (cuts : ChordCyclicCutAssignment pair embedded hdata htriple widthBound) :
    ∃ (cut : Fin pair.firstPath.path.length) (side : Bool)
        (inner outer : SectorChord pair embedded hdata htriple cut side),
      (inner ≠ outer) ∧ (inner.1.NestedIn outer.1) ∧
        ((cuts.toSideAssignment.profile hC cut side inner =
          cuts.toSideAssignment.profile hC cut side outer) ∧
        (HoleFreeChordSide embedded.cellulation
            (chordBoundary inner)
            (canonicalFaceSide embedded hdata htriple inner) ∧
          HoleFreeChordSide embedded.cellulation
            (chordBoundary outer)
            (canonicalFaceSide embedded hdata htriple outer))) := by
  exact exists_nested_equal_computed_depthProfile_of_hasDeepChordTransversal
    embedded hdata pair htriple hC widthBound hdeep cuts.toSideAssignment

/-!
The two equal-state projections below are intentionally small, but they are
the first pieces of the source's splice checklist that can be consumed
without any geometric assumption.  Equality in the varying-width carrier
already includes equality of the actual crossing-port count; because the
profile payload is dependent on that count, it also includes equality of the
number of retained face fragments.  Keeping these facts as named lemmas
prevents a later splice proof from recovering them by fragile dependent
elimination at every use site.
-/

theorem closedWebDepthProfile_crossingEdgeCount_val_eq_of_eq
    {widthBound : Nat}
    {left right : ClosedWebDepthProfile widthBound}
    (hprofiles : left = right) :
    left.crossingEdgeCount.val = right.crossingEdgeCount.val := by
  exact congrArg (fun profile => profile.crossingEdgeCount.val) hprofiles

theorem closedWebDepthProfile_faceFragmentCount_val_eq_of_eq
    {widthBound : Nat}
    {left right : ClosedWebDepthProfile widthBound}
    (hprofiles : left = right) :
    left.profile.faceFragmentCount.val = right.profile.faceFragmentCount.val := by
  cases hprofiles
  rfl

/-
The edge-color coordinate is dependent on the crossing-port count.  Expose
its transport explicitly: a later splice proof can compare the corresponding
finite interface colors without reopening the dependent profile equality.
-/
theorem closedWebDepthProfile_edgeColor_eq_of_eq
    {widthBound : Nat}
    {left right : ClosedWebDepthProfile widthBound}
    (hprofiles : left = right) :
    ∀ (index : Fin left.crossingEdgeCount.val),
      left.profile.profile.edgeColor index =
        right.profile.profile.edgeColor
          (Fin.cast
            (closedWebDepthProfile_crossingEdgeCount_val_eq_of_eq hprofiles)
            index) := by
  intro index
  cases hprofiles
  rfl

end

end GoertzelV24ClosedWebComputedDepthProfile

end Mettapedia.GraphTheory.FourColor
