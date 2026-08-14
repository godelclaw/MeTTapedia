import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLaminarProfileRepeat
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebChordRotationNoncrossing
import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteDeletionCyclicCut

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
open GoertzelV24ClosedWebChordCycleFaceSideTransport
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
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24OrbitFaceTwoSided
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

/-- A coordinate choice for every actual chord side.  This is where a later
simple-transversal or layer-boundary construction supplies its geometric port
order.  The structure asserts only that the coordinates cover the computed
crossing support; it does not claim that a chord cycle itself supplies such an
order. -/
structure ChordSideIndexingAssignment
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    {embedded : ClosedWebAnnularEmbedding data}
    {hdata : data.WellFormed}
    {htriple : IsTaitColorTriple majority first second}
    {widthBound : Nat}
    (assignment : ChordSideAssignment pair embedded hdata htriple widthBound) where
  indexing : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
    (chord : SectorChord pair embedded hdata htriple cut side),
    VertexSetCrossingIndexing embedded.RS (assignment.inside cut side chord)

/-- The exact geometric input that is sufficient to build a side assignment:
each chord receives a cyclic edge-cut realization, together with a uniform
finite cut bound.  It is a generic endpoint for a genuine transversal or
layer boundary; it does not identify the chord-cycle support itself with the
crossed-edge set.  Constructing this family is the remaining Jordan/sector
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

/-- A source-style transversal is represented by the finite set of graph
edges it crosses.  Deleting those edges exposes the two vertex regions, so a
chosen deletion component supplies the side used by the finite profile.

The chord merely indexes the geometry that selects the transversal.  In
particular, this structure deliberately does *not* set `removed` equal to a
chord boundary wall: Addendum XXVII calls for simple transversals/layer
boundaries, whose crossed edges are a separate object. -/
structure ChordTransversalDeletionAssignment
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second)
    (widthBound : Nat) where
  removed : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
    (_chord : SectorChord pair embedded hdata htriple cut side), Finset G.edgeSet
  component : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
    (chord : SectorChord pair embedded hdata htriple cut side),
    (G.deleteEdges (edgeFinsetValueSet (removed cut side chord))).ConnectedComponent
  boundary : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
    (chord : SectorChord pair embedded hdata htriple cut side),
    componentCrossingEdges (removed cut side chord) (component cut side chord) =
      removed cut side chord
  insideCycle : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
    (chord : SectorChord pair embedded hdata htriple cut side),
    HasCycleOnSide G (fun vertex => vertex ∈ (component cut side chord).supp)
  outsideCycle : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
    (chord : SectorChord pair embedded hdata htriple cut side),
    HasCycleOnSide G (fun vertex => ¬ vertex ∈ (component cut side chord).supp)
  width : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
    (chord : SectorChord pair embedded hdata htriple cut side),
    (removed cut side chord).card ≤ widthBound

namespace ChordTransversalDeletionAssignment

/-- The component boundary supplies the exact cut realization consumed by
the graph-derived profile layer.  All of the nontrivial geometry remains in
the explicit deletion-boundary and cycle fields of the transversal witness. -/
noncomputable def toCyclicCutAssignment
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    {embedded : ClosedWebAnnularEmbedding data}
    {hdata : data.WellFormed}
    {htriple : IsTaitColorTriple majority first second}
    {widthBound : Nat}
    (transversal : ChordTransversalDeletionAssignment pair embedded hdata htriple
      widthBound) :
    ChordCyclicCutAssignment pair embedded hdata htriple widthBound where
  edgeCut := fun cut side chord => transversal.removed cut side chord
  realization := by
    intro cut side chord
    exact componentCyclicEdgeCutRealization_of_edgeCut_eq
      (transversal.removed cut side chord)
      (transversal.component cut side chord)
      (transversal.boundary cut side chord)
      (transversal.insideCycle cut side chord)
      (transversal.outsideCycle cut side chord)
  width := transversal.width

end ChordTransversalDeletionAssignment

/-! This constructor makes the remaining geometric obligation explicit in
the language of the route, but only for the stronger special case in which
the chord-cycle support really is a primal cut.  The ordinary source path is
`ChordTransversalDeletionAssignment` above.  No catalogue or finite
configuration data is introduced. -/

noncomputable def ChordCyclicCutAssignment.ofCycleSideCertificates
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second)
    (widthBound : Nat)
    (certificates : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
      (chord : SectorChord pair embedded hdata htriple cut side),
      GoertzelV24ClosedWebChordCycleFaceSideTransport.CycleSideCertificate
        (G := G)
        (materializedChord chord).cycleWalk)
    (hwidth : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
      (chord : SectorChord pair embedded hdata htriple cut side),
      (chordBoundary chord).wall.card ≤ widthBound) :
    ChordCyclicCutAssignment pair embedded hdata htriple widthBound where
  edgeCut := fun _cut _side chord => (chordBoundary chord).wall
  realization := by
    intro cut side chord
    simpa only [chordBoundary_eq_materializedChord_boundary] using
      (GoertzelV24ClosedWebChordCycleFaceSideTransport.cyclicEdgeCutRealization_of_chordCycleSideCertificate
        (embedded := embedded) (chord := materializedChord chord)
        htriple (certificates cut side chord))
  width := by
    intro cut side chord
    exact hwidth cut side chord

/-! The exact-label route packages the same geometric input in a form that is
convenient for a whole sector family.  Keeping the rotated-port orientation
and the two cycle witnesses as fields is deliberate: this wrapper does not
silently turn a face label into a primal Jordan side. -/

structure ExactCutLabelSideCertificate
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    {embedded : ClosedWebAnnularEmbedding data}
    {hdata : data.WellFormed}
    {htriple : IsTaitColorTriple majority first second}
    {cut : Fin pair.firstPath.path.length} {side : Bool}
    (chord : SectorChord pair embedded hdata htriple cut side) where
  labels : OrbitFace embedded.RS → F2
  selected : F2
  hexact : ∀ dart : embedded.RS.D,
    labels (dartOrbitFace embedded.RS dart) ≠
        labels (dartOrbitFace embedded.RS (embedded.RS.alpha dart)) ↔
      (embedded.RS.edgeOf dart).1 ∈ (materializedChord chord).cycleWalk.edges
  hrotated : ChordWallRotatedExternalPorts embedded (materializedChord chord)
    htriple
  hinside_cycle : HasCycleOnSide G
    (exactCutLabelSide embedded.RS
      ((materializedChord chord).boundary htriple).wall labels selected)
  houtside_cycle : HasCycleOnSide G
    (fun vertex => ¬ exactCutLabelSide embedded.RS
      ((materializedChord chord).boundary htriple).wall labels selected vertex)

noncomputable def ChordCyclicCutAssignment.ofExactCutLabelSideCertificates
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (hC : IsTaitEdgeColoring G C)
    (htriple : IsTaitColorTriple majority first second)
    (widthBound : Nat)
    (certificates : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
      (chord : SectorChord pair embedded hdata htriple cut side),
      ExactCutLabelSideCertificate chord)
    (hwidth : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool)
      (chord : SectorChord pair embedded hdata htriple cut side),
      (chordBoundary chord).wall.card ≤ widthBound) :
    ChordCyclicCutAssignment pair embedded hdata htriple widthBound := by
  apply ChordCyclicCutAssignment.ofCycleSideCertificates
    embedded hdata htriple widthBound
  · intro cut side chord
    let certificate := certificates cut side chord
    exact cycleSideCertificate_of_exactCutLabelSide_of_rotated_external_ports
      embedded (materializedChord chord) htriple hdata hC
      certificate.labels certificate.selected certificate.hexact
      certificate.hrotated certificate.hinside_cycle certificate.houtside_cycle
  · exact hwidth

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

/-- The same graph-derived depth state, read through caller-supplied port
coordinates.  This is the source-facing form used when the geometry has
proved an actual transversal order rather than relying on the canonical
finite-type enumeration. -/
def ChordSideAssignment.profileWithIndexing
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
    (chord : SectorChord pair embedded hdata htriple cut side)
    (indexing : VertexSetCrossingIndexing embedded.RS
      (assignment.inside cut side chord)) :
    ClosedWebDepthProfile widthBound :=
  vertexSetClosedWebCutProfileOfDartOccurrencesWithIndexing widthBound
    embedded.RS (assignment.inside cut side chord) indexing
    (rotationColoringOfGraph embedded C)
    (rotationColoringOfGraph_isTait embedded C hC)
    (assignment.crossingWidth cut side chord)

/-- Assemble the coordinate-aware profile from a family of actual side
coordinates. -/
def ChordSideIndexingAssignment.profile
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    {embedded : ClosedWebAnnularEmbedding data}
    {hdata : data.WellFormed}
    {htriple : IsTaitColorTriple majority first second}
    {widthBound : Nat}
    {assignment : ChordSideAssignment pair embedded hdata htriple widthBound}
    (indexings : ChordSideIndexingAssignment assignment)
    (hC : IsTaitEdgeColoring G C)
    (cut : Fin pair.firstPath.path.length) (side : Bool)
    (chord : SectorChord pair embedded hdata htriple cut side) :
    ClosedWebDepthProfile widthBound :=
  assignment.profileWithIndexing hC cut side chord
    (indexings.indexing cut side chord)

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

/-- The depth-pigeonhole theorem in caller-supplied transversal coordinates.
The returned equality is therefore equality at the same caller-supplied
interface coordinates on the two nested sides, rather than equality under
unrelated canonical finite enumerations.  A separate geometric theorem must
certify that these coordinates have the source's transversal order. -/
theorem exists_nested_equal_coordinate_depthProfile_of_hasDeepChordTransversal
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
    (assignment : ChordSideAssignment pair embedded hdata htriple widthBound)
    (indexings : ChordSideIndexingAssignment assignment) :
    ∃ (cut : Fin pair.firstPath.path.length) (side : Bool)
        (inner outer : SectorChord pair embedded hdata htriple cut side),
      (inner ≠ outer) ∧ (inner.1.NestedIn outer.1) ∧
        ((indexings.profile hC cut side inner =
          indexings.profile hC cut side outer) ∧
        (HoleFreeChordSide embedded.cellulation
            (chordBoundary inner)
            (canonicalFaceSide embedded hdata htriple inner) ∧
          HoleFreeChordSide embedded.cellulation
            (chordBoundary outer)
            (canonicalFaceSide embedded hdata htriple outer))) := by
  let profile : ∀ (cut : Fin pair.firstPath.path.length) (side : Bool),
      SectorChord pair embedded hdata htriple cut side →
        ClosedWebDepthProfile widthBound :=
    fun cut side chord => indexings.profile hC cut side chord
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

/-- The ordinary source-facing depth route: a simple transversal/layer
boundary is supplied as a deleted edge set, its component boundary gives the
profile side, and finite repetition produces two nested equal states.  This
uses no identification of a chord cycle with a primal edge cut. -/
theorem exists_nested_equal_computed_depthProfile_of_hasDeepChordTransversal_of_deletionTransversals
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
    (transversals : ChordTransversalDeletionAssignment pair embedded hdata
      htriple widthBound) :
    ∃ (cut : Fin pair.firstPath.path.length) (side : Bool)
        (inner outer : SectorChord pair embedded hdata htriple cut side),
      (inner ≠ outer) ∧ (inner.1.NestedIn outer.1) ∧
        ((transversals.toCyclicCutAssignment.toSideAssignment.profile hC cut side inner =
          transversals.toCyclicCutAssignment.toSideAssignment.profile hC cut side outer) ∧
        (HoleFreeChordSide embedded.cellulation
            (chordBoundary inner)
            (canonicalFaceSide embedded hdata htriple inner) ∧
          HoleFreeChordSide embedded.cellulation
            (chordBoundary outer)
            (canonicalFaceSide embedded hdata htriple outer))) := by
  exact exists_nested_equal_computed_depthProfile_of_hasDeepChordTransversal_of_cyclicCuts
    embedded hdata pair htriple hC widthBound hdeep
      transversals.toCyclicCutAssignment

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

/-- Equal coordinate-aware depth profiles identify the actual Tait colors on
their corresponding crossing edges.  This is the properness entry of the
source splice checklist, stated against real graph edges rather than only the
finite profile field.  It is coordinate-faithful; a separate geometric theorem
must show that the supplied coordinates are the source's transversal order. -/
theorem ChordSideIndexingAssignment.crossingEdgeColor_eq_of_profile_eq
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    {embedded : ClosedWebAnnularEmbedding data}
    {hdata : data.WellFormed}
    {htriple : IsTaitColorTriple majority first second}
    {widthBound : Nat}
    {assignment : ChordSideAssignment pair embedded hdata htriple widthBound}
    (indexings : ChordSideIndexingAssignment assignment)
    (hC : IsTaitEdgeColoring G C)
    (cut : Fin pair.firstPath.path.length) (side : Bool)
    (inner outer : SectorChord pair embedded hdata htriple cut side)
    (hprofiles : indexings.profile hC cut side inner =
      indexings.profile hC cut side outer)
    (index : Fin (Fintype.card (VertexSetCrossingEdge embedded.RS
      (assignment.inside cut side inner)))) :
    C (vertexSetCrossingEdgeAtWithIndexing embedded.RS
        (assignment.inside cut side inner)
        (indexings.indexing cut side inner) index) =
      C (vertexSetCrossingEdgeAtWithIndexing embedded.RS
        (assignment.inside cut side outer)
        (indexings.indexing cut side outer)
        (Fin.cast (closedWebDepthProfile_crossingEdgeCount_val_eq_of_eq
          hprofiles) index)) := by
  have hcolors := closedWebDepthProfile_edgeColor_eq_of_eq hprofiles index
  have htoColor := congrArg GoertzelV24WindingClassification.StrandColor.toColor
    hcolors
  simpa [ChordSideIndexingAssignment.profile,
    ChordSideAssignment.profileWithIndexing,
    vertexSetClosedWebCutProfileOfDartOccurrencesWithIndexing,
    Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryProfileFiniteState.vertexSetBoundaryBoundedProfileOfDartOccurrencesWithIndexing,
    Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedCorridorCutProfile.GraphCorridorCutData.profile_edgeColor_toColor,
    Mettapedia.GraphTheory.FourColor.GoertzelV24RotationBoundaryFaceCutProfile.vertexSetBoundaryGraphCutDataWithIndexing,
    rotationColoringOfGraph, SimpleGraph.Coloring.mk] using htoColor

/-
The remaining profile coordinates have dependent finite indices as well.  The
following transport is deliberately just a sum map: crossing ports are
cast along the repeated width, while the terminal-port part is unchanged
(the closed-web carrier uses zero terminals).  Naming this map keeps later
splice statements about connectivity and fragment incidence readable.
-/
def transportClosedWebCorridorPort
    {leftCount rightCount terminalCount : Nat}
    (hcount : leftCount = rightCount) :
    CorridorPort leftCount terminalCount →
      CorridorPort rightCount terminalCount
  | .inl index => .inl (Fin.cast hcount index)
  | .inr index => .inr index

theorem closedWebDepthProfile_strandConnected_eq_of_eq
    {widthBound : Nat}
    {left right : ClosedWebDepthProfile widthBound}
    (hprofiles : left = right) :
    ∀ (pair : TrackedColorPair)
      (first second : CorridorPort left.crossingEdgeCount.val 0),
      left.profile.profile.strandConnected pair first second =
        right.profile.profile.strandConnected pair
          (transportClosedWebCorridorPort
            (closedWebDepthProfile_crossingEdgeCount_val_eq_of_eq hprofiles)
            first)
          (transportClosedWebCorridorPort
            (closedWebDepthProfile_crossingEdgeCount_val_eq_of_eq hprofiles)
            second) := by
  intro pair first second
  cases hprofiles
  simp only [transportClosedWebCorridorPort]
  cases first <;> cases second <;> rfl

theorem closedWebDepthProfile_faceContinues_eq_of_eq
    {widthBound : Nat}
    {left right : ClosedWebDepthProfile widthBound}
    (hprofiles : left = right) :
    ∀ (first second : Fin left.profile.faceFragmentCount.val),
      left.profile.profile.faceContinues first second =
        right.profile.profile.faceContinues
          (Fin.cast
            (closedWebDepthProfile_faceFragmentCount_val_eq_of_eq hprofiles)
            first)
          (Fin.cast
            (closedWebDepthProfile_faceFragmentCount_val_eq_of_eq hprofiles)
            second) := by
  intro first second
  cases hprofiles
  simp

theorem closedWebDepthProfile_fragmentContainsPort_eq_of_eq
    {widthBound : Nat}
    {left right : ClosedWebDepthProfile widthBound}
    (hprofiles : left = right) :
    ∀ (fragment : Fin left.profile.faceFragmentCount.val)
      (port : CorridorPort left.crossingEdgeCount.val 0),
      left.profile.profile.fragmentContainsPort fragment port =
        right.profile.profile.fragmentContainsPort
          (Fin.cast
            (closedWebDepthProfile_faceFragmentCount_val_eq_of_eq hprofiles)
            fragment)
          (transportClosedWebCorridorPort
            (closedWebDepthProfile_crossingEdgeCount_val_eq_of_eq hprofiles)
            port) := by
  intro fragment port
  cases hprofiles
  simp only [transportClosedWebCorridorPort]
  cases port <;> rfl

theorem closedWebDepthProfile_faceLengthCap_eq_of_eq
    {widthBound : Nat}
    {left right : ClosedWebDepthProfile widthBound}
    (hprofiles : left = right) :
    ∀ (fragment : Fin left.profile.faceFragmentCount.val),
      left.profile.profile.faceLengthCap fragment =
        right.profile.profile.faceLengthCap
          (Fin.cast
            (closedWebDepthProfile_faceFragmentCount_val_eq_of_eq hprofiles)
            fragment) := by
  intro fragment
  cases hprofiles
  simp

end

end GoertzelV24ClosedWebComputedDepthProfile

end Mettapedia.GraphTheory.FourColor
