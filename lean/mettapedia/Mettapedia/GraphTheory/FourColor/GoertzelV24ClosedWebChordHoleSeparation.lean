import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialPathSectorAnchors
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceCutVertexAvoidingTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedAnnularFaceParityCut

/-!
# The comparison radial path keeps chord-cycle holes on one side

For a same-path chord on one of the two disjoint radial paths, the chord and
its intervening path subarc form a simple cycle.  The second radial path is
vertex-disjoint from that cycle and still runs from the inner interface to the
outer interface.  Exact-cut transport along this comparison path therefore
forces the two named hole faces to receive the same binary side label.

This is the topological content missing from the manuscript's incompatible
descriptions of the chord region.  It does not choose a side by prose: it
derives the same-hole-side fact from the two actual radial paths.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebChordHoleSeparation

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24FaceCutVertexAvoidingTransport
open GoertzelV24FaceCutTransport
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24OrbitFaceParityBoundary
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- A same-path chord cycle carried by one radial component admits an exact
face cut in which the two annular hole faces have the same label. -/
theorem exists_exact_chordCycle_faceCut_with_holes_sameSide
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (chord : MajorityChordOnRadialPath C majority first second
      pair.firstPath)
    (htriple : IsTaitColorTriple majority first second) :
    ∃ labels : OrbitFace embedded.RS → F2,
      orbitFaceParityBoundaryLinearMap embedded.RS labels =
          walkEdgeParity chord.cycleWalk ∧
        (∀ dart : embedded.RS.D,
          labels (dartOrbitFace embedded.RS dart) ≠
              labels (dartOrbitFace embedded.RS
                (embedded.RS.alpha dart)) ↔
            (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges) ∧
        labels embedded.cellulation.innerHole =
          labels embedded.cellulation.outerHole := by
  have hcycle : chord.cycleWalk.IsCycle :=
    chord.cycleWalk_isCycle htriple
  rcases embedded.cellulation.exists_exact_orbitFaceCut_of_isTrail
      chord.cycleWalk hcycle.isTrail with ⟨labels, hlabels, hexact⟩
  let comparison := ambientRadialPath pair.secondPath
  have hcomparisonEndpoints :
      pair.secondPath.start.1 ≠ pair.secondPath.finish.1 := by
    intro heq
    apply hdata.inner_outer_stub_disjoint
      pair.secondPath.inner pair.secondPath.outer
    exact pair.secondPath.start_eq_innerStub.symm.trans <|
      heq.trans pair.secondPath.finish_eq_outerStub
  have hcomparisonNonempty : ¬comparison.Nil :=
    SimpleGraph.Walk.not_nil_of_ne hcomparisonEndpoints
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  have hcomparisonAvoids :
      ∀ based ∈ comparison.darts, ∀ incident : G.Dart,
        incident.fst = based.fst →
          (embedded.RS.edgeOf incident).1 ∉ chord.cycleWalk.edges := by
    intro based hbased incident hincident hcut
    have hsecondSupport : based.fst ∈ comparison.support :=
      comparison.dart_fst_mem_support_of_mem_darts hbased
    have hincidentVertex : based.fst ∈
        ((embedded.RS.edgeOf incident).1 : Sym2 V) := by
      change based.fst ∈ incident.edge
      rw [← hincident]
      simp [SimpleGraph.Dart.edge]
    have hfirstSupport : based.fst ∈
        (ambientRadialPath pair.firstPath).support :=
      chord.mem_ambientRadialPath_support_of_mem_cycleWalk_edges
        htriple (embedded.RS.edgeOf incident) hcut hincidentVertex
    have hfirstVerts : based.fst ∈
        (ambientRadialPath pair.firstPath).toSubgraph.verts := by
      rw [SimpleGraph.Walk.mem_verts_toSubgraph]
      exact hfirstSupport
    have hsecondVerts : based.fst ∈ comparison.toSubgraph.verts := by
      rw [SimpleGraph.Walk.mem_verts_toSubgraph]
      exact hsecondSupport
    exact (Set.disjoint_left.1 pair.ambientPathVerts_disjoint)
      hfirstVerts hsecondVerts
  have htransport :=
    walk_labels_eq_firstDart_alpha_lastDart_of_vertices_avoid_cut
      embedded.cellulation.rotation hrotation labels
        (fun edge => edge.1 ∈ chord.cycleWalk.edges) hexact
        comparison hcomparisonNonempty hcomparisonAvoids
  have hfirstFace :
      dartOrbitFace embedded.RS
          (comparison.firstDart hcomparisonNonempty) =
        embedded.cellulation.innerHole := by
    apply embedded.innerBoundaryEdgeDarts_on_innerHole
      pair.secondPath.inner
    apply (embedded.RS.mem_dartsOn).2
    apply Subtype.ext
    exact ambientRadialPath_firstDart_edgeOf_eq_innerBoundaryEdge
      hdata pair.secondPath hcomparisonNonempty
  have hlastFace :
      dartOrbitFace embedded.RS
          (embedded.RS.alpha
            (comparison.lastDart hcomparisonNonempty)) =
        embedded.cellulation.outerHole := by
    apply embedded.outerBoundaryEdgeDarts_on_outerHole
      pair.secondPath.outer
    apply (embedded.RS.mem_dartsOn).2
    rw [embedded.RS.edge_alpha]
    apply Subtype.ext
    exact ambientRadialPath_lastDart_edgeOf_eq_outerBoundaryEdge
      hdata pair.secondPath hcomparisonNonempty
  refine ⟨labels, hlabels, hexact, ?_⟩
  rwa [hfirstFace, hlastFace] at htransport

/-- Along a facial-dual edge that avoids the chord wall, an exact chord-cycle
cut has equal labels at the two endpoint faces. -/
theorem labels_eq_of_faceAdjacencyAvoiding_chordCycle
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    {left right : FullFace embedded.cellulation}
    (hadj : (faceAdjacencyAvoiding
      (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))
      (chord.boundary htriple).wall).Adj left right) :
    labels left.1 = labels right.1 := by
  rcases (faceAdjacencyAvoiding_adj_iff
      (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))
      (chord.boundary htriple).wall).1 hadj with
    ⟨hfaces, edge, _hinterior, hedgeAway, hedgeLeft, hedgeRight⟩
  rcases (mem_orbitFaceBoundary_iff embedded.RS left.1 edge).1
      hedgeLeft with ⟨leftDart, hleftDart, hleftEdge⟩
  rcases (mem_orbitFaceBoundary_iff embedded.RS right.1 edge).1
      hedgeRight with ⟨rightDart, hrightDart, hrightEdge⟩
  have hleftFace : dartOrbitFace embedded.RS leftDart = left.1 :=
    (mem_orbitFaceDarts_iff embedded.RS left.1 leftDart).1 hleftDart
  have hrightFace : dartOrbitFace embedded.RS rightDart = right.1 :=
    (mem_orbitFaceDarts_iff embedded.RS right.1 rightDart).1 hrightDart
  have hrightDartEq : rightDart = embedded.RS.alpha leftDart := by
    rcases embedded.RS.edge_fiber_two_cases hleftEdge hrightEdge with
      heq | heq
    · exfalso
      apply hfaces
      rw [← hleftFace, ← hrightFace, heq]
    · exact heq
  have hedgeNotCycle : edge.1 ∉ chord.cycleWalk.edges := by
    intro hedgeCycle
    exact hedgeAway <|
      (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple edge).2
        hedgeCycle
  have hnotLeft :
      (embedded.RS.edgeOf leftDart).1 ∉ chord.cycleWalk.edges := by
    rw [hleftEdge]
    exact hedgeNotCycle
  have hcross := labels_eq_alpha_of_not_cut embedded.RS labels
    (fun candidate => candidate.1 ∈ chord.cycleWalk.edges)
      hexact leftDart hnotLeft
  have halphaFace :
      dartOrbitFace embedded.RS (embedded.RS.alpha leftDart) = right.1 := by
    rw [← hrightDartEq]
    exact hrightFace
  rwa [hleftFace, halphaFace] at hcross

/-- Exact chord-cycle labels are constant on every connected component of the
facial dual after the chord wall is removed. -/
theorem labels_eq_of_reachable_avoiding_chordCycle
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    {left right : FullFace embedded.cellulation}
    (hreach : (faceAdjacencyAvoiding
      (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))
      (chord.boundary htriple).wall).Reachable left right) :
    labels left.1 = labels right.1 := by
  rcases hreach with ⟨walk⟩
  induction walk with
  | nil => rfl
  | @cons firstFace secondFace lastFace hadjacent tail ih =>
      exact (labels_eq_of_faceAdjacencyAvoiding_chordCycle
        embedded chord htriple labels hexact hadjacent).trans ih

/-- One of the two actual facial sides of every same-path chord cycle is
hole-free.  The side is derived from the exact cut and the comparison radial
path; it is not selected by a manuscript convention. -/
theorem exists_holeFreeChordSide
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (chord : MajorityChordOnRadialPath C majority first second
      pair.firstPath)
    (htriple : IsTaitColorTriple majority first second) :
    ∃ side : Bool,
      HoleFreeChordSide embedded.cellulation
        (chord.boundary htriple) side := by
  rcases exists_exact_chordCycle_faceCut_with_holes_sameSide
      embedded hdata pair chord htriple with
    ⟨labels, _hlabels, hexact, hholes⟩
  have hchordEdge :
      (embedded.RS.edgeOf chord.chordDart).1 ∈
        chord.cycleWalk.edges := by
    simp [MajorityChordOnRadialPath.cycleWalk]
    exact Or.inl rfl
  have hchordSides :
      labels (dartOrbitFace embedded.RS chord.chordDart) ≠
        labels (dartOrbitFace embedded.RS
          (embedded.RS.alpha chord.chordDart)) :=
    (hexact chord.chordDart).2 hchordEdge
  by_cases hfirstHole :
      labels (dartOrbitFace embedded.RS chord.chordDart) =
        labels embedded.cellulation.innerHole
  · refine ⟨true, ?_⟩
    have hseedInner :
        labels (chordSideFace embedded.cellulation
          (chord.boundary htriple) true) ≠
            labels embedded.cellulation.innerHole := by
      simp only [chordSideFace, if_true]
      change labels (dartOrbitFace embedded.RS
        (embedded.RS.alpha chord.chordDart)) ≠
          labels embedded.cellulation.innerHole
      intro heq
      exact hchordSides (hfirstHole.trans heq.symm)
    rw [holeFreeChordSide_iff]
    constructor
    · intro hreach
      exact hseedInner <|
        labels_eq_of_reachable_avoiding_chordCycle
          embedded chord htriple labels hexact hreach
    · intro hreach
      have hseedOuter := labels_eq_of_reachable_avoiding_chordCycle
        embedded chord htriple labels hexact hreach
      exact hseedInner (hseedOuter.trans hholes.symm)
  · refine ⟨false, ?_⟩
    have hseedInner :
        labels (chordSideFace embedded.cellulation
          (chord.boundary htriple) false) ≠
            labels embedded.cellulation.innerHole := by
      simpa [chordSideFace,
        MajorityChordOnRadialPath.boundary] using hfirstHole
    rw [holeFreeChordSide_iff]
    constructor
    · intro hreach
      exact hseedInner <|
        labels_eq_of_reachable_avoiding_chordCycle
          embedded chord htriple labels hexact hreach
    · intro hreach
      have hseedOuter := labels_eq_of_reachable_avoiding_chordCycle
        embedded chord htriple labels hexact hreach
      exact hseedInner (hseedOuter.trans hholes.symm)

end

end GoertzelV24ClosedWebChordHoleSeparation

end Mettapedia.GraphTheory.FourColor
