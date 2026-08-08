import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebTotalClosure
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebHoleBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialPathChords

/-!
# Radial-path anchors for the two closed-web sectors

The source's L8 sector argument starts with two distinct radial components.
Before one may speak about the two sectors between them, their path
realizations must be disjoint and must land at distinct cyclic positions on
both hole faces.

This module proves exactly those prerequisites.  It does not choose hole arcs
between the four anchors and does not assert that either side of a
same-path-chord wall is hole-free.  Those are the remaining embedded
face-separation obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebRadialPathSectorAnchors

open SimpleGraph
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebSelectedEdgeStructure
open GoertzelV24ClosedWebTotalClosure

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

/-- The forward closed arc from `start` to `finish` in the standard cyclic
order on `Fin length`.  When the endpoint order wraps through zero, the arc
is the corresponding union of the two end intervals. -/
def cyclicForwardArc {length : Nat} (start finish : Fin length) :
    Finset (Fin length) :=
  Finset.univ.filter fun position =>
    if start.val ≤ finish.val then
      start.val ≤ position.val ∧ position.val ≤ finish.val
    else
      start.val ≤ position.val ∨ position.val ≤ finish.val

@[simp] theorem start_mem_cyclicForwardArc {length : Nat}
    (start finish : Fin length) :
    start ∈ cyclicForwardArc start finish := by
  classical
  simp [cyclicForwardArc]

@[simp] theorem finish_mem_cyclicForwardArc {length : Nat}
    (start finish : Fin length) :
    finish ∈ cyclicForwardArc start finish := by
  classical
  simp [cyclicForwardArc]

/-- The two directed arcs between distinct endpoints cover the whole cyclic
face boundary. -/
theorem cyclicForwardArc_union_reverse {length : Nat}
    {first second : Fin length} (hne : first ≠ second) :
    cyclicForwardArc first second ∪ cyclicForwardArc second first =
      Finset.univ := by
  classical
  ext position
  by_cases horder : first.val ≤ second.val
  · have hreverse : ¬ second.val ≤ first.val := by
      intro hback
      apply hne
      apply Fin.ext
      omega
    simp [cyclicForwardArc, horder, hreverse]
    omega
  · have hreverse : second.val ≤ first.val := by omega
    simp [cyclicForwardArc, horder, hreverse]
    omega

/-- The two directed closed arcs between distinct endpoints overlap exactly
at their common endpoints. -/
theorem cyclicForwardArc_inter_reverse {length : Nat}
    {first second : Fin length} (hne : first ≠ second) :
    cyclicForwardArc first second ∩ cyclicForwardArc second first =
      {first, second} := by
  classical
  ext position
  by_cases horder : first.val ≤ second.val
  · have hreverse : ¬ second.val ≤ first.val := by
      intro hback
      apply hne
      apply Fin.ext
      omega
    simp [cyclicForwardArc, horder, hreverse, Fin.ext_iff]
    omega
  · have hreverse : second.val ≤ first.val := by omega
    simp [cyclicForwardArc, horder, hreverse, Fin.ext_iff]
    omega

/-- Select either of the two closed cyclic arcs between distinct anchors.
Both choices include both endpoints; their interiors are the complementary
hole-boundary arcs used by the two sector candidates. -/
def selectedCyclicArc {length : Nat} (first second : Fin length)
    (side : Bool) : Finset (Fin length) :=
  if side then cyclicForwardArc first second
  else cyclicForwardArc second first

@[simp] theorem first_mem_selectedCyclicArc {length : Nat}
    (first second : Fin length) (side : Bool) :
    first ∈ selectedCyclicArc first second side := by
  cases side <;> simp [selectedCyclicArc]

@[simp] theorem second_mem_selectedCyclicArc {length : Nat}
    (first second : Fin length) (side : Bool) :
    second ∈ selectedCyclicArc first second side := by
  cases side <;> simp [selectedCyclicArc]

/-- Map a selected cyclic position arc back to the actual darts of one orbit
face. -/
noncomputable def holeArcDarts (cell : FramedAnnularCellulation G)
    (face : OrbitFace cell.rotation.toRotationSystem)
    (first second :
      Fin (orbitFaceDarts cell.rotation.toRotationSystem face).card)
    (side : Bool) : Finset cell.rotation.toRotationSystem.D :=
  (selectedCyclicArc first second side).image fun position =>
    (holeFaceDartEquiv cell face position).1

@[simp] theorem firstDart_mem_holeArcDarts
    (cell : FramedAnnularCellulation G)
    (face : OrbitFace cell.rotation.toRotationSystem)
    (first second :
      Fin (orbitFaceDarts cell.rotation.toRotationSystem face).card)
    (side : Bool) :
    (holeFaceDartEquiv cell face first).1 ∈
      holeArcDarts cell face first second side := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨first, first_mem_selectedCyclicArc first second side, rfl⟩

@[simp] theorem secondDart_mem_holeArcDarts
    (cell : FramedAnnularCellulation G)
    (face : OrbitFace cell.rotation.toRotationSystem)
    (first second :
      Fin (orbitFaceDarts cell.rotation.toRotationSystem face).card)
    (side : Bool) :
    (holeFaceDartEquiv cell face second).1 ∈
      holeArcDarts cell face first second side := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨second, second_mem_selectedCyclicArc first second side, rfl⟩

/-- The underlying graph edges of a selected cyclic hole-face arc. -/
noncomputable def holeArcEdges (cell : FramedAnnularCellulation G)
    (face : OrbitFace cell.rotation.toRotationSystem)
    (first second :
      Fin (orbitFaceDarts cell.rotation.toRotationSystem face).card)
    (side : Bool) : Finset G.edgeSet :=
  (selectedCyclicArc first second side).image fun position =>
    cell.rotation.toRotationSystem.edgeOf
      (holeFaceDartEquiv cell face position).1

@[simp] theorem firstEdge_mem_holeArcEdges
    (cell : FramedAnnularCellulation G)
    (face : OrbitFace cell.rotation.toRotationSystem)
    (first second :
      Fin (orbitFaceDarts cell.rotation.toRotationSystem face).card)
    (side : Bool) :
    cell.rotation.toRotationSystem.edgeOf
        (holeFaceDartEquiv cell face first).1 ∈
      holeArcEdges cell face first second side := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨first, first_mem_selectedCyclicArc first second side, rfl⟩

@[simp] theorem secondEdge_mem_holeArcEdges
    (cell : FramedAnnularCellulation G)
    (face : OrbitFace cell.rotation.toRotationSystem)
    (first second :
      Fin (orbitFaceDarts cell.rotation.toRotationSystem face).card)
    (side : Bool) :
    cell.rotation.toRotationSystem.edgeOf
        (holeFaceDartEquiv cell face second).1 ∈
      holeArcEdges cell face first second side := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨second, second_mem_selectedCyclicArc first second side, rfl⟩

/-- The two path realizations of two distinct components of one selected
two-color support graph.  The coverage field is the exact conclusion of the
closed-web radial-component theorem. -/
structure RadialPathPair
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (first second : Color) where
  firstComponent :
    (colorPairSupportGraph C first second).ConnectedComponent
  secondComponent :
    (colorPairSupportGraph C first second).ConnectedComponent
  components_ne : firstComponent ≠ secondComponent
  firstPath : ComponentRadialPath
    data C first second firstComponent
  secondPath : ComponentRadialPath
    data C first second secondComponent
  cover_support :
    firstPath.path.toSubgraph.verts ∪ secondPath.path.toSubgraph.verts =
      Set.univ

namespace RadialPathPair

variable {data : AnnularBoundaryData G outerCount}
  {C : G.EdgeColoring Color} {first second : Color}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Distinct support components give vertex-disjoint radial paths. -/
theorem pathVerts_disjoint
    (pair : RadialPathPair data C first second) :
    Disjoint pair.firstPath.path.toSubgraph.verts
      pair.secondPath.path.toSubgraph.verts := by
  rw [pair.firstPath.path_vertices, pair.secondPath.path_vertices]
  exact pairwise_disjoint_supp_connectedComponent
    (colorPairSupportGraph C first second) pair.components_ne

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The two radial paths remain vertex-disjoint after forgetting the selected
color-pair support subtype and viewing them in the ambient graph. -/
theorem ambientPathVerts_disjoint
    (pair : RadialPathPair data C first second) :
    Disjoint (ambientRadialPath pair.firstPath).toSubgraph.verts
      (ambientRadialPath pair.secondPath).toSubgraph.verts := by
  rw [Set.disjoint_left]
  intro vertex hfirst hsecond
  rw [SimpleGraph.Walk.mem_verts_toSubgraph] at hfirst hsecond
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hfirst with
    ⟨firstPosition, hfirstValue, _hfirstBound⟩
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hsecond with
    ⟨secondPosition, hsecondValue, _hsecondBound⟩
  let firstVertex := pair.firstPath.path.getVert firstPosition
  let secondVertex := pair.secondPath.path.getVert secondPosition
  have hvertices : firstVertex = secondVertex :=
    Subtype.ext (by
      change (pair.firstPath.path.getVert firstPosition).1 =
        (pair.secondPath.path.getVert secondPosition).1
      rw [← ambientRadialPath_getVert pair.firstPath,
        ← ambientRadialPath_getVert pair.secondPath,
        hfirstValue, hsecondValue])
  have hfirstSubgraph : firstVertex ∈
      pair.firstPath.path.toSubgraph.verts := by
    rw [SimpleGraph.Walk.mem_verts_toSubgraph]
    exact pair.firstPath.path.getVert_mem_support firstPosition
  have hsecondSubgraph : secondVertex ∈
      pair.secondPath.path.toSubgraph.verts := by
    rw [SimpleGraph.Walk.mem_verts_toSubgraph]
    exact pair.secondPath.path.getVert_mem_support secondPosition
  have hfirstInSecond : firstVertex ∈
      pair.secondPath.path.toSubgraph.verts := by
    rw [hvertices]
    exact hsecondSubgraph
  exact (Set.disjoint_left.1 pair.pathVerts_disjoint)
    hfirstSubgraph hfirstInSecond

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Two distinct radial components cannot start at the same inner stub. -/
theorem inner_ne (pair : RadialPathPair data C first second) :
    pair.firstPath.inner ≠ pair.secondPath.inner := by
  intro hinner
  have hstart : pair.firstPath.start = pair.secondPath.start := by
    apply Subtype.ext
    calc
      pair.firstPath.start.1 = data.innerStub pair.firstPath.inner :=
        pair.firstPath.start_eq_innerStub
      _ = data.innerStub pair.secondPath.inner :=
        congrArg data.innerStub hinner
      _ = pair.secondPath.start.1 :=
        pair.secondPath.start_eq_innerStub.symm
  have hfirstComponent :
      (colorPairSupportGraph C first second).connectedComponentMk
          pair.firstPath.start = pair.firstComponent :=
    (ConnectedComponent.mem_supp_iff pair.firstComponent
      pair.firstPath.start).mp pair.firstPath.start_mem
  have hsecondComponent :
      (colorPairSupportGraph C first second).connectedComponentMk
          pair.secondPath.start = pair.secondComponent :=
    (ConnectedComponent.mem_supp_iff pair.secondComponent
      pair.secondPath.start).mp pair.secondPath.start_mem
  apply pair.components_ne
  exact hfirstComponent.symm.trans <|
    (congrArg
      (colorPairSupportGraph C first second).connectedComponentMk hstart).trans
        hsecondComponent

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Two distinct radial components cannot finish at the same outer stub. -/
theorem outer_ne (pair : RadialPathPair data C first second) :
    pair.firstPath.outer ≠ pair.secondPath.outer := by
  intro houter
  have hfinish : pair.firstPath.finish = pair.secondPath.finish := by
    apply Subtype.ext
    calc
      pair.firstPath.finish.1 = data.outerStub pair.firstPath.outer :=
        pair.firstPath.finish_eq_outerStub
      _ = data.outerStub pair.secondPath.outer :=
        congrArg data.outerStub houter
      _ = pair.secondPath.finish.1 :=
        pair.secondPath.finish_eq_outerStub.symm
  have hfirstComponent :
      (colorPairSupportGraph C first second).connectedComponentMk
          pair.firstPath.finish = pair.firstComponent :=
    (ConnectedComponent.mem_supp_iff pair.firstComponent
      pair.firstPath.finish).mp pair.firstPath.finish_mem
  have hsecondComponent :
      (colorPairSupportGraph C first second).connectedComponentMk
          pair.secondPath.finish = pair.secondComponent :=
    (ConnectedComponent.mem_supp_iff pair.secondComponent
      pair.secondPath.finish).mp pair.secondPath.finish_mem
  apply pair.components_ne
  exact hfirstComponent.symm.trans <|
    (congrArg
      (colorPairSupportGraph C first second).connectedComponentMk hfinish).trans
        hsecondComponent

/-- The two inner radial endpoints occupy distinct cyclic positions on the
actual inner hole face. -/
theorem innerBoundaryPositions_ne
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) :
    innerBoundaryPosition embedded hdata pair.firstPath.inner ≠
      innerBoundaryPosition embedded hdata pair.secondPath.inner := by
  intro hposition
  exact pair.inner_ne <|
    innerBoundaryPosition_injective embedded hdata hposition

/-- The two outer radial endpoints occupy distinct cyclic positions on the
actual outer hole face. -/
theorem outerBoundaryPositions_ne
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) :
    outerBoundaryPosition embedded hdata pair.firstPath.outer ≠
      outerBoundaryPosition embedded hdata pair.secondPath.outer := by
  intro hposition
  exact pair.outer_ne <|
    outerBoundaryPosition_injective embedded hdata hposition

/-- One of the two actual inner-hole dart arcs between the radial paths. -/
noncomputable def innerHoleArcDarts
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (side : Bool) :
    Finset embedded.cellulation.rotation.toRotationSystem.D :=
  holeArcDarts embedded.cellulation embedded.cellulation.innerHole
    (innerBoundaryPosition embedded hdata pair.firstPath.inner)
    (innerBoundaryPosition embedded hdata pair.secondPath.inner) side

/-- One of the two actual outer-hole dart arcs between the radial paths. -/
noncomputable def outerHoleArcDarts
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (side : Bool) :
    Finset embedded.cellulation.rotation.toRotationSystem.D :=
  holeArcDarts embedded.cellulation embedded.cellulation.outerHole
    (outerBoundaryPosition embedded hdata pair.firstPath.outer)
    (outerBoundaryPosition embedded hdata pair.secondPath.outer) side

/-- The two ambient radial paths, as the primal edge wall common to every
sector candidate. -/
noncomputable def radialPathEdges
    (pair : RadialPathPair data C first second) : Finset G.edgeSet :=
  walkEdgeFinset (ambientRadialPath pair.firstPath) ∪
    walkEdgeFinset (ambientRadialPath pair.secondPath)

/-- One of the two inner-hole edge arcs between the radial endpoints. -/
noncomputable def innerHoleArcEdges
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (side : Bool) : Finset G.edgeSet :=
  holeArcEdges embedded.cellulation embedded.cellulation.innerHole
    (innerBoundaryPosition embedded hdata pair.firstPath.inner)
    (innerBoundaryPosition embedded hdata pair.secondPath.inner) side

/-- One of the two outer-hole edge arcs between the radial endpoints. -/
noncomputable def outerHoleArcEdges
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (side : Bool) : Finset G.edgeSet :=
  holeArcEdges embedded.cellulation embedded.cellulation.outerHole
    (outerBoundaryPosition embedded hdata pair.firstPath.outer)
    (outerBoundaryPosition embedded hdata pair.secondPath.outer) side

/-- A candidate sector boundary consists of both radial paths and one of the
two arcs on each hole face.  There are four such combinatorial candidates.
The missing rotation-system separation theorem must identify the two genuine
complementary sectors; no compatibility is assumed here. -/
noncomputable def sectorCandidateWall
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (innerSide outerSide : Bool) :
    Finset G.edgeSet :=
  pair.radialPathEdges ∪ pair.innerHoleArcEdges embedded hdata innerSide ∪
    pair.outerHoleArcEdges embedded hdata outerSide

theorem radialPathEdges_subset_sectorCandidateWall
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (innerSide outerSide : Bool) :
    pair.radialPathEdges ⊆
      pair.sectorCandidateWall embedded hdata innerSide outerSide := by
  intro edge hedge
  simp [sectorCandidateWall, hedge]

theorem innerHoleArcEdges_subset_sectorCandidateWall
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (innerSide outerSide : Bool) :
    pair.innerHoleArcEdges embedded hdata innerSide ⊆
      pair.sectorCandidateWall embedded hdata innerSide outerSide := by
  intro edge hedge
  simp [sectorCandidateWall, hedge]

theorem outerHoleArcEdges_subset_sectorCandidateWall
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (innerSide outerSide : Bool) :
    pair.outerHoleArcEdges embedded hdata outerSide ⊆
      pair.sectorCandidateWall embedded hdata innerSide outerSide := by
  intro edge hedge
  simp [sectorCandidateWall, hedge]

end RadialPathPair

/-- Source-facing L8 entry point.  At the sharp five-stub boundary, total
closure and a good word produce two disjoint radial paths with four distinct
cyclic sector anchors.  Choosing the two complementary hole arcs between
these anchors is the next topological step. -/
theorem exists_radialPathPair_with_distinct_hole_positions_at_five
    {data : AnnularBoundaryData G 5}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (hconnected : G.Connected)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hclosed : TotallyClosedWeb data C)
    (hgood : CAP5BoundaryWordHasColoredBlock311
      (data.innerBoundaryWord C)) :
    ∃ majority singletonFirst singletonSecond : Color,
      IsTaitColorTriple majority singletonFirst singletonSecond ∧
      ∃ pair : RadialPathPair data C singletonFirst singletonSecond,
        Disjoint pair.firstPath.path.toSubgraph.verts
            pair.secondPath.path.toSubgraph.verts ∧
        innerBoundaryPosition embedded hdata pair.firstPath.inner ≠
            innerBoundaryPosition embedded hdata pair.secondPath.inner ∧
        outerBoundaryPosition embedded hdata pair.firstPath.outer ≠
            outerBoundaryPosition embedded hdata pair.secondPath.outer := by
  rcases exists_singletonPair_two_radialPaths_at_five_of_totallyClosed
      data hdata hconnected C hC hclosed hgood with
    ⟨majority, singletonFirst, singletonSecond, htriple,
      firstComponent, secondComponent, hcomponents,
      firstPath, secondPath, hcover⟩
  let pair : RadialPathPair data C singletonFirst singletonSecond :=
    { firstComponent := firstComponent
      secondComponent := secondComponent
      components_ne := hcomponents
      firstPath := firstPath
      secondPath := secondPath
      cover_support := hcover }
  exact ⟨majority, singletonFirst, singletonSecond, htriple, pair,
    pair.pathVerts_disjoint,
    pair.innerBoundaryPositions_ne embedded hdata,
    pair.outerBoundaryPositions_ne embedded hdata⟩

end GoertzelV24ClosedWebRadialPathSectorAnchors

end Mettapedia.GraphTheory.FourColor
