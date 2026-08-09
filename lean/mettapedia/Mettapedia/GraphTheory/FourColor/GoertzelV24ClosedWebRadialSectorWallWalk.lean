import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialPathSectorAnchors
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebTrimmedRadialPath

/-!
# Closed sector walks from two radial paths

The two trimmed radial cores and the corresponding inner- and outer-hole core
arcs have matching endpoints.  This module composes those four actual graph
walks into a closed sector walk.  Simplicity and planar separation are not
included: they are the next geometric obligations, not structure fields.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebRadialSectorWallWalk

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24ClosedWebHoleCoreArcWalk
open GoertzelV24OrbitFaceArcWalk
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24ClosedWebTrimmedRadialPath
open GoertzelV24FaceOrbitIncidence
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

/-- The four compatible pieces of one oriented sector boundary. -/
structure RadialSectorWallWalk
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (first second : Color)
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) where
  firstCore : RadialCorePath data C first second pair.firstPath hdata
  secondCore : RadialCorePath data C first second pair.secondPath hdata
  outerArc : G.Walk
    (outerBoundaryDart data hdata pair.firstPath.outer).snd
    (outerBoundaryDart data hdata pair.secondPath.outer).snd
  outerArc_on_outerHole : ∀ dart ∈ outerArc.darts,
    dartOrbitFace embedded.RS dart = embedded.cellulation.outerHole
  outerArc_avoids_first :
    (data.outerBoundaryEdge pair.firstPath.outer).1 ∉ outerArc.edges
  outerArc_avoids_second :
    (data.outerBoundaryEdge pair.secondPath.outer).1 ∉ outerArc.edges
  innerArc : G.Walk
    (innerBoundaryDart data hdata pair.secondPath.inner).snd
    (innerBoundaryDart data hdata pair.firstPath.inner).snd
  innerArc_on_innerHole : ∀ dart ∈ innerArc.darts,
    dartOrbitFace embedded.RS dart = embedded.cellulation.innerHole
  innerArc_avoids_second :
    (data.innerBoundaryEdge pair.secondPath.inner).1 ∉ innerArc.edges
  innerArc_avoids_first :
    (data.innerBoundaryEdge pair.firstPath.inner).1 ∉ innerArc.edges

namespace RadialSectorWallWalk

variable {data : AnnularBoundaryData G outerCount}
  {C : G.EdgeColoring Color} {first second : Color}
  {pair : RadialPathPair data C first second}
  {embedded : ClosedWebAnnularEmbedding data}
  {hdata : data.WellFormed}

/-- Follow the first radial core outward, cross the outer hole, return on the
second core, and close along the inner hole. -/
noncomputable def walk
    (wall : RadialSectorWallWalk data C first second pair embedded hdata) :
    G.Walk
      (innerBoundaryDart data hdata pair.firstPath.inner).snd
      (innerBoundaryDart data hdata pair.firstPath.inner).snd :=
  (((wall.firstCore.path.append wall.outerArc).append
    wall.secondCore.path.reverse).append wall.innerArc)

@[simp] theorem walk_length
    (wall : RadialSectorWallWalk data C first second pair embedded hdata) :
    wall.walk.length = wall.firstCore.path.length + wall.outerArc.length +
      wall.secondCore.path.length + wall.innerArc.length := by
  simp [walk, Nat.add_assoc]

/-- Every edge of the closed walk comes from one of its four geometric
pieces, and conversely. -/
theorem mem_walk_edges_iff
    (wall : RadialSectorWallWalk data C first second pair embedded hdata)
    (edge : Sym2 V) :
    edge ∈ wall.walk.edges ↔
      edge ∈ wall.firstCore.path.edges ∨ edge ∈ wall.outerArc.edges ∨
      edge ∈ wall.secondCore.path.edges ∨ edge ∈ wall.innerArc.edges := by
  simp [walk]

/-- The two trimmed radial sides of a sector wall remain edge-disjoint.
This is inherited from the stronger vertex-disjointness of their two ambient
support components; trimming cannot introduce a new edge. -/
theorem radialCore_edges_disjoint
    (wall : RadialSectorWallWalk data C first second pair embedded hdata) :
    wall.firstCore.path.edges.Disjoint wall.secondCore.path.edges := by
  rw [List.disjoint_left]
  intro edge hfirst hsecond
  have hfirstAmbient : edge ∈
      (ambientRadialPath pair.firstPath).edges := by
    rw [wall.firstCore.edges_eq] at hfirst
    exact List.mem_of_mem_tail (List.mem_of_mem_dropLast hfirst)
  have hsecondAmbient : edge ∈
      (ambientRadialPath pair.secondPath).edges := by
    rw [wall.secondCore.edges_eq] at hsecond
    exact List.mem_of_mem_tail (List.mem_of_mem_dropLast hsecond)
  induction edge using Sym2.inductionOn with
  | _ left right =>
      have hleftFirst : left ∈
          (ambientRadialPath pair.firstPath).toSubgraph.verts := by
        rw [Walk.mem_verts_toSubgraph]
        exact (ambientRadialPath pair.firstPath).fst_mem_support_of_mem_edges
          hfirstAmbient
      have hleftSecond : left ∈
          (ambientRadialPath pair.secondPath).toSubgraph.verts := by
        rw [Walk.mem_verts_toSubgraph]
        exact (ambientRadialPath pair.secondPath).fst_mem_support_of_mem_edges
          hsecondAmbient
      exact (Set.disjoint_left.1 pair.ambientPathVerts_disjoint)
        hleftFirst hleftSecond

/-! The sector constructor deliberately leaves simplicity and separation to
the geometric layer.  The following finite interface records the exact
cross-piece edge obligations needed for the graph-theoretic part.  The
radial-core pair is omitted because `radialCore_edges_disjoint` proves it
from the path-component invariant; the five remaining pairs are supplied by
the geometric layer.  It is stronger than the fields needed to form the
closed walk, but weaker than any Jordan conclusion. -/

def PiecewiseEdgeDisjoint
    (wall : RadialSectorWallWalk data C first second pair embedded hdata) : Prop :=
  wall.firstCore.path.edges.Disjoint wall.outerArc.edges ∧
    wall.firstCore.path.edges.Disjoint wall.innerArc.edges ∧
    wall.outerArc.edges.Disjoint wall.secondCore.path.edges ∧
    wall.outerArc.edges.Disjoint wall.innerArc.edges ∧
    wall.secondCore.path.edges.Disjoint wall.innerArc.edges

theorem walk_isTrail_of_piecewiseEdgeDisjoint
    (wall : RadialSectorWallWalk data C first second pair embedded hdata)
    (houter : wall.outerArc.IsTrail)
    (hinner : wall.innerArc.IsTrail)
    (hpieces : wall.PiecewiseEdgeDisjoint) :
    wall.walk.IsTrail := by
  rcases hpieces with
    ⟨hfirstOuter, hfirstInner, houterSecond,
      houterInner, hsecondInner⟩
  have hfirstSecond :
      wall.firstCore.path.edges.Disjoint wall.secondCore.path.edges :=
    wall.radialCore_edges_disjoint
  have hfirst : wall.firstCore.path.IsTrail :=
    wall.firstCore.path_isPath.isTrail
  have hsecond : wall.secondCore.path.reverse.IsTrail :=
    wall.secondCore.path_isPath.isTrail.reverse
  have houter' : wall.outerArc.IsTrail := houter
  have hinner' : wall.innerArc.IsTrail := hinner
  have hfirstOuter' :
      wall.firstCore.path.edges.Disjoint wall.outerArc.edges := hfirstOuter
  have hfirstSecond' :
      wall.firstCore.path.edges.Disjoint wall.secondCore.path.reverse.edges := by
    simpa using hfirstSecond
  have hfirstInner' :
      wall.firstCore.path.edges.Disjoint wall.innerArc.edges := hfirstInner
  have houterSecond' :
      wall.outerArc.edges.Disjoint wall.secondCore.path.reverse.edges := by
    simpa using houterSecond
  have houterInner' :
      wall.outerArc.edges.Disjoint wall.innerArc.edges := houterInner
  have hsecondInner' :
      wall.secondCore.path.reverse.edges.Disjoint wall.innerArc.edges := by
    simpa using hsecondInner
  unfold walk
  rw [SimpleGraph.Walk.isTrail_append,
    SimpleGraph.Walk.isTrail_append,
    SimpleGraph.Walk.isTrail_append]
  refine ⟨?_, hinner', ?_⟩
  ·
    refine ⟨⟨hfirst, houter', hfirstOuter'⟩, hsecond, ?_⟩
    rw [SimpleGraph.Walk.edges_append, List.disjoint_left]
    intro edge hedge hsecondEdge
    rcases List.mem_append.mp hedge with hfirstEdge | houterEdge
    · exact (List.disjoint_left.mp hfirstSecond') hfirstEdge hsecondEdge
    · exact (List.disjoint_left.mp houterSecond') houterEdge hsecondEdge
  · rw [SimpleGraph.Walk.edges_append, List.disjoint_left]
    intro edge hedge hinnerEdge
    rcases List.mem_append.mp hedge with hfirstSecondEdge | hsecondEdge
    · have hfirstSecondEdge' :
          edge ∈ wall.firstCore.path.edges ++ wall.outerArc.edges := by
        simpa only [SimpleGraph.Walk.edges_append] using hfirstSecondEdge
      rcases List.mem_append.mp hfirstSecondEdge' with hfirstEdge | houterEdge
      · exact (List.disjoint_left.mp hfirstInner') hfirstEdge hinnerEdge
      · exact (List.disjoint_left.mp houterInner') houterEdge hinnerEdge
    · exact (List.disjoint_left.mp hsecondInner') hsecondEdge hinnerEdge

/-- The finite cross-piece condition is not merely sufficient: after the
two radial cores are trimmed, it is exactly what remains for the four-piece
sector wall to be a trail.  This makes the L8 simplicity obligation a
checkable property of the concrete wall, rather than a hidden topological
assumption. -/
theorem walk_isTrail_iff
    (wall : RadialSectorWallWalk data C first second pair embedded hdata) :
    wall.walk.IsTrail ↔
      wall.outerArc.IsTrail ∧ wall.innerArc.IsTrail ∧
        wall.PiecewiseEdgeDisjoint := by
  constructor
  · intro htrail
    unfold walk at htrail
    rw [SimpleGraph.Walk.isTrail_append,
      SimpleGraph.Walk.isTrail_append,
      SimpleGraph.Walk.isTrail_append] at htrail
    rcases htrail with
      ⟨⟨⟨_hfirst, houter, hfirstOuter⟩, _hsecond,
        hfirstOuterSecond⟩, hinner, hwholeInner⟩
    rw [SimpleGraph.Walk.edges_append] at hfirstOuterSecond
    rw [SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_append] at hwholeInner
    have hfirstInner :
        wall.firstCore.path.edges.Disjoint wall.innerArc.edges := by
      rw [List.disjoint_left]
      intro edge hfirst hinnerEdge
      exact (List.disjoint_left.mp hwholeInner)
        (List.mem_append_left _ (List.mem_append_left _ hfirst)) hinnerEdge
    have houterSecond :
        wall.outerArc.edges.Disjoint wall.secondCore.path.edges := by
      rw [List.disjoint_left]
      intro edge houterEdge hsecond
      exact (List.disjoint_left.mp hfirstOuterSecond)
        (List.mem_append_right _ houterEdge) (by simpa using hsecond)
    have houterInner :
        wall.outerArc.edges.Disjoint wall.innerArc.edges := by
      rw [List.disjoint_left]
      intro edge houterEdge hinnerEdge
      exact (List.disjoint_left.mp hwholeInner)
        (List.mem_append_left _ (List.mem_append_right _ houterEdge)) hinnerEdge
    have hsecondInner :
        wall.secondCore.path.edges.Disjoint wall.innerArc.edges := by
      rw [List.disjoint_left]
      intro edge hsecond hinnerEdge
      exact (List.disjoint_left.mp hwholeInner)
        (List.mem_append_right _ (by simpa using hsecond)) hinnerEdge
    exact ⟨houter, hinner,
      ⟨hfirstOuter, hfirstInner, houterSecond, houterInner, hsecondInner⟩⟩
  · rintro ⟨houter, hinner, hpieces⟩
    exact wall.walk_isTrail_of_piecewiseEdgeDisjoint houter hinner hpieces

/-! A positive trail-shaped sector wall contains a genuine simple cycle.
This is the graph-side bridge; the remaining geometric work is to establish
the trail/disjointness interface above and to place the resulting cycle on
the desired complementary side. -/

theorem exists_cycle_subsupport_of_piecewiseEdgeDisjoint
    (wall : RadialSectorWallWalk data C first second pair embedded hdata)
    (houter : wall.outerArc.IsTrail)
    (hinner : wall.innerArc.IsTrail)
    (hpieces : wall.PiecewiseEdgeDisjoint)
    (hpositive : 0 < wall.walk.length) :
    ∃ (cycleStart : V) (cycle : G.Walk cycleStart cycleStart),
      cycle.IsCycle ∧ cycle.edges ⊆ wall.walk.edges := by
  have htrail := wall.walk_isTrail_of_piecewiseEdgeDisjoint
    houter hinner hpieces
  have hnotnil : wall.walk ≠ .nil := by
    intro hnil
    have hzero : wall.walk.length = 0 := by simp [hnil]
    omega
  let cycle := wall.walk.cycleBypass
  have hcycle : cycle.IsCycle := htrail.isCycle_cycleBypass hnotnil
  exact ⟨_, cycle, hcycle,
    wall.walk.edges_cycleBypass_subset_edges⟩

end RadialSectorWallWalk

/-- The two distinct radial paths canonically supply all four compatible
pieces of an oriented closed sector walk. -/
theorem exists_radialSectorWallWalk
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {first second : Color}
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) :
    Nonempty (RadialSectorWallWalk data C first second pair embedded hdata) := by
  rcases exists_radialCorePath hdata pair.firstPath with ⟨firstCore⟩
  rcases exists_radialCorePath hdata pair.secondPath with ⟨secondCore⟩
  rcases exists_outerHoleCoreArcWalk_avoids_boundaryEdges embedded hdata
      pair.outer_ne with
    ⟨outerArc, outerFace, _outerLength, outerFirst, outerSecond⟩
  rcases exists_innerHoleCoreArcWalk_avoids_boundaryEdges embedded hdata
      pair.inner_ne.symm with
    ⟨innerArc, innerFace, _innerLength, innerSecond, innerFirst⟩
  exact ⟨{
    firstCore := firstCore
    secondCore := secondCore
    outerArc := outerArc
    outerArc_on_outerHole := outerFace
    outerArc_avoids_first := outerFirst
    outerArc_avoids_second := outerSecond
    innerArc := innerArc
    innerArc_on_innerHole := innerFace
    innerArc_avoids_second := innerSecond
    innerArc_avoids_first := innerFirst
  }⟩

/-! With the retained-prefix local two-sidedness certificates, the two hole
arcs can be selected as genuine trails while preserving the endpoint-edge
avoidance required by the sector wall.  Cross-piece disjointness and planar
separation remain separate geometric premises. -/

theorem exists_radialSectorWallWalk_with_local_twoSided_arcs
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {first second : Color}
    (pair : RadialPathPair data C first second)
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (houterTarget : embedded.RS.alpha
        (outerBoundaryDart data hdata pair.secondPath.outer) ∈
      embedded.RS.faceOrbit
        (embedded.RS.phi
          (outerBoundaryDart data hdata pair.firstPath.outer)))
    (houterLocal : ∀ dart ∈ faceArcDarts embedded.cellulation.rotation
        (embedded.RS.phi
          (outerBoundaryDart data hdata pair.firstPath.outer))
        (embedded.RS.alpha
          (outerBoundaryDart data hdata pair.secondPath.outer))
        houterTarget,
      dartOrbitFace embedded.RS dart ≠
        dartOrbitFace embedded.RS (embedded.RS.alpha dart))
    (hinnerTarget : embedded.RS.alpha
        (innerBoundaryDart data hdata pair.firstPath.inner) ∈
      embedded.RS.faceOrbit
        (embedded.RS.phi
          (innerBoundaryDart data hdata pair.secondPath.inner)))
    (hinnerLocal : ∀ dart ∈ faceArcDarts embedded.cellulation.rotation
        (embedded.RS.phi
          (innerBoundaryDart data hdata pair.secondPath.inner))
        (embedded.RS.alpha
          (innerBoundaryDart data hdata pair.firstPath.inner))
        hinnerTarget,
      dartOrbitFace embedded.RS dart ≠
        dartOrbitFace embedded.RS (embedded.RS.alpha dart)) :
    ∃ wall : RadialSectorWallWalk data C first second pair embedded hdata,
      wall.outerArc.IsTrail ∧ wall.innerArc.IsTrail := by
  rcases exists_radialCorePath hdata pair.firstPath with ⟨firstCore⟩
  rcases exists_radialCorePath hdata pair.secondPath with ⟨secondCore⟩
  rcases exists_outerHoleCoreArcWalk_isTrail_of_local_twoSided_avoids_boundaryEdges
      embedded hdata pair.outer_ne houterTarget houterLocal with
    ⟨outerArc, outerTrail, outerFace, _outerLength,
      outerFirst, outerSecond⟩
  rcases exists_innerHoleCoreArcWalk_isTrail_of_local_twoSided_avoids_boundaryEdges
      embedded hdata pair.inner_ne.symm hinnerTarget hinnerLocal with
    ⟨innerArc, innerTrail, innerFace, _innerLength,
      innerSecond, innerFirst⟩
  refine ⟨{
    firstCore := firstCore
    secondCore := secondCore
    outerArc := outerArc
    outerArc_on_outerHole := outerFace
    outerArc_avoids_first := outerFirst
    outerArc_avoids_second := outerSecond
    innerArc := innerArc
    innerArc_on_innerHole := innerFace
    innerArc_avoids_second := innerSecond
    innerArc_avoids_first := innerFirst
  }, outerTrail, innerTrail⟩

end GoertzelV24ClosedWebRadialSectorWallWalk

end Mettapedia.GraphTheory.FourColor
