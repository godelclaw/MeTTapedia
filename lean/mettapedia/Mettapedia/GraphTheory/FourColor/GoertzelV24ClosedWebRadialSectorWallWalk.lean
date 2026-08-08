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
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24ClosedWebHoleCoreArcWalk
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

end GoertzelV24ClosedWebRadialSectorWallWalk

end Mettapedia.GraphTheory.FourColor
