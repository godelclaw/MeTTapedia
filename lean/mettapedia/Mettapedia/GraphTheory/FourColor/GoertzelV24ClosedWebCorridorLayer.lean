import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebMinimalCorridor
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLoop
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathTransversalAppend
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualCycleCrossingInjective
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorInterfaceMatching

/-!
# Source-local layer boundaries in a closed-web corridor

Addendum XXVII(iii) takes profiles on *simple layer boundaries*, not on a
chord wall.  The Cell-3 L1 extraction now gives a boundary-clean hexagonal
corridor with canonical rungs.  This file turns two consecutive rungs into
the first concrete piece of such a boundary: two simple facial-dual paths
through consecutive corridor hexagons with the same two exterior faces.

The construction is performed directly on `ClosedWebAtGoodWord.Instance`.
It does not coerce that source carrier into the separate framed-trail model,
and it retains the proof that every face of the local layer is annular
interior.  Extending these local pieces to the named holes is a later step.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24DualPathTransversal
open GoertzelV24CleanHexCorridor
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorSlab
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrientedHexSlab
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebCorridorLayerEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

/-- The two locally parallel, source-derived paths through consecutive clean
corridor hexagons.  They have the same external endpoint faces, but use
different central corridor faces.  The two interior assertions are what keep
the eventual layer away from both named holes. -/
structure LocalLayerPair
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) where
  firstFace : AmbientFace (Finset.univ : Finset
    (OrbitFace web.annular.RS))
  secondFace : AmbientFace (Finset.univ : Finset
    (OrbitFace web.annular.RS))
  first_ne_second : firstFace ≠ secondFace
  center_ne_nextCenter :
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        leftInterior.center ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior leftInterior hnext).center
  first_adjacent_center :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        firstFace
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          leftInterior.center)
  center_adjacent_second :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          leftInterior.center)
        secondFace
  first_adjacent_nextCenter :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        firstFace
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior leftInterior hnext).center)
  nextCenter_adjacent_second :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior leftInterior hnext).center)
        secondFace
  first_internal : firstFace.1 ∈ web.annular.cellulation.interiorFaces
  second_internal : secondFace.1 ∈ web.annular.cellulation.interiorFaces

namespace LocalLayerPair

/-- The source corridor face through which the first local layer passes. -/
def centerFace
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (_layers : LocalLayerPair web corridor leftInterior hnext) :
    AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)) :=
  corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
    leftInterior.center

/-- The source corridor face through which the next local layer passes. -/
def nextCenterFace
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (_layers : LocalLayerPair web corridor leftInterior hnext) :
    AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)) :=
  corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
    (nextCorridorInterior leftInterior hnext).center

/-- The first local simple layer runs through the left selected corridor
hexagon. -/
noncomputable def firstWalk
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
      layers.firstFace layers.secondFace :=
  SimpleGraph.Walk.cons layers.first_adjacent_center
    (SimpleGraph.Walk.cons layers.center_adjacent_second SimpleGraph.Walk.nil)

/-- The first local layer is simple: its two exterior faces are distinct and
neither is the central corridor face. -/
theorem firstWalk_isPath
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext) :
    layers.firstWalk.IsPath := by
  unfold firstWalk
  apply SimpleGraph.Walk.IsPath.cons
  · apply SimpleGraph.Walk.IsPath.cons
    · exact SimpleGraph.Walk.IsPath.nil
    · simpa using layers.center_adjacent_second.ne
  · simp [layers.first_adjacent_center.ne, layers.first_ne_second]

/-- The second local simple layer runs through the next selected corridor
hexagon, sharing exactly the two exterior faces with the first. -/
noncomputable def secondWalk
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
      layers.firstFace layers.secondFace :=
  SimpleGraph.Walk.cons layers.first_adjacent_nextCenter
    (SimpleGraph.Walk.cons layers.nextCenter_adjacent_second SimpleGraph.Walk.nil)

/-- The second local layer is simple for the same direct incidence reason. -/
theorem secondWalk_isPath
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext) :
    layers.secondWalk.IsPath := by
  unfold secondWalk
  apply SimpleGraph.Walk.IsPath.cons
  · apply SimpleGraph.Walk.IsPath.cons
    · exact SimpleGraph.Walk.IsPath.nil
    · simpa using layers.nextCenter_adjacent_second.ne
  · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, not_or]
    exact ⟨by
      simpa [nextCorridorInterior] using layers.first_adjacent_nextCenter.ne,
      ⟨layers.first_ne_second, by simp⟩⟩

/-- Package the first literal source layer as the generic simple dual
crosscut interface used by the profile machinery.  It is only a local layer,
not yet a claimed hole-to-hole transversal. -/
noncomputable def firstLayer
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext) :
    SimpleDualCrosscut (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      layers.firstFace layers.secondFace where
  walk := layers.firstWalk
  isPath := layers.firstWalk_isPath

/-- The next literal source layer has the same source endpoints. -/
noncomputable def secondLayer
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext) :
    SimpleDualCrosscut (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      layers.firstFace layers.secondFace where
  walk := layers.secondWalk
  isPath := layers.secondWalk_isPath

/-- The two local source layers meet only at their named exterior endpoints.
After deleting those endpoints from the two path supports, the remaining two
corridor faces are distinct.  This is a finite, checked separation fact for
one Cell-3 layer tile, not an assumed Jordan separation. -/
theorem localLayers_tail_disjoint
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext) :
    layers.firstWalk.support.tail.Disjoint
      layers.secondWalk.reverse.support.tail := by
  have hnext_ne_center :
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior leftInterior hnext).center ≠
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          leftInterior.center :=
    layers.center_ne_nextCenter.symm
  have hnext_ne_second :
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior leftInterior hnext).center ≠ layers.secondFace :=
    layers.nextCenter_adjacent_second.ne
  have hfirst_ne_center : layers.firstFace ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        leftInterior.center := layers.first_adjacent_center.ne
  have hnext_ne_center' :
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          leftInterior.outgoing.right ≠
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          leftInterior.center := by
    simpa [nextCorridorInterior] using hnext_ne_center
  have hnext_ne_second' :
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          leftInterior.outgoing.right ≠ layers.secondFace := by
    simpa [nextCorridorInterior] using hnext_ne_second
  simp [firstWalk, secondWalk, hnext_ne_center', hnext_ne_second',
    hfirst_ne_center, layers.first_ne_second]

/-- Following the first local layer and returning through the next corridor
hexagon is the literal dual loop around a Cell-3 corridor tile. -/
noncomputable def localLayerLoop
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
      layers.firstFace layers.firstFace :=
  layers.firstWalk.append layers.secondWalk.reverse

/-- The local Cell-3 layer loop is simple.  Lean checks the four distinct
facial-dual cells directly; no topological assertion is inferred from a
drawing. -/
theorem localLayerLoop_isCycle
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext) :
    layers.localLayerLoop.IsCycle := by
  exact SimpleGraph.Walk.IsPath.isCycle_append layers.firstWalk_isPath
    layers.secondWalk_isPath.reverse layers.localLayers_tail_disjoint
      (Or.inl (by simp [firstWalk]))

/-- Every face of a local Cell-3 layer loop lies in the one-neighbourhood of
one of its two consecutive corridor centres.  The later remote-separation
argument therefore needs only the source geodesic, not a topological drawing
of the annulus. -/
theorem localLayerLoop_support_near_centers
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hface : face ∈ layers.localLayerLoop.support) :
    face = layers.centerFace ∨ face = layers.nextCenterFace ∨
      (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          layers.centerFace face ∨
      (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          layers.nextCenterFace face := by
  rw [localLayerLoop, SimpleGraph.Walk.mem_support_append_iff] at hface
  rcases hface with hfirst | hsecond
  · change face ∈ layers.firstWalk.support at hfirst
    simp only [firstWalk, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_cons] at hfirst
    rcases hfirst with hfirst | hcenter | hsecond
    · subst face
      exact Or.inr (Or.inr (Or.inl layers.first_adjacent_center.symm))
    · subst face
      exact Or.inl rfl
    · rcases hsecond with hsecond | hnone
      · subst face
        exact Or.inr (Or.inr (Or.inl layers.center_adjacent_second))
      · simp at hnone
  · change face ∈ layers.secondWalk.reverse.support at hsecond
    rw [SimpleGraph.Walk.support_reverse] at hsecond
    simp only [secondWalk, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_reverse, List.mem_cons] at hsecond
    rcases hsecond with hfirst | hcenter | hsecond
    · subst face
      exact Or.inr (Or.inr (Or.inr layers.first_adjacent_nextCenter.symm))
    · subst face
      exact Or.inr (Or.inl rfl)
    · rcases hsecond with hsecond | hnone
      · subst face
        exact Or.inr (Or.inr (Or.inr layers.nextCenter_adjacent_second))
      · simp at hnone

/-- Local layer loops based at Cell-3 corridor positions with a three-cell
gap have disjoint facial-dual supports.  The finite corridor skeleton rules
out direct adjacency, and the retained L1 geodesic rules out the only
remaining common-neighbour collision. -/
theorem localLayerLoop_support_disjoint_of_add_three_lt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {rightInterior : CorridorInterior blockLength}
    {hrightNext : rightInterior.center.val + 2 < blockLength}
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (left : LocalLayerPair web corridor leftInterior hnext)
    (right : LocalLayerPair web corridor rightInterior hrightNext)
    (hseparated : leftInterior.center.val + 3 < rightInterior.center.val) :
    left.localLayerLoop.support.Disjoint right.localLayerLoop.support := by
  have h00ne : left.centerFace ≠ right.centerFace := by
    simpa [centerFace] using
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt_ne
        (by
          intro h
          have hvalues := congrArg Fin.val h
          omega)
  have h01ne : left.centerFace ≠ right.nextCenterFace := by
    simpa [centerFace, nextCenterFace] using
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt_ne
        (by
          intro h
          have hvalues := congrArg Fin.val h
          change leftInterior.center.val = rightInterior.center.val + 1 at hvalues
          omega)
  have h10ne : left.nextCenterFace ≠ right.centerFace := by
    simpa [centerFace, nextCenterFace] using
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt_ne
        (by
          intro h
          have hvalues := congrArg Fin.val h
          change leftInterior.center.val + 1 = rightInterior.center.val at hvalues
          omega)
  have h11ne : left.nextCenterFace ≠ right.nextCenterFace := by
    simpa [nextCenterFace] using
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt_ne
        (by
          intro h
          have hvalues := congrArg Fin.val h
          change leftInterior.center.val + 1 = rightInterior.center.val + 1 at hvalues
          omega)
  have h00notadj : ¬ (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
      left.centerFace right.centerFace := by
    simpa [centerFace] using
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).separated_not_adjacent leftInterior.center rightInterior.center (by omega)
  have h01notadj : ¬ (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
      left.centerFace right.nextCenterFace := by
    simpa [centerFace, nextCenterFace] using
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).separated_not_adjacent leftInterior.center
          (nextCorridorInterior rightInterior hrightNext).center (by
            change leftInterior.center.val + 1 < rightInterior.center.val + 1
            omega)
  have h10notadj : ¬ (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
      left.nextCenterFace right.centerFace := by
    simpa [centerFace, nextCenterFace] using
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).separated_not_adjacent
          (nextCorridorInterior leftInterior hnext).center rightInterior.center (by
            change leftInterior.center.val + 1 + 1 < rightInterior.center.val
            omega)
  have h11notadj : ¬ (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
      left.nextCenterFace right.nextCenterFace := by
    simpa [nextCenterFace] using
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).separated_not_adjacent
          (nextCorridorInterior leftInterior hnext).center
          (nextCorridorInterior rightInterior hrightNext).center (by
            change leftInterior.center.val + 1 + 1 < rightInterior.center.val + 1
            omega)
  rw [List.disjoint_left]
  intro face hleft hright
  rcases left.localLayerLoop_support_near_centers face hleft with
    hleft0 | hleft1 | hleft0adj | hleft1adj
  · rcases right.localLayerLoop_support_near_centers face hright with
      hright0 | hright1 | hright0adj | hright1adj
    · exact h00ne (hleft0.symm.trans hright0)
    · exact h01ne (hleft0.symm.trans hright1)
    · subst face
      exact h00notadj hright0adj.symm
    · subst face
      exact h01notadj hright1adj.symm
  · rcases right.localLayerLoop_support_near_centers face hright with
      hright0 | hright1 | hright0adj | hright1adj
    · exact h10ne (hleft1.symm.trans hright0)
    · exact h11ne (hleft1.symm.trans hright1)
    · subst face
      exact h10notadj hright0adj.symm
    · subst face
      exact h11notadj hright1adj.symm
  · rcases right.localLayerLoop_support_near_centers face hright with
      hright0 | hright1 | hright0adj | hright1adj
    · subst face
      exact h00notadj hleft0adj
    · subst face
      exact h01notadj hleft0adj
    · exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
        leftInterior.center rightInterior.center (by omega)
        ⟨face, hleft0adj, hright0adj⟩
    · exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
        leftInterior.center (nextCorridorInterior rightInterior hrightNext).center (by
          change leftInterior.center.val + 2 < rightInterior.center.val + 1
          omega)
        ⟨face, hleft0adj, hright1adj⟩
  · rcases right.localLayerLoop_support_near_centers face hright with
      hright0 | hright1 | hright0adj | hright1adj
    · subst face
      exact h10notadj hleft1adj
    · subst face
      exact h11notadj hleft1adj
    · exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
        (nextCorridorInterior leftInterior hnext).center rightInterior.center (by
          change leftInterior.center.val + 1 + 2 < rightInterior.center.val
          omega)
        ⟨face, hleft1adj, hright0adj⟩
    · exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
        (nextCorridorInterior leftInterior hnext).center
        (nextCorridorInterior rightInterior hrightNext).center (by
          change leftInterior.center.val + 1 + 2 < rightInterior.center.val + 1
          omega)
        ⟨face, hleft1adj, hright1adj⟩

/-- A simple local layer loop crosses every primal edge at most once.  This
is the finite incidence fact that keeps the two sides of the local layer
from quietly reusing a corridor edge. -/
theorem localLayerLoop_crossingEdge_injective
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    Function.Injective
      (dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        layers.localLayerLoop) := by
  exact dualWalkCrossingEdge_injective_of_isCycle_core
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))
    (orbitFace_incidence_le_two web.annular.RS) hunique
    layers.localLayerLoop layers.localLayerLoop_isCycle

/-- The two literal local layers cross disjoint primal-edge supports.  Read
both crossings into their common simple four-cell dual loop; injectivity of
that loop then forbids a shared source edge. -/
theorem localLayers_crossing_disjoint
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    Disjoint (layers.firstLayer.crossingEdges hunique)
      (layers.secondLayer.crossingEdges hunique) := by
  refine Finset.disjoint_left.2 ?_
  intro edge hfirst hsecond
  rcases (layers.firstLayer.mem_crossingEdges_iff hunique edge).1 hfirst with
    ⟨firstStep, hfirstStep⟩
  rcases (layers.secondLayer.mem_crossingEdges_iff hunique edge).1 hsecond with
    ⟨secondStep, hsecondStep⟩
  have hfirstStepLt : firstStep.val < layers.firstWalk.length := by
    simp [firstLayer]
  have hsecondStepLt : secondStep.val < layers.secondWalk.length := by
    simp [secondLayer]
  let firstLoopStep : Fin layers.localLayerLoop.length :=
    ⟨firstStep.val, by
      rw [localLayerLoop, SimpleGraph.Walk.length_append]
      exact hfirstStepLt.trans_le (Nat.le_add_right _ _)⟩
  let secondReverseStep : Fin layers.secondWalk.reverse.length :=
    ⟨layers.secondWalk.length - (secondStep.val + 1), by
      rw [SimpleGraph.Walk.length_reverse]
      omega⟩
  let secondLoopStep : Fin layers.localLayerLoop.length :=
    ⟨layers.firstWalk.length + secondReverseStep.val, by
      rw [localLayerLoop, SimpleGraph.Walk.length_append]
      exact Nat.add_lt_add_left secondReverseStep.isLt layers.firstWalk.length⟩
  have hfirstLoop :
      dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
          layers.localLayerLoop firstLoopStep = edge := by
    calc
      dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
          layers.localLayerLoop firstLoopStep =
        dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
          layers.firstWalk firstStep := by
            simpa [localLayerLoop, firstLoopStep] using
              (dualWalkCrossingEdge_append_left
                (orbitFaceBoundary web.annular.RS)
                (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
                layers.firstWalk layers.secondWalk.reverse firstStep)
      _ = edge := by
        simpa [firstLayer, SimpleDualCrosscut.crossingEdge] using hfirstStep
  have hsecondLoop :
      dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
          layers.localLayerLoop secondLoopStep = edge := by
    calc
      dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
          layers.localLayerLoop secondLoopStep =
        dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
          layers.secondWalk.reverse secondReverseStep := by
            simpa [localLayerLoop, secondLoopStep] using
              (dualWalkCrossingEdge_append_right
                (orbitFaceBoundary web.annular.RS)
                (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
                layers.firstWalk layers.secondWalk.reverse secondReverseStep)
      _ = dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
          layers.secondWalk secondStep := by
            simpa [secondReverseStep] using
              (dualWalkCrossingEdge_reverse
                (orbitFaceBoundary web.annular.RS)
                (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
                layers.secondWalk secondStep)
      _ = edge := by
        simpa [secondLayer, SimpleDualCrosscut.crossingEdge] using hsecondStep
  have hpositions := layers.localLayerLoop_crossingEdge_injective hunique
    (hfirstLoop.trans hsecondLoop.symm)
  have hvalues := congrArg Fin.val hpositions
  have hfirstLt : firstLoopStep.val < layers.firstWalk.length := hfirstStepLt
  have hsecondGe : layers.firstWalk.length ≤ secondLoopStep.val := by
    simp [secondLoopStep]
  omega

/-- The local Cell-3 tile now has exactly the finite interface shape used by
the open splice: two equal-width simple paths whose crossed primal edges are
disjoint.  This remains a local layer pair; it is not yet claimed to be the
full annular transversal pair. -/
noncomputable def alignedLocalLayerPair
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    AlignedSimpleDualCrosscuts (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      layers.firstFace layers.secondFace hunique where
  left := layers.firstLayer
  right := layers.secondLayer
  length_eq := by
    simp [firstLayer, secondLayer, firstWalk, secondWalk]
  crossing_disjoint := layers.localLayers_crossing_disjoint hunique

/-- The local source layers are separated as facial-dual paths except at
their two named endpoints.  Their closed composite is therefore a genuine
source-derived layer cycle, ready for the later annular formation step. -/
noncomputable def separatedLocalLayerPair
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    SeparatedAlignedSimpleDualCrosscuts (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      layers.firstFace layers.secondFace hunique where
  left := layers.firstLayer
  right := layers.secondLayer
  length_eq := by
    simp [firstLayer, secondLayer, firstWalk, secondWalk]
  crossing_disjoint := layers.localLayers_crossing_disjoint hunique
  transverse_disjoint := layers.localLayers_tail_disjoint
  nondegenerate := Or.inl (by
    simp [firstLayer, firstWalk])

/-- The generic dual loop of the packaged local pair is the checked layer
cycle constructed above. -/
theorem separatedLocalLayerPair_dualLoop_isCycle
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    (layers.separatedLocalLayerPair hunique).dualLoop.IsCycle := by
  exact (layers.separatedLocalLayerPair hunique).dualLoop_isCycle

end LocalLayerPair

/-- Consecutive source-selected Cell-3 hexagons construct a pair of simple
local layer boundaries.  This is the local, source-faithful replacement for
assuming that a chord cycle itself was already a transversal. -/
theorem exists_localLayerPair_of_minimal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      web.annular.cellulation.rotation)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    Nonempty (LocalLayerPair web corridor leftInterior hnext) := by
  let clean := corridor.toCleanOrbitHexCorridorSkeleton
  let htwoSided := web.facesTwoSided_of_minimal minimal
  let hunique := web.pairwiseUniqueSharedInteriorEdges_of_minimal minimal
  let leftPlacement := Classical.choice
    (exists_internalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton htwoSided hunique leftInterior)
  let rightInterior := nextCorridorInterior leftInterior hnext
  let rightPlacement := Classical.choice
    (exists_internalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton htwoSided hunique rightInterior)
  rcases consecutiveSlabInterfacesMatch clean minimal.spherical.cubic
      minimal.vertexRotationCyclic htwoSided hunique leftInterior hnext
      leftPlacement rightPlacement with
    ⟨leftBefore, leftAfter, rightBefore, rightAfter,
      hleftDistinct, _hrightDistinct, hbeforeMatch, hafterMatch⟩
  let firstFace := placementSideNeighbor clean htwoSided hunique
    leftPlacement leftBefore
  let secondFace := placementSideNeighbor clean htwoSided hunique
    leftPlacement leftAfter
  refine ⟨{
    firstFace := firstFace
    secondFace := secondFace
    first_ne_second := by
      intro hfaces
      apply hleftDistinct
      apply placementSideNeighbor_injective clean htwoSided hunique leftPlacement
      simpa [firstFace, secondFace] using hfaces
    center_ne_nextCenter := by
      apply clean.toOrbitHexCorridorSkeleton.faceAt_ne
      intro hindices
      have hvalues := congrArg Fin.val hindices
      change leftInterior.center.val = leftInterior.center.val + 1 at hvalues
      omega
    first_adjacent_center := by
      simpa [firstFace, placementSideNeighbor] using
        (internalSideNeighbor_adjacent clean htwoSided hunique leftInterior
          (placementSideEdge htwoSided leftPlacement leftBefore)).symm
    center_adjacent_second := by
      simpa [secondFace, placementSideNeighbor] using
        internalSideNeighbor_adjacent clean htwoSided hunique leftInterior
          (placementSideEdge htwoSided leftPlacement leftAfter)
    first_adjacent_nextCenter := by
      rw [show firstFace = placementSideNeighbor clean htwoSided hunique
        rightPlacement rightBefore by simpa [firstFace] using hbeforeMatch]
      simpa [rightInterior, placementSideNeighbor] using
        (internalSideNeighbor_adjacent clean htwoSided hunique rightInterior
          (placementSideEdge htwoSided rightPlacement rightBefore)).symm
    nextCenter_adjacent_second := by
      rw [show secondFace = placementSideNeighbor clean htwoSided hunique
        rightPlacement rightAfter by simpa [secondFace] using hafterMatch]
      simpa [rightInterior, placementSideNeighbor] using
        internalSideNeighbor_adjacent clean htwoSided hunique rightInterior
          (placementSideEdge htwoSided rightPlacement rightAfter)
    first_internal := by
      apply corridor.neighbor_internal leftInterior.center firstFace
      simpa [firstFace, placementSideNeighbor] using
        internalSideNeighbor_adjacent clean htwoSided hunique leftInterior
          (placementSideEdge htwoSided leftPlacement leftBefore)
    second_internal := by
      apply corridor.neighbor_internal leftInterior.center secondFace
      simpa [secondFace, placementSideNeighbor] using
        internalSideNeighbor_adjacent clean htwoSided hunique leftInterior
          (placementSideEdge htwoSided leftPlacement leftAfter)
  }⟩

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
