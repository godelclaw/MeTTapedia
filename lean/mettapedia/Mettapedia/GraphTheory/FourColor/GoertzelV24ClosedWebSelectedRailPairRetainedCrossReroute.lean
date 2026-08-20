import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedRailPairRetainedCrossAppend

/-!
# L1: literal reroutes from retained assembly collisions

A collision which survives loop erasure still carries its exact old/new
cross-track origin.  Cutting the old rail at that face, following the new
rail from the same face, and erasing loops therefore constructs one simple
route with the required outer endpoints.  The construction works for
arbitrary accumulated rail assemblies, not only for one local successor.

This is deliberately a one-route repair.  It does not construct a mutually
disjoint rail pair, choose compatible repairs for two collisions, supply end
caps, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

private theorem support_dropUntil_subset_tail_of_mem_tail_of_isPath
    {F : Type*} [DecidableEq F] {H : SimpleGraph F}
    {start finish face : F}
    (walk : H.Walk start finish) (hpath : walk.IsPath)
    (hface : face ∈ walk.support.tail) :
    (walk.dropUntil face (List.mem_of_mem_tail hface)).support ⊆
      walk.support.tail := by
  cases walk with
  | nil => simp at hface
  | @cons next _ _ hadj tail =>
      have hne : start ≠ face := by
        intro heq
        subst face
        have hnodup := hpath.support_nodup
        simp only [SimpleGraph.Walk.support_cons] at hnodup
        exact (List.nodup_cons.mp hnodup).1 hface
      simpa [SimpleGraph.Walk.dropUntil, hne] using
        tail.support_dropUntil_subset_support hface

/-- One simple route obtained by switching from the old first rail to the
new second rail at an ordered retained collision. -/
structure RetainedFirstToSecondReroute
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish)
    (collisionFace : SelectedFace (web := web)) where
  route : SelectedDualGraph (web := web).Walk firstStart secondFinish
  route_isPath : route.IsPath
  route_support_subset : ∀ face ∈ route.support,
    face ∈ oldAssembly.firstRail.support ∨
      face ∈ newAssembly.secondRail.support.tail

/-- The symmetric ordered repair switches from the old second rail to the
new first rail. -/
structure RetainedSecondToFirstReroute
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish)
    (collisionFace : SelectedFace (web := web)) where
  route : SelectedDualGraph (web := web).Walk secondStart firstFinish
  route_isPath : route.IsPath
  route_support_subset : ∀ face ∈ route.support,
    face ∈ oldAssembly.secondRail.support ∨
      face ∈ newAssembly.firstRail.support.tail

/-- Construct the first-to-second route from the retained collision's exact
origin. -/
private noncomputable def retainedFirstToSecondReroute
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish)
    (collisionFace : SelectedFace (web := web))
    (hold : collisionFace ∈ oldAssembly.firstRail.support)
    (hnew : collisionFace ∈ newAssembly.secondRail.support.tail) :
    RetainedFirstToSecondReroute oldAssembly newAssembly collisionFace := by
  let hnewFull : collisionFace ∈ newAssembly.secondRail.support :=
    List.mem_of_mem_tail hnew
  let raw :=
    (oldAssembly.firstRail.takeUntil collisionFace hold).append
      (newAssembly.secondRail.dropUntil collisionFace hnewFull)
  refine {
    route := raw.bypass
    route_isPath := raw.bypass_isPath
    route_support_subset := ?_
  }
  intro face hface
  have hraw := raw.support_bypass_subset_support hface
  rw [SimpleGraph.Walk.support_append] at hraw
  rcases List.mem_append.mp hraw with hprefix | hsuffix
  · exact Or.inl
      (oldAssembly.firstRail.support_takeUntil_subset_support hold hprefix)
  · exact Or.inr
      (support_dropUntil_subset_tail_of_mem_tail_of_isPath
        newAssembly.secondRail newAssembly.secondRail_isPath hnew
          (List.mem_of_mem_tail hsuffix))

/-- Construct the symmetric second-to-first route. -/
private noncomputable def retainedSecondToFirstReroute
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish)
    (collisionFace : SelectedFace (web := web))
    (hold : collisionFace ∈ oldAssembly.secondRail.support)
    (hnew : collisionFace ∈ newAssembly.firstRail.support.tail) :
    RetainedSecondToFirstReroute oldAssembly newAssembly collisionFace := by
  let hnewFull : collisionFace ∈ newAssembly.firstRail.support :=
    List.mem_of_mem_tail hnew
  let raw :=
    (oldAssembly.secondRail.takeUntil collisionFace hold).append
      (newAssembly.firstRail.dropUntil collisionFace hnewFull)
  refine {
    route := raw.bypass
    route_isPath := raw.bypass_isPath
    route_support_subset := ?_
  }
  intro face hface
  have hraw := raw.support_bypass_subset_support hface
  rw [SimpleGraph.Walk.support_append] at hraw
  rcases List.mem_append.mp hraw with hprefix | hsuffix
  · exact Or.inl
      (oldAssembly.secondRail.support_takeUntil_subset_support hold hprefix)
  · exact Or.inr
      (support_dropUntil_subset_tail_of_mem_tail_of_isPath
        newAssembly.firstRail newAssembly.firstRail_isPath hnew
          (List.mem_of_mem_tail hsuffix))

/-- **L1 retained collision repair.** Every ordered retained collision
constructs one of the two literal crossed simple routes. -/
noncomputable def RetainedBypassCrossCollision.toReroute
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish}
    (collision : RetainedBypassCrossCollision oldAssembly newAssembly) :
    Nonempty (RetainedFirstToSecondReroute oldAssembly newAssembly
      collision.face) ∨
      Nonempty (RetainedSecondToFirstReroute oldAssembly newAssembly
        collision.face) := by
  cases collision.origin with
  | firstSecond hold hnew =>
      exact .inl ⟨retainedFirstToSecondReroute oldAssembly newAssembly
        collision.face hold hnew⟩
  | secondFirst hold hnew =>
      exact .inr ⟨retainedSecondToFirstReroute oldAssembly newAssembly
        collision.face hold hnew⟩

/-- In crossed endpoint order, an old-first/new-first collision constructs
a simple route from the old first start to the new first finish. -/
structure CrossedRetainedFirstReroute
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish)
    (collisionFace : SelectedFace (web := web)) where
  route : SelectedDualGraph (web := web).Walk firstStart firstFinish
  route_isPath : route.IsPath
  route_support_subset : ∀ face ∈ route.support,
    face ∈ oldAssembly.firstRail.support ∨
      face ∈ newAssembly.firstRail.support.tail

/-- The symmetric crossed-order collision constructs an old-second to
new-second route. -/
structure CrossedRetainedSecondReroute
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish)
    (collisionFace : SelectedFace (web := web)) where
  route : SelectedDualGraph (web := web).Walk secondStart secondFinish
  route_isPath : route.IsPath
  route_support_subset : ∀ face ∈ route.support,
    face ∈ oldAssembly.secondRail.support ∨
      face ∈ newAssembly.secondRail.support.tail

/-- Every crossed-order retained collision likewise yields one explicit
simple route.  The route is not asserted disjoint from the other rail. -/
noncomputable def CrossedRetainedBypassCrossCollision.toReroute
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish}
    (collision : CrossedRetainedBypassCrossCollision oldAssembly newAssembly) :
    Nonempty (CrossedRetainedFirstReroute oldAssembly newAssembly
      collision.face) ∨
      Nonempty (CrossedRetainedSecondReroute oldAssembly newAssembly
        collision.face) := by
  cases collision.origin with
  | firstFirst hold hnew =>
      let hnewFull : collision.face ∈ newAssembly.firstRail.support :=
        List.mem_of_mem_tail hnew
      let raw :=
        (oldAssembly.firstRail.takeUntil collision.face hold).append
          (newAssembly.firstRail.dropUntil collision.face hnewFull)
      refine .inl ⟨{
        route := raw.bypass
        route_isPath := raw.bypass_isPath
        route_support_subset := ?_
      }⟩
      intro face hface
      have hraw := raw.support_bypass_subset_support hface
      rw [SimpleGraph.Walk.support_append] at hraw
      rcases List.mem_append.mp hraw with hprefix | hsuffix
      · exact Or.inl
          (oldAssembly.firstRail.support_takeUntil_subset_support hold hprefix)
      · exact Or.inr
          (support_dropUntil_subset_tail_of_mem_tail_of_isPath
            newAssembly.firstRail newAssembly.firstRail_isPath hnew
              (List.mem_of_mem_tail hsuffix))
  | secondSecond hold hnew =>
      let hnewFull : collision.face ∈ newAssembly.secondRail.support :=
        List.mem_of_mem_tail hnew
      let raw :=
        (oldAssembly.secondRail.takeUntil collision.face hold).append
          (newAssembly.secondRail.dropUntil collision.face hnewFull)
      refine .inr ⟨{
        route := raw.bypass
        route_isPath := raw.bypass_isPath
        route_support_subset := ?_
      }⟩
      intro face hface
      have hraw := raw.support_bypass_subset_support hface
      rw [SimpleGraph.Walk.support_append] at hraw
      rcases List.mem_append.mp hraw with hprefix | hsuffix
      · exact Or.inl
          (oldAssembly.secondRail.support_takeUntil_subset_support hold hprefix)
      · exact Or.inr
          (support_dropUntil_subset_tail_of_mem_tail_of_isPath
            newAssembly.secondRail newAssembly.secondRail_isPath hnew
              (List.mem_of_mem_tail hsuffix))

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
