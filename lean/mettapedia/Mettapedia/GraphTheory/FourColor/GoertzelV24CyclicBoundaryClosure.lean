import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicBoundaryAlternatingTrail

/-!
# Closing a trail across a cyclic bond boundary

Two paths confined to complementary vertex shores can be joined by the two
boundary edges at their endpoints.  This file proves that the result is a
closed trail and that it meets the cyclic boundary at exactly those two
coordinates.  The statement is independent of the boundary width.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CyclicBoundaryClosure

open GoertzelV24CyclicBondBoundary
open GoertzelV24RotationCutDartDecomposition
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Vertices on one side of a predicate. -/
abbrev SideVertex (keep : V → Prop) := {vertex : V // keep vertex}

/-- The graph induced by one vertex-side predicate. -/
abbrev SideGraph (G : SimpleGraph V) (keep : V → Prop) :
    SimpleGraph (SideVertex keep) :=
  G.induce {vertex | keep vertex}

/-- Inclusion of an induced vertex side into the ambient graph. -/
abbrev sideGraphHom (G : SimpleGraph V) (keep : V → Prop) :
    SideGraph G keep →g G where
  toFun := Subtype.val
  map_rel' := fun {_ _} hedge ↦ hedge

/-- Map a walk in an induced vertex side to the ambient graph. -/
def sideWalkToAmbient (G : SimpleGraph V) (keep : V → Prop)
    {left right : SideVertex keep}
    (walk : (SideGraph G keep).Walk left right) :
    G.Walk left.1 right.1 :=
  (walk.map (sideGraphHom G keep)).copy rfl rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Injective side inclusion preserves pathhood. -/
theorem sideWalkToAmbient_isPath
    (keep : V → Prop) {left right : SideVertex keep}
    {walk : (SideGraph G keep).Walk left right}
    (hwalk : walk.IsPath) :
    (sideWalkToAmbient G keep walk).IsPath := by
  simpa [sideWalkToAmbient] using
    Walk.map_isPath_of_injective Subtype.val_injective hwalk

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Injective side inclusion preserves trailhood. -/
theorem sideWalkToAmbient_isTrail
    (keep : V → Prop) {left right : SideVertex keep}
    {walk : (SideGraph G keep).Walk left right}
    (hwalk : walk.IsTrail) :
    (sideWalkToAmbient G keep walk).IsTrail := by
  simpa [sideWalkToAmbient] using
    Walk.map_isTrail_of_injective Subtype.val_injective hwalk

/-- The retained endpoint of a cyclic boundary coordinate. -/
def retainedPort (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (port : Fin data.length) : SideVertex keep :=
  ⟨graphData.toRotationSystem.vertOf (data.order port).1.1,
    (data.order port).1.2⟩

/-- The opposite endpoint of a cyclic boundary coordinate. -/
def deletedPort (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (port : Fin data.length) : SideVertex (fun vertex ↦ ¬keep vertex) :=
  ⟨graphData.toRotationSystem.vertOf
      (graphData.toRotationSystem.alpha (data.order port).1.1),
    (data.order port).2⟩

/-- The ambient edge underlying one cyclic boundary coordinate. -/
def boundaryEdge (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (port : Fin data.length) : Sym2 V :=
  (graphData.toRotationSystem.edgeOf (data.order port).1.1).1

/-- The one-edge walk from the retained endpoint of a boundary coordinate
to its deleted endpoint. -/
def boundaryWalk (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (port : Fin data.length) :
    G.Walk (retainedPort graphData keep data port).1
      (deletedPort graphData keep data port).1 :=
  (data.order port).1.1.adj.toWalk

@[simp]
theorem boundaryWalk_edges (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (port : Fin data.length) :
    (boundaryWalk graphData keep data port).edges =
      [boundaryEdge graphData keep data port] := by
  rfl

/-- Distinct cyclic coordinates name distinct ambient edges. -/
theorem boundaryEdge_injective
    (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep) :
    Function.Injective (boundaryEdge graphData keep data) := by
  intro first second hedge
  apply data.order.injective
  apply boundaryDart_eq_of_edgeOf_eq
  apply Subtype.ext
  exact hedge

/-- Every recorded boundary coordinate is an edge crossing the vertex-side
predicate. -/
theorem boundaryEdge_crosses
    (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (port : Fin data.length) :
    EdgeCrossesVertexSide G keep
      (graphData.toRotationSystem.edgeOf (data.order port).1.1) := by
  let dart : G.Dart := (data.order port).1.1
  change EdgeCrossesVertexSide G keep
    (⟨dart.edge, dart.edge_mem⟩ : G.edgeSet)
  refine ⟨dart.fst, dart.snd, ?_, ?_, ?_, ?_⟩
  · change dart.fst ∈ s(dart.fst, dart.snd)
    simp
  · change dart.snd ∈ s(dart.fst, dart.snd)
    simp
  · simpa [dart, Data.toRotationSystem_vertOf] using
      (data.order port).1.2
  · simpa [dart, Data.toRotationSystem_vertOf,
      Data.toRotationSystem_alpha] using (data.order port).2

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An edge crossing a side predicate cannot occur in a walk confined to
that induced side. -/
theorem crossingEdge_not_mem_sideWalkToAmbient_edges
    (keep : V → Prop) {edge : G.edgeSet}
    (hcross : EdgeCrossesVertexSide G keep edge)
    {left right : SideVertex keep}
    (walk : (SideGraph G keep).Walk left right) :
    edge.1 ∉ (sideWalkToAmbient G keep walk).edges := by
  intro hmem
  simp only [sideWalkToAmbient, Walk.edges_copy, Walk.edges_map] at hmem
  rcases List.mem_map.mp hmem with
    ⟨sideEdge, _hsideEdge, hedgeEq⟩
  rcases hcross with
    ⟨inside, outside, hinside, houtside, hinsideSide, houtsideSide⟩
  have everyMappedEndpoint : ∀ vertex : V,
      vertex ∈ sideEdge.map (sideGraphHom G keep) → keep vertex := by
    intro vertex hvertex
    rcases Sym2.mem_map.mp hvertex with
      ⟨sideVertex, _hsideVertex, rfl⟩
    exact sideVertex.2
  apply houtsideSide
  apply everyMappedEndpoint outside
  rw [hedgeEq]
  exact houtside

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Walks confined to complementary induced sides have disjoint ambient
edge lists. -/
theorem sideWalkToAmbient_edges_disjoint_compl
    (keep : V → Prop)
    {insideLeft insideRight : SideVertex keep}
    (insideWalk : (SideGraph G keep).Walk insideLeft insideRight)
    {outsideLeft outsideRight : SideVertex (fun vertex ↦ ¬keep vertex)}
    (outsideWalk : (SideGraph G (fun vertex ↦ ¬keep vertex)).Walk
      outsideLeft outsideRight) :
    (sideWalkToAmbient G keep insideWalk).edges.Disjoint
      (sideWalkToAmbient G (fun vertex ↦ ¬keep vertex) outsideWalk).edges := by
  rw [List.disjoint_left]
  intro edge hinside houtside
  simp only [sideWalkToAmbient, Walk.edges_copy, Walk.edges_map] at hinside houtside
  rcases List.mem_map.mp hinside with
    ⟨insideEdge, _hinsideEdge, hinsideEq⟩
  rcases List.mem_map.mp houtside with
    ⟨outsideEdge, _houtsideEdge, houtsideEq⟩
  induction insideEdge using Sym2.inductionOn with
  | _ insideFirst insideSecond =>
      have hfirstMem : insideFirst.1 ∈
          s(insideFirst, insideSecond).map (sideGraphHom G keep) := by
        exact Sym2.mem_map.mpr ⟨insideFirst, by simp, rfl⟩
      have hfirstOutside : insideFirst.1 ∈
          outsideEdge.map (sideGraphHom G (fun vertex ↦ ¬keep vertex)) := by
        rw [hinsideEq, ← houtsideEq] at hfirstMem
        exact hfirstMem
      rcases Sym2.mem_map.mp hfirstOutside with
        ⟨outsideVertex, _houtsideVertex, hvalue⟩
      apply outsideVertex.2
      change outsideVertex.1 = insideFirst.1 at hvalue
      rw [hvalue]
      exact insideFirst.2

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Edge-disjoint walks within one induced shore remain edge-disjoint after
inclusion into the ambient graph. -/
theorem sideWalkToAmbient_edges_disjoint_of_disjoint
    (keep : V → Prop)
    {firstLeft firstRight secondLeft secondRight : SideVertex keep}
    (first : (SideGraph G keep).Walk firstLeft firstRight)
    (second : (SideGraph G keep).Walk secondLeft secondRight)
    (hdisjoint : first.edges.Disjoint second.edges) :
    (sideWalkToAmbient G keep first).edges.Disjoint
      (sideWalkToAmbient G keep second).edges := by
  simp only [sideWalkToAmbient, Walk.edges_copy, Walk.edges_map]
  exact hdisjoint.map (Sym2.map.injective Subtype.val_injective)

/-- Return from one retained boundary port to another through the opposite
shore. -/
def boundaryReturn
    (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (first second : Fin data.length)
    (outsidePath : (SideGraph G (fun vertex ↦ ¬keep vertex)).Walk
      (deletedPort graphData keep data second)
      (deletedPort graphData keep data first)) :
    G.Walk (retainedPort graphData keep data second).1
      (retainedPort graphData keep data first).1 :=
  (boundaryWalk graphData keep data second).append
    ((sideWalkToAmbient G (fun vertex ↦ ¬keep vertex) outsidePath).append
      (boundaryWalk graphData keep data first).reverse)

/-- The opposite-shore return is a trail. -/
theorem boundaryReturn_isTrail
    (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (first second : Fin data.length) (hne : first ≠ second)
    (outsidePath : (SideGraph G (fun vertex ↦ ¬keep vertex)).Walk
      (deletedPort graphData keep data second)
      (deletedPort graphData keep data first))
    (houtsidePath : outsidePath.IsTrail) :
    (boundaryReturn graphData keep data first second outsidePath).IsTrail := by
  let edgeFirst := graphData.toRotationSystem.edgeOf (data.order first).1.1
  let edgeSecond := graphData.toRotationSystem.edgeOf (data.order second).1.1
  have hfirstCross : EdgeCrossesVertexSide G (fun vertex ↦ ¬keep vertex)
      edgeFirst := (edgeCrossesVertexSide_compl G keep edgeFirst).2
        (boundaryEdge_crosses graphData keep data first)
  have hsecondCross : EdgeCrossesVertexSide G (fun vertex ↦ ¬keep vertex)
      edgeSecond := (edgeCrossesVertexSide_compl G keep edgeSecond).2
        (boundaryEdge_crosses graphData keep data second)
  have hfirstNotPath : edgeFirst.1 ∉
      (sideWalkToAmbient G (fun vertex ↦ ¬keep vertex) outsidePath).edges :=
    crossingEdge_not_mem_sideWalkToAmbient_edges _ hfirstCross outsidePath
  have hsecondNotPath : edgeSecond.1 ∉
      (sideWalkToAmbient G (fun vertex ↦ ¬keep vertex) outsidePath).edges :=
    crossingEdge_not_mem_sideWalkToAmbient_edges _ hsecondCross outsidePath
  have hsecondFirst : edgeSecond.1 ≠ edgeFirst.1 := by
    intro hedge
    have hport := boundaryEdge_injective graphData keep data hedge
    exact hne hport.symm
  change ((boundaryWalk graphData keep data second).append
    ((sideWalkToAmbient G (fun vertex ↦ ¬keep vertex) outsidePath).append
      (boundaryWalk graphData keep data first).reverse)).IsTrail
  rw [Walk.isTrail_append]
  refine ⟨?_, ?_, ?_⟩
  · exact (Walk.IsPath.of_adj (data.order second).1.1.adj).isTrail
  · rw [Walk.isTrail_append]
    refine ⟨sideWalkToAmbient_isTrail _ houtsidePath, ?_, ?_⟩
    · exact (Walk.IsPath.of_adj (data.order first).1.1.adj).reverse.isTrail
    · rw [List.disjoint_left]
      intro edge hedge hboundary
      simp only [boundaryWalk_edges, Walk.edges_reverse,
        List.reverse_singleton, List.mem_singleton] at hboundary
      subst edge
      exact hfirstNotPath hedge
  · rw [List.disjoint_left]
    intro edge hsecond hright
    simp only [boundaryWalk_edges, List.mem_singleton] at hsecond
    subst edge
    rw [Walk.edges_append] at hright
    simp only [boundaryWalk_edges, Walk.edges_reverse,
      List.reverse_singleton, List.mem_append, List.mem_singleton] at hright
    exact hright.elim hsecondNotPath hsecondFirst

/-- The opposite-shore return contains a boundary edge exactly at its two
endpoint coordinates. -/
theorem boundaryEdge_mem_boundaryReturn_edges_iff
    (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (first second : Fin data.length)
    (outsidePath : (SideGraph G (fun vertex ↦ ¬keep vertex)).Walk
      (deletedPort graphData keep data second)
      (deletedPort graphData keep data first))
    (port : Fin data.length) :
    boundaryEdge graphData keep data port ∈
        (boundaryReturn graphData keep data first second outsidePath).edges ↔
      port = first ∨ port = second := by
  let edge := graphData.toRotationSystem.edgeOf (data.order port).1.1
  have hedgeCross : EdgeCrossesVertexSide G (fun vertex ↦ ¬keep vertex)
      edge := (edgeCrossesVertexSide_compl G keep edge).2
        (boundaryEdge_crosses graphData keep data port)
  have hedgeNotPath : edge.1 ∉
      (sideWalkToAmbient G (fun vertex ↦ ¬keep vertex) outsidePath).edges :=
    crossingEdge_not_mem_sideWalkToAmbient_edges _ hedgeCross outsidePath
  change edge.1 ∈ (boundaryReturn graphData keep data first second outsidePath).edges ↔ _
  rw [boundaryReturn, Walk.edges_append, Walk.edges_append]
  simp only [boundaryWalk_edges, Walk.edges_reverse,
    List.reverse_singleton, List.mem_append, List.mem_singleton]
  constructor
  · rintro (hsecond | hpath | hfirst)
    · exact Or.inr (boundaryEdge_injective graphData keep data hsecond)
    · exact False.elim (hedgeNotPath hpath)
    · exact Or.inl (boundaryEdge_injective graphData keep data hfirst)
  · rintro (rfl | rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl

/-- Close a path in the retained shore through a path in the complementary
shore. -/
def boundaryClosure
    (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (first second : Fin data.length)
    (insidePath : (SideGraph G keep).Walk
      (retainedPort graphData keep data first)
      (retainedPort graphData keep data second))
    (outsidePath : (SideGraph G (fun vertex ↦ ¬keep vertex)).Walk
      (deletedPort graphData keep data second)
      (deletedPort graphData keep data first)) :
    G.Walk (retainedPort graphData keep data first).1
      (retainedPort graphData keep data first).1 :=
  (sideWalkToAmbient G keep insidePath).append
    (boundaryReturn graphData keep data first second outsidePath)

/-- The two-shore boundary closure is a closed trail. -/
theorem boundaryClosure_isTrail
    (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (first second : Fin data.length) (hne : first ≠ second)
    (insidePath : (SideGraph G keep).Walk
      (retainedPort graphData keep data first)
      (retainedPort graphData keep data second))
    (outsidePath : (SideGraph G (fun vertex ↦ ¬keep vertex)).Walk
      (deletedPort graphData keep data second)
      (deletedPort graphData keep data first))
    (hinsidePath : insidePath.IsTrail)
    (houtsidePath : outsidePath.IsTrail) :
    (boundaryClosure graphData keep data first second
      insidePath outsidePath).IsTrail := by
  let edgeFirst := graphData.toRotationSystem.edgeOf (data.order first).1.1
  let edgeSecond := graphData.toRotationSystem.edgeOf (data.order second).1.1
  have hfirstNotInside : edgeFirst.1 ∉
      (sideWalkToAmbient G keep insidePath).edges :=
    crossingEdge_not_mem_sideWalkToAmbient_edges _
      (boundaryEdge_crosses graphData keep data first) insidePath
  have hsecondNotInside : edgeSecond.1 ∉
      (sideWalkToAmbient G keep insidePath).edges :=
    crossingEdge_not_mem_sideWalkToAmbient_edges _
      (boundaryEdge_crosses graphData keep data second) insidePath
  have hsides := sideWalkToAmbient_edges_disjoint_compl
    (G := G) keep insidePath outsidePath
  change ((sideWalkToAmbient G keep insidePath).append
    (boundaryReturn graphData keep data first second outsidePath)).IsTrail
  rw [Walk.isTrail_append]
  refine ⟨sideWalkToAmbient_isTrail _ hinsidePath,
    boundaryReturn_isTrail graphData keep data first second hne
      outsidePath houtsidePath, ?_⟩
  rw [List.disjoint_left]
  intro edge hinside hreturn
  rw [boundaryReturn, Walk.edges_append, Walk.edges_append] at hreturn
  simp only [boundaryWalk_edges, Walk.edges_reverse,
    List.reverse_singleton, List.mem_append, List.mem_singleton] at hreturn
  rcases hreturn with hsecond | houtside | hfirst
  · subst edge
    exact hsecondNotInside hinside
  · exact (List.disjoint_left.mp hsides) hinside houtside
  · subst edge
    exact hfirstNotInside hinside

/-- The closed trail meets the cyclic boundary exactly at its endpoint
coordinates. -/
theorem boundaryEdge_mem_boundaryClosure_edges_iff
    (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (first second : Fin data.length)
    (insidePath : (SideGraph G keep).Walk
      (retainedPort graphData keep data first)
      (retainedPort graphData keep data second))
    (outsidePath : (SideGraph G (fun vertex ↦ ¬keep vertex)).Walk
      (deletedPort graphData keep data second)
      (deletedPort graphData keep data first))
    (port : Fin data.length) :
    boundaryEdge graphData keep data port ∈
        (boundaryClosure graphData keep data first second
          insidePath outsidePath).edges ↔
      port = first ∨ port = second := by
  let edge := graphData.toRotationSystem.edgeOf (data.order port).1.1
  have hedgeNotInside : edge.1 ∉
      (sideWalkToAmbient G keep insidePath).edges :=
    crossingEdge_not_mem_sideWalkToAmbient_edges _
      (boundaryEdge_crosses graphData keep data port) insidePath
  change edge.1 ∈ (boundaryClosure graphData keep data first second
    insidePath outsidePath).edges ↔ _
  rw [boundaryClosure, Walk.edges_append]
  constructor
  · rw [List.mem_append]
    rintro (hinside | hreturn)
    · exact False.elim (hedgeNotInside hinside)
    · exact (boundaryEdge_mem_boundaryReturn_edges_iff
        graphData keep data first second outsidePath port).1 hreturn
  · intro hport
    apply List.mem_append_right
    exact (boundaryEdge_mem_boundaryReturn_edges_iff
      graphData keep data first second outsidePath port).2 hport

/-- A third walk in the retained shore which is edge-disjoint from the
retained part of a boundary closure is disjoint from the entire closed
trail. -/
theorem sideWalkToAmbient_edges_disjoint_boundaryClosure
    (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (first second : Fin data.length)
    (insidePath : (SideGraph G keep).Walk
      (retainedPort graphData keep data first)
      (retainedPort graphData keep data second))
    (outsidePath : (SideGraph G (fun vertex ↦ ¬keep vertex)).Walk
      (deletedPort graphData keep data second)
      (deletedPort graphData keep data first))
    {routeLeft routeRight : SideVertex keep}
    (route : (SideGraph G keep).Walk routeLeft routeRight)
    (hrouteInside : route.edges.Disjoint insidePath.edges) :
    (sideWalkToAmbient G keep route).edges.Disjoint
      (boundaryClosure graphData keep data first second
        insidePath outsidePath).edges := by
  have hinside := sideWalkToAmbient_edges_disjoint_of_disjoint
    (G := G) keep route insidePath hrouteInside
  have houtside := sideWalkToAmbient_edges_disjoint_compl
    (G := G) keep route outsidePath
  let edgeFirst := graphData.toRotationSystem.edgeOf (data.order first).1.1
  let edgeSecond := graphData.toRotationSystem.edgeOf (data.order second).1.1
  have hfirstNotRoute : edgeFirst.1 ∉
      (sideWalkToAmbient G keep route).edges :=
    crossingEdge_not_mem_sideWalkToAmbient_edges _
      (boundaryEdge_crosses graphData keep data first) route
  have hsecondNotRoute : edgeSecond.1 ∉
      (sideWalkToAmbient G keep route).edges :=
    crossingEdge_not_mem_sideWalkToAmbient_edges _
      (boundaryEdge_crosses graphData keep data second) route
  rw [List.disjoint_left]
  intro edge hroute hclosure
  rw [boundaryClosure, Walk.edges_append, boundaryReturn,
    Walk.edges_append, Walk.edges_append] at hclosure
  simp only [boundaryWalk_edges, Walk.edges_reverse,
    List.reverse_singleton, List.mem_append, List.mem_singleton] at hclosure
  rcases hclosure with hinsideEdge | hsecond | houtsideEdge | hfirst
  · exact (List.disjoint_left.mp hinside) hroute hinsideEdge
  · subst edge
    exact hsecondNotRoute hroute
  · exact (List.disjoint_left.mp houtside) hroute houtsideEdge
  · subst edge
    exact hfirstNotRoute hroute

end

end GoertzelV24CyclicBoundaryClosure

end Mettapedia.GraphTheory.FourColor
