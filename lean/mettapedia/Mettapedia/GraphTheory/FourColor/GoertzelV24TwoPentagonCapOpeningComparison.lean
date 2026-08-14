import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapOpeningBoundary

/-!
# Carrier comparison for the two pentagon openings

For a separated pair of pentagon caps, the supplied toolchain keeps the ten
cap vertices and deletes their cycle edges.  The manuscript instead deletes
the ten cap vertices and creates one fresh stub per outward dart.  The exact
port enumeration proves that these are two presentations of the same intended
open boundary.  This file gives the canonical vertex equivalence and proves
that it is a graph isomorphism: old vertices keep their names and a fresh port
becomes its deleted cap endpoint.  The isomorphism preserves both ordered
five-stub families definitionally.

It deliberately does not identify the dependent face-fragment carriers or
their cyclic orders.  A simple-graph isomorphism alone is not an annular
rotation embedding.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoPentagonCapOpening

open SimpleGraph
open GoertzelV24DeletedRegionSlitGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace PentagonCapPair

/-- The carrier comparison for the two-cap opening.  A manuscript-side fresh
stub receives the name of the deleted cap vertex at the end of its outward
dart; the exact port classification makes this a bijection. -/
def slitToOpenVertexEquiv (caps : PentagonCapPair G) :
    DeletedRegionSlitVertex G caps.deletedVertexSupport ≃ V :=
  Equiv.ofBijective
    (fun vertex => match vertex with
      | Sum.inl oldVertex => oldVertex.1
      | Sum.inr boundaryPort => boundaryPort.dart.snd)
    ⟨by
      intro first second heq
      rcases first with oldFirst | portFirst <;>
        rcases second with oldSecond | portSecond
      · exact congrArg Sum.inl (Subtype.ext heq)
      · exact False.elim (oldFirst.2 (by simpa [← heq] using portSecond.removed))
      · exact False.elim (oldSecond.2 (by simpa [heq] using portFirst.removed))
      · rcases caps.boundaryPort_eq_inner_or_outer portFirst with hfirst | hfirst
        · rcases hfirst with ⟨firstStep, hfirstStep⟩
          subst portFirst
          rcases caps.boundaryPort_eq_inner_or_outer portSecond with hsecond | hsecond
          · rcases hsecond with ⟨secondStep, hsecondStep⟩
            subst portSecond
            have hsteps : firstStep = secondStep := caps.inner.vertex.injective (by
              simpa using heq)
            cases hsteps
            rfl
          · rcases hsecond with ⟨secondStep, hsecondStep⟩
            subst portSecond
            exact False.elim (caps.inner_vertex_not_mem_outerSupport firstStep
              ((caps.outer.mem_vertexSupport_iff _).mpr ⟨secondStep, by
                simpa using heq.symm⟩))
        · rcases hfirst with ⟨firstStep, hfirstStep⟩
          subst portFirst
          rcases caps.boundaryPort_eq_inner_or_outer portSecond with hsecond | hsecond
          · rcases hsecond with ⟨secondStep, hsecondStep⟩
            subst portSecond
            exact False.elim (caps.inner_vertex_not_mem_outerSupport secondStep
              ((caps.outer.mem_vertexSupport_iff _).mpr ⟨firstStep, by
                simpa using heq⟩))
          · rcases hsecond with ⟨secondStep, hsecondStep⟩
            subst portSecond
            have hsteps : firstStep = secondStep := caps.outer.vertex.injective (by
              simpa using heq)
            cases hsteps
            rfl,
      by
        intro vertex
        by_cases hdeleted : vertex ∈ caps.deletedVertexSupport
        · have hmember : vertex ∈ caps.inner.vertexSupport ∪ caps.outer.vertexSupport := by
            simpa only [deletedVertexSupport] using hdeleted
          rcases Finset.mem_union.mp hmember with hinner | houter
          · rcases (caps.inner.mem_vertexSupport_iff vertex).mp hinner with ⟨step, hstep⟩
            refine ⟨Sum.inr (caps.innerBoundaryPort step), ?_⟩
            simpa [hstep]
          · rcases (caps.outer.mem_vertexSupport_iff vertex).mp houter with ⟨step, hstep⟩
            refine ⟨Sum.inr (caps.outerBoundaryPort step), ?_⟩
            simpa [hstep]
        · exact ⟨Sum.inl ⟨vertex, hdeleted⟩, rfl⟩⟩

@[simp] theorem slitToOpenVertexEquiv_old (caps : PentagonCapPair G)
    (vertex : {vertex // vertex ∉ caps.deletedVertexSupport}) :
    caps.slitToOpenVertexEquiv (Sum.inl vertex) = vertex.1 :=
  rfl

@[simp] theorem slitToOpenVertexEquiv_innerStub (caps : PentagonCapPair G)
    (step : Fin 5) :
    caps.slitToOpenVertexEquiv (Sum.inr (caps.innerBoundaryPort step)) =
      caps.inner.vertex step :=
  rfl

@[simp] theorem slitToOpenVertexEquiv_outerStub (caps : PentagonCapPair G)
    (step : Fin 5) :
    caps.slitToOpenVertexEquiv (Sum.inr (caps.outerBoundaryPort step)) =
      caps.outer.vertex step :=
  rfl

/-- Away from the two deleted cap supports, the toolchain opening has exactly
the ambient adjacency.  This is the old--old case needed for the eventual
opening graph isomorphism. -/
theorem openGraph_adj_iff_of_not_mem_deletedVertexSupport
    (caps : PentagonCapPair G) {left right : V}
    (hleft : left ∉ caps.deletedVertexSupport) :
    caps.openGraph.Adj left right ↔ G.Adj left right := by
  have hleftInner : left ∉ caps.inner.vertexSupport := by
    intro hmem
    exact hleft (by
      change left ∈ caps.inner.vertexSupport ∪ caps.outer.vertexSupport
      exact Finset.mem_union_left _ hmem)
  have hleftOuter : left ∉ caps.outer.vertexSupport := by
    intro hmem
    exact hleft (by
      change left ∈ caps.inner.vertexSupport ∪ caps.outer.vertexSupport
      exact Finset.mem_union_right _ hmem)
  have hneighbors := caps.openGraph_neighborFinset_eq_of_not_mem_supports
    hleftInner hleftOuter
  have hmembership := congrArg (fun neighbors => right ∈ neighbors) hneighbors
  exact Iff.of_eq (by
    simpa only [SimpleGraph.mem_neighborFinset] using hmembership)

theorem openGraph_adj_old_innerVertex_iff (caps : PentagonCapPair G)
    (step : Fin 5) (outside : {vertex // vertex ∉ caps.deletedVertexSupport}) :
    caps.openGraph.Adj outside.1 (caps.inner.vertex step) ↔
      outside.1 = caps.inner.spokeOuter step := by
  constructor
  · exact caps.eq_inner_spokeOuter_of_openGraph_adj_vertex step
  · intro houtside
    simpa [houtside] using caps.openGraph_adj_spokeOuter_innerVertex step

theorem openGraph_adj_old_outerVertex_iff (caps : PentagonCapPair G)
    (step : Fin 5) (outside : {vertex // vertex ∉ caps.deletedVertexSupport}) :
    caps.openGraph.Adj outside.1 (caps.outer.vertex step) ↔
      outside.1 = caps.outer.spokeOuter step := by
  constructor
  · exact caps.eq_outer_spokeOuter_of_openGraph_adj_vertex step
  · intro houtside
    simpa [houtside] using caps.openGraph_adj_spokeOuter_outerVertex step

/-- The manuscript-side two-cap slit and the supplied two-cap opening are
isomorphic as simple graphs.  This is stronger than matching the ten boundary
ports: it checks adjacency in all four old/stub cases. -/
def openingGraphIso (caps : PentagonCapPair G) :
    (deletedRegionSlitGraph (G := G) caps.deletedVertexSupport).Iso caps.openGraph where
  toEquiv := caps.slitToOpenVertexEquiv
  map_rel_iff' := by
    intro first second
    rcases first with oldFirst | portFirst <;>
      rcases second with oldSecond | portSecond
    · change caps.openGraph.Adj oldFirst.1 oldSecond.1 ↔ G.Adj oldFirst.1 oldSecond.1
      exact caps.openGraph_adj_iff_of_not_mem_deletedVertexSupport oldFirst.2
    · change caps.openGraph.Adj oldFirst.1 portSecond.dart.snd ↔
        oldFirst.1 = portSecond.dart.fst
      rcases caps.boundaryPort_eq_inner_or_outer portSecond with hinner | houter
      · rcases hinner with ⟨step, hport⟩
        subst portSecond
        simpa using caps.openGraph_adj_old_innerVertex_iff step oldFirst
      · rcases houter with ⟨step, hport⟩
        subst portSecond
        simpa using caps.openGraph_adj_old_outerVertex_iff step oldFirst
    · change caps.openGraph.Adj portFirst.dart.snd oldSecond.1 ↔
        portFirst.dart.fst = oldSecond.1
      rcases caps.boundaryPort_eq_inner_or_outer portFirst with hinner | houter
      · rcases hinner with ⟨step, hport⟩
        subst portFirst
        constructor
        · intro hadj
          exact ((caps.openGraph_adj_old_innerVertex_iff step oldSecond).mp
            (caps.openGraph.adj_symm hadj)).symm
        · intro houtside
          exact caps.openGraph.adj_symm
            ((caps.openGraph_adj_old_innerVertex_iff step oldSecond).mpr houtside.symm)
      · rcases houter with ⟨step, hport⟩
        subst portFirst
        constructor
        · intro hadj
          exact ((caps.openGraph_adj_old_outerVertex_iff step oldSecond).mp
            (caps.openGraph.adj_symm hadj)).symm
        · intro houtside
          exact caps.openGraph.adj_symm
            ((caps.openGraph_adj_old_outerVertex_iff step oldSecond).mpr houtside.symm)
    · change caps.openGraph.Adj portFirst.dart.snd portSecond.dart.snd ↔ False
      rcases caps.boundaryPort_eq_inner_or_outer portFirst with hfirst | hfirst <;>
        rcases caps.boundaryPort_eq_inner_or_outer portSecond with hsecond | hsecond
      · rcases hfirst with ⟨firstStep, hfirstStep⟩
        rcases hsecond with ⟨secondStep, hsecondStep⟩
        subst portFirst
        subst portSecond
        exact ⟨caps.not_openGraph_adj_innerVertices firstStep secondStep, False.elim⟩
      · rcases hfirst with ⟨firstStep, hfirstStep⟩
        rcases hsecond with ⟨secondStep, hsecondStep⟩
        subst portFirst
        subst portSecond
        exact ⟨caps.not_openGraph_adj_inner_outerVertices firstStep secondStep, False.elim⟩
      · rcases hfirst with ⟨firstStep, hfirstStep⟩
        rcases hsecond with ⟨secondStep, hsecondStep⟩
        subst portFirst
        subst portSecond
        constructor
        · intro hadj
          exact caps.not_openGraph_adj_inner_outerVertices secondStep firstStep
            (caps.openGraph.adj_symm hadj)
        · exact False.elim
      · rcases hfirst with ⟨firstStep, hfirstStep⟩
        rcases hsecond with ⟨secondStep, hsecondStep⟩
        subst portFirst
        subst portSecond
        exact ⟨caps.not_openGraph_adj_outerVertices firstStep secondStep, False.elim⟩

/-- The graph comparison fixes the source's ordered inner coordinates
definitionally: fresh stub `i` maps to retained cap vertex `i`.  The `rfl`
proof is intentional; replacing it by a merely propositional transport would
silently weaken the ordered-boundary guarantee. -/
theorem openingGraphIso_ordered_innerStub (caps : PentagonCapPair G)
    (step : Fin 5) :
    caps.openingGraphIso (Sum.inr (caps.innerBoundaryPort step)) =
      caps.inner.vertex step :=
  rfl

/-- The graph comparison fixes the source's ordered outer coordinates
definitionally as well. -/
theorem openingGraphIso_ordered_outerStub (caps : PentagonCapPair G)
    (step : Fin 5) :
    caps.openingGraphIso (Sum.inr (caps.outerBoundaryPort step)) =
      caps.outer.vertex step :=
  rfl

end PentagonCapPair

end

end GoertzelV24TwoPentagonCapOpening

end Mettapedia.GraphTheory.FourColor
