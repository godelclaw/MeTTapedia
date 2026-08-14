import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapOpeningBoundary

/-!
# Carrier comparison for the two pentagon openings

For a separated pair of pentagon caps, the supplied toolchain keeps the ten
cap vertices and deletes their cycle edges.  The manuscript instead deletes
the ten cap vertices and creates one fresh stub per outward dart.  The exact
port enumeration proves that these are two presentations of the same intended
open boundary.  This file starts their comparison by giving the canonical
vertex equivalence: old vertices keep their names and a fresh port becomes its
deleted cap endpoint.

The later graph/rotation comparison must still prove adjacency and cyclic face
order are respected.  A carrier equivalence alone is not an annular embedding.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoPentagonCapOpening

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

end PentagonCapPair

end

end GoertzelV24TwoPentagonCapOpening

end Mettapedia.GraphTheory.FourColor
