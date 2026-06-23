import Mathlib.Logic.Relation
import Mettapedia.GraphTheory.FourColor.KempeCycles
import Mettapedia.GraphTheory.FourColor.KempeSwitch

namespace Mettapedia.GraphTheory.FourColor

namespace EdgeKempe

open Relation

variable {V E : Type*}

/-- Two graph edges are adjacent in the line graph when they are distinct and
share an incident vertex. -/
def edgeAdj (incident : V → Finset E) (e e' : E) : Prop :=
  e ≠ e' ∧ ∃ v, e ∈ incident v ∧ e' ∈ incident v

/-- The shared-vertex part of line-graph edge adjacency. -/
def hasSharedVertex (incident : V → Finset E) (e e' : E) : Prop :=
  ∃ v, e ∈ incident v ∧ e' ∈ incident v

theorem edgeAdj_iff (incident : V → Finset E) (e e' : E) :
    edgeAdj incident e e' ↔ e ≠ e' ∧ hasSharedVertex incident e e' :=
  Iff.rfl

theorem hasSharedVertex_comm (incident : V → Finset E) (e e' : E) :
    hasSharedVertex incident e e' ↔ hasSharedVertex incident e' e := by
  constructor
  · intro ⟨v, he, he'⟩
    exact ⟨v, he', he⟩
  · intro ⟨v, he', he⟩
    exact ⟨v, he, he'⟩

theorem edgeAdj_comm (incident : V → Finset E) (e e' : E) :
    edgeAdj incident e e' ↔ edgeAdj incident e' e := by
  constructor
  · intro ⟨hne, v, he, he'⟩
    exact ⟨hne.symm, v, he', he⟩
  · intro ⟨hne, v, he', he⟩
    exact ⟨hne.symm, v, he, he'⟩

theorem not_edgeAdj_self (incident : V → Finset E) (e : E) :
    ¬ edgeAdj incident e e := by
  intro h
  exact h.1 rfl

/-- Color predicate for the selected two-color edge subgraph. -/
def inTwoColors (x : E → Color) (α β : Color) (e : E) : Prop :=
  x e = α ∨ x e = β

/-- Interior predicate for zero-boundary edge data. -/
def interior (D : ZeroBoundaryData V E) (e : E) : Prop :=
  e ∉ D.boundaryEdges

/-- Predicate-level two-color adjacency restricted to interior edges. -/
def twoColorInteriorAdj (incident : V → Finset E) (D : ZeroBoundaryData V E)
    (x : E → Color) (α β : Color) (e e' : E) : Prop :=
  edgeAdj incident e e' ∧
    inTwoColors x α β e ∧
    inTwoColors x α β e' ∧
    interior D e ∧
    interior D e'

theorem twoColorInteriorAdj_left_interior
    (incident : V → Finset E) (D : ZeroBoundaryData V E)
    (x : E → Color) (α β : Color) {e e' : E}
    (h : twoColorInteriorAdj incident D x α β e e') :
    e ∉ D.boundaryEdges :=
  h.2.2.2.1

theorem twoColorInteriorAdj_right_interior
    (incident : V → Finset E) (D : ZeroBoundaryData V E)
    (x : E → Color) (α β : Color) {e e' : E}
    (h : twoColorInteriorAdj incident D x α β e e') :
    e' ∉ D.boundaryEdges :=
  h.2.2.2.2

/-- Predicate form of an edge-Kempe component: an interior αβ edge is selected
when it is reachable from an interior αβ seed edge incident to the chosen seed
vertex. This ports the decidability-free core of the old `KempePred` API. -/
def edgeKempePred (incident : V → Finset E) (D : ZeroBoundaryData V E)
    (x : E → Color) (seed : V) (α β : Color) : E → Prop :=
  fun e =>
    inTwoColors x α β e ∧
      interior D e ∧
      ∃ e₀, e₀ ∈ incident seed ∧ inTwoColors x α β e₀ ∧ interior D e₀ ∧
        ReflTransGen (twoColorInteriorAdj incident D x α β) e₀ e

theorem edgeKempePred_inTwoColors
    (incident : V → Finset E) (D : ZeroBoundaryData V E)
    (x : E → Color) (seed : V) (α β : Color) {e : E}
    (h : edgeKempePred incident D x seed α β e) :
    inTwoColors x α β e :=
  h.1

theorem edgeKempePred_interior
    (incident : V → Finset E) (D : ZeroBoundaryData V E)
    (x : E → Color) (seed : V) (α β : Color) {e : E}
    (h : edgeKempePred incident D x seed α β e) :
    e ∉ D.boundaryEdges :=
  h.2.1

/-- Switching along any interior edge-Kempe predicate preserves zero vertex sums, provided
the selected predicate has even two-color incidence at every vertex. This is the modern
predicate-level replacement for the old `edgeKempeSwitchP_preserves_zero` lemma. -/
theorem switch_edgeKempePred_preserves_isZeroBoundary
    (D : ZeroBoundaryData V E) (x : E → Color) (seed : V) (α β : Color)
    [DecidablePred (edgeKempePred D.incident D x seed α β)]
    (zero_at : D.isZeroBoundary x)
    (even_at : ∀ v : V, Even ((D.incident v).filter
      (edgeKempePred D.incident D x seed α β)).card) :
    D.isZeroBoundary (switch α β {e | edgeKempePred D.incident D x seed α β e} x) := by
  classical
  have even_selected :
      ∀ v : V,
        Even ((D.incident v).filter
          (fun e => edgeKempePred D.incident D x seed α β e ∧
            (x e = α ∨ x e = β))).card := by
    intro v
    have hfilter :
        (D.incident v).filter
            (fun e => edgeKempePred D.incident D x seed α β e ∧
              (x e = α ∨ x e = β)) =
          (D.incident v).filter (edgeKempePred D.incident D x seed α β) := by
      ext e
      constructor
      · intro he
        exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 he).1, (Finset.mem_filter.1 he).2.1⟩
      · intro he
        have hpred : edgeKempePred D.incident D x seed α β e := (Finset.mem_filter.1 he).2
        exact Finset.mem_filter.2
          ⟨(Finset.mem_filter.1 he).1, hpred, edgeKempePred_inTwoColors D.incident D x seed α β hpred⟩
    rw [hfilter]
    exact even_at v
  exact switch_preserves_zero_incidence_sum_pred
    (incident := D.incident) (x := x)
    (p := edgeKempePred D.incident D x seed α β)
    (α := α) (β := β) zero_at even_selected

/-- Switching along an interior edge-Kempe predicate preserves the full zero-boundary set:
vertex sums remain zero, and boundary edges remain zero because the predicate selects only
interior edges. This ports the full content of the old predicate Kempe-switch preservation
lemma into the modern `ZeroBoundaryData.zeroBoundarySet` API. -/
theorem switch_edgeKempePred_mem_zeroBoundarySet
    (D : ZeroBoundaryData V E) (x : E → Color) (seed : V) (α β : Color)
    [DecidablePred (edgeKempePred D.incident D x seed α β)]
    (hx : x ∈ D.zeroBoundarySet)
    (even_at : ∀ v : V, Even ((D.incident v).filter
      (edgeKempePred D.incident D x seed α β)).card) :
    switch α β {e | edgeKempePred D.incident D x seed α β e} x ∈ D.zeroBoundarySet := by
  classical
  rcases hx with ⟨zero_at, boundary_at⟩
  refine ⟨switch_edgeKempePred_preserves_isZeroBoundary D x seed α β zero_at even_at, ?_⟩
  intro e he
  have hp : ¬ edgeKempePred D.incident D x seed α β e := by
    intro hpred
    exact edgeKempePred_interior D.incident D x seed α β hpred he
  have hnot : e ∉ {e | edgeKempePred D.incident D x seed α β e} := hp
  simp [switch, hnot, boundary_at e he]

/-- Finset wrapper for the predicate edge-Kempe component. Classical
decidability is used only at this boundary. -/
noncomputable def edgeKempeFinset [Fintype E] [DecidableEq E]
    (incident : V → Finset E) (D : ZeroBoundaryData V E)
    (x : E → Color) (seed : V) (α β : Color) : Finset E :=
  by
    classical
    exact Finset.univ.filter (edgeKempePred incident D x seed α β)

@[simp]
theorem mem_edgeKempeFinset_iff [Fintype E] [DecidableEq E]
    (incident : V → Finset E) (D : ZeroBoundaryData V E)
    (x : E → Color) (seed : V) (α β : Color) {e : E} :
    e ∈ edgeKempeFinset incident D x seed α β ↔
      edgeKempePred incident D x seed α β e := by
  classical
  simp [edgeKempeFinset]

theorem edgeKempeFinset_inTwoColors [Fintype E] [DecidableEq E]
    (incident : V → Finset E) (D : ZeroBoundaryData V E)
    (x : E → Color) (seed : V) (α β : Color) {e : E}
    (he : e ∈ edgeKempeFinset incident D x seed α β) :
    inTwoColors x α β e :=
  edgeKempePred_inTwoColors incident D x seed α β
    ((mem_edgeKempeFinset_iff incident D x seed α β).1 he)

theorem edgeKempeFinset_interior [Fintype E] [DecidableEq E]
    (incident : V → Finset E) (D : ZeroBoundaryData V E)
    (x : E → Color) (seed : V) (α β : Color) {e : E}
    (he : e ∈ edgeKempeFinset incident D x seed α β) :
    e ∉ D.boundaryEdges :=
  edgeKempePred_interior incident D x seed α β
    ((mem_edgeKempeFinset_iff incident D x seed α β).1 he)

/-- Finset-wrapper form of `switch_edgeKempePred_mem_zeroBoundarySet`. This lets later
finite-component arguments use `edgeKempeFinset` directly while preserving the same
zero-boundary invariant. -/
theorem switch_edgeKempeFinset_mem_zeroBoundarySet [Fintype E] [DecidableEq E]
    (D : ZeroBoundaryData V E) (x : E → Color) (seed : V) (α β : Color)
    (hx : x ∈ D.zeroBoundarySet)
    (even_at : ∀ v : V,
      Even ((edgeKempeFinset D.incident D x seed α β ∩ D.incident v).card)) :
    switch α β (edgeKempeFinset D.incident D x seed α β : Set E) x ∈
      D.zeroBoundarySet := by
  classical
  have even_pred :
      ∀ v : V,
        Even ((D.incident v).filter
          (edgeKempePred D.incident D x seed α β)).card := by
    intro v
    have hfilter :
        (D.incident v).filter (edgeKempePred D.incident D x seed α β) =
          edgeKempeFinset D.incident D x seed α β ∩ D.incident v := by
      ext e
      simp [edgeKempeFinset, and_comm]
    rw [hfilter]
    exact even_at v
  have hset :
      (edgeKempeFinset D.incident D x seed α β : Set E) =
        {e | edgeKempePred D.incident D x seed α β e} := by
    ext e
    simp [edgeKempeFinset]
  rw [hset]
  exact switch_edgeKempePred_mem_zeroBoundarySet D x seed α β hx even_pred

/-- The deliberately over-approximated "all αβ edges" set. It is useful as a
guardrail: many false old Kempe claims accidentally used this set instead of a
connected component. -/
noncomputable def overapprox [Fintype E] [DecidableEq E]
    (x : E → Color) (α β : Color) : Finset E :=
  by
    classical
    exact Finset.univ.filter (fun e => inTwoColors x α β e)

@[simp]
theorem mem_overapprox_iff [Fintype E] [DecidableEq E]
    (x : E → Color) (α β : Color) {e : E} :
    e ∈ overapprox x α β ↔ inTwoColors x α β e := by
  simp [overapprox, inTwoColors]

theorem overapprox_hits_boundary [Fintype E] [DecidableEq E]
    (D : ZeroBoundaryData V E) (x : E → Color) (α β : Color)
    (h : ∃ e, e ∈ D.boundaryEdges ∧ inTwoColors x α β e) :
    ∃ e, e ∈ D.boundaryEdges ∧ e ∈ overapprox x α β := by
  rcases h with ⟨e, heBoundary, heColor⟩
  exact ⟨e, heBoundary, by simp [heColor]⟩

/-- If the over-approximation contains at least three selected-color edges at
one vertex, it cannot be a true Kempe cycle. -/
theorem overapprox_not_isKempeCycle_of_three [Fintype E] [DecidableEq E]
    (incident : V → Finset E) (x : E → Color) (v : V) (α β : Color)
    (h3 : 3 ≤ (overapprox x α β ∩ incident v).card) :
    ¬ IsKempeCycle incident x (overapprox x α β) α β := by
  intro hC
  have h_le2 : (overapprox x α β ∩ incident v).card ≤ 2 := hC.1.2 v
  omega

end EdgeKempe

end Mettapedia.GraphTheory.FourColor
