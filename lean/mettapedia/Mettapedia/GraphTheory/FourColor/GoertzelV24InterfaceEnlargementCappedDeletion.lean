import Mettapedia.GraphTheory.FourColor.GoertzelV24DegreeTwoExteriorCappedDeletion
import Mettapedia.GraphTheory.FourColor.GoertzelV24LowDegreeVertexDeletion

/-!
# Capped deletion under a boundary-local interface enlargement

Let a finite interface be enlarged by naming additional ambient vertices.
Inside one component of the old strict exterior, the vertices newly promoted
to the interface are finite and explicit.  If each promoted vertex is
adjacent to the old interface, then it is one of the component's boundary
vertices.  In a maximum-degree-two graph there are at most two such vertices,
so a cap at seven determines the exact cap at five after their labels are
removed.

This isolates the reusable graph-theoretic part of a rolling facial update.
A concrete corridor construction may prove boundary locality componentwise;
it may instead erase a whole old component by exhibiting one newly named
isolated vertex.  Neither alternative is hidden in the code.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceEnlargementCappedDeletion

open Finset
open GoertzelV24DegreeTwoExteriorBoundary
open GoertzelV24DegreeTwoExteriorCappedDeletion
open GoertzelV24InterfaceDeletionComponentFactor
open SimpleGraph

variable {N Old New Added Label : Type*}
  [Fintype N] [DecidableEq N] [Fintype Old] [Fintype New]
  [DecidableEq Label]

/-- Vertices of one old exterior component that the enlarged interface names.
Because every component vertex is outside the old interface, these are
precisely the genuinely promoted vertices, even if the new presentation also
retains old coordinates. -/
noncomputable def promotedExteriorComponentVertices
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent) :
    Finset component := by
  classical
  letI : Fintype component := Fintype.ofFinite component
  exact Finset.univ.filter fun vertex => ∃ slot, newVertex slot = vertex.1

omit [Fintype Old] in
@[simp]
theorem mem_promotedExteriorComponentVertices_iff
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (vertex : component) :
    vertex ∈ promotedExteriorComponentVertices graph oldVertex newVertex
        component ↔
      ∃ slot, newVertex slot = vertex.1 := by
  classical
  simp [promotedExteriorComponentVertices]

/-- Distinct ambient labels removed from one old exterior component when the
interface is enlarged. -/
noncomputable def promotedExteriorComponentLabels
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent) :
    Finset Label :=
  (promotedExteriorComponentVertices graph oldVertex newVertex component).image
    fun vertex => label vertex.1

omit [Fintype Old] in
@[simp]
theorem mem_promotedExteriorComponentLabels_iff
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (value : Label) :
    value ∈ promotedExteriorComponentLabels graph oldVertex newVertex label
        component ↔
      ∃ vertex : component, (∃ slot, newVertex slot = vertex.1) ∧
        label vertex.1 = value := by
  classical
  simp [promotedExteriorComponentLabels]

/-- Boundary locality turns every promoted label into an exposed boundary
label of the old exterior component. -/
theorem promotedExteriorComponentLabels_subset_boundaryLabels
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (hboundary : ∀ vertex : component,
      vertex ∈ promotedExteriorComponentVertices graph oldVertex newVertex
        component →
      ∃ slot, graph.Adj (oldVertex slot) vertex.1) :
    promotedExteriorComponentLabels graph oldVertex newVertex label component ⊆
      exteriorComponentBoundaryLabels graph oldVertex label component := by
  classical
  intro value hvalue
  rcases (mem_promotedExteriorComponentLabels_iff graph oldVertex newVertex
    label component value).1 hvalue with ⟨vertex, hpromoted, rfl⟩
  rw [mem_exteriorComponentBoundaryLabels_iff]
  refine ⟨vertex, ?_, rfl⟩
  rw [mem_exteriorComponentBoundaryVertices_iff]
  exact hboundary vertex
    ((mem_promotedExteriorComponentVertices_iff graph oldVertex newVertex
      component vertex).2 hpromoted)

/-- A boundary-local enlargement promotes at most two distinct labels from
one component of a maximum-degree-two exterior. -/
theorem card_promotedExteriorComponentLabels_le_two
    (graph : SimpleGraph N) [DecidableRel graph.Adj]
    (oldVertex : Old → N) (newVertex : New → N) (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    {root : N} (hroot : root ∈ component.supp)
    (hrootOutside : OutsideInterface oldVertex root)
    (hdegree : ∀ vertex, (graph.neighborSet vertex).ncard ≤ 2)
    (hboundary : ∀ vertex : component,
      vertex ∈ promotedExteriorComponentVertices graph oldVertex newVertex
        component →
      ∃ slot, graph.Adj (oldVertex slot) vertex.1) :
    (promotedExteriorComponentLabels graph oldVertex newVertex label component
      ).card ≤ 2 := by
  calc
    (promotedExteriorComponentLabels graph oldVertex newVertex label component
      ).card ≤
        (exteriorComponentBoundaryLabels graph oldVertex label component).card :=
      Finset.card_le_card
        (promotedExteriorComponentLabels_subset_boundaryLabels graph oldVertex
          newVertex label component hboundary)
    _ ≤ 2 := card_exteriorComponentBoundaryLabels_le_two graph oldVertex
      label component hroot hrootOutside hdegree

/-- Removing the vertices promoted by a boundary-local enlargement cannot
split an old maximum-degree-two exterior component.  The result is stated as
preconnected because a component consisting entirely of promoted endpoints
may leave an empty induced graph. -/
theorem promotedExteriorComponentInducePreconnected
    (graph : SimpleGraph N) [DecidableRel graph.Adj]
    (oldVertex : Old → N) (newVertex : New → N)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    {root : N} (hroot : root ∈ component.supp)
    (hrootOutside : OutsideInterface oldVertex root)
    (hdegree : ∀ vertex, (graph.neighborSet vertex).ncard ≤ 2)
    (hboundary : ∀ vertex : component,
      vertex ∈ promotedExteriorComponentVertices graph oldVertex newVertex
        component →
      ∃ slot, graph.Adj (oldVertex slot) vertex.1) :
    (component.toSimpleGraph.induce
      (↑(promotedExteriorComponentVertices graph oldVertex newVertex
        component) : Set component)ᶜ).Preconnected := by
  classical
  letI : Fintype component := Fintype.ofFinite component
  apply GoertzelV24LowDegreeVertexDeletion.preconnected_induce_compl_of_degree_le_one
    component.connected_toSimpleGraph
  intro vertex hpromoted
  apply exteriorComponent_degree_le_one_of_mem_boundary graph oldVertex
    component hroot hrootOutside hdegree vertex
  rw [mem_exteriorComponentBoundaryVertices_iff]
  exact hboundary vertex hpromoted

omit [Fintype N] [DecidableEq N] [Fintype Old] in
/-- Isolation in the ambient graph descends to every old exterior component
containing the vertex.  This is the adapter needed when a concrete rolling
interface proves that a newly named vertex is harmlessly isolated before the
interface enlargement is interpreted componentwise. -/
theorem exteriorComponent_isIsolated_of_ambient
    (graph : SimpleGraph N) (oldVertex : Old → N)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (vertex : component) (hisolated : graph.IsIsolated vertex.1) :
    component.toSimpleGraph.IsIsolated vertex := by
  intro other hadj
  apply hisolated other.1
  have hexterior : (exteriorGraph graph oldVertex).Adj vertex.1 other.1 :=
    (component.toSimpleGraph_adj vertex.2 other.2).1 hadj
  exact hexterior.1

/-- Removing promoted vertices also preserves preconnectedness when an old
exterior component is erased completely.  This is the exact harmless
alternative to boundary locality: a component with no retained vertex cannot
split into two successor components.

The disjunction is deliberately stated per old component.  Concrete rolling
interfaces may therefore use boundary locality on ordinary path components
and the second branch on an isolated component named in its entirety. -/
theorem promotedExteriorComponentInducePreconnected_of_boundary_or_erased
    (graph : SimpleGraph N) [DecidableRel graph.Adj]
    (oldVertex : Old → N) (newVertex : New → N)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    {root : N} (hroot : root ∈ component.supp)
    (hrootOutside : OutsideInterface oldVertex root)
    (hdegree : ∀ vertex, (graph.neighborSet vertex).ncard ≤ 2)
    (hcase :
      (∀ vertex : component,
        vertex ∈ promotedExteriorComponentVertices graph oldVertex newVertex
            component →
          ∃ slot, graph.Adj (oldVertex slot) vertex.1) ∨
      (∀ vertex : component,
        vertex ∈ promotedExteriorComponentVertices graph oldVertex newVertex
          component)) :
    (component.toSimpleGraph.induce
      (↑(promotedExteriorComponentVertices graph oldVertex newVertex
        component) : Set component)ᶜ).Preconnected := by
  rcases hcase with hboundary | herased
  · exact promotedExteriorComponentInducePreconnected graph oldVertex
      newVertex component hroot hrootOutside hdegree hboundary
  · intro left _right
    have hnotSet : left.1 ∉
        (↑(promotedExteriorComponentVertices graph oldVertex newVertex
          component) : Set component) :=
      ((Set.mem_compl_iff _ _).mp left.2)
    have hnot : left.1 ∉
        promotedExteriorComponentVertices graph oldVertex newVertex
          component := hnotSet
    exact (hnot (herased left.1)).elim

omit [Fintype Old] in
/-- An isolated promoted vertex forces its whole old connected component to
be that promoted vertex.  Hence the "erased" branch above can be supplied by
a local isolation proof rather than by enumerating the component support. -/
theorem all_mem_promotedExteriorComponentVertices_of_isolated
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (vertex : component)
    (hpromoted : vertex ∈
      promotedExteriorComponentVertices graph oldVertex newVertex component)
    (hisolated : component.toSimpleGraph.IsIsolated vertex) :
    ∀ other : component,
      other ∈ promotedExteriorComponentVertices graph oldVertex newVertex
        component := by
  intro other
  have heq : other = vertex := by
    by_contra hne
    have hreachable := component.connected_toSimpleGraph.preconnected
      vertex other
    rcases hreachable.nonempty_neighborSet_left (Ne.symm hne) with
      ⟨neighbor, hadj⟩
    exact hisolated neighbor hadj
  simpa [heq] using hpromoted

/-- Boundary attachment and complete isolated-component deletion are the two
locally checkable non-splitting cases for one old exterior component. -/
theorem promotedExteriorComponentInducePreconnected_of_boundary_or_isolated
    (graph : SimpleGraph N) [DecidableRel graph.Adj]
    (oldVertex : Old → N) (newVertex : New → N)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    {root : N} (hroot : root ∈ component.supp)
    (hrootOutside : OutsideInterface oldVertex root)
    (hdegree : ∀ vertex, (graph.neighborSet vertex).ncard ≤ 2)
    (hcase :
      (∀ vertex : component,
        vertex ∈ promotedExteriorComponentVertices graph oldVertex newVertex
            component →
          ∃ slot, graph.Adj (oldVertex slot) vertex.1) ∨
      (∃ vertex : component,
        vertex ∈ promotedExteriorComponentVertices graph oldVertex newVertex
            component ∧
          component.toSimpleGraph.IsIsolated vertex)) :
    (component.toSimpleGraph.induce
      (↑(promotedExteriorComponentVertices graph oldVertex newVertex
        component) : Set component)ᶜ).Preconnected := by
  apply promotedExteriorComponentInducePreconnected_of_boundary_or_erased
    graph oldVertex newVertex component hroot hrootOutside hdegree
  rcases hcase with hboundary | ⟨vertex, hpromoted, hisolated⟩
  · exact Or.inl hboundary
  · exact Or.inr
      (all_mem_promotedExteriorComponentVertices_of_isolated graph oldVertex
        newVertex component vertex hpromoted hisolated)

/-- Ambient boundary attachment and ambient isolation are enough to apply the
componentwise non-splitting theorem.  The isolated branch needs no separate
connectivity calculation inside the old exterior presentation. -/
theorem promotedExteriorComponentInducePreconnected_of_boundary_or_ambientIsolated
    (graph : SimpleGraph N) [DecidableRel graph.Adj]
    (oldVertex : Old → N) (newVertex : New → N)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    {root : N} (hroot : root ∈ component.supp)
    (hrootOutside : OutsideInterface oldVertex root)
    (hdegree : ∀ vertex, (graph.neighborSet vertex).ncard ≤ 2)
    (hcase :
      (∀ vertex : component,
        vertex ∈ promotedExteriorComponentVertices graph oldVertex newVertex
            component →
          ∃ slot, graph.Adj (oldVertex slot) vertex.1) ∨
      (∃ vertex : component,
        vertex ∈ promotedExteriorComponentVertices graph oldVertex newVertex
            component ∧
          graph.IsIsolated vertex.1)) :
    (component.toSimpleGraph.induce
      (↑(promotedExteriorComponentVertices graph oldVertex newVertex
        component) : Set component)ᶜ).Preconnected := by
  apply promotedExteriorComponentInducePreconnected_of_boundary_or_isolated
    graph oldVertex newVertex component hroot hrootOutside hdegree
  rcases hcase with hboundary | ⟨vertex, hpromoted, hisolated⟩
  · exact Or.inl hboundary
  · exact Or.inr ⟨vertex, hpromoted,
      exteriorComponent_isIsolated_of_ambient graph oldVertex component vertex
        hisolated⟩

/-- The cap at seven of an old component determines exactly its cap at five
after a boundary-local interface enlargement removes the promoted labels. -/
theorem min_componentLabelSupport_sdiff_promoted_five_eq
    (graph : SimpleGraph N) [DecidableRel graph.Adj]
    (oldVertex : Old → N) (newVertex : New → N) (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    {root : N} (hroot : root ∈ component.supp)
    (hrootOutside : OutsideInterface oldVertex root)
    (hdegree : ∀ vertex, (graph.neighborSet vertex).ncard ≤ 2)
    (hboundary : ∀ vertex : component,
      vertex ∈ promotedExteriorComponentVertices graph oldVertex newVertex
        component →
      ∃ slot, graph.Adj (oldVertex slot) vertex.1) :
    min ((exteriorComponentLabelSupport graph oldVertex label component) \
        promotedExteriorComponentLabels graph oldVertex newVertex label
          component).card 5 =
      min (min (exteriorComponentLabelSupport graph oldVertex label component
        ).card 7 -
          (promotedExteriorComponentLabels graph oldVertex newVertex label
            component).card) 5 := by
  exact min_exteriorComponentLabelSupport_sdiff_five_eq graph oldVertex label
    component hroot hrootOutside hdegree
    (promotedExteriorComponentLabels graph oldVertex newVertex label component)
    (promotedExteriorComponentLabels_subset_boundaryLabels graph oldVertex
      newVertex label component hboundary)

/-! ## Conservative bounded enlargement

Boundary locality gives the sharp deletion budget two above.  Exactness does
not depend on that optimization.  If a finite added carrier covers every
promoted vertex, its cardinality is a conservative deletion budget.  This is
the structural escape hatch for a fixed-width rolling interface: enlarge the
stored cap once by the complete collar bound instead of repeatedly guessing
which collar positions are endpoints.
-/

omit [Fintype Old] in
/-- Every promoted label is already a label of its old exterior component. -/
theorem promotedExteriorComponentLabels_subset_componentLabelSupport
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent) :
    promotedExteriorComponentLabels graph oldVertex newVertex label component ⊆
      exteriorComponentLabelSupport graph oldVertex label component := by
  classical
  intro value hvalue
  rcases (mem_promotedExteriorComponentLabels_iff graph oldVertex newVertex
    label component value).1 hvalue with ⟨vertex, _hpromoted, hlabel⟩
  rw [mem_exteriorComponentLabelSupport_iff]
  exact ⟨vertex, hlabel⟩

omit [Fintype Old] in
/-- A finite added carrier which covers every promoted vertex also covers all
of their distinct labels.  No injectivity of the added presentation is
required. -/
theorem promotedExteriorComponentLabels_subset_addedLabelImage
    [Fintype Added]
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (addedVertex : Added → N) (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (hcover : ∀ vertex : component, (∃ slot, newVertex slot = vertex.1) →
      ∃ added, addedVertex added = vertex.1) :
    promotedExteriorComponentLabels graph oldVertex newVertex label component ⊆
      (Finset.univ : Finset Added).image (fun added =>
        label (addedVertex added)) := by
  classical
  intro value hvalue
  rcases (mem_promotedExteriorComponentLabels_iff graph oldVertex newVertex
    label component value).1 hvalue with
    ⟨vertex, hpromoted, hlabel⟩
  rcases hcover vertex hpromoted with ⟨added, hadd⟩
  apply Finset.mem_image.mpr
  exact ⟨added, Finset.mem_univ added, by simpa [hadd] using hlabel⟩

omit [Fintype Old] in
/-- The number of distinct promoted labels is bounded by any finite carrier
covering the promoted vertices.  Aliases can only reduce the count. -/
theorem card_promotedExteriorComponentLabels_le_card_added
    [Fintype Added]
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (addedVertex : Added → N) (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (hcover : ∀ vertex : component, (∃ slot, newVertex slot = vertex.1) →
      ∃ added, addedVertex added = vertex.1) :
    (promotedExteriorComponentLabels graph oldVertex newVertex label component
      ).card ≤ Fintype.card Added := by
  classical
  calc
    (promotedExteriorComponentLabels graph oldVertex newVertex label component
      ).card ≤
        ((Finset.univ : Finset Added).image (fun added =>
          label (addedVertex added))).card :=
      Finset.card_le_card
        (promotedExteriorComponentLabels_subset_addedLabelImage graph oldVertex
          newVertex addedVertex label component hcover)
    _ ≤ (Finset.univ : Finset Added).card := Finset.card_image_le
    _ = Fintype.card Added := Finset.card_univ

omit [Fintype Old] in
/-- A cap enlarged by the full added-carrier size recovers cap five after an
arbitrary interface enlargement covered by that carrier.  Unlike the sharp
cap-seven theorem, this requires no boundary-locality or degree bound. -/
theorem min_componentLabelSupport_sdiff_promoted_five_eq_bounded
    [Fintype Added]
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (addedVertex : Added → N) (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (hcover : ∀ vertex : component, (∃ slot, newVertex slot = vertex.1) →
      ∃ added, addedVertex added = vertex.1) :
    min ((exteriorComponentLabelSupport graph oldVertex label component) \
        promotedExteriorComponentLabels graph oldVertex newVertex label
          component).card 5 =
      min (min (exteriorComponentLabelSupport graph oldVertex label component
        ).card (5 + Fintype.card Added) -
          (promotedExteriorComponentLabels graph oldVertex newVertex label
            component).card) 5 := by
  exact GoertzelV24CappedCardSubtraction.min_card_sdiff_eq_min_min_card_add_sub
    (exteriorComponentLabelSupport graph oldVertex label component)
    (promotedExteriorComponentLabels graph oldVertex newVertex label component)
    5 (Fintype.card Added)
    (promotedExteriorComponentLabels_subset_componentLabelSupport graph
      oldVertex newVertex label component)
    (card_promotedExteriorComponentLabels_le_card_added graph oldVertex
      newVertex addedVertex label component hcover)

omit [Fintype Old] in
/-- A numerically bounded version of
`min_componentLabelSupport_sdiff_promoted_five_eq_bounded`.  The covering
carrier need not itself have the chosen fixed size; an external cardinality
bound is enough to select a source-independent cap. -/
theorem min_componentLabelSupport_sdiff_promoted_five_eq_of_card_added_le
    [Fintype Added]
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (addedVertex : Added → N) (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (deletionBound : Nat)
    (hcover : ∀ vertex : component, (∃ slot, newVertex slot = vertex.1) →
      ∃ added, addedVertex added = vertex.1)
    (hcard : Fintype.card Added ≤ deletionBound) :
    min ((exteriorComponentLabelSupport graph oldVertex label component) \
        promotedExteriorComponentLabels graph oldVertex newVertex label
          component).card 5 =
      min (min (exteriorComponentLabelSupport graph oldVertex label component
        ).card (5 + deletionBound) -
          (promotedExteriorComponentLabels graph oldVertex newVertex label
            component).card) 5 := by
  apply GoertzelV24CappedCardSubtraction.min_card_sdiff_eq_min_min_card_add_sub
    (exteriorComponentLabelSupport graph oldVertex label component)
    (promotedExteriorComponentLabels graph oldVertex newVertex label component)
    5 deletionBound
  · exact promotedExteriorComponentLabels_subset_componentLabelSupport graph
      oldVertex newVertex label component
  · exact (card_promotedExteriorComponentLabels_le_card_added graph oldVertex
      newVertex addedVertex label component hcover).trans hcard

end GoertzelV24InterfaceEnlargementCappedDeletion

end Mettapedia.GraphTheory.FourColor
