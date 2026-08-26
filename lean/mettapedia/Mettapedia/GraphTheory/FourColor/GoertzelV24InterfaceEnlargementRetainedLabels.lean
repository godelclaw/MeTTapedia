import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceEnlargementCappedDeletion

/-!
# Retained labels of an old exterior component under interface enlargement

An interface enlargement promotes some vertices of an old exterior component
into the interface.  The remaining vertices are *retained*, and their ambient
labels are what a rolling presentation must still store for that component.

This module isolates the retained side as a reusable brick.  Under injectivity
of the ambient label on a single component, the retained labels are exactly the
component's label support with the promoted labels removed, so the cap-five
equations already proved for the set difference transfer verbatim.

Scope, stated so it is not overread: nothing here concerns whether deleting the
promoted vertices leaves the component connected.  Every statement is about one
fixed old component and its label sets.  A post-deletion component analysis is a
separate obligation and is not addressed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceEnlargementRetainedLabels

open Finset
open GoertzelV24DegreeTwoExteriorBoundary
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceEnlargementCappedDeletion
open SimpleGraph

variable {N Old New Added Label : Type*}
  [Fintype N] [DecidableEq N] [Fintype Old] [Fintype New]
  [DecidableEq Label]

/-- Vertices of one old exterior component that the enlarged interface does
*not* name.  These are the vertices the component keeps. -/
noncomputable def retainedExteriorComponentVertices
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent) :
    Finset component := by
  classical
  letI : Fintype component := Fintype.ofFinite component
  exact Finset.univ.filter fun vertex => ¬ ∃ slot, newVertex slot = vertex.1

omit [Fintype Old] in
@[simp]
theorem mem_retainedExteriorComponentVertices_iff
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (vertex : component) :
    vertex ∈ retainedExteriorComponentVertices graph oldVertex newVertex
        component ↔
      ¬ ∃ slot, newVertex slot = vertex.1 := by
  classical
  simp [retainedExteriorComponentVertices]

omit [Fintype Old] in
/-- Retained and promoted vertices are complementary inside the component. -/
theorem retained_iff_not_promoted
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (vertex : component) :
    vertex ∈ retainedExteriorComponentVertices graph oldVertex newVertex
        component ↔
      vertex ∉ promotedExteriorComponentVertices graph oldVertex newVertex
        component := by
  classical
  simp

/-- Ambient labels that one old exterior component retains after the interface
is enlarged. -/
noncomputable def retainedExteriorComponentLabels
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent) :
    Finset Label :=
  (retainedExteriorComponentVertices graph oldVertex newVertex component).image
    fun vertex => label vertex.1

omit [Fintype Old] in
@[simp]
theorem mem_retainedExteriorComponentLabels_iff
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (value : Label) :
    value ∈ retainedExteriorComponentLabels graph oldVertex newVertex label
        component ↔
      ∃ vertex : component, (¬ ∃ slot, newVertex slot = vertex.1) ∧
        label vertex.1 = value := by
  classical
  simp [retainedExteriorComponentLabels]

omit [Fintype Old] in
/-- Every retained label is a label of the component.  No hypothesis needed. -/
theorem retainedExteriorComponentLabels_subset_componentLabelSupport
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent) :
    retainedExteriorComponentLabels graph oldVertex newVertex label component ⊆
      exteriorComponentLabelSupport graph oldVertex label component := by
  classical
  intro value hvalue
  rw [mem_retainedExteriorComponentLabels_iff] at hvalue
  obtain ⟨vertex, -, hlabel⟩ := hvalue
  rw [mem_exteriorComponentLabelSupport_iff]
  exact ⟨vertex, hlabel⟩

omit [Fintype Old] in
/-- One inclusion needs no injectivity: a component label that is not promoted
is retained, because the vertex realizing it cannot be a promoted vertex. -/
theorem sdiff_subset_retainedExteriorComponentLabels
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent) :
    (exteriorComponentLabelSupport graph oldVertex label component) \
        promotedExteriorComponentLabels graph oldVertex newVertex label
          component ⊆
      retainedExteriorComponentLabels graph oldVertex newVertex label
        component := by
  classical
  intro value hvalue
  rw [Finset.mem_sdiff] at hvalue
  obtain ⟨hsupport, hnotpromoted⟩ := hvalue
  rw [mem_exteriorComponentLabelSupport_iff] at hsupport
  obtain ⟨vertex, hlabel⟩ := hsupport
  rw [mem_retainedExteriorComponentLabels_iff]
  refine ⟨vertex, ?_, hlabel⟩
  intro hpromoted
  exact hnotpromoted
    (mem_promotedExteriorComponentLabels_iff graph oldVertex newVertex label
      component value |>.mpr ⟨vertex, hpromoted, hlabel⟩)

omit [Fintype Old] in
/-- **The retained-label partition.**  If the ambient label is injective on the
component, the retained labels are exactly the component's label support minus
the promoted labels.

Injectivity is used only for the forward inclusion: without it a retained
vertex and a promoted vertex could share a label, and that label would be both
retained and promoted. -/
theorem retainedExteriorComponentLabels_eq_sdiff
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (hinj : Function.Injective fun vertex : component => label vertex.1) :
    retainedExteriorComponentLabels graph oldVertex newVertex label component =
      (exteriorComponentLabelSupport graph oldVertex label component) \
        promotedExteriorComponentLabels graph oldVertex newVertex label
          component := by
  classical
  refine Finset.Subset.antisymm ?_
    (sdiff_subset_retainedExteriorComponentLabels graph oldVertex newVertex
      label component)
  intro value hvalue
  have hsupport :
      value ∈ exteriorComponentLabelSupport graph oldVertex label component :=
    retainedExteriorComponentLabels_subset_componentLabelSupport graph oldVertex
      newVertex label component hvalue
  rw [mem_retainedExteriorComponentLabels_iff] at hvalue
  obtain ⟨vertex, hnotslot, hlabel⟩ := hvalue
  rw [Finset.mem_sdiff]
  refine ⟨hsupport, ?_⟩
  intro hpromoted
  rw [mem_promotedExteriorComponentLabels_iff] at hpromoted
  obtain ⟨other, hotherslot, hotherlabel⟩ := hpromoted
  have hsame : vertex = other := hinj (by simp [hlabel, hotherlabel])
  exact hnotslot (hsame ▸ hotherslot)

/-! ## Labels which disappear completely

The injective partition above is useful when the ambient label has one
occurrence in the old component.  A facial dart component need not have that
property on an opened carrier: the two darts of a boundary edge may lie on the
same face.  The invariant which is valid without two-sidedness is the set of
labels having no retained occurrence at all.
-/

/-- Labels of the old component for which every realizing component vertex is
promoted.  These, and only these, disappear under the interface enlargement. -/
noncomputable def lostExteriorComponentLabels
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent) :
    Finset Label :=
  exteriorComponentLabelSupport graph oldVertex label component \
    retainedExteriorComponentLabels graph oldVertex newVertex label component

omit [Fintype Old] in
@[simp]
theorem mem_lostExteriorComponentLabels_iff
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (value : Label) :
    value ∈ lostExteriorComponentLabels graph oldVertex newVertex label
        component ↔
      value ∈ exteriorComponentLabelSupport graph oldVertex label component ∧
        value ∉ retainedExteriorComponentLabels graph oldVertex newVertex
          label component := by
  simp [lostExteriorComponentLabels]

omit [Fintype Old] in
/-- Every completely lost label has a promoted witness.  Aliasing is harmless:
a promoted label with a retained mate is simply not lost. -/
theorem lostExteriorComponentLabels_subset_promotedExteriorComponentLabels
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent) :
    lostExteriorComponentLabels graph oldVertex newVertex label component ⊆
      promotedExteriorComponentLabels graph oldVertex newVertex label
        component := by
  classical
  intro value hvalue
  rw [mem_lostExteriorComponentLabels_iff] at hvalue
  rcases (mem_exteriorComponentLabelSupport_iff graph oldVertex label component
    value).1 hvalue.1 with ⟨vertex, hlabel⟩
  have hpromoted : vertex ∈
      promotedExteriorComponentVertices graph oldVertex newVertex component := by
    by_contra hnotPromoted
    apply hvalue.2
    rw [mem_retainedExteriorComponentLabels_iff]
    refine ⟨vertex, ?_, hlabel⟩
    simpa only [mem_promotedExteriorComponentVertices_iff] using hnotPromoted
  exact (mem_promotedExteriorComponentLabels_iff graph oldVertex newVertex
    label component value).2 ⟨vertex,
      (mem_promotedExteriorComponentVertices_iff graph oldVertex newVertex
        component vertex).1 hpromoted, hlabel⟩

omit [Fintype Old] in
/-- The retained labels are the old support minus precisely the labels which
disappear completely.  This partition needs no injectivity hypothesis. -/
theorem retainedExteriorComponentLabels_eq_sdiff_lost
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent) :
    retainedExteriorComponentLabels graph oldVertex newVertex label component =
      exteriorComponentLabelSupport graph oldVertex label component \
        lostExteriorComponentLabels graph oldVertex newVertex label
          component := by
  classical
  apply Finset.Subset.antisymm
  · intro value hretained
    rw [Finset.mem_sdiff]
    refine ⟨
      retainedExteriorComponentLabels_subset_componentLabelSupport graph
        oldVertex newVertex label component hretained, ?_⟩
    intro hlost
    exact (mem_lostExteriorComponentLabels_iff graph oldVertex newVertex label
      component value).1 hlost |>.2 hretained
  · intro value hvalue
    rw [Finset.mem_sdiff] at hvalue
    by_contra hnotRetained
    exact hvalue.2 ((mem_lostExteriorComponentLabels_iff graph oldVertex
      newVertex label component value).2 ⟨hvalue.1, hnotRetained⟩)

omit [Fintype N] [DecidableEq N] [Fintype Old] [Fintype New] in
/-- Enlarging an interface can only delete edges from its strict-exterior
graph. -/
theorem exteriorGraph_mono_of_old_covered
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (holdCovered : ∀ old, ∃ new, newVertex new = oldVertex old) :
    exteriorGraph graph newVertex ≤ exteriorGraph graph oldVertex := by
  intro left right hadj
  refine ⟨hadj.1, ?_, ?_⟩
  · intro old heq
    rcases holdCovered old with ⟨new, hnew⟩
    exact hadj.2.1 new (heq.trans hnew.symm)
  · intro old heq
    rcases holdCovered old with ⟨new, hnew⟩
    exact hadj.2.2 new (heq.trans hnew.symm)

omit [Fintype Old] in
/-- If deleting the promoted vertices does not split an old exterior
component, then the successor exterior component rooted at any retained vertex
has exactly the retained label support of the old component.

This is the component-identification theorem deliberately omitted from the
first retained-label ledger.  It needs no injectivity of `label` and no degree
bound; all geometry is concentrated in the stated preconnectedness premise. -/
theorem exteriorComponentLabelSupport_eq_retained_of_preconnected
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (holdCovered : ∀ old, ∃ new, newVertex new = oldVertex old)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (start : component)
    (hstartRetained : start ∈
      retainedExteriorComponentVertices graph oldVertex newVertex component)
    (hpreconnected :
      (component.toSimpleGraph.induce
        (↑(promotedExteriorComponentVertices graph oldVertex newVertex
          component) : Set component)ᶜ).Preconnected) :
    exteriorComponentLabelSupport graph newVertex label
        ((exteriorGraph graph newVertex).connectedComponentMk start.1) =
      retainedExteriorComponentLabels graph oldVertex newVertex label
        component := by
  classical
  let promoted := promotedExteriorComponentVertices graph oldVertex newVertex
    component
  let retainedSet : Set component := (↑promoted : Set component)ᶜ
  have hstartNotPromoted : start ∉ promoted :=
    (retained_iff_not_promoted graph oldVertex newVertex component start).1
      hstartRetained
  have hstartOutsideNew : OutsideInterface newVertex start.1 := by
    intro slot heq
    apply hstartNotPromoted
    exact (mem_promotedExteriorComponentVertices_iff graph oldVertex newVertex
      component start).2 ⟨slot, heq.symm⟩
  let retainedToNewExterior :
      (component.toSimpleGraph.induce retainedSet) →g
        exteriorGraph graph newVertex :=
    { toFun := fun vertex => vertex.1.1
      map_rel' := by
        intro left right hadj
        have holdAdj : (exteriorGraph graph oldVertex).Adj left.1.1
            right.1.1 :=
          (component.toSimpleGraph_adj left.1.2 right.1.2).1 hadj
        refine ⟨holdAdj.1, ?_, ?_⟩
        · intro slot heq
          have hnot : left.1 ∉ promoted := left.2
          apply hnot
          exact (mem_promotedExteriorComponentVertices_iff graph oldVertex
            newVertex component left.1).2 ⟨slot, heq.symm⟩
        · intro slot heq
          have hnot : right.1 ∉ promoted := right.2
          apply hnot
          exact (mem_promotedExteriorComponentVertices_iff graph oldVertex
            newVertex component right.1).2 ⟨slot, heq.symm⟩ }
  ext value
  constructor
  · intro hvalue
    rcases (mem_exteriorComponentLabelSupport_iff graph newVertex label
      ((exteriorGraph graph newVertex).connectedComponentMk start.1)
      value).1 hvalue with ⟨vertex, hlabel⟩
    have hnewReach : (exteriorGraph graph newVertex).Reachable start.1
        vertex.1 := by
      apply SimpleGraph.ConnectedComponent.exact
      exact ((exteriorGraph graph newVertex).connectedComponentMk start.1
        |>.mem_supp_iff vertex.1).1 vertex.2 |>.symm
    have holdReach : (exteriorGraph graph oldVertex).Reachable start.1
        vertex.1 :=
      hnewReach.mono
        (exteriorGraph_mono_of_old_covered graph oldVertex newVertex
          holdCovered)
    have hstartComponent :
        (exteriorGraph graph oldVertex).connectedComponentMk start.1 =
          component :=
      (component.mem_supp_iff start.1).1 start.2
    have hvertexComponent : vertex.1 ∈ component.supp := by
      apply (component.mem_supp_iff vertex.1).2
      exact (SimpleGraph.ConnectedComponent.sound holdReach).symm.trans
        hstartComponent
    have hvertexOutsideNew : OutsideInterface newVertex vertex.1 :=
      outsideInterface_of_exteriorGraph_reachable graph newVertex
        hstartOutsideNew hnewReach
    apply (mem_retainedExteriorComponentLabels_iff graph oldVertex newVertex
      label component value).2
    refine ⟨⟨vertex.1, hvertexComponent⟩, ?_, hlabel⟩
    intro hslot
    rcases hslot with ⟨slot, hslot⟩
    exact hvertexOutsideNew slot hslot.symm
  · intro hvalue
    rcases (mem_retainedExteriorComponentLabels_iff graph oldVertex newVertex
      label component value).1 hvalue with ⟨vertex, hnotNew, hlabel⟩
    have hvertexNotPromoted : vertex ∉ promoted := by
      intro hpromoted
      exact hnotNew
        ((mem_promotedExteriorComponentVertices_iff graph oldVertex newVertex
          component vertex).1 hpromoted)
    let startRetained : {vertex : component // vertex ∈ retainedSet} :=
      ⟨start, hstartNotPromoted⟩
    let vertexRetained : {point : component // point ∈ retainedSet} :=
      ⟨vertex, hvertexNotPromoted⟩
    have hnewReach : (exteriorGraph graph newVertex).Reachable start.1
        vertex.1 := by
      have hinduced := hpreconnected startRetained vertexRetained
      have hmapped := hinduced.map retainedToNewExterior
      exact hmapped
    apply (mem_exteriorComponentLabelSupport_iff graph newVertex label
      ((exteriorGraph graph newVertex).connectedComponentMk start.1)
      value).2
    refine ⟨⟨vertex.1, ?_⟩, hlabel⟩
    apply (((exteriorGraph graph newVertex).connectedComponentMk start.1
      ).mem_supp_iff vertex.1).2
    exact (SimpleGraph.ConnectedComponent.sound hnewReach).symm

/-! ## Cap-five equations for the retained labels

With the partition in hand, the capped-deletion equations proved for the set
difference are statements about the retained labels themselves.
-/

omit [Fintype Old] in
/-- If a touched component's complete old label support has size at most six,
then cap six contains exactly the information needed to recover cap five after
promotion.  This bound is independent of the size of the enlarged interface. -/
theorem min_card_retainedExteriorComponentLabels_five_eq_cap_six
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (hinj : Function.Injective fun vertex : component => label vertex.1)
    (hsupport :
      (exteriorComponentLabelSupport graph oldVertex label component).card ≤
        6) :
    min (retainedExteriorComponentLabels graph oldVertex newVertex label
        component).card 5 =
      min (min (exteriorComponentLabelSupport graph oldVertex label component
        ).card 6 -
          (promotedExteriorComponentLabels graph oldVertex newVertex label
            component).card) 5 := by
  classical
  rw [retainedExteriorComponentLabels_eq_sdiff graph oldVertex newVertex label
    component hinj]
  rw [Finset.card_sdiff_of_subset
    (promotedExteriorComponentLabels_subset_componentLabelSupport graph
      oldVertex newVertex label component)]
  rw [Nat.min_eq_left hsupport]

omit [Fintype Old] in
/-- Cap five for the retained labels, from a cap enlarged by the added carrier.
No boundary-locality or degree hypothesis. -/
theorem min_card_retainedExteriorComponentLabels_five_eq_bounded
    [Fintype Added]
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (addedVertex : Added → N) (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (hinj : Function.Injective fun vertex : component => label vertex.1)
    (hcover : ∀ vertex : component, (∃ slot, newVertex slot = vertex.1) →
      ∃ added, addedVertex added = vertex.1) :
    min (retainedExteriorComponentLabels graph oldVertex newVertex label
        component).card 5 =
      min (min (exteriorComponentLabelSupport graph oldVertex label component
        ).card (5 + Fintype.card Added) -
          (promotedExteriorComponentLabels graph oldVertex newVertex label
            component).card) 5 := by
  classical
  rw [retainedExteriorComponentLabels_eq_sdiff graph oldVertex newVertex label
    component hinj]
  exact min_componentLabelSupport_sdiff_promoted_five_eq_bounded graph oldVertex
    newVertex addedVertex label component hcover

omit [Fintype Old] in
/-- Cap five for the retained labels against an external cardinality bound on
the added carrier. -/
theorem min_card_retainedExteriorComponentLabels_five_eq_of_card_added_le
    [Fintype Added]
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (addedVertex : Added → N) (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (deletionBound : Nat)
    (hinj : Function.Injective fun vertex : component => label vertex.1)
    (hcover : ∀ vertex : component, (∃ slot, newVertex slot = vertex.1) →
      ∃ added, addedVertex added = vertex.1)
    (hcard : Fintype.card Added ≤ deletionBound) :
    min (retainedExteriorComponentLabels graph oldVertex newVertex label
        component).card 5 =
      min (min (exteriorComponentLabelSupport graph oldVertex label component
        ).card (5 + deletionBound) -
          (promotedExteriorComponentLabels graph oldVertex newVertex label
            component).card) 5 := by
  classical
  rw [retainedExteriorComponentLabels_eq_sdiff graph oldVertex newVertex label
    component hinj]
  exact min_componentLabelSupport_sdiff_promoted_five_eq_of_card_added_le graph
    oldVertex newVertex addedVertex label component deletionBound hcover hcard

omit [Fintype Old] in
/-- Cap five for retained labels without any label-injectivity assumption.
The subtracted quantity is the number of labels which disappear completely,
not the number having at least one promoted occurrence. -/
theorem min_card_retainedExteriorComponentLabels_five_eq_lost_of_card_added_le
    [Fintype Added]
    (graph : SimpleGraph N) (oldVertex : Old → N) (newVertex : New → N)
    (addedVertex : Added → N) (label : N → Label)
    (component : (exteriorGraph graph oldVertex).ConnectedComponent)
    (deletionBound : Nat)
    (hcover : ∀ vertex : component, (∃ slot, newVertex slot = vertex.1) →
      ∃ added, addedVertex added = vertex.1)
    (hcard : Fintype.card Added ≤ deletionBound) :
    min (retainedExteriorComponentLabels graph oldVertex newVertex label
        component).card 5 =
      min (min (exteriorComponentLabelSupport graph oldVertex label component
        ).card (5 + deletionBound) -
          (lostExteriorComponentLabels graph oldVertex newVertex label
            component).card) 5 := by
  classical
  rw [retainedExteriorComponentLabels_eq_sdiff_lost graph oldVertex newVertex
    label component]
  apply GoertzelV24CappedCardSubtraction.min_card_sdiff_eq_min_min_card_add_sub
    (exteriorComponentLabelSupport graph oldVertex label component)
    (lostExteriorComponentLabels graph oldVertex newVertex label component)
    5 deletionBound
  · exact Finset.sdiff_subset
  · calc
      (lostExteriorComponentLabels graph oldVertex newVertex label component
        ).card ≤
          (promotedExteriorComponentLabels graph oldVertex newVertex label
            component).card :=
        Finset.card_le_card
          (lostExteriorComponentLabels_subset_promotedExteriorComponentLabels
            graph oldVertex newVertex label component)
      _ ≤ Fintype.card Added :=
        card_promotedExteriorComponentLabels_le_card_added graph oldVertex
          newVertex addedVertex label component hcover
      _ ≤ deletionBound := hcard

end GoertzelV24InterfaceEnlargementRetainedLabels

end Mettapedia.GraphTheory.FourColor
