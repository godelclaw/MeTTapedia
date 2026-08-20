import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# L1: splice two paths around a shared interior vertex

Two path pieces may meet at a vertex which a later disjoint-pair construction
must avoid.  If the predecessor on the first path is adjacent to the successor
on the second path, delete the two darts incident to the shared vertex, insert
that bypass edge, and erase any remaining loops.

This is generic walk surgery.  It neither supplies the bypass adjacency nor
proves separation from a companion path; those are the source-local geometric
obligations in the Cell--3 corridor.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualPathInteriorCrossSplice

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

noncomputable section

/-- The predecessor-to-successor edge splices the prefix of `oldWalk` to the
suffix of `newWalk`, omitting their shared interior vertex.  Loop erasure is
part of the construction, so the returned walk is definitionally a path
candidate with the original outer endpoints. -/
noncomputable def crossSpliceAround
    {oldStart oldFinish newStart newFinish current : V}
    (oldWalk : G.Walk oldStart oldFinish)
    (newWalk : G.Walk newStart newFinish)
    (hold : current ∈ oldWalk.support)
    (hnew : current ∈ newWalk.support)
    (hbypass : G.Adj
      (oldWalk.takeUntil current hold).penultimate
      (newWalk.dropUntil current hnew).snd) :
    G.Walk oldStart newFinish :=
  let oldPrefix := oldWalk.takeUntil current hold
  let newSuffix := newWalk.dropUntil current hnew
  (oldPrefix.dropLast.append (newSuffix.tail.cons hbypass)).bypass

/-- The cross-spliced walk is simple by construction. -/
theorem crossSpliceAround_isPath
    {oldStart oldFinish newStart newFinish current : V}
    (oldWalk : G.Walk oldStart oldFinish)
    (newWalk : G.Walk newStart newFinish)
    (hold : current ∈ oldWalk.support)
    (hnew : current ∈ newWalk.support)
    (hbypass : G.Adj
      (oldWalk.takeUntil current hold).penultimate
      (newWalk.dropUntil current hnew).snd) :
    (crossSpliceAround oldWalk newWalk hold hnew hbypass).IsPath := by
  exact SimpleGraph.Walk.bypass_isPath _

/-- If the shared vertex is internal to both selected pieces, it is absent
from the support of the cross-spliced path. -/
theorem current_not_mem_crossSpliceAround_support
    {oldStart oldFinish newStart newFinish current : V}
    (oldWalk : G.Walk oldStart oldFinish)
    (newWalk : G.Walk newStart newFinish)
    (holdPath : oldWalk.IsPath)
    (hnewPath : newWalk.IsPath)
    (hold : current ∈ oldWalk.support)
    (hnew : current ∈ newWalk.support)
    (holdStart : oldStart ≠ current)
    (hnewEnd : current ≠ newFinish)
    (hbypass : G.Adj
      (oldWalk.takeUntil current hold).penultimate
      (newWalk.dropUntil current hnew).snd) :
    current ∉ (crossSpliceAround oldWalk newWalk hold hnew hbypass).support := by
  let oldPrefix := oldWalk.takeUntil current hold
  let newSuffix := newWalk.dropUntil current hnew
  have hprefixNotNil : ¬ oldPrefix.Nil := by
    simpa only [oldPrefix, SimpleGraph.Walk.nil_takeUntil] using holdStart
  have hsuffixNotNil : ¬ newSuffix.Nil := by
    intro hnil
    exact hnewEnd hnil.eq
  have hprefixPath : oldPrefix.IsPath := by
    exact holdPath.takeUntil hold
  have hsuffixPath : newSuffix.IsPath := by
    exact hnewPath.dropUntil hnew
  have hprefixAvoids : current ∉ oldPrefix.dropLast.support := by
    rw [oldPrefix.support_dropLast hprefixNotNil]
    intro hmem
    have hne := hprefixPath.support_nodup.rel_dropLast_getLast hmem
    exact hne (oldPrefix.getLast_support).symm
  have hstartNotTail : current ∉ newSuffix.support.tail := by
    have hnodup := hsuffixPath.support_nodup
    rw [← newSuffix.cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hsuffixAvoids : current ∉ newSuffix.tail.support := by
    rw [newSuffix.support_tail_of_not_nil hsuffixNotNil]
    exact hstartNotTail
  intro hcurrent
  have hraw := (oldPrefix.dropLast.append (newSuffix.tail.cons hbypass))
    |>.support_bypass_subset_support hcurrent
  rw [SimpleGraph.Walk.support_append] at hraw
  rcases List.mem_append.mp hraw with hprefix | hsuffix
  · exact hprefixAvoids hprefix
  · apply hsuffixAvoids
    simpa only [SimpleGraph.Walk.support_cons, List.tail_cons] using hsuffix

/-- The literal four-edge bridge through three displayed corridor centres.
The endpoint adjacencies come from the two local rail packets, while the two
middle adjacencies come from consecutive corridor faces. -/
def threeCenterBridge
    {left firstCenter middleCenter lastCenter right : V}
    (hleft : G.Adj left firstCenter)
    (hfirstMiddle : G.Adj firstCenter middleCenter)
    (hmiddleLast : G.Adj middleCenter lastCenter)
    (hright : G.Adj lastCenter right) :
    G.Walk left right :=
  .cons hleft (.cons hfirstMiddle (.cons hmiddleLast (.cons hright .nil)))

@[simp] theorem threeCenterBridge_length
    {left firstCenter middleCenter lastCenter right : V}
    (hleft : G.Adj left firstCenter)
    (hfirstMiddle : G.Adj firstCenter middleCenter)
    (hmiddleLast : G.Adj middleCenter lastCenter)
    (hright : G.Adj lastCenter right) :
    (threeCenterBridge hleft hfirstMiddle hmiddleLast hright).length = 4 := by
  rfl

@[simp] theorem threeCenterBridge_support
    {left firstCenter middleCenter lastCenter right : V}
    (hleft : G.Adj left firstCenter)
    (hfirstMiddle : G.Adj firstCenter middleCenter)
    (hmiddleLast : G.Adj middleCenter lastCenter)
    (hright : G.Adj lastCenter right) :
    (threeCenterBridge hleft hfirstMiddle hmiddleLast hright).support =
      [left, firstCenter, middleCenter, lastCenter, right] := by
  rfl

/-- Exact support makes collision avoidance of the centre bridge a finite
five-vertex check. -/
theorem current_not_mem_threeCenterBridge_support
    {left firstCenter middleCenter lastCenter right current : V}
    (hleft : G.Adj left firstCenter)
    (hfirstMiddle : G.Adj firstCenter middleCenter)
    (hmiddleLast : G.Adj middleCenter lastCenter)
    (hright : G.Adj lastCenter right)
    (hcurrentLeft : current ≠ left)
    (hcurrentFirst : current ≠ firstCenter)
    (hcurrentMiddle : current ≠ middleCenter)
    (hcurrentLast : current ≠ lastCenter)
    (hcurrentRight : current ≠ right) :
    current ∉
      (threeCenterBridge hleft hfirstMiddle hmiddleLast hright).support := by
  simp [threeCenterBridge, hcurrentLeft, hcurrentFirst, hcurrentMiddle,
    hcurrentLast, hcurrentRight]

/-- A whole bridge walk may replace the single bypass edge.  This is the form
needed when source geometry routes from a rail attachment face through one or
more displayed corridor centres before returning to the other rail. -/
noncomputable def crossSpliceAroundWithBridge
    {oldStart oldFinish newStart newFinish current : V}
    (oldWalk : G.Walk oldStart oldFinish)
    (newWalk : G.Walk newStart newFinish)
    (hold : current ∈ oldWalk.support)
    (hnew : current ∈ newWalk.support)
    (bridge : G.Walk
      (oldWalk.takeUntil current hold).penultimate
      (newWalk.dropUntil current hnew).snd) :
    G.Walk oldStart newFinish :=
  let oldPrefix := oldWalk.takeUntil current hold
  let newSuffix := newWalk.dropUntil current hnew
  (oldPrefix.dropLast.append (bridge.append newSuffix.tail)).bypass

/-- Loop erasure makes the bridge-spliced walk simple. -/
theorem crossSpliceAroundWithBridge_isPath
    {oldStart oldFinish newStart newFinish current : V}
    (oldWalk : G.Walk oldStart oldFinish)
    (newWalk : G.Walk newStart newFinish)
    (hold : current ∈ oldWalk.support)
    (hnew : current ∈ newWalk.support)
    (bridge : G.Walk
      (oldWalk.takeUntil current hold).penultimate
      (newWalk.dropUntil current hnew).snd) :
    (crossSpliceAroundWithBridge oldWalk newWalk hold hnew bridge).IsPath := by
  exact SimpleGraph.Walk.bypass_isPath _

/-- Loop erasure introduces no new vertex: every face of the bridge splice
comes from the old path, the supplied bridge, or the new path. -/
theorem crossSpliceAroundWithBridge_support_subset
    {oldStart oldFinish newStart newFinish current : V}
    (oldWalk : G.Walk oldStart oldFinish)
    (newWalk : G.Walk newStart newFinish)
    (hold : current ∈ oldWalk.support)
    (hnew : current ∈ newWalk.support)
    (holdStart : oldStart ≠ current)
    (hnewEnd : current ≠ newFinish)
    (bridge : G.Walk
      (oldWalk.takeUntil current hold).penultimate
      (newWalk.dropUntil current hnew).snd) :
    ∀ vertex ∈
        (crossSpliceAroundWithBridge oldWalk newWalk hold hnew bridge).support,
      vertex ∈ oldWalk.support ∨ vertex ∈ bridge.support ∨
        vertex ∈ newWalk.support := by
  let oldPrefix := oldWalk.takeUntil current hold
  let newSuffix := newWalk.dropUntil current hnew
  have hprefixNotNil : ¬ oldPrefix.Nil := by
    simpa only [oldPrefix, SimpleGraph.Walk.nil_takeUntil] using holdStart
  have hsuffixNotNil : ¬ newSuffix.Nil := by
    intro hnil
    exact hnewEnd hnil.eq
  intro vertex hvertex
  have hraw :=
    (oldPrefix.dropLast.append (bridge.append newSuffix.tail))
      |>.support_bypass_subset_support hvertex
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hraw with
    hprefix | hrest
  · left
    apply oldWalk.support_takeUntil_subset_support hold
    rw [oldPrefix.support_dropLast hprefixNotNil] at hprefix
    exact List.dropLast_subset _ hprefix
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hrest with
      hbridge | hsuffix
    · exact .inr (.inl hbridge)
    · right
      right
      apply newWalk.support_dropUntil_subset_support hnew
      rw [newSuffix.support_tail_of_not_nil hsuffixNotNil] at hsuffix
      exact List.mem_of_mem_tail hsuffix

/-- Sharp support receipt for the bridge splice.  Unlike the coarser public
receipt above, this remembers that only the prefix before `current` and the
suffix after `current` survive.  This distinction is needed when a later
separation proof may legitimately ignore collisions in the discarded pieces. -/
theorem crossSpliceAroundWithBridge_support_subset_sharp
    {oldStart oldFinish newStart newFinish current : V}
    (oldWalk : G.Walk oldStart oldFinish)
    (newWalk : G.Walk newStart newFinish)
    (hold : current ∈ oldWalk.support)
    (hnew : current ∈ newWalk.support)
    (bridge : G.Walk
      (oldWalk.takeUntil current hold).penultimate
      (newWalk.dropUntil current hnew).snd) :
    ∀ vertex ∈
        (crossSpliceAroundWithBridge oldWalk newWalk hold hnew bridge).support,
      vertex ∈ (oldWalk.takeUntil current hold).dropLast.support ∨
        vertex ∈ bridge.support ∨
        vertex ∈ (newWalk.dropUntil current hnew).tail.support := by
  intro vertex hvertex
  have hraw :=
    ((oldWalk.takeUntil current hold).dropLast.append
      (bridge.append (newWalk.dropUntil current hnew).tail))
      |>.support_bypass_subset_support hvertex
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hraw with
    hprefix | hrest
  · exact .inl hprefix
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hrest with
      hbridge | hsuffix
    · exact .inr (.inl hbridge)
    · exact .inr (.inr hsuffix)

/-- Pairwise separation from the two source pieces and the bridge implies
separation from the final loop-erased splice. -/
theorem crossSpliceAroundWithBridge_support_disjoint
    {oldStart oldFinish newStart newFinish current : V}
    (oldWalk : G.Walk oldStart oldFinish)
    (newWalk : G.Walk newStart newFinish)
    (hold : current ∈ oldWalk.support)
    (hnew : current ∈ newWalk.support)
    (holdStart : oldStart ≠ current)
    (hnewEnd : current ≠ newFinish)
    (bridge : G.Walk
      (oldWalk.takeUntil current hold).penultimate
      (newWalk.dropUntil current hnew).snd)
    {companionStart companionFinish : V}
    (companion : G.Walk companionStart companionFinish)
    (holdDisjoint : oldWalk.support.Disjoint companion.support)
    (hbridgeDisjoint : bridge.support.Disjoint companion.support)
    (hnewDisjoint : newWalk.support.Disjoint companion.support) :
    (crossSpliceAroundWithBridge oldWalk newWalk hold hnew bridge).support.Disjoint
      companion.support := by
  rw [List.disjoint_left]
  intro vertex hroute hcompanion
  rcases crossSpliceAroundWithBridge_support_subset oldWalk newWalk hold hnew
      holdStart hnewEnd bridge vertex hroute with hold | hbridge | hnew
  · exact (List.disjoint_left.mp holdDisjoint hold) hcompanion
  · exact (List.disjoint_left.mp hbridgeDisjoint hbridge) hcompanion
  · exact (List.disjoint_left.mp hnewDisjoint hnew) hcompanion

/-- A bridge which avoids the removed vertex yields a simple splice which
also avoids it. -/
theorem current_not_mem_crossSpliceAroundWithBridge_support
    {oldStart oldFinish newStart newFinish current : V}
    (oldWalk : G.Walk oldStart oldFinish)
    (newWalk : G.Walk newStart newFinish)
    (holdPath : oldWalk.IsPath)
    (hnewPath : newWalk.IsPath)
    (hold : current ∈ oldWalk.support)
    (hnew : current ∈ newWalk.support)
    (holdStart : oldStart ≠ current)
    (hnewEnd : current ≠ newFinish)
    (bridge : G.Walk
      (oldWalk.takeUntil current hold).penultimate
      (newWalk.dropUntil current hnew).snd)
    (hbridge : current ∉ bridge.support) :
    current ∉
      (crossSpliceAroundWithBridge oldWalk newWalk hold hnew bridge).support := by
  let oldPrefix := oldWalk.takeUntil current hold
  let newSuffix := newWalk.dropUntil current hnew
  have hprefixNotNil : ¬ oldPrefix.Nil := by
    simpa only [oldPrefix, SimpleGraph.Walk.nil_takeUntil] using holdStart
  have hsuffixNotNil : ¬ newSuffix.Nil := by
    intro hnil
    exact hnewEnd hnil.eq
  have hprefixPath : oldPrefix.IsPath := holdPath.takeUntil hold
  have hsuffixPath : newSuffix.IsPath := hnewPath.dropUntil hnew
  have hprefixAvoids : current ∉ oldPrefix.dropLast.support := by
    rw [oldPrefix.support_dropLast hprefixNotNil]
    intro hmem
    have hne := hprefixPath.support_nodup.rel_dropLast_getLast hmem
    exact hne (oldPrefix.getLast_support).symm
  have hstartNotTail : current ∉ newSuffix.support.tail := by
    have hnodup := hsuffixPath.support_nodup
    rw [← newSuffix.cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hsuffixAvoids : current ∉ newSuffix.tail.support := by
    rw [newSuffix.support_tail_of_not_nil hsuffixNotNil]
    exact hstartNotTail
  intro hcurrent
  have hraw :=
    (oldPrefix.dropLast.append (bridge.append newSuffix.tail))
      |>.support_bypass_subset_support hcurrent
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hraw with
    hprefix | hrest
  · exact hprefixAvoids hprefix
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hrest with
      hbridge' | hsuffix
    · exact hbridge hbridge'
    · exact hsuffixAvoids hsuffix

end

end GoertzelV24DualPathInteriorCrossSplice

end Mettapedia.GraphTheory.FourColor
