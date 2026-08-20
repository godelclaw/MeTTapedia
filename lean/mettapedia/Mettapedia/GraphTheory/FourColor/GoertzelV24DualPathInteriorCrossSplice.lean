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

end

end GoertzelV24DualPathInteriorCrossSplice

end Mettapedia.GraphTheory.FourColor
