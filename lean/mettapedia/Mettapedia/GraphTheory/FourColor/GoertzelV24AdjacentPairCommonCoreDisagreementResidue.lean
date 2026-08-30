import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCommonCoreKempeBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24LocalSwapKempeGeneration

/-!
# The exact residue of an adjacent-pair common-core disagreement

Compare colourings of two adjacent-pair deletions on their common four-vertex
deletion.  If the restrictions disagree, there are exactly three outcomes
available to the present Kempe machinery:

* the target restriction is outside the source restriction's Kempe closure,
  in which case some common-core vertex has a discrepancy not governed by one
  colour transposition;
* a component used by a lifting sequence reaches an edge at the second deleted
  pair; or
* the whole sequence lifts and gives a different source-deletion colouring
  whose common-core restriction agrees literally with the target.

The theorem is purely structural.  It does not turn either of the first two
horns into wall exclusion or support-preserving replacement.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairCommonCoreDisagreementResidue

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24LocalSwapKempeGeneration
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The two common-core restrictions fail to differ by one colour
transposition at some common-core vertex. -/
def HasCommonCoreBranchingDiscrepancy
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) : Prop :=
  let sourceCommon := firstDeletionCommonCoreColoring
    (third := target.firstVertex) (fourth := target.secondVertex)
    sourceColoring
  let targetCommon := secondDeletionCommonCoreColoring
    (first := source.firstVertex) (second := source.secondVertex)
    targetColoring
  ∃ vertex, ¬ ∃ first second : Color,
    ∀ edge, vertex ∈ (edge.1 : Sym2
        {vertex : V |
          vertex ≠ source.firstVertex ∧
          vertex ≠ source.secondVertex ∧
          vertex ≠ target.firstVertex ∧
          vertex ≠ target.secondVertex}) →
      targetCommon edge = Equiv.swap first second (sourceCommon edge)

/-- A different representative of the first deletion's Kempe orbit agrees
literally with the target colouring on the common core. -/
def HasStrictCommonCoreRepair
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) : Prop :=
  ∃ repaired,
    repaired ∈ (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeKempeClosure sourceColoring ∧
    firstDeletionCommonCoreColoring
        (third := target.firstVertex) (fourth := target.secondVertex)
        repaired =
      secondDeletionCommonCoreColoring
        (first := source.firstVertex) (second := source.secondVertex)
        targetColoring ∧
    repaired ≠ sourceColoring

/-- **Common-core disagreement residue.**  A literal disagreement between
two adjacent-pair deletion colourings forces a non-transposition branching
vertex, a Kempe component reaching the exposed pair, or a strict Kempe-orbit
repair that removes this particular disagreement. -/
theorem branching_or_reachesSecondPair_or_strictRepair
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (hdisagrees :
      firstDeletionCommonCoreColoring
          (third := target.firstVertex) (fourth := target.secondVertex)
          sourceColoring ≠
        secondDeletionCommonCoreColoring
          (first := source.firstVertex) (second := source.secondVertex)
          targetColoring) :
    HasCommonCoreBranchingDiscrepancy source target
        sourceColoring targetColoring ∨
      FirstOrbitReachesSecondPair source target sourceColoring ∨
      HasStrictCommonCoreRepair source target sourceColoring targetColoring := by
  let sourceCommon := firstDeletionCommonCoreColoring
    (third := target.firstVertex) (fourth := target.secondVertex)
    sourceColoring
  let targetCommon := secondDeletionCommonCoreColoring
    (first := source.firstVertex) (second := source.secondVertex)
    targetColoring
  by_cases hreachable : targetCommon ∈
      (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex).EdgeKempeClosure sourceCommon
  · rcases firstOrbitReachesSecondPair_or_exists_liftedColoring
      source target sourceColoring targetCommon hreachable with
      hboundary | ⟨repaired, hrepaired, hrestriction⟩
    · exact Or.inr (Or.inl hboundary)
    · right
      right
      refine ⟨repaired, hrepaired, hrestriction, ?_⟩
      intro heq
      subst repaired
      exact hdisagrees hrestriction
  · left
    exact exists_not_locallySwapRelated_of_not_mem_edgeKempeClosure
      sourceCommon targetCommon hreachable

end

end GoertzelV24AdjacentPairCommonCoreDisagreementResidue

end Mettapedia.GraphTheory.FourColor
