import Mettapedia.GraphTheory.FourColor.SeparatedDeletionFusion
import Mettapedia.GraphTheory.FourColor.DeletionOrbitCompatibility

/-!
# Disagreement minima independent of the initial Kempe orbits

Minimize over all proper nonzero colourings of both deletion graphs.
This is stronger than minimizing over two chosen Kempe orbits: changing
either orbit, or both at once, cannot improve the constructed minimum.

On separated deletions of a least counterexample the minimum is positive.
The existing wrong-edge blocker proof then supplies the branching-or-fusion
alternative at these same absolute minimizers. The final ordered-row
statement supplies both the separated pair and the colourings. It does not
claim that the remaining geometric alternative is impossible.
-/

namespace Mettapedia.GraphTheory.FourColor.DeletionAbsoluteMinimum

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24LocalSwapKempeGeneration GoertzelV24KempeComponentEmbeddingBoundary
open KempeTargetFusion

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section
universe u v w

section Generic
variable {A : Type u} {B : Type v} {D : Type w}
  [Fintype A] [DecidableEq A] {G : SimpleGraph A} [DecidableRel G.Adj]
  {H : SimpleGraph B} {J : SimpleGraph D}

/-- A joint minimum over all Tait colourings, with no prescribed orbits. -/
structure AbsoluteMinimum (le : G ↪g H) (re : G ↪g J)
    (left : H.EdgeColoring Color) (right : J.EdgeColoring Color) : Prop where
  left_tait : IsTaitEdgeColoring H left
  right_tait : IsTaitEdgeColoring J right
  minimal : ∀ (nextLeft : H.EdgeColoring Color) (nextRight : J.EdgeColoring Color),
    IsTaitEdgeColoring H nextLeft → IsTaitEdgeColoring J nextRight →
      (disagreementEdges (left.pullbackEmbedding le) (right.pullbackEmbedding re)).card ≤
      (disagreementEdges (nextLeft.pullbackEmbedding le) (nextRight.pullbackEmbedding re)).card

omit [DecidableEq A] in
/-- The input colourings witness only nonemptiness. The output is optimal
across every orbit, not necessarily reachable from either input. -/
theorem exists_absolute_minimum (le : G ↪g H) (re : G ↪g J)
    (leftBase : H.EdgeColoring Color) (rightBase : J.EdgeColoring Color)
    (hl : IsTaitEdgeColoring H leftBase) (hr : IsTaitEdgeColoring J rightBase) :
    ∃ left right, AbsoluteMinimum le re left right := by
  classical
  let P : Nat → Prop := fun n => ∃ left : H.EdgeColoring Color,
    ∃ right : J.EdgeColoring Color, IsTaitEdgeColoring H left ∧ IsTaitEdgeColoring J right ∧
      (disagreementEdges (left.pullbackEmbedding le) (right.pullbackEmbedding re)).card = n
  have hp : ∃ n, P n := ⟨_, leftBase, rightBase, hl, hr, rfl⟩
  obtain ⟨left, right, hleft, hright, hmeasure⟩ := Nat.find_spec hp
  refine ⟨left, right, hleft, hright, ?_⟩
  intro nextLeft nextRight hnl hnr
  rw [hmeasure]
  exact Nat.find_min' hp ⟨nextLeft, nextRight, hnl, hnr, rfl⟩

omit [DecidableEq A] in
/-- The absolute minimum supplies both one-sided orbit minima needed by
the already verified wrong-edge / correct-edge blocker construction. -/
theorem AbsoluteMinimum.orbit_minima {le : G ↪g H} {re : G ↪g J}
    {left : H.EdgeColoring Color} {right : J.EdgeColoring Color}
    (h : AbsoluteMinimum le re left right) :
    MinimumAt left le (right.pullbackEmbedding re) left ∧
    MinimumAt right re (left.pullbackEmbedding le) right := by
  constructor
  · exact ⟨.refl, fun next hn => h.minimal next right
      (isTaitEdgeColoring_of_taitKempeReachable h.left_tait hn) h.right_tait⟩
  · refine ⟨.refl, fun next hn => ?_⟩
    rw [disagreementEdges_symm (right.pullbackEmbedding re),
      disagreementEdges_symm (next.pullbackEmbedding re)]
    exact h.minimal left next h.left_tait
      (isTaitEdgeColoring_of_taitKempeReachable h.right_tait hn)

end Generic

open GoertzelV24AdjacentPairBoundary GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairCommonCoreDisagreementResidue
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24TwoEdgeCutMinimality GoertzelV24RotationMultigraphAdapter
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites GoertzelV24OrderedMeshColoringAtlas
open SeparatedPairDeletion SeparatedOrderedMeshSites

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The rooted alternative at an absolute minimum of the actual deletions. -/
def AbsoluteObstruction (source target : AdjacentPairData G) : Prop :=
  let le := deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
    target.firstVertex target.secondVertex
  let re := deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex source.secondVertex
    target.firstVertex target.secondVertex
  ∃ left right, AbsoluteMinimum le re left right ∧
    (∃ seed, left.pullbackEmbedding le seed ≠ right.pullbackEmbedding re seed) ∧
    (HasCommonCoreBranchingDiscrepancy source target left right ∨
      ∀ seed, left.pullbackEmbedding le seed ≠ right.pullbackEmbedding re seed →
        SeedBlockingFusion left le (right.pullbackEmbedding re) seed ∧
        SeedBlockingFusion right re (left.pullbackEmbedding le) seed)

/-- Positivity follows from actual ambient noncolourability, not from a
bad choice of Kempe orbits. The same minimizing representatives carry the
rooted alternative. -/
theorem absoluteObstruction_of_separated (source target : AdjacentPairData G)
    (leftBase : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).EdgeColoring Color)
    (rightBase : (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex).EdgeColoring Color)
    (hl : IsTaitEdgeColoring _ leftBase) (hr : IsTaitEdgeColoring _ rightBase)
    (rotation : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (sep : Separated source target) : AbsoluteObstruction source target := by
  let le := deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
    target.firstVertex target.secondVertex
  let re := deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex source.secondVertex
    target.firstVertex target.secondVertex
  obtain ⟨left, right, h⟩ := exists_absolute_minimum le re leftBase rightBase hl hr
  have hne := not_commonCore_eq_of_minimal source target left right
    h.left_tait h.right_tait rotation minimal sep
  refine ⟨left, right, h, ?_, ?_⟩
  · by_contra hn
    push Not at hn
    exact hne (DFunLike.ext _ _ hn)
  · by_cases localRel : LocallySwapRelated (left.pullbackEmbedding le) (right.pullbackEmbedding re)
    · right
      intro seed hseed
      exact ⟨seedBlockingFusion_of_minimum_of_local left left le _ h.left_tait
          (isTaitEdgeColoring_pullbackEmbedding right re h.right_tait)
          h.orbit_minima.1 localRel seed hseed,
        seedBlockingFusion_of_minimum_of_local right right re _ h.right_tait
          (isTaitEdgeColoring_pullbackEmbedding left le h.left_tait)
          h.orbit_minima.2 (locallySwapRelated_symm localRel) seed hseed.symm⟩
    · exact Or.inl (Classical.not_forall.mp localRel)

/-- A colourable ambient graph has zero disagreement at every absolute
minimum, independently of the chosen deletion orbits. -/
theorem absolute_minimum_eq_of_tait (source target : AdjacentPairData G)
    {left : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).EdgeColoring Color}
    {right : (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex).EdgeColoring Color}
    (h : AbsoluteMinimum
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex)
      (deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex) left right)
    (c : G.EdgeColoring Color) (hc : IsTaitEdgeColoring G c) :
    firstDeletionCommonCoreColoring (third := target.firstVertex) (fourth := target.secondVertex) left =
      secondDeletionCommonCoreColoring (first := source.firstVertex) (second := source.secondVertex) right := by
  have bound := h.minimal (c.pullbackEmbedding (retainedGraphEmbedding source))
    (c.pullbackEmbedding (retainedGraphEmbedding target))
    (isTaitEdgeColoring_pullbackEmbedding c _ hc) (isTaitEdgeColoring_pullbackEmbedding c _ hc)
  have same := DeletionOrbitCompatibility.common_restrictions_eq source target c
  change firstDeletionCommonCoreColoring _ = secondDeletionCommonCoreColoring _ at same
  change (disagreementEdges (firstDeletionCommonCoreColoring left)
    (secondDeletionCommonCoreColoring right)).card ≤
      (disagreementEdges (firstDeletionCommonCoreColoring _)
        (secondDeletionCommonCoreColoring _)).card at bound
  rw [same] at bound
  have hempty : disagreementEdges (firstDeletionCommonCoreColoring left)
      (secondDeletionCommonCoreColoring right) = ∅ := by
    apply Finset.card_eq_zero.mp
    apply Nat.eq_zero_of_le_zero
    simpa only [disagreementEdges, ne_self_iff_false, Finset.filter_false,
      Finset.card_empty] using bound
  apply DFunLike.ext _ _
  intro e
  by_contra hn
  have hm : e ∈ disagreementEdges (firstDeletionCommonCoreColoring left)
      (secondDeletionCommonCoreColoring right) := (mem_disagreementEdges _ _ e).mpr hn
  rw [hempty] at hm
  exact Finset.notMem_empty e hm

theorem absolute_minimum_eq_iff_taitColorable (source target : AdjacentPairData G)
    {left : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).EdgeColoring Color}
    {right : (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex).EdgeColoring Color}
    (h : AbsoluteMinimum
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex)
      (deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex) left right)
    (sep : Separated source target) :
    (firstDeletionCommonCoreColoring (third := target.firstVertex) (fourth := target.secondVertex) left =
      secondDeletionCommonCoreColoring (first := source.firstVertex) (second := source.secondVertex) right) ↔
    ∃ c : G.EdgeColoring Color, IsTaitEdgeColoring G c := by
  constructor
  · intro agree
    obtain ⟨c, hc, _, _⟩ := DeletionOrbitCompatibility.exists_extension_of_agreement
      source target left right h.left_tait h.right_tait sep agree
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact absolute_minimum_eq_of_tait source target h c hc

/-- The absolute obstruction is supplied on every sufficiently long ordered
row. Neither a choice of colouring nor a choice of Kempe orbit is an input. -/
theorem exists_rowSite_with_absolute_obstruction
    (rotation : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {a n : Nat}
    (ordered : OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a (n + 1))
    (row : Fin a) (source : Fin n) (hlarge : 64 < n) :
    ∃ target : Fin n, source ≠ target ∧
      AbsoluteObstruction (siteData rotation minimal ordered row source)
        (siteData rotation minimal ordered row target) := by
  obtain ⟨target, hne, sep⟩ := exists_separated_rowSite rotation minimal ordered row source hlarge
  let left := selectedGlobalKempeSite rotation minimal ordered (globalRowStep rotation ordered row source)
  let right := selectedGlobalKempeSite rotation minimal ordered (globalRowStep rotation ordered row target)
  exact ⟨target, hne, absoluteObstruction_of_separated _ _ left.base right.base
    left.baseTait right.baseTait rotation minimal sep⟩

end
end Mettapedia.GraphTheory.FourColor.DeletionAbsoluteMinimum
