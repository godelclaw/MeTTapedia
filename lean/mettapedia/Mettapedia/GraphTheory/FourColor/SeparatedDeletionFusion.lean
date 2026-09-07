import Mettapedia.GraphTheory.FourColor.KempeTargetFusion
import Mettapedia.GraphTheory.FourColor.SeparatedOrderedMeshSites

/-!
# Target-directed fusion at supplied separated deletion sites

The two separated deletions cannot admit Tait colourings agreeing on the
common core.  Thus a common-core sequence aimed at the other deletion's
restriction cannot lift to completion.  It supplies a genuinely fusing step
after an exactly lifted prefix, with the intended target still reachable
after that step.  The alternative that the target is not Kempe-reachable is
retained, along with its existing local non-transposition discrepancy.

The fusion has an ambient bicoloured walk through an edge at the second
deleted pair.  Neither that walk nor its endpoints are asserted to reach the
first pair; remote anchoring and physical reduction remain open.
-/

namespace Mettapedia.GraphTheory.FourColor.SeparatedDeletionFusion

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24AdjacentPairBoundary GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairCommonCoreDisagreementResidue
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24KempeComponentEmbeddingBoundary GoertzelV24LocalSwapKempeGeneration
open GoertzelV24TwoEdgeCutMinimality GoertzelV24RotationMultigraphAdapter
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open SeparatedPairDeletion SeparatedOrderedMeshSites KempeEmbeddingFusion KempeTargetFusion

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

abbrev RepairFusion (source target : AdjacentPairData G)
    (sourceColor : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColor : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) : Prop :=
  TargetFusion sourceColor
    (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex)
    (secondDeletionCommonCoreColoring (first := source.firstVertex)
      (second := source.secondVertex) targetColor)

/-- At separated sites a target-reaching common-core sequence has an actual
failed single-switch lift.  A completed lift would glue to an ambient Tait
colouring and contradict minimality. -/
theorem repairFusion_of_reachable
    (source target : AdjacentPairData G)
    (sourceColor : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColor : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (hsource : IsTaitEdgeColoring _ sourceColor) (htarget : IsTaitEdgeColoring _ targetColor)
    (rotation : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hsep : Separated source target)
    (hreach : TaitKempeReachable
      (firstDeletionCommonCoreColoring (third := target.firstVertex)
        (fourth := target.secondVertex) sourceColor)
      (secondDeletionCommonCoreColoring (first := source.firstVertex)
        (second := source.secondVertex) targetColor)) :
    RepairFusion source target sourceColor targetColor := by
  rcases targetFusion_or_lifted sourceColor
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex) _ hreach with hf | ⟨current, hpref, heq⟩
  · exact hf
  · exact False.elim (not_commonCore_eq_of_minimal source target current targetColor
      (hpref.isTait hsource) htarget rotation minimal hsep heq)

/-- No reachability is assumed: the two alternatives record either its actual
failure (and the branching discrepancy), or a target-directed fusion. -/
theorem nonreachable_or_repairFusion
    (source target : AdjacentPairData G)
    (sourceColor : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColor : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (hsource : IsTaitEdgeColoring _ sourceColor) (htarget : IsTaitEdgeColoring _ targetColor)
    (rotation : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hsep : Separated source target) :
    (¬ TaitKempeReachable
      (firstDeletionCommonCoreColoring (third := target.firstVertex)
        (fourth := target.secondVertex) sourceColor)
      (secondDeletionCommonCoreColoring (first := source.firstVertex)
        (second := source.secondVertex) targetColor)) ∧
        HasCommonCoreBranchingDiscrepancy source target sourceColor targetColor ∨
      RepairFusion source target sourceColor targetColor := by
  by_cases hreach : TaitKempeReachable
      (firstDeletionCommonCoreColoring (third := target.firstVertex)
        (fourth := target.secondVertex) sourceColor)
      (secondDeletionCommonCoreColoring (first := source.firstVertex)
        (second := source.secondVertex) targetColor)
  · exact Or.inr (repairFusion_of_reachable source target sourceColor targetColor
      hsource htarget rotation minimal hsep hreach)
  · exact Or.inl ⟨hreach, exists_not_locallySwapRelated_of_not_taitKempeReachable _ _
      (isTaitEdgeColoring_firstDeletionCommonCoreColoring sourceColor hsource)
      (isTaitEdgeColoring_secondDeletionCommonCoreColoring targetColor htarget) hreach⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- A fusion walk connects distinct common-core components and includes an
edge incident to the second deleted pair.  It need not meet the first pair. -/
theorem physical_walk_of_fusion
    (source target : AdjacentPairData G)
    (coloring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (first second : Color)
    (K : ((firstDeletionCommonCoreColoring (third := target.firstVertex)
      (fourth := target.secondVertex) coloring).bicoloredSubgraph first second).ConnectedComponent)
    (h : ComponentFuses coloring
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex) first second K) :
    let embedding := deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex
    let f := bicoloredSubgraphEmbedding coloring embedding first second
    ∃ x y, x ∈ K ∧ y ∉ K ∧
      ∃ p : (coloring.bicoloredSubgraph first second).Walk (f x) (f y),
        ∃ z ∈ p.support,
          (¬ ∃ edge, embedding.mapEdgeSet edge = z.val) ∧
          ∃ endpoint : retainedVertexSet source.firstVertex source.secondVertex,
            endpoint ∈ (z.val.val : Sym2 (retainedVertexSet source.firstVertex source.secondVertex)) ∧
            (endpoint.val = target.firstVertex ∨ endpoint.val = target.secondVertex) := by
  dsimp only
  obtain ⟨x, y, hx, hy, p, z, hz, hn⟩ := exists_fusion_walk _ K h
  have hout := not_edge_in_range_of_not_selected_in_range coloring
    (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex) first second z hn
  exact ⟨x, y, hx, hy, p, z, hz, hout,
    exists_endpoint_at_second_pair_of_not_in_firstCommonCore_range source target z.val hout⟩

/-- The separated target is constructed from the actual ordered row, for
every source and every choice of the two proper deletion colourings. -/
theorem exists_rowSite_forcing_nonreachable_or_fusion
    (rotation : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {a n : Nat}
    (ordered : OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a (n + 1))
    (row : Fin a) (source : Fin n) (hlarge : 64 < n) :
    ∃ target : Fin n, source ≠ target ∧
      ∀ sourceColor : (DeletedAdjacentPairGraph G
          (siteData rotation minimal ordered row source).firstVertex
          (siteData rotation minimal ordered row source).secondVertex).EdgeColoring Color,
      ∀ targetColor : (DeletedAdjacentPairGraph G
          (siteData rotation minimal ordered row target).firstVertex
          (siteData rotation minimal ordered row target).secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring _ sourceColor → IsTaitEdgeColoring _ targetColor →
          (¬ TaitKempeReachable
            (firstDeletionCommonCoreColoring
              (third := (siteData rotation minimal ordered row target).firstVertex)
              (fourth := (siteData rotation minimal ordered row target).secondVertex) sourceColor)
            (secondDeletionCommonCoreColoring
              (first := (siteData rotation minimal ordered row source).firstVertex)
              (second := (siteData rotation minimal ordered row source).secondVertex) targetColor)) ∧
              HasCommonCoreBranchingDiscrepancy
                (siteData rotation minimal ordered row source)
                (siteData rotation minimal ordered row target) sourceColor targetColor ∨
            RepairFusion (siteData rotation minimal ordered row source)
              (siteData rotation minimal ordered row target) sourceColor targetColor := by
  obtain ⟨target, hne, hsep⟩ := exists_separated_rowSite rotation minimal ordered row source hlarge
  exact ⟨target, hne, fun sourceColor targetColor hs ht =>
    nonreachable_or_repairFusion _ _ sourceColor targetColor hs ht rotation minimal hsep⟩

end
end Mettapedia.GraphTheory.FourColor.SeparatedDeletionFusion

/-! ## Productive, discrepancy-rooted obstruction at a constructed minimum -/

namespace Mettapedia.GraphTheory.FourColor.SeparatedDeletionFusion

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24AdjacentPairBoundary GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairCommonCoreDisagreementResidue
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24KempeComponentEmbeddingBoundary GoertzelV24LocalSwapKempeGeneration
open GoertzelV24TwoEdgeCutMinimality GoertzelV24RotationMultigraphAdapter
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open SeparatedPairDeletion SeparatedOrderedMeshSites KempeEmbeddingFusion KempeTargetFusion

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Constructed output: an orbit minimum with an actual wrong edge, and either
a local branching discrepancy or a correct-edge blocker for every wrong edge.
Neither the minimum nor the discrepancy roots are caller-supplied. -/
def MinimumObstruction (source target : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).EdgeColoring Color)
    (targetColor : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) : Prop :=
  let embedding := deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
    target.firstVertex target.secondVertex
  let desired := secondDeletionCommonCoreColoring (first := source.firstVertex)
    (second := source.secondVertex) targetColor
  ∃ current : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).EdgeColoring Color,
    MinimumAt base embedding desired current ∧ IsTaitEdgeColoring _ current ∧
    (∃ seed, current.pullbackEmbedding embedding seed ≠ desired seed) ∧
    (HasCommonCoreBranchingDiscrepancy source target current targetColor ∨
      ∀ seed, current.pullbackEmbedding embedding seed ≠ desired seed →
        SeedBlockingFusion current embedding desired seed)

/-- Separation forces a nonempty discrepancy even at the orbit minimum.
Local transposition discrepancies then force wrong-to-correct fusion walks;
failure of local transposition is retained as the other explicit alternative. -/
theorem minimumObstruction_of_separated
    (source target : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).EdgeColoring Color)
    (targetColor : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (hbase : IsTaitEdgeColoring _ base) (htarget : IsTaitEdgeColoring _ targetColor)
    (rotation : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hsep : Separated source target) : MinimumObstruction source target base targetColor := by
  let embedding := deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
    target.firstVertex target.secondVertex
  let desired := secondDeletionCommonCoreColoring (first := source.firstVertex)
    (second := source.secondVertex) targetColor
  obtain ⟨current, hmin⟩ := exists_minimum base embedding desired
  have hcurrent := isTaitEdgeColoring_of_taitKempeReachable hbase hmin.1
  have hne := not_commonCore_eq_of_minimal source target current targetColor
    hcurrent htarget rotation minimal hsep
  refine ⟨current, hmin, hcurrent, ?_, ?_⟩
  · by_contra hnone
    push Not at hnone
    exact hne (DFunLike.ext _ _ hnone)
  · by_cases hlocal : LocallySwapRelated (current.pullbackEmbedding embedding) desired
    · exact Or.inr (fun seed hseed => seedBlockingFusion_of_minimum_of_local
        base current embedding desired hbase
        (isTaitEdgeColoring_secondDeletionCommonCoreColoring targetColor htarget)
        hmin hlocal seed hseed)
    · exact Or.inl (Classical.not_forall.mp hlocal)

omit [Fintype V] [DecidableRel G.Adj] in
/-- The wrong-to-correct witness has a walk whose outside-image edge is
incident to the second deletion.  This keeps both discrepancy endpoints. -/
theorem physical_walk_of_seedBlockingFusion
    (source target : AdjacentPairData G)
    (current : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).EdgeColoring Color)
    (desired : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).EdgeColoring Color)
    (seed : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).edgeSet)
    (h : SeedBlockingFusion current
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex) desired seed) :
    let embedding := deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex
    let small := current.pullbackEmbedding embedding
    let first := small seed
    let second := desired seed
    let x : small.bicoloredSet first second := ⟨seed, Or.inl rfl⟩
    let K := (small.bicoloredSubgraph first second).connectedComponentMk x
    let f := bicoloredSubgraphEmbedding current embedding first second
    ∃ y : small.bicoloredSet first second, small y.val = desired y.val ∧ y ∉ K ∧
      ∃ p : (current.bicoloredSubgraph first second).Walk (f x) (f y),
        ∃ z ∈ p.support,
          (¬ ∃ edge, embedding.mapEdgeSet edge = z.val) ∧
          ∃ endpoint : retainedVertexSet source.firstVertex source.secondVertex,
            endpoint ∈ (z.val.val : Sym2 (retainedVertexSet source.firstVertex source.secondVertex)) ∧
            (endpoint.val = target.firstVertex ∨ endpoint.val = target.secondVertex) := by
  obtain ⟨y, hagrees, hy, ⟨p⟩⟩ := h
  dsimp only
  obtain ⟨z, hz, hn⟩ := walk_leaves_range _
    (fun hxy => hy (SimpleGraph.ConnectedComponent.sound hxy).symm) p
  have hout := not_edge_in_range_of_not_selected_in_range current
    (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex) _ _ z hn
  exact ⟨y, hagrees, hy, p, z, hz, hout,
    exists_endpoint_at_second_pair_of_not_in_firstCommonCore_range source target z.val hout⟩

/-- Every source on a sufficiently long ordered row supplies a separated
target and the minimum obstruction for all proper deletion colourings. -/
theorem exists_rowSite_with_minimum_obstruction
    (rotation : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {a n : Nat}
    (ordered : OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a (n + 1))
    (row : Fin a) (source : Fin n) (hlarge : 64 < n) :
    ∃ target : Fin n, source ≠ target ∧
      ∀ sourceColor : (DeletedAdjacentPairGraph G
          (siteData rotation minimal ordered row source).firstVertex
          (siteData rotation minimal ordered row source).secondVertex).EdgeColoring Color,
      ∀ targetColor : (DeletedAdjacentPairGraph G
          (siteData rotation minimal ordered row target).firstVertex
          (siteData rotation minimal ordered row target).secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring _ sourceColor → IsTaitEdgeColoring _ targetColor →
          MinimumObstruction (siteData rotation minimal ordered row source)
            (siteData rotation minimal ordered row target) sourceColor targetColor := by
  obtain ⟨target, hne, hsep⟩ := exists_separated_rowSite rotation minimal ordered row source hlarge
  exact ⟨target, hne, fun sourceColor targetColor hs ht =>
    minimumObstruction_of_separated _ _ sourceColor targetColor hs ht rotation minimal hsep⟩

/-- Simultaneous orbit minima, an actual discrepancy root, and either local
branching or blocking fusions in both deletions rooted at every wrong edge. -/
def JointMinimumObstruction (source target : AdjacentPairData G)
    (leftBase : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (rightBase : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) : Prop :=
  let leftEmbedding := deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
    source.secondVertex target.firstVertex target.secondVertex
  let rightEmbedding := deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex
    source.secondVertex target.firstVertex target.secondVertex
  ∃ left : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).EdgeColoring Color,
    ∃ right : (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex).EdgeColoring Color,
      MinimumAt leftBase leftEmbedding (right.pullbackEmbedding rightEmbedding) left ∧
      MinimumAt rightBase rightEmbedding (left.pullbackEmbedding leftEmbedding) right ∧
      IsTaitEdgeColoring _ left ∧ IsTaitEdgeColoring _ right ∧
      (∃ seed, left.pullbackEmbedding leftEmbedding seed ≠ right.pullbackEmbedding rightEmbedding seed) ∧
      (HasCommonCoreBranchingDiscrepancy source target left right ∨
        ∀ seed, left.pullbackEmbedding leftEmbedding seed ≠ right.pullbackEmbedding rightEmbedding seed →
          SeedBlockingFusion left leftEmbedding (right.pullbackEmbedding rightEmbedding) seed ∧
          SeedBlockingFusion right rightEmbedding (left.pullbackEmbedding leftEmbedding) seed)

/-- Neither minimum is assumed.  Separation rules out agreement for the two
constructed representatives, and local swap symmetry gives blockers on both
sides of each discrepancy root. -/
theorem jointMinimumObstruction_of_separated
    (source target : AdjacentPairData G)
    (leftBase : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (rightBase : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (hleft : IsTaitEdgeColoring _ leftBase) (hright : IsTaitEdgeColoring _ rightBase)
    (rotation : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hsep : Separated source target) : JointMinimumObstruction source target leftBase rightBase := by
  let le := deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
    source.secondVertex target.firstVertex target.secondVertex
  let re := deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex
    source.secondVertex target.firstVertex target.secondVertex
  obtain ⟨left, right, hl, hr⟩ := exists_joint_minimum leftBase rightBase le re
  have hlt := isTaitEdgeColoring_of_taitKempeReachable hleft hl.1
  have hrt := isTaitEdgeColoring_of_taitKempeReachable hright hr.1
  have hne := not_commonCore_eq_of_minimal source target left right hlt hrt rotation minimal hsep
  refine ⟨left, right, hl, hr, hlt, hrt, ?_, ?_⟩
  · by_contra hnone
    push Not at hnone
    exact hne (DFunLike.ext _ _ hnone)
  · by_cases hlocal : LocallySwapRelated (left.pullbackEmbedding le) (right.pullbackEmbedding re)
    · right
      intro seed hseed
      exact ⟨seedBlockingFusion_of_minimum_of_local leftBase left le _ hleft
          (isTaitEdgeColoring_pullbackEmbedding right re hrt) hl hlocal seed hseed,
        seedBlockingFusion_of_minimum_of_local rightBase right re _ hright
          (isTaitEdgeColoring_pullbackEmbedding left le hlt) hr
          (locallySwapRelated_symm hlocal) seed hseed.symm⟩
    · exact Or.inl (Classical.not_forall.mp hlocal)

/-- The two-sided, discrepancy-rooted alternative on an actually supplied
separated pair of row sites.  No Kempe-reachability or minimum input remains. -/
theorem exists_rowSite_with_joint_minimum_obstruction
    (rotation : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {a n : Nat}
    (ordered : OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a (n + 1))
    (row : Fin a) (source : Fin n) (hlarge : 64 < n) :
    ∃ target : Fin n, source ≠ target ∧
      ∀ leftBase : (DeletedAdjacentPairGraph G
          (siteData rotation minimal ordered row source).firstVertex
          (siteData rotation minimal ordered row source).secondVertex).EdgeColoring Color,
      ∀ rightBase : (DeletedAdjacentPairGraph G
          (siteData rotation minimal ordered row target).firstVertex
          (siteData rotation minimal ordered row target).secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring _ leftBase → IsTaitEdgeColoring _ rightBase →
          JointMinimumObstruction (siteData rotation minimal ordered row source)
            (siteData rotation minimal ordered row target) leftBase rightBase := by
  obtain ⟨target, hne, hsep⟩ := exists_separated_rowSite rotation minimal ordered row source hlarge
  exact ⟨target, hne, fun leftBase rightBase hl hr =>
    jointMinimumObstruction_of_separated _ _ leftBase rightBase hl hr rotation minimal hsep⟩

open GoertzelV24OrderedMeshGlobalSites GoertzelV24OrderedMeshColoringAtlas in
/-- Minimality already supplies the two base colourings.  Instantiating them
leaves only the actual ordered row and its length as geometric inputs. -/
theorem exists_selected_joint_minimum_obstruction
    (rotation : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {a n : Nat}
    (ordered : OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a (n + 1))
    (row : Fin a) (source : Fin n) (hlarge : 64 < n) :
    let site := fun column => selectedGlobalKempeSite rotation minimal ordered
      (globalRowStep rotation ordered row column)
    ∃ target : Fin n, source ≠ target ∧
      JointMinimumObstruction (site source).data (site target).data
        (site source).base (site target).base := by
  dsimp only
  obtain ⟨target, hne, h⟩ :=
    exists_rowSite_with_joint_minimum_obstruction rotation minimal ordered row source hlarge
  exact ⟨target, hne, h _ _
    (selectedGlobalKempeSite rotation minimal ordered (globalRowStep rotation ordered row source)).baseTait
    (selectedGlobalKempeSite rotation minimal ordered (globalRowStep rotation ordered row target)).baseTait⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- The companion endpoint fact for the second deletion embedding, keeping
the original common-core coordinate order. -/
theorem endpoint_at_first_pair_of_not_in_second_range
    (source target : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex).edgeSet)
    (hout : ¬ ∃ preimage,
      (deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex).mapEdgeSet preimage = edge) :
    ∃ endpoint : retainedVertexSet target.firstVertex target.secondVertex,
      endpoint ∈ (edge.val : Sym2 (retainedVertexSet target.firstVertex target.secondVertex)) ∧
      (endpoint.val = source.firstVertex ∨ endpoint.val = source.secondVertex) := by
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right =>
      by_cases hl1 : left.val = source.firstVertex
      · exact ⟨left, Sym2.mem_mk_left _ _, Or.inl hl1⟩
      by_cases hl2 : left.val = source.secondVertex
      · exact ⟨left, Sym2.mem_mk_left _ _, Or.inr hl2⟩
      by_cases hr1 : right.val = source.firstVertex
      · exact ⟨right, Sym2.mem_mk_right _ _, Or.inl hr1⟩
      by_cases hr2 : right.val = source.secondVertex
      · exact ⟨right, Sym2.mem_mk_right _ _, Or.inr hr2⟩
      exact False.elim (hout ⟨⟨s(⟨left.val, hl1, hl2, left.property⟩,
        ⟨right.val, hr1, hr2, right.property⟩), hedge⟩, rfl⟩)

omit [Fintype V] [DecidableRel G.Adj] in
/-- The other blocking walk reaches the first deleted pair.  Combined with
the first-deletion walk, the joint minimum gives two differently coloured
walks with the same common-edge root and encounters at opposite deleted pairs.
No disjointness, noose, or bounded-width conclusion is asserted. -/
theorem physical_second_walk_of_seedBlockingFusion
    (source target : AdjacentPairData G)
    (current : (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex).EdgeColoring Color)
    (desired : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).EdgeColoring Color)
    (seed : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).edgeSet)
    (h : SeedBlockingFusion current
      (deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex) desired seed) :
    let embedding := deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex
    let small := current.pullbackEmbedding embedding
    let first := small seed
    let second := desired seed
    let x : small.bicoloredSet first second := ⟨seed, Or.inl rfl⟩
    let K := (small.bicoloredSubgraph first second).connectedComponentMk x
    let f := bicoloredSubgraphEmbedding current embedding first second
    ∃ y : small.bicoloredSet first second, small y.val = desired y.val ∧ y ∉ K ∧
      ∃ p : (current.bicoloredSubgraph first second).Walk (f x) (f y),
        ∃ z ∈ p.support,
          (¬ ∃ edge, embedding.mapEdgeSet edge = z.val) ∧
          ∃ endpoint : retainedVertexSet target.firstVertex target.secondVertex,
            endpoint ∈ (z.val.val : Sym2 (retainedVertexSet target.firstVertex target.secondVertex)) ∧
            (endpoint.val = source.firstVertex ∨ endpoint.val = source.secondVertex) := by
  obtain ⟨y, hagrees, hy, ⟨p⟩⟩ := h
  dsimp only
  obtain ⟨z, hz, hn⟩ := walk_leaves_range _
    (fun hxy => hy (SimpleGraph.ConnectedComponent.sound hxy).symm) p
  have hout := not_edge_in_range_of_not_selected_in_range current
    (deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex) _ _ z hn
  exact ⟨y, hagrees, hy, p, z, hz, hout,
    endpoint_at_first_pair_of_not_in_second_range source target z.val hout⟩

end
end Mettapedia.GraphTheory.FourColor.SeparatedDeletionFusion
