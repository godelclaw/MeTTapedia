import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentJunctionNormalForm
import Mettapedia.GraphTheory.FourColor.GoertzelV24LineGraphOpenPrimalLift

set_option autoImplicit false

namespace SimpleGraph.Coloring

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Forget the selected-subgraph subtype on a bicolored walk. -/
def bicoloredAmbientWalk
    (C : G.EdgeColoring Mettapedia.GraphTheory.FourColor.Color)
    (first second : Mettapedia.GraphTheory.FourColor.Color)
    {source target : C.bicoloredSet first second}
    (walk : (C.bicoloredSubgraph first second).Walk source target) :
    G.lineGraph.Walk source.1 target.1 :=
  walk.map
    (SimpleGraph.Embedding.induce
      (G := G.lineGraph) (C.bicoloredSet first second)).toHom

@[simp] theorem bicoloredAmbientWalk_length
    (C : G.EdgeColoring Mettapedia.GraphTheory.FourColor.Color)
    (first second : Mettapedia.GraphTheory.FourColor.Color)
    {source target : C.bicoloredSet first second}
    (walk : (C.bicoloredSubgraph first second).Walk source target) :
    (C.bicoloredAmbientWalk first second walk).length = walk.length := by
  exact walk.length_map _

theorem bicoloredAmbientWalk_isPath
    (C : G.EdgeColoring Mettapedia.GraphTheory.FourColor.Color)
    (first second : Mettapedia.GraphTheory.FourColor.Color)
    {source target : C.bicoloredSet first second}
    (walk : (C.bicoloredSubgraph first second).Walk source target)
    (isPath : walk.IsPath) :
    (C.bicoloredAmbientWalk first second walk).IsPath := by
  apply SimpleGraph.Walk.map_isPath_of_injective Subtype.val_injective
  exact isPath

theorem mem_bicoloredAmbientWalk_support_iff
    (C : G.EdgeColoring Mettapedia.GraphTheory.FourColor.Color)
    (first second : Mettapedia.GraphTheory.FourColor.Color)
    {source target : C.bicoloredSet first second}
    (walk : (C.bicoloredSubgraph first second).Walk source target)
    (edge : G.edgeSet) :
    edge ∈ (C.bicoloredAmbientWalk first second walk).support ↔
      edge ∈ C.bicoloredWalkUnderlyingSupport first second walk := by
  exact C.mem_support_map_bicoloredWalk_iff first second walk edge

/-- Every simple bicolored ambient path is internally primal-coherent. -/
theorem bicoloredAmbientWalk_isPrimalCoherent
    (C : G.EdgeColoring Mettapedia.GraphTheory.FourColor.Color)
    (first second : Mettapedia.GraphTheory.FourColor.Color)
    {source target : C.bicoloredSet first second}
    (walk : (C.bicoloredSubgraph first second).Walk source target)
    (isPath : walk.IsPath) :
    (C.bicoloredAmbientWalk first second walk).IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := first) (b := second)
    (walk := C.bicoloredAmbientWalk first second walk)
    (hpath := C.bicoloredAmbientWalk_isPath first second walk isPath)
    (hcolors := by
      intro edge edge_mem
      rcases (C.mem_bicoloredAmbientWalk_support_iff
          first second walk edge).1 edge_mem with
        ⟨selected, _⟩
      exact selected)
    (position := position) hposition

end SimpleGraph.Coloring

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- The first common site along one of two paths ending at a common vertex. -/
structure LeftmostCommonPrefixSplice
    {firstStart secondStart common : V}
    (first : G.Walk firstStart common)
    (second : G.Walk secondStart common) where
  site : V
  site_mem_first : site ∈ first.support
  site_mem_second : site ∈ second.support
  leftmost : ∀ vertex : V,
    vertex ∈ (first.takeUntil site site_mem_first).support →
      vertex ∈ second.support →
        vertex = site

namespace LeftmostCommonPrefixSplice

variable {firstStart secondStart common : V}
  {first : G.Walk firstStart common}
  {second : G.Walk secondStart common}

/-- The first path stopped at the first common site. -/
def firstPrefix (splice : LeftmostCommonPrefixSplice first second) :
    G.Walk firstStart splice.site :=
  first.takeUntil splice.site splice.site_mem_first

/-- The second path stopped at the same site. -/
def secondPrefix (splice : LeftmostCommonPrefixSplice first second) :
    G.Walk secondStart splice.site :=
  second.takeUntil splice.site splice.site_mem_second

/-- Enter along the first prefix and leave along the reversed second prefix. -/
def walk (splice : LeftmostCommonPrefixSplice first second) :
    G.Walk firstStart secondStart :=
  splice.firstPrefix.append splice.secondPrefix.reverse

theorem firstPrefix_isPath
    (splice : LeftmostCommonPrefixSplice first second)
    (first_isPath : first.IsPath) : splice.firstPrefix.IsPath :=
  first_isPath.takeUntil splice.site_mem_first

theorem secondPrefix_isPath
    (splice : LeftmostCommonPrefixSplice first second)
    (second_isPath : second.IsPath) : splice.secondPrefix.IsPath :=
  second_isPath.takeUntil splice.site_mem_second

theorem firstPrefix_support_subset
    (splice : LeftmostCommonPrefixSplice first second) :
    splice.firstPrefix.support ⊆ first.support :=
  first.support_takeUntil_subset_support splice.site_mem_first

theorem secondPrefix_support_subset
    (splice : LeftmostCommonPrefixSplice first second) :
    splice.secondPrefix.support ⊆ second.support :=
  second.support_takeUntil_subset_support splice.site_mem_second

/-- Leftmost intersection makes the prefix splice simple. -/
theorem walk_isPath
    (splice : LeftmostCommonPrefixSplice first second)
    (first_isPath : first.IsPath) (second_isPath : second.IsPath) :
    splice.walk.IsPath := by
  let firstPrefix := splice.firstPrefix
  let secondReverse := splice.secondPrefix.reverse
  have firstPrefix_isPath : firstPrefix.IsPath :=
    splice.firstPrefix_isPath first_isPath
  have secondReverse_isPath : secondReverse.IsPath :=
    (splice.secondPrefix_isPath second_isPath).reverse
  have site_not_mem_second_tail : splice.site ∉ secondReverse.support.tail := by
    have nodup := secondReverse_isPath.support_nodup
    rw [← secondReverse.cons_tail_support] at nodup
    exact (List.nodup_cons.mp nodup).1
  have disjoint :
      firstPrefix.support.Disjoint secondReverse.support.tail := by
    rw [List.disjoint_left]
    intro vertex vertex_mem_first vertex_mem_second_tail
    have vertex_mem_second_reverse : vertex ∈ secondReverse.support :=
      List.mem_of_mem_tail vertex_mem_second_tail
    have vertex_mem_second_prefix : vertex ∈ splice.secondPrefix.support := by
      simpa only [secondReverse, SimpleGraph.Walk.support_reverse,
        List.mem_reverse] using vertex_mem_second_reverse
    have vertex_mem_second : vertex ∈ second.support :=
      splice.secondPrefix_support_subset vertex_mem_second_prefix
    have vertex_eq : vertex = splice.site :=
      splice.leftmost vertex vertex_mem_first vertex_mem_second
    exact site_not_mem_second_tail (vertex_eq ▸ vertex_mem_second_tail)
  rw [LeftmostCommonPrefixSplice.walk,
    SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    List.nodup_append']
  exact ⟨firstPrefix_isPath.support_nodup,
    secondReverse_isPath.support_nodup.tail, disjoint⟩

end LeftmostCommonPrefixSplice

/-- Two paths with a common endpoint have a canonical first-intersection
prefix splice. -/
theorem nonempty_leftmostCommonPrefixSplice
    {firstStart secondStart common : V}
    (first : G.Walk firstStart common)
    (second : G.Walk secondStart common) :
    Nonempty (LeftmostCommonPrefixSplice first second) := by
  let sites : List V :=
    first.support.filter fun vertex ↦ vertex ∈ second.support
  have common_mem_sites : common ∈ sites := by
    simp only [sites, List.mem_filter, decide_eq_true_eq]
    exact ⟨first.end_mem_support, second.end_mem_support⟩
  rcases first.exists_mem_support_forall_mem_support_imp_eq
      sites.toFinset (by
        refine ⟨common, ?_⟩
        simp only [Finset.mem_filter, List.mem_toFinset]
        exact ⟨common_mem_sites, first.end_mem_support⟩) with
    ⟨site, site_mem_finset, site_mem_first, leftmost⟩
  have site_mem_sites : site ∈ sites := by
    simpa only [List.mem_toFinset] using site_mem_finset
  have site_mem_both : site ∈ first.support ∧ site ∈ second.support := by
    simpa only [sites, List.mem_filter, decide_eq_true_eq] using site_mem_sites
  refine ⟨{
    site := site
    site_mem_first := site_mem_both.1
    site_mem_second := site_mem_both.2
    leftmost := ?_ }⟩
  intro candidate candidate_mem_prefix candidate_mem_second
  have candidate_mem_first : candidate ∈ first.support :=
    first.support_takeUntil_subset_support site_mem_both.1
      candidate_mem_prefix
  have candidate_mem_sites : candidate ∈ sites := by
    simp only [sites, List.mem_filter, decide_eq_true_eq]
    exact ⟨candidate_mem_first, candidate_mem_second⟩
  have candidate_mem_finset : candidate ∈ sites.toFinset := by
    simpa only [List.mem_toFinset]
  exact leftmost candidate candidate_mem_finset candidate_mem_prefix

omit [DecidableEq V] in
/-- The positive-arm coherent shortcut also covers a degenerate arm: if
one prefix has length zero, the other prefix is already the joined path. -/
theorem exists_isPath_isPrimalCoherent_length_le_of_append_isPath_of_endpoints_ne
    {first middle last : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle last)
    (left_isPath : left.IsPath) (right_isPath : right.IsPath)
    (left_isPrimalCoherent : left.IsPrimalCoherent)
    (right_isPrimalCoherent : right.IsPrimalCoherent)
    (append_isPath : (left.append right).IsPath)
    (endpoints_ne : first ≠ last) :
    ∃ joined : G.lineGraph.Walk first last,
      joined.IsPath ∧ joined.IsPrimalCoherent ∧
        0 < joined.length ∧
        joined.length ≤ (left.append right).length ∧
        joined.support ⊆ (left.append right).support ∧
        (∀ edge ∈ (left.append right).support,
          edge = middle ∨ edge ∈ joined.support) := by
  by_cases left_positive : 0 < left.length
  · by_cases right_positive : 0 < right.length
    · exact exists_isPath_isPrimalCoherent_length_le_of_append_isPath
        left right left_isPath right_isPath
        left_isPrimalCoherent right_isPrimalCoherent
        left_positive right_positive append_isPath
    · refine ⟨left.append right, append_isPath, ?_, ?_, le_rfl,
        fun _ edge_mem ↦ edge_mem,
        fun _ edge_mem ↦ Or.inr edge_mem⟩
      · apply left_isPrimalCoherent.append right_isPrimalCoherent
        intro _ right_positive'
        exact (right_positive right_positive').elim
      · exact SimpleGraph.Walk.not_nil_iff_lt_length.mp
          (SimpleGraph.Walk.not_nil_of_ne endpoints_ne)
  · refine ⟨left.append right, append_isPath, ?_, ?_, le_rfl,
      fun _ edge_mem ↦ edge_mem,
      fun _ edge_mem ↦ Or.inr edge_mem⟩
    · apply left_isPrimalCoherent.append right_isPrimalCoherent
      intro left_positive' _
      exact (left_positive left_positive').elim
    · exact SimpleGraph.Walk.not_nil_iff_lt_length.mp
        (SimpleGraph.Walk.not_nil_of_ne endpoints_ne)

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CorridorPumping
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {start : sourceNormal.KempeOrbitAdjacentEscape}

namespace CompanionCrossPairJunctionNormalForm

variable (normal : CompanionCrossPairJunctionNormalForm collar start)

/-- The return root and the selected launch edge are distinct component
vertices. -/
theorem rootEdge_ne_launchEdge : normal.rootEdge ≠ normal.launchEdge := by
  intro edge_eq
  apply normal.root_not_mem_selectedComponent
  change normal.rootEdge ∈
    normal.sourceState.coloring.kempeComponentSet
      (crossFaceZeroColor normal.step.firstHit.transfer.coordinate)
      normal.step.reentry.realization.companion
      normal.step.reentry.realization.component
  rw [edge_eq]
  exact normal.launchEdge_mem_selectedComponent

/-- A coherent simple line-graph fusion path from the fixed return root to
the cross-pair launch edge. -/
structure FusedLinePath where
  path :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).lineGraph.Walk
        normal.rootEdge normal.launchEdge
  isPath : path.IsPath
  isPrimalCoherent : path.IsPrimalCoherent
  positive : 0 < path.length

/-- The two canonical bicolored junction paths splice, and the open
coherent-shortcut lemma repairs their sole possible primal seam. -/
theorem nonempty_fusedLinePath : Nonempty normal.FusedLinePath := by
  let coloring := normal.canonicalState.coloring
  let fixed := normal.returnData.lastOverlap.overlap.fixedColor
  let outer := normal.returnData.lastOverlap.overlap.breakOuterColor
  let first := crossFaceZeroColor normal.step.firstHit.transfer.coordinate
  let second := normal.step.reentry.realization.companion
  rcases normal.exists_returnPath_to_junction with
    ⟨rootSelected, returnJunctionSelected, returnPath,
      returnPath_isPath, _returnPath_positive⟩
  rcases normal.exists_selectedPath_to_junction with
    ⟨launchSelected, selectedJunctionSelected, selectedPath,
      selectedPath_isPath⟩
  let returnAmbient :=
    coloring.bicoloredAmbientWalk fixed outer returnPath
  let selectedAmbient :=
    coloring.bicoloredAmbientWalk first second selectedPath
  have returnAmbient_isPath : returnAmbient.IsPath :=
    coloring.bicoloredAmbientWalk_isPath
      fixed outer returnPath returnPath_isPath
  have selectedAmbient_isPath : selectedAmbient.IsPath :=
    coloring.bicoloredAmbientWalk_isPath
      first second selectedPath selectedPath_isPath
  rcases SimpleGraph.Walk.nonempty_leftmostCommonPrefixSplice
      returnAmbient selectedAmbient with ⟨splice⟩
  have firstPrefix_isPath : splice.firstPrefix.IsPath :=
    splice.firstPrefix_isPath returnAmbient_isPath
  have secondPrefixReverse_isPath : splice.secondPrefix.reverse.IsPath :=
    (splice.secondPrefix_isPath selectedAmbient_isPath).reverse
  have firstPrefix_isPrimalCoherent :
      splice.firstPrefix.IsPrimalCoherent := by
    intro position hposition
    apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
      (C := coloring) (a := fixed) (b := outer)
      (walk := splice.firstPrefix)
      (hpath := firstPrefix_isPath)
      (hcolors := by
        intro edge edge_mem
        have ambient_mem : edge ∈ returnAmbient.support :=
          splice.firstPrefix_support_subset edge_mem
        rcases (coloring.mem_bicoloredAmbientWalk_support_iff
            fixed outer returnPath edge).1 (by
              simpa only [returnAmbient] using ambient_mem) with
          ⟨selected, _⟩
        exact selected)
      (position := position) hposition
  have secondPrefixReverse_isPrimalCoherent :
      splice.secondPrefix.reverse.IsPrimalCoherent := by
    intro position hposition
    apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
      (C := coloring) (a := first) (b := second)
      (walk := splice.secondPrefix.reverse)
      (hpath := secondPrefixReverse_isPath)
      (hcolors := by
        intro edge edge_mem
        have prefix_mem : edge ∈ splice.secondPrefix.support := by
          simpa only [SimpleGraph.Walk.support_reverse,
            List.mem_reverse] using edge_mem
        have ambient_mem : edge ∈ selectedAmbient.support :=
          splice.secondPrefix_support_subset prefix_mem
        rcases (coloring.mem_bicoloredAmbientWalk_support_iff
            first second selectedPath edge).1 (by
              simpa only [selectedAmbient] using ambient_mem) with
          ⟨selected, _⟩
        exact selected)
      (position := position) hposition
  have splice_isPath : splice.walk.IsPath :=
    splice.walk_isPath returnAmbient_isPath selectedAmbient_isPath
  rcases
      SimpleGraph.Walk.exists_isPath_isPrimalCoherent_length_le_of_append_isPath_of_endpoints_ne
        splice.firstPrefix splice.secondPrefix.reverse
        firstPrefix_isPath secondPrefixReverse_isPath
        firstPrefix_isPrimalCoherent secondPrefixReverse_isPrimalCoherent
        splice_isPath normal.rootEdge_ne_launchEdge with
    ⟨joined, joined_isPath, joined_isPrimalCoherent,
      joined_positive, _joined_length, _joined_support, _joined_coverage⟩
  exact ⟨⟨joined, joined_isPath, joined_isPrimalCoherent,
    joined_positive⟩⟩

end CompanionCrossPairJunctionNormalForm

/-- A normalized cross-pair junction together with its coherent fusion
path. -/
structure CompanionCrossPairFusionLinePath
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  normal : CompanionCrossPairJunctionNormalForm collar start
  fused : normal.FusedLinePath

/-- Package the path produced by a normalized junction for downstream
fusion and primal-lift arguments. -/
theorem CompanionCrossPairJunctionNormalForm.nonempty_crossPairFusionLinePath
    (normal : CompanionCrossPairJunctionNormalForm collar start) :
    Nonempty (CompanionCrossPairFusionLinePath collar start) := by
  rcases normal.nonempty_fusedLinePath with ⟨fused⟩
  exact ⟨⟨normal, fused⟩⟩

/-- A closed companion circuit has only local cancellation, a coherent
cross-pair fusion path, a shared-edge pivot, or full three-pair monodromy. -/
theorem closedCircuit_exists_localCancellation_or_fusionLinePath_or_edgePivot_or_threePairMonodromy
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    Nonempty (CompanionCanonicalComponentDisjointClosure collar start) ∨
      Nonempty (CompanionCrossPairFusionLinePath collar start) ∨
        Nonempty (CompanionSameOuterTargetAvoidingEdgePivot collar start) ∨
          Nonempty (CompanionThreePairMonodromy collar start) := by
  rcases
      closedCircuit_exists_localCancellation_or_crossPairJunction_or_edgePivot_or_threePairMonodromy
        closed with cancellation | junction | pivot | monodromy
  · exact Or.inl cancellation
  · rcases junction with ⟨normal⟩
    exact Or.inr (Or.inl normal.nonempty_crossPairFusionLinePath)
  · exact Or.inr (Or.inr (Or.inl pivot))
  · exact Or.inr (Or.inr (Or.inr monodromy))

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
