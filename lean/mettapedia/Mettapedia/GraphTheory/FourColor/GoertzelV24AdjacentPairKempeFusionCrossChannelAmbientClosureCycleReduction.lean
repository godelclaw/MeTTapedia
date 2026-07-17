import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureFacePairCompatibility

namespace SimpleGraph.Walk

variable {V : Type*} [DecidableEq V]
  {G : SimpleGraph V} {vertex : V}

/-- A closed walk is unchanged by cycle bypass whenever bypass did not
strictly decrease its length. -/
theorem cycleBypass_eq_self_of_length_le_length_cycleBypass
    (walk : G.Walk vertex vertex)
    (hlength : walk.length ≤ walk.cycleBypass.length) :
    walk.cycleBypass = walk :=
  SimpleGraph.Walk.ext_support <|
    walk.support_cycleBypass_sublist_support.eq_of_length_le <| by
      simpa using hlength

/-- Every nonempty closed trail is either already a simple cycle or cycle
bypass extracts a strictly shorter simple cycle from it. -/
theorem IsTrail.isCycle_or_cycleBypass_length_lt
    {walk : G.Walk vertex vertex}
    (htrail : walk.IsTrail) (hnil : walk ≠ .nil) :
    walk.IsCycle ∨
      (walk.cycleBypass.IsCycle ∧
        walk.cycleBypass.length < walk.length ∧
        walk.cycleBypass.edges ⊆ walk.edges) := by
  by_cases hcycle : walk.IsCycle
  · exact Or.inl hcycle
  · right
    have hbypassCycle : walk.cycleBypass.IsCycle :=
      htrail.isCycle_cycleBypass hnil
    have hlengthNe : walk.cycleBypass.length ≠ walk.length := by
      intro hlength
      apply hcycle
      have hself : walk.cycleBypass = walk :=
        walk.cycleBypass_eq_self_of_length_le_length_cycleBypass (by
          omega)
      exact hself ▸ hbypassCycle
    exact ⟨hbypassCycle,
      lt_of_le_of_ne walk.length_cycleBypass_le_length hlengthNe,
      walk.edges_cycleBypass_subset_edges⟩

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open SimpleGraph

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Simplicity of the first ambient closure reflects back to simplicity of
its retained opposite-port segment. -/
theorem isPath_of_oppositePortClosure_isCycle
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hcycle : (data.oppositePortClosure path).IsCycle) :
    path.IsPath := by
  have hreturn : ¬ data.oppositePortCentralReturn.Nil :=
    SimpleGraph.Walk.not_nil_of_ne
      (data.portVertex_ne (by decide : (2 : Fin 4) ≠ 0))
  have hambient : (data.retainedWalkToAmbient path).IsPath := by
    apply hcycle.isPath_of_append_left hreturn
  exact SimpleGraph.Walk.IsPath.of_map hambient

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Simplicity of the complementary ambient closure likewise reflects to
its retained segment. -/
theorem isPath_of_alternateOppositePortClosure_isCycle
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (hcycle : (data.alternateOppositePortClosure path).IsCycle) :
    path.IsPath := by
  have hreturn :
      ¬ data.alternateOppositePortCentralReturnRetained.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    exact data.portVertex_ne (by decide : (3 : Fin 4) ≠ 1)
  have hambient : (data.retainedWalkToAmbient path).IsPath := by
    apply hcycle.isPath_of_append_left hreturn
  exact SimpleGraph.Walk.IsPath.of_map hambient

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The first ambient closure of an exact cross-central pair is nonempty. -/
theorem CrossCentralExactFaceCutPair.oppositePortClosure_ne_nil
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    data.oppositePortClosure pair.prefixTrail ≠ .nil := by
  intro hnil
  have hcentral :=
    data.centralEdgeValue_mem_oppositePortClosure_edges pair.prefixTrail
  rw [hnil] at hcentral
  simp at hcentral

/-- The complementary ambient closure of an exact cross-central pair is
nonempty. -/
theorem CrossCentralExactFaceCutPair.alternateOppositePortClosure_ne_nil
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    data.alternateOppositePortClosure pair.suffixTrail ≠ .nil := by
  intro hnil
  have hcentral :=
    data.centralEdgeValue_mem_alternateOppositePortClosure_edges
      pair.suffixTrail
  rw [hnil] at hcentral
  simp at hcentral

/-- An exact cross-central pair has a precise descent normal form. If either
ambient closure repeats a vertex, cycle bypass produces a strictly shorter
simple cycle supported on that closure. Otherwise both closures are simple
cycles and their common edge set is exactly the retained cross edge together
with the restored central edge. -/
theorem CrossCentralExactFaceCutPair.cycleDescent_or_exactSimpleCyclePair
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    (((data.oppositePortClosure pair.prefixTrail).cycleBypass.IsCycle ∧
        (data.oppositePortClosure pair.prefixTrail).cycleBypass.length <
          (data.oppositePortClosure pair.prefixTrail).length ∧
        (data.oppositePortClosure pair.prefixTrail).cycleBypass.edges ⊆
          (data.oppositePortClosure pair.prefixTrail).edges) ∨
      ((data.alternateOppositePortClosure
            pair.suffixTrail).cycleBypass.IsCycle ∧
        (data.alternateOppositePortClosure
            pair.suffixTrail).cycleBypass.length <
          (data.alternateOppositePortClosure pair.suffixTrail).length ∧
        (data.alternateOppositePortClosure
            pair.suffixTrail).cycleBypass.edges ⊆
          (data.alternateOppositePortClosure pair.suffixTrail).edges)) ∨
      ((data.oppositePortClosure pair.prefixTrail).IsCycle ∧
        (data.alternateOppositePortClosure pair.suffixTrail).IsCycle ∧
        pair.prefixTrail.IsPath ∧ pair.suffixTrail.IsPath ∧
        (retainedEdgeToAmbientEdge data cross).1 ≠
          centralEdgeValue data ∧
        ∀ edge : Sym2 V,
          edge ∈ (data.oppositePortClosure pair.prefixTrail).edges ∧
              edge ∈
                (data.alternateOppositePortClosure pair.suffixTrail).edges ↔
            edge = (retainedEdgeToAmbientEdge data cross).1 ∨
              edge = centralEdgeValue data) := by
  rcases pair.prefixTrail_isTrail.isCycle_or_cycleBypass_length_lt
      pair.oppositePortClosure_ne_nil with hprefixCycle | hprefixDescent
  · rcases pair.suffixTrail_isTrail.isCycle_or_cycleBypass_length_lt
        pair.alternateOppositePortClosure_ne_nil with
      hsuffixCycle | hsuffixDescent
    · right
      exact ⟨hprefixCycle, hsuffixCycle,
        data.isPath_of_oppositePortClosure_isCycle
          pair.prefixTrail hprefixCycle,
        data.isPath_of_alternateOppositePortClosure_isCycle
          pair.suffixTrail hsuffixCycle,
        pair.edgesDistinct,
        data.mem_both_oppositePortClosures_iff_of_exact_retained_intersection
          pair.prefixTrail pair.suffixTrail cross
            pair.retainedIntersectionExact⟩
    · exact Or.inl (Or.inr hsuffixDescent)
  · exact Or.inl (Or.inl hprefixDescent)

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
