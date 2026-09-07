import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairColoringAtlas
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCommonCoreDisagreementResidue
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedDegreePath

/-!
# Two separated deletions suffice for common-core gluing

If the closed neighborhoods of two deleted pairs are disjoint, their
complements cover every ambient edge and every incident pair of edges.
Literal agreement on the common four-vertex deletion therefore glues two
proper nonzero colourings to an ambient Tait colouring.  In a least
counterexample, even a repaired representative cannot agree.  The existing
three-way common-core residue consequently loses its strict-repair branch.

Separation concerns the whole ambient graph, not distance along a mesh row.
The neighborhood estimate is supplied for the subsequent ordered-row
construction.  No local configuration or colouring table is enumerated.
-/

namespace Mettapedia.GraphTheory.FourColor.SeparatedPairDeletion

open GoertzelV24AdjacentPairBoundary GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairCommonCoreDisagreementResidue
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph SimpleGraphDartRotation

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- One closed ambient neighborhood of a finite vertex set. -/
def close (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : Finset V :=
  s.biUnion fun v => insert v (G.neighborFinset v)

theorem mem_close {s : Finset V} {v : V} :
    v ∈ close G s ↔ ∃ w ∈ s, w = v ∨ G.Adj w v := by
  simp [close, eq_comm]

theorem subset_close (s : Finset V) : s ⊆ close G s := by
  intro v hv
  exact mem_close.mpr ⟨v, hv, Or.inl rfl⟩

theorem card_close_le (d : Nat) (hdegree : ∀ v, G.degree v ≤ d) (s : Finset V) :
    (close G s).card ≤ s.card * (d + 1) := by
  calc
    (close G s).card ≤ ∑ v ∈ s, (insert v (G.neighborFinset v)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ s, (d + 1) := Finset.sum_le_sum fun v _ =>
      GoertzelV24BoundedDegreePath.card_closedNeighborFinset_le G d hdegree v
    _ = s.card * (d + 1) := by simp

theorem disjoint_close_of_avoid_twice (s t : Finset V)
    (h : ∀ v ∈ t, v ∉ close G (close G s)) :
    Disjoint (close G s) (close G t) := by
  apply Finset.disjoint_left.mpr
  intro v hs ht
  obtain ⟨w, hw, heq | hadj⟩ := mem_close.mp ht
  · subst w
    exact h v hw (subset_close _ hs)
  · exact h w hw (mem_close.mpr ⟨v, hs, Or.inr hadj.symm⟩)

def deleted (data : AdjacentPairData G) : Finset V :=
  {data.firstVertex, data.secondVertex}

def Separated (source target : AdjacentPairData G) : Prop :=
  Disjoint (close G (deleted source)) (close G (deleted target))

theorem mem_close_of_edge_endpoints (s : Finset V) (edge : G.edgeSet)
    {v w : V} (hv : v ∈ (edge.1 : Sym2 V))
    (hw : w ∈ (edge.1 : Sym2 V)) (hs : w ∈ s) : v ∈ close G s := by
  apply mem_close.mpr
  refine ⟨w, hs, ?_⟩
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ a b =>
    have hab : G.Adj a b := hedge
    simp only [Sym2.mem_iff] at hv hw
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hab.symm
    · exact Or.inr hab
    · exact Or.inl rfl

/-- Every endpoint of an edge removed at a pair lies in that pair's closed
neighborhood, including the retained endpoint of a boundary edge. -/
theorem mem_close_of_not_retained (data : AdjacentPairData G)
    (edge : G.edgeSet) (hnot : ¬ IsRetainedAmbientEdge data edge)
    {v : V} (hv : v ∈ (edge.1 : Sym2 V)) : v ∈ close G (deleted data) := by
  have hends : data.firstVertex ∈ edge.1.toFinset ∨
      data.secondVertex ∈ edge.1.toFinset := by
    by_contra h
    push Not at h
    exact hnot (isRetainedAmbientEdge_of_deleted_vertices_not_mem data edge h.1 h.2)
  rcases hends with hfirst | hsecond
  · exact mem_close_of_edge_endpoints _ edge hv (Sym2.mem_toFinset.mp hfirst)
      (by simp [deleted])
  · exact mem_close_of_edge_endpoints _ edge hv (Sym2.mem_toFinset.mp hsecond)
      (by simp [deleted])

theorem retained_or_retained (source target : AdjacentPairData G)
    (hsep : Separated source target) (edge : G.edgeSet) :
    IsRetainedAmbientEdge source edge ∨ IsRetainedAmbientEdge target edge := by
  by_cases hs : IsRetainedAmbientEdge source edge
  · exact Or.inl hs
  right
  by_contra ht
  obtain ⟨v, hv⟩ : ∃ v, v ∈ (edge.1 : Sym2 V) := by
    rcases edge with ⟨edge, hedge⟩
    induction edge using Sym2.inductionOn with
    | _ a b => exact ⟨a, Sym2.mem_mk_left _ _⟩
  exact Finset.disjoint_left.mp hsep
    (mem_close_of_not_retained source edge hs hv)
    (mem_close_of_not_retained target edge ht hv)

theorem adjacent_retained_or_retained (source target : AdjacentPairData G)
    (hsep : Separated source target) (first second : G.edgeSet)
    (hadj : G.lineGraph.Adj first second) :
    (IsRetainedAmbientEdge source first ∧ IsRetainedAmbientEdge source second) ∨
      (IsRetainedAmbientEdge target first ∧ IsRetainedAmbientEdge target second) := by
  obtain ⟨_, v, hvf, hvs⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadj
  by_cases hs : IsRetainedAmbientEdge source first ∧
      IsRetainedAmbientEdge source second
  · exact Or.inl hs
  right
  have hv : v ∈ close G (deleted source) := by
    by_cases hf : IsRetainedAmbientEdge source first
    · exact mem_close_of_not_retained source second (fun h => hs ⟨hf, h⟩) hvs
    · exact mem_close_of_not_retained source first hf hvf
  constructor
  · by_contra ht
    exact Finset.disjoint_left.mp hsep hv
      (mem_close_of_not_retained target first ht hvf)
  · by_contra ht
    exact Finset.disjoint_left.mp hsep hv
      (mem_close_of_not_retained target second ht hvs)

variable (source target : AdjacentPairData G)
  (sourceColor : (DeletedAdjacentPairGraph G source.firstVertex
    source.secondVertex).EdgeColoring Color)
  (targetColor : (DeletedAdjacentPairGraph G target.firstVertex
    target.secondVertex).EdgeColoring Color)
  (hsource : IsTaitEdgeColoring _ sourceColor)
  (htarget : IsTaitEdgeColoring _ targetColor)

def twoPatchFamily : PairDeletionColoringFamily (G := G) Bool where
  data | false => source | true => target
  coloring | false => sourceColor | true => targetColor
  tait | false => hsource | true => htarget

include hsource htarget in
/-- Separation supplies all coverage fields; common-core equality supplies
the only colour coherence field. -/
theorem not_commonCore_eq_of_minimal
    (rotation : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hsep : Separated source target) :
    firstDeletionCommonCoreColoring (third := target.firstVertex)
        (fourth := target.secondVertex) sourceColor ≠
      secondDeletionCommonCoreColoring (first := source.firstVertex)
        (second := source.secondVertex) targetColor := by
  intro hagrees
  let family := twoPatchFamily source target sourceColor targetColor hsource htarget
  have cover : family.CoversEdges := by
    intro edge
    rcases retained_or_retained source target hsep edge with hs | ht
    · exact ⟨false, hs⟩
    · exact ⟨true, ht⟩
  have adjacentCover : family.CoversAdjacentEdges := by
    intro first second hadj
    rcases adjacent_retained_or_retained source target hsep first second hadj with hs | ht
    · exact ⟨false, hs⟩
    · exact ⟨true, ht⟩
  apply family.not_pairwiseAgrees_of_minimal rotation minimal cover adjacentCover
  intro first second edge hf hs
  have heq := coloring_eq_on_common_retained_edge source target sourceColor targetColor
  cases first <;> cases second
  · rfl
  · exact heq edge hf hs ((commonRestrictionAgreementBit_eq_true_iff _ _ _ _).mpr hagrees)
  · exact (heq edge hs hf ((commonRestrictionAgreementBit_eq_true_iff _ _ _ _).mpr hagrees)).symm
  · rfl

include hsource htarget in
/-- The strict common-core repair branch is impossible at separated sites,
for every choice of the two proper deletion colourings. -/
theorem branching_or_taitReachesSecondPair_of_separated
    (rotation : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hsep : Separated source target) :
    HasCommonCoreBranchingDiscrepancy source target sourceColor targetColor ∨
      FirstTaitOrbitReachesSecondPair source target sourceColor := by
  rcases branching_or_taitReachesSecondPair_or_strictTaitRepair
      source target sourceColor targetColor hsource htarget
      (not_commonCore_eq_of_minimal source target sourceColor targetColor
        hsource htarget rotation minimal hsep) with hb | he | hr
  · exact Or.inl hb
  · exact Or.inr he
  · obtain ⟨repaired, _, htait, heq, _⟩ := hr
    exact (not_commonCore_eq_of_minimal source target repaired targetColor
      htait htarget rotation minimal hsep heq).elim

end
end Mettapedia.GraphTheory.FourColor.SeparatedPairDeletion
