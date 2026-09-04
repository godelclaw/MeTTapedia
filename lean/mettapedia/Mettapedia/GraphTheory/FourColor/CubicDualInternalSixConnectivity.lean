import Mettapedia.GraphTheory.FourColor.FiveCutSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceSize

/-!
# Cubic-dual internal six-connectivity

For a cubic plane graph, the dual form of internal six-connectivity has two
parts: cyclic cuts of size at most four do not exist, and every cyclic cut of
size five has a shore of bounded size.  The first part was established by the
two-, three-, and four-cut reductions.  The second part is the compositional
five-cut theorem.

This file packages those two results as a reusable normal form.  It also
removes the exact-cardinality bookkeeping for consumers: any realized cyclic
cut with at most five edges has a shore with at most five vertices.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FourEdgeCutGluing
open GoertzelV24MinimalFaceSize
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace CyclicEdgeCutRealization

/-- The finite set of vertices on the selected shore of a realized cyclic
edge cut. -/
def vertexSide {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut) : Finset V := by
  classical
  exact Finset.univ.filter realization.side

omit [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem mem_vertexSide_iff {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut) (vertex : V) :
    vertex ∈ realization.vertexSide ↔ realization.side vertex := by
  simp [vertexSide]

/-- A realized cyclic cut has a shore of size at most `bound` when either its
selected shore or its complementary shore satisfies that bound. -/
def HasShoreOfSizeAtMost {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut) (bound : Nat) : Prop :=
  realization.vertexSide.card ≤ bound ∨
    realization.compl.vertexSide.card ≤ bound

end CyclicEdgeCutRealization

/-- A shore containing a cycle has at least five vertices in a graph-backed
vertex-minimal counterexample.  This is the vertex-set form of the already
proved absence of three- and four-cycles. -/
theorem five_le_card_vertexSide_of_hasCycleOnSide_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (side : V → Prop) [DecidablePred side]
    (hcycleOnSide : HasCycleOnSide G side) :
    5 ≤ (Finset.univ.filter side).card := by
  classical
  rcases hcycleOnSide with ⟨root, _hroot, cycle, hcycle, hcycleSide⟩
  have hlength : 5 ≤ cycle.length := by
    have hnot := not_isCycle_length_le_four_of_vertexMinimalTaitCounterexample
      graphData minimal cycle hcycle
    omega
  let cycleVertex : Fin cycle.length → {vertex : V // side vertex} :=
    fun index =>
      ⟨cycle.getVert index.val,
        hcycleSide _ (cycle.getVert_mem_support index.val)⟩
  have hinjective : Function.Injective cycleVertex := by
    intro first second heq
    apply Fin.ext
    apply hcycle.getVert_injOn'
    · exact Nat.le_sub_one_of_lt first.isLt
    · exact Nat.le_sub_one_of_lt second.isLt
    · exact congrArg Subtype.val heq
  have hcycleCard : cycle.length ≤ Fintype.card {vertex : V // side vertex} := by
    simpa using Fintype.card_le_of_injective cycleVertex hinjective
  calc
    5 ≤ cycle.length := hlength
    _ ≤ Fintype.card {vertex : V // side vertex} := hcycleCard
    _ = (Finset.univ.filter side).card := by rw [Fintype.card_subtype]

/-- A predicate cuts out a pentagonal cycle shore when its vertices are
exactly the support of a simple cycle of length five. -/
def HasPentagonalCycleShore (G : SimpleGraph V) (side : V → Prop) : Prop :=
  ∃ root : V, ∃ cycle : G.Walk root root,
    cycle.IsCycle ∧ cycle.length = 5 ∧
      ∀ vertex, side vertex ↔ vertex ∈ cycle.support

/-- In a vertex-minimal counterexample, a cyclic shore with at most five
vertices is exactly the vertex support of a pentagonal cycle. -/
theorem hasPentagonalCycleShore_of_hasCycleOnSide_of_card_le_five
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (side : V → Prop) [DecidablePred side]
    (hcycleOnSide : HasCycleOnSide G side)
    (hsmall : (Finset.univ.filter side).card ≤ 5) :
    HasPentagonalCycleShore G side := by
  classical
  rcases hcycleOnSide with ⟨root, _hroot, cycle, hcycle, hcycleSide⟩
  have hlengthLower : 5 ≤ cycle.length := by
    have hnot := not_isCycle_length_le_four_of_vertexMinimalTaitCounterexample
      graphData minimal cycle hcycle
    omega
  let cycleVertex : Fin cycle.length → {vertex : V // side vertex} :=
    fun index =>
      ⟨cycle.getVert index.val,
        hcycleSide _ (cycle.getVert_mem_support index.val)⟩
  have hinjective : Function.Injective cycleVertex := by
    intro first second heq
    apply Fin.ext
    apply hcycle.getVert_injOn'
    · exact Nat.le_sub_one_of_lt first.isLt
    · exact Nat.le_sub_one_of_lt second.isLt
    · exact congrArg Subtype.val heq
  have hlengthUpper : cycle.length ≤
      Fintype.card {vertex : V // side vertex} := by
    simpa using Fintype.card_le_of_injective cycleVertex hinjective
  have hsideCard : Fintype.card {vertex : V // side vertex} = 5 := by
    have hcardEq : Fintype.card {vertex : V // side vertex} =
        (Finset.univ.filter side).card := by
      rw [Fintype.card_subtype]
    omega
  have hlengthFive : cycle.length = 5 := by omega
  have hcardEq : Fintype.card (Fin cycle.length) =
      Fintype.card {vertex : V // side vertex} := by
    simp [hlengthFive, hsideCard]
  have hsurjective : Function.Surjective cycleVertex :=
    ((Fintype.bijective_iff_injective_and_card cycleVertex).2
      ⟨hinjective, hcardEq⟩).2
  refine ⟨root, cycle, hcycle, hlengthFive, ?_⟩
  intro vertex
  constructor
  · intro hside
    rcases hsurjective ⟨vertex, hside⟩ with ⟨index, hindex⟩
    have hget : cycle.getVert index.val = vertex :=
      congrArg Subtype.val hindex
    rw [← hget]
    exact cycle.getVert_mem_support index.val
  · exact hcycleSide vertex

/-- The cubic-graph formulation corresponding to internal six-connectivity
of the planar dual.  We keep the name explicitly dual-facing until a formal
planar-duality bridge identifies it with the standard triangulation notion. -/
def CubicDualInternallySixConnected (G : SimpleGraph V) : Prop :=
  CyclicallyFiveEdgeConnected G ∧
    ∀ cut : ExactSizedCyclicEdgeCut G 5,
      (exactCutVertexSide cut).card ≤ 5 ∨
        (exactCutVertexSide cut.compl).card ≤ 5

/-- A graph-backed vertex-minimal Tait counterexample satisfies the full
cubic-dual internal-six normal form. -/
theorem cubicDualInternallySixConnected_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData) :
    CubicDualInternallySixConnected G := by
  refine ⟨cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample
      graphData minimal, ?_⟩
  exact FiveCutSplice.exactCyclicFiveEdgeCut_has_small_shore_of_vertexMinimalTaitCounterexample
    graphData minimal

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Consumer form of the normal form: every realized cyclic cut with at most
five edges has a shore with at most five vertices.  Cuts of size at most four
are impossible; the remaining exact-five case is W1. -/
theorem CyclicEdgeCutRealization.hasShoreOfSizeAtMost_five
    (internalSix : CubicDualInternallySixConnected G)
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hcard : edgeCut.card ≤ 5) :
    realization.HasShoreOfSizeAtMost 5 := by
  classical
  rcases internalSix with ⟨hcyclicFive, hfive⟩
  by_cases hcardFour : edgeCut.card ≤ 4
  · exact (hcyclicFive.noCyclicEdgeCutOfSizeAtMostFour
      (realization.hasCyclicEdgeCutOfSizeAtMostFour hcardFour)).elim
  · have hcardFive : edgeCut.card = 5 := by omega
    let cut : ExactSizedCyclicEdgeCut G 5 :=
      { edgeCut := edgeCut
        side := realization.side
        hcut_eq := realization.hcut_eq
        hcard_eq := hcardFive
        hinside_cycle := realization.hinside_cycle
        houtside_cycle := realization.houtside_cycle }
    have hsmall := hfive cut
    simp only [CyclicEdgeCutRealization.HasShoreOfSizeAtMost,
      CyclicEdgeCutRealization.vertexSide,
      CyclicEdgeCutRealization.compl]
    rcases hsmall with hsmall | hsmall
    · left
      simpa [exactCutVertexSide, cut] using hsmall
    · right
      simpa [exactCutVertexSide, ExactSizedCyclicEdgeCut.compl, cut]
        using hsmall

/-- In a graph-backed vertex-minimal counterexample, a realized cyclic cut of
size at most five cannot have more than five vertices on both shores. -/
theorem CyclicEdgeCutRealization.not_both_shores_large_of_card_le_five
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hcard : edgeCut.card ≤ 5) :
    ¬ (6 ≤ realization.vertexSide.card ∧
      6 ≤ realization.compl.vertexSide.card) := by
  intro hlarge
  have hsmall := realization.hasShoreOfSizeAtMost_five
    (cubicDualInternallySixConnected_of_vertexMinimalTaitCounterexample
      graphData minimal)
    hcard
  rcases hsmall with hsmall | hsmall <;> omega

/-- The bounded shore of an exact cyclic five-cut has exactly five vertices.
Both shores contain cycles, hence have at least five vertices; W1 supplies
the reverse inequality on one shore. -/
theorem exactCyclicFiveEdgeCut_has_five_vertex_shore_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : ExactSizedCyclicEdgeCut G 5) :
    (exactCutVertexSide cut).card = 5 ∨
      (exactCutVertexSide cut.compl).card = 5 := by
  classical
  have hinside : 5 ≤ (exactCutVertexSide cut).card := by
    simpa [exactCutVertexSide] using
      five_le_card_vertexSide_of_hasCycleOnSide_of_vertexMinimalTaitCounterexample
        graphData minimal cut.side cut.hinside_cycle
  have houtside : 5 ≤ (exactCutVertexSide cut.compl).card := by
    simpa [exactCutVertexSide, ExactSizedCyclicEdgeCut.compl] using
      five_le_card_vertexSide_of_hasCycleOnSide_of_vertexMinimalTaitCounterexample
        graphData minimal (fun vertex => ¬ cut.side vertex) cut.houtside_cycle
  rcases FiveCutSplice.exactCyclicFiveEdgeCut_has_small_shore_of_vertexMinimalTaitCounterexample
        graphData minimal cut with hsmall | hsmall
  · exact Or.inl (Nat.le_antisymm hsmall hinside)
  · exact Or.inr (Nat.le_antisymm hsmall houtside)

/-- Geometric classification of the W1 conclusion: one shore of every exact
cyclic five-cut is precisely a pentagonal cycle shore. -/
theorem exactCyclicFiveEdgeCut_has_pentagonal_shore_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : ExactSizedCyclicEdgeCut G 5) :
    HasPentagonalCycleShore G cut.side ∨
      HasPentagonalCycleShore G (fun vertex => ¬ cut.side vertex) := by
  classical
  rcases FiveCutSplice.exactCyclicFiveEdgeCut_has_small_shore_of_vertexMinimalTaitCounterexample
      graphData minimal cut with hsmall | hsmall
  · exact Or.inl
      (hasPentagonalCycleShore_of_hasCycleOnSide_of_card_le_five
        graphData minimal cut.side cut.hinside_cycle
        (by simpa [exactCutVertexSide] using hsmall))
  · exact Or.inr
      (hasPentagonalCycleShore_of_hasCycleOnSide_of_card_le_five
        graphData minimal (fun vertex => ¬ cut.side vertex) cut.houtside_cycle
        (by simpa [exactCutVertexSide, ExactSizedCyclicEdgeCut.compl]
          using hsmall))

/-- Cardinality-free consumer form: every realized cyclic cut with at most
five edges in a minimal counterexample has an exactly five-vertex shore.
The cut itself must therefore also have exactly five edges. -/
theorem CyclicEdgeCutRealization.has_five_vertex_shore_of_card_le_five
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hcard : edgeCut.card ≤ 5) :
    realization.vertexSide.card = 5 ∨
      realization.compl.vertexSide.card = 5 := by
  classical
  have hnotFour : ¬ edgeCut.card ≤ 4 := by
    intro hfour
    exact (cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample
      graphData minimal).noCyclicEdgeCutOfSizeAtMostFour
        (realization.hasCyclicEdgeCutOfSizeAtMostFour hfour)
  have hcardFive : edgeCut.card = 5 := by omega
  let cut : ExactSizedCyclicEdgeCut G 5 :=
    { edgeCut := edgeCut
      side := realization.side
      hcut_eq := realization.hcut_eq
      hcard_eq := hcardFive
      hinside_cycle := realization.hinside_cycle
      houtside_cycle := realization.houtside_cycle }
  have hshore :=
    exactCyclicFiveEdgeCut_has_five_vertex_shore_of_vertexMinimalTaitCounterexample
      graphData minimal cut
  rcases hshore with hshore | hshore
  · left
    simpa [CyclicEdgeCutRealization.vertexSide, exactCutVertexSide, cut]
      using hshore
  · right
    simpa [CyclicEdgeCutRealization.vertexSide,
      CyclicEdgeCutRealization.compl, exactCutVertexSide,
      ExactSizedCyclicEdgeCut.compl, cut] using hshore

end

end Mettapedia.GraphTheory.FourColor
