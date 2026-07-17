import Mettapedia.GraphTheory.FourColor.CDLFlow
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairInsertion

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open SimpleGraph
open scoped BigOperators

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance oneZeroRetainedVertexSetFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance oneZeroRetainedVertexSetDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- Restore an adjacent pair from a coloring of its deletion, assigning zero
to the central edge and the requested missing color to every boundary edge. -/
def oneZeroAmbientChain
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color) : G.edgeSet → Color :=
  insertAdjacentPairColorFunction data C 0

@[simp]
theorem oneZeroAmbientChain_central
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color) :
    oneZeroAmbientChain data C (centralEdge data) = 0 := by
  simp [oneZeroAmbientChain]

@[simp]
theorem oneZeroAmbientChain_boundary
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (port : Fin 4) :
    oneZeroAmbientChain data C (boundaryEdge data port) =
      data.degreeTwoBoundaryData.colorWord C port := by
  exact insertAdjacentPairColorFunction_boundary data C 0 port

@[simp]
theorem oneZeroAmbientChain_retained
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (edge : G.edgeSet) (hretained : IsRetainedAmbientEdge data edge) :
    oneZeroAmbientChain data C edge =
      C (ambientEdgeToRetainedEdge data edge hretained) := by
  exact insertAdjacentPairColorFunction_retained data C 0 edge hretained

/-- The reconstructed chain has no zero away from the restored central edge. -/
theorem oneZeroAmbientChain_ne_zero_of_ne_central
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (edge : G.edgeSet) (hne : edge ≠ centralEdge data) :
    oneZeroAmbientChain data C edge ≠ 0 := by
  let hboundary := data.degreeTwoBoundaryData_wellFormed hcubic
  by_cases hretained : IsRetainedAmbientEdge data edge
  · rw [oneZeroAmbientChain_retained data C edge hretained]
    exact hC (ambientEdgeToRetainedEdge data edge hretained)
  · rcases (not_isRetainedAmbientEdge_iff data edge).1 hretained with
      hcentral | ⟨port, hport⟩
    · exact False.elim (hne (Subtype.ext hcentral))
    · have hedge : edge = boundaryEdge data port := Subtype.ext hport
      subst edge
      rw [oneZeroAmbientChain_boundary]
      exact data.degreeTwoBoundaryData.colorWord_ne_zero hboundary C port

/-- The restored central edge is exactly the zero set of the reconstructed
chain. -/
theorem oneZeroAmbientChain_eq_zero_iff
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (edge : G.edgeSet) :
    oneZeroAmbientChain data C edge = 0 ↔ edge = centralEdge data := by
  constructor
  · intro hzero
    by_contra hne
    exact oneZeroAmbientChain_ne_zero_of_ne_central data hcubic C hC edge hne hzero
  · rintro rfl
    exact oneZeroAmbientChain_central data C

/-- The finite zero support of the reconstructed chain is the singleton
central edge. -/
theorem zeroEdgeFinset_oneZeroAmbientChain
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    zeroEdgeFinset G (oneZeroAmbientChain data C) = {centralEdge data} := by
  ext edge
  simp [zeroEdgeFinset, oneZeroAmbientChain_eq_zero_iff data hcubic C hC edge]

/-- The reconstructed chain has exactly one zero edge. -/
theorem zeroEdgeCount_oneZeroAmbientChain
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    zeroEdgeCount G (oneZeroAmbientChain data C) = 1 := by
  rw [zeroEdgeCount, zeroEdgeFinset_oneZeroAmbientChain data hcubic C hC]
  simp

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem retainedVertex_eq_portVertex_of_mem_boundaryEdge
    (data : AdjacentPairData G) (vertex : V)
    (hvertex : vertex ∈
      retainedVertexSet data.firstVertex data.secondVertex)
    (port : Fin 4)
    (hmem : vertex ∈ ((boundaryEdge data port).1 : Sym2 V)) :
    vertex = data.portVertex port := by
  fin_cases port <;>
    simpa [boundaryEdge, boundaryEdgeValue, hvertex.1, hvertex.2] using hmem

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem centralEdge_not_mem_at_retainedVertex
    (data : AdjacentPairData G) (vertex : V)
    (hvertex : vertex ∈
      retainedVertexSet data.firstVertex data.secondVertex) :
    vertex ∉ ((centralEdge data).1 : Sym2 V) := by
  simp [centralEdge, centralEdgeValue, hvertex.1, hvertex.2]

private theorem oneZeroAmbientChain_ne_of_distinct_at_retainedVertex
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (vertex : V)
    (hvertex : vertex ∈
      retainedVertexSet data.firstVertex data.secondVertex)
    (first second : G.edgeSet)
    (hfirstMem : vertex ∈ (first.1 : Sym2 V))
    (hsecondMem : vertex ∈ (second.1 : Sym2 V))
    (hne : first ≠ second) :
    oneZeroAmbientChain data C first ≠
      oneZeroAmbientChain data C second := by
  let hboundary := data.degreeTwoBoundaryData_wellFormed hcubic
  have hadj : G.lineGraph.Adj first second :=
    (SimpleGraph.lineGraph_adj_iff_exists).2
      ⟨hne, vertex, hfirstMem, hsecondMem⟩
  by_cases hfirst : IsRetainedAmbientEdge data first
  · by_cases hsecond : IsRetainedAmbientEdge data second
    · rw [oneZeroAmbientChain_retained data C first hfirst,
        oneZeroAmbientChain_retained data C second hsecond]
      exact C.valid
        (ambientEdgeToRetainedEdge_adj data first second hfirst hsecond hadj)
    · rcases (not_isRetainedAmbientEdge_iff data second).1 hsecond with
        hcentral | ⟨port, hport⟩
      · have hsecondEq : second = centralEdge data := Subtype.ext hcentral
        subst second
        exact False.elim
          (centralEdge_not_mem_at_retainedVertex data vertex hvertex hsecondMem)
      · have hsecondEq : second = boundaryEdge data port := Subtype.ext hport
        subst second
        rw [oneZeroAmbientChain_retained data C first hfirst,
          oneZeroAmbientChain_boundary]
        exact (data.degreeTwoBoundaryData.colorWord_ne_incidentColor
          hboundary C hC port (ambientEdgeToRetainedEdge data first hfirst)
          (ambientEdgeToRetainedEdge_mem_incident_of_adj_boundaryEdge
            data first hfirst port hadj)).symm
  · by_cases hsecond : IsRetainedAmbientEdge data second
    · rcases (not_isRetainedAmbientEdge_iff data first).1 hfirst with
        hcentral | ⟨port, hport⟩
      · have hfirstEq : first = centralEdge data := Subtype.ext hcentral
        subst first
        exact False.elim
          (centralEdge_not_mem_at_retainedVertex data vertex hvertex hfirstMem)
      · have hfirstEq : first = boundaryEdge data port := Subtype.ext hport
        subst first
        rw [oneZeroAmbientChain_boundary,
          oneZeroAmbientChain_retained data C second hsecond]
        exact data.degreeTwoBoundaryData.colorWord_ne_incidentColor
          hboundary C hC port (ambientEdgeToRetainedEdge data second hsecond)
          (ambientEdgeToRetainedEdge_mem_incident_of_adj_boundaryEdge
            data second hsecond port hadj.symm)
    · rcases (not_isRetainedAmbientEdge_iff data first).1 hfirst with
          hfirstCentral | ⟨firstPort, hfirstPort⟩ <;>
        rcases (not_isRetainedAmbientEdge_iff data second).1 hsecond with
          hsecondCentral | ⟨secondPort, hsecondPort⟩
      · have hfirstEq : first = centralEdge data := Subtype.ext hfirstCentral
        subst first
        exact False.elim
          (centralEdge_not_mem_at_retainedVertex data vertex hvertex hfirstMem)
      · have hfirstEq : first = centralEdge data := Subtype.ext hfirstCentral
        subst first
        exact False.elim
          (centralEdge_not_mem_at_retainedVertex data vertex hvertex hfirstMem)
      · have hsecondEq : second = centralEdge data := Subtype.ext hsecondCentral
        subst second
        exact False.elim
          (centralEdge_not_mem_at_retainedVertex data vertex hvertex hsecondMem)
      · have hfirstEq : first = boundaryEdge data firstPort :=
          Subtype.ext hfirstPort
        have hsecondEq : second = boundaryEdge data secondPort :=
          Subtype.ext hsecondPort
        subst first
        subst second
        have hvertexFirst :=
          retainedVertex_eq_portVertex_of_mem_boundaryEdge data vertex hvertex
            firstPort hfirstMem
        have hvertexSecond :=
          retainedVertex_eq_portVertex_of_mem_boundaryEdge data vertex hvertex
            secondPort hsecondMem
        have hports : firstPort = secondPort :=
          data.portInjective (hvertexFirst.symm.trans hvertexSecond)
        subst secondPort
        exact False.elim (hne rfl)

theorem incidentEdgeFinset_firstVertex
    (data : AdjacentPairData G) :
    incidentEdgeFinset G data.firstVertex =
      {centralEdge data, boundaryEdge data 0, boundaryEdge data 1} := by
  ext edge
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hmem
    rcases edge_eq_central_or_firstPort_of_mem data edge hmem with
      hcentral | hzero | hone
    · exact Or.inl (Subtype.ext hcentral)
    · exact Or.inr (Or.inl (Subtype.ext hzero))
    · exact Or.inr (Or.inr (Subtype.ext hone))
  · rintro (rfl | rfl | rfl)
    · simp [centralEdge, centralEdgeValue]
    · simp [boundaryEdge, boundaryEdgeValue]
    · simp [boundaryEdge, boundaryEdgeValue]

theorem incidentEdgeFinset_secondVertex
    (data : AdjacentPairData G) :
    incidentEdgeFinset G data.secondVertex =
      {centralEdge data, boundaryEdge data 2, boundaryEdge data 3} := by
  ext edge
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hmem
    rcases edge_eq_central_or_secondPort_of_mem data edge hmem with
      hcentral | htwo | hthree
    · exact Or.inl (Subtype.ext hcentral)
    · exact Or.inr (Or.inl (Subtype.ext htwo))
    · exact Or.inr (Or.inr (Subtype.ext hthree))
  · rintro (rfl | rfl | rfl)
    · simp [centralEdge, centralEdgeValue]
    · simp [boundaryEdge, boundaryEdgeValue]
    · simp [boundaryEdge, boundaryEdgeValue]

/-- Equal same-side boundary requests make the unique-zero reconstruction a
genuine ambient graph flow. -/
theorem oneZeroAmbientChain_isGraphFlow
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3) :
    IsGraphFlow G (oneZeroAmbientChain data C) := by
  have hchainSameFirst :
      oneZeroAmbientChain data C (boundaryEdge data 0) =
        oneZeroAmbientChain data C (boundaryEdge data 1) := by
    rw [oneZeroAmbientChain_boundary, oneZeroAmbientChain_boundary]
    exact hsame.1
  have hchainSameSecond :
      oneZeroAmbientChain data C (boundaryEdge data 2) =
        oneZeroAmbientChain data C (boundaryEdge data 3) := by
    rw [oneZeroAmbientChain_boundary, oneZeroAmbientChain_boundary]
    exact hsame.2
  intro vertex
  by_cases hfirst : vertex = data.firstVertex
  · subst vertex
    unfold vertexKirchhoffSum
    rw [incidentEdgeFinset_firstVertex data]
    have hcentralZero := oneZeroAmbientChain_central data C
    have hcentralBoundaryZero :
        centralEdge data ≠ boundaryEdge data 0 := by
      intro hedge
      exact centralEdgeValue_ne_boundaryEdgeValue data 0
        (congrArg Subtype.val hedge)
    have hcentralBoundaryOne :
        centralEdge data ≠ boundaryEdge data 1 := by
      intro hedge
      exact centralEdgeValue_ne_boundaryEdgeValue data 1
        (congrArg Subtype.val hedge)
    have hboundaryZeroOne :
        boundaryEdge data 0 ≠ boundaryEdge data 1 := by
      intro hedge
      apply boundaryEdgeValue_ne data (show (0 : Fin 4) ≠ 1 by decide)
      simpa using congrArg Subtype.val hedge
    simp [hcentralBoundaryZero, hcentralBoundaryOne, hboundaryZeroOne,
      hcentralZero, hchainSameFirst]
  · by_cases hsecond : vertex = data.secondVertex
    · subst vertex
      unfold vertexKirchhoffSum
      rw [incidentEdgeFinset_secondVertex data]
      have hcentralZero := oneZeroAmbientChain_central data C
      have hcentralBoundaryTwo :
          centralEdge data ≠ boundaryEdge data 2 := by
        intro hedge
        exact centralEdgeValue_ne_boundaryEdgeValue data 2
          (congrArg Subtype.val hedge)
      have hcentralBoundaryThree :
          centralEdge data ≠ boundaryEdge data 3 := by
        intro hedge
        exact centralEdgeValue_ne_boundaryEdgeValue data 3
          (congrArg Subtype.val hedge)
      have hboundaryTwoThree :
          boundaryEdge data 2 ≠ boundaryEdge data 3 := by
        intro hedge
        apply boundaryEdgeValue_ne data (show (2 : Fin 4) ≠ 3 by decide)
        simpa using congrArg Subtype.val hedge
      simp [hcentralBoundaryTwo, hcentralBoundaryThree, hboundaryTwoThree,
        hcentralZero, hchainSameSecond]
    · have hvertex : vertex ∈
          retainedVertexSet data.firstVertex data.secondVertex :=
        ⟨hfirst, hsecond⟩
      rcases Finset.card_eq_three.mp (hcubic vertex) with
        ⟨first, second, third, hfirstSecond, hfirstThird,
          hsecondThird, hset⟩
      have hfirstMem : vertex ∈ (first.1 : Sym2 V) := by
        have : first ∈ incidentEdgeFinset G vertex := by
          rw [hset]
          simp
        simpa [incidentEdgeFinset] using this
      have hsecondMem : vertex ∈ (second.1 : Sym2 V) := by
        have : second ∈ incidentEdgeFinset G vertex := by
          rw [hset]
          simp
        simpa [incidentEdgeFinset] using this
      have hthirdMem : vertex ∈ (third.1 : Sym2 V) := by
        have : third ∈ incidentEdgeFinset G vertex := by
          rw [hset]
          simp
        simpa [incidentEdgeFinset] using this
      have hfirstCentral : first ≠ centralEdge data := by
        intro hedge
        subst first
        exact centralEdge_not_mem_at_retainedVertex data vertex hvertex
          hfirstMem
      have hsecondCentral : second ≠ centralEdge data := by
        intro hedge
        subst second
        exact centralEdge_not_mem_at_retainedVertex data vertex hvertex
          hsecondMem
      have hthirdCentral : third ≠ centralEdge data := by
        intro hedge
        subst third
        exact centralEdge_not_mem_at_retainedVertex data vertex hvertex
          hthirdMem
      have hlocal : IsLocalTaitTriple
          (oneZeroAmbientChain data C first)
          (oneZeroAmbientChain data C second)
          (oneZeroAmbientChain data C third) := by
        exact ⟨⟨
          oneZeroAmbientChain_ne_zero_of_ne_central data hcubic C hC first
            hfirstCentral,
          oneZeroAmbientChain_ne_zero_of_ne_central data hcubic C hC second
            hsecondCentral,
          oneZeroAmbientChain_ne_zero_of_ne_central data hcubic C hC third
            hthirdCentral⟩,
          oneZeroAmbientChain_ne_of_distinct_at_retainedVertex
            data hcubic C hC vertex hvertex first second hfirstMem hsecondMem
              hfirstSecond,
          oneZeroAmbientChain_ne_of_distinct_at_retainedVertex
            data hcubic C hC vertex hvertex first third hfirstMem hthirdMem
              hfirstThird,
          oneZeroAmbientChain_ne_of_distinct_at_retainedVertex
            data hcubic C hC vertex hvertex second third hsecondMem hthirdMem
              hsecondThird⟩
      unfold vertexKirchhoffSum
      rw [hset]
      simpa [IsLocalKirchhoffTriple, hfirstSecond, hfirstThird,
        hsecondThird, add_assoc] using isLocalKirchhoffTriple_of_tait hlocal

/-- At every cubic vertex the singleton-zero reconstruction has a nonzero
incident edge. -/
theorem oneZeroAmbientChain_isCDLGoodAtVertex
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (vertex : V) :
    IsCDLGoodAtVertex G (oneZeroAmbientChain data C) vertex := by
  rcases Finset.card_eq_three.mp (hcubic vertex) with
    ⟨first, second, _third, hfirstSecond, _hfirstThird,
      _hsecondThird, hset⟩
  have hfirstMem : first ∈ incidentEdgeFinset G vertex := by
    rw [hset]
    simp
  have hsecondMem : second ∈ incidentEdgeFinset G vertex := by
    rw [hset]
    simp
  by_cases hfirstCentral : first = centralEdge data
  · refine ⟨second, hsecondMem,
      oneZeroAmbientChain_ne_zero_of_ne_central data hcubic C hC second ?_⟩
    intro hsecondCentral
    exact hfirstSecond (hfirstCentral.trans hsecondCentral.symm)
  · exact ⟨first, hfirstMem,
      oneZeroAmbientChain_ne_zero_of_ne_central data hcubic C hC first
        hfirstCentral⟩

/-- Equal same-side boundary requests produce a globally CDL-good ambient
flow with one zero edge. -/
theorem oneZeroAmbientChain_isCDLGoodFlow
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3) :
    IsCDLGoodFlow G (oneZeroAmbientChain data C) := by
  exact ⟨oneZeroAmbientChain_isGraphFlow data hcubic C hC hsame,
    oneZeroAmbientChain_isCDLGoodAtVertex data hcubic C hC⟩

/-- An uncolorable cubic ambient graph forces every colored adjacent-pair
deletion to reconstruct as a CDL-good singleton-zero flow. -/
theorem oneZeroAmbientChain_isCDLGoodFlow_of_not_taitColorable
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    IsCDLGoodFlow G (oneZeroAmbientChain data C) := by
  exact oneZeroAmbientChain_isCDLGoodFlow data hcubic C hC
    (sameSidePairs_of_not_taitColorable data hcubic hnotColorable C hC)

/-- Graph-backed singleton-zero package: a colored adjacent-pair deletion of
an uncolorable cubic graph yields a CDL-good flow with exact zero support. -/
theorem exists_cdlGoodFlow_zeroEdgeFinset_eq_singleton_of_deletedAdjacentPair
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    ∃ chain : G.edgeSet → Color,
      IsCDLGoodFlow G chain ∧
        zeroEdgeFinset G chain = {centralEdge data} := by
  exact ⟨oneZeroAmbientChain data C,
    oneZeroAmbientChain_isCDLGoodFlow_of_not_taitColorable
      data hcubic hnotColorable C hC,
    zeroEdgeFinset_oneZeroAmbientChain data hcubic C hC⟩

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
