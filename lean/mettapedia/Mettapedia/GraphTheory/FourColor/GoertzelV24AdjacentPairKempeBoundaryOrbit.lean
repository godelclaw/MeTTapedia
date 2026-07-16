import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeSwitchSquare

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary
open GoertzelV24FramedTrail
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance boundaryOrbitGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance boundaryOrbitRetainedVertexSetFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance boundaryOrbitRetainedVertexSetDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- If both side requests belong to the selected pair, a component touching
the first side cannot also touch the second side. -/
theorem not_kempeComponentMeetsPort_two_of_meetsPort_zero
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (hselectedZero :
      data.degreeTwoBoundaryData.colorWord C 0 = a ∨
        data.degreeTwoBoundaryData.colorWord C 0 = b)
    (hselectedTwo :
      data.degreeTwoBoundaryData.colorWord C 2 = a ∨
        data.degreeTwoBoundaryData.colorWord C 2 = b)
    (hmeetsZero :
      data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K 0) :
    ¬ data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K 2 := by
  have hsame :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data hcubic hnotColorable C hC
  have hmeetsOne :
      data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K 1 :=
    (data.kempeComponentMeetsPort_zero_iff_one_of_selected_request
      hcubic hnotColorable C hC hab K hselectedZero).1 hmeetsZero
  intro hmeetsTwo
  have hmeetsThree :
      data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K 3 :=
    (data.kempeComponentMeetsPort_two_iff_three_of_selected_request
      hcubic hnotColorable C hC hab K hselectedTwo).1 hmeetsTwo
  have hselected : ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord C port = a ∨
        data.degreeTwoBoundaryData.colorWord C port = b := by
    intro port
    fin_cases port
    · exact hselectedZero
    · rcases hselectedZero with hfirst | hsecond
      · exact Or.inl (hsame.1.symm.trans hfirst)
      · exact Or.inr (hsame.1.symm.trans hsecond)
    · exact hselectedTwo
    · rcases hselectedTwo with hfirst | hsecond
      · exact Or.inl (hsame.2.symm.trans hfirst)
      · exact Or.inr (hsame.2.symm.trans hsecond)
  apply data.degreeTwoBoundaryData.not_exists_allPort_kempeComponent
    (data.degreeTwoBoundaryData_wellFormed hcubic) C hab hselected
  refine ⟨K, ?_⟩
  ext port
  simp only [Finset.mem_univ, iff_true]
  apply (data.degreeTwoBoundaryData.mem_kempePortSupport_iff
    C a b K port).2
  fin_cases port
  · exact hmeetsZero
  · exact hmeetsOne
  · exact hmeetsTwo
  · exact hmeetsThree

/-- Symmetric cross-side exclusion for a component touching the second
side. -/
theorem not_kempeComponentMeetsPort_zero_of_meetsPort_two
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (hselectedZero :
      data.degreeTwoBoundaryData.colorWord C 0 = a ∨
        data.degreeTwoBoundaryData.colorWord C 0 = b)
    (hselectedTwo :
      data.degreeTwoBoundaryData.colorWord C 2 = a ∨
        data.degreeTwoBoundaryData.colorWord C 2 = b)
    (hmeetsTwo :
      data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K 2) :
    ¬ data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K 0 := by
  intro hmeetsZero
  exact data.not_kempeComponentMeetsPort_two_of_meetsPort_zero
    hcubic hnotColorable C hC hab K hselectedZero hselectedTwo
      hmeetsZero hmeetsTwo

/-- The first same-side request can be changed to any nonzero color by a
Kempe-closure move while the second side remains fixed. -/
theorem exists_kempeClosure_recolor_firstSide
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (target : Color) (htarget : target ≠ 0) :
    ∃ C' : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).EdgeColoring Color,
      C' ∈ (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).lineGraph.KempeClosure C ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C' ∧
      data.degreeTwoBoundaryData.colorWord C' 0 = target ∧
      data.degreeTwoBoundaryData.colorWord C' 1 = target ∧
      data.degreeTwoBoundaryData.colorWord C' 2 =
        data.degreeTwoBoundaryData.colorWord C 2 ∧
      data.degreeTwoBoundaryData.colorWord C' 3 =
        data.degreeTwoBoundaryData.colorWord C 3 := by
  let deleted := DeletedAdjacentPairGraph G data.firstVertex data.secondVertex
  let boundary := data.degreeTwoBoundaryData
  have hwell := data.degreeTwoBoundaryData_wellFormed hcubic
  have hsame :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data hcubic hnotColorable C hC
  let current := boundary.colorWord C 0
  by_cases hcurrentTarget : current = target
  · refine ⟨C, deleted.lineGraph.mem_kempeClosure_self C, hC,
      hcurrentTarget, ?_, rfl, rfl⟩
    exact hsame.1.symm.trans hcurrentTarget
  have hcurrentNonzero : current ≠ 0 :=
    boundary.colorWord_ne_zero hwell C 0
  have hab : ValidColorPair current target :=
    ⟨hcurrentNonzero, htarget, hcurrentTarget⟩
  rcases boundary.exists_kempeComponentMeetsPort_of_colorWord_selected
    hwell C hab 0 (Or.inl rfl) with ⟨K, hmeetsZero⟩
  have hmeetsOne : boundary.KempeComponentMeetsPort C current target K 1 :=
    (data.kempeComponentMeetsPort_zero_iff_one_of_selected_request
      hcubic hnotColorable C hC hab K (Or.inl rfl)).1 hmeetsZero
  let C' := C.swapOnKempeComponent current target K
  have hC' : IsTaitEdgeColoring deleted C' :=
    isTaitEdgeColoring_swapOnKempeComponent hC hab K
  have hzero : boundary.colorWord C' 0 = target := by
    change boundary.colorWord
      (C.swapOnKempeComponent current target K) 0 = target
    rw [boundary.colorWord_swapOnKempeComponent_of_meetsPort
      C hab K 0 hmeetsZero]
    simp [current]
  have hone : boundary.colorWord C' 1 = target := by
    change boundary.colorWord
      (C.swapOnKempeComponent current target K) 1 = target
    rw [boundary.colorWord_swapOnKempeComponent_of_meetsPort
      C hab K 1 hmeetsOne, ← hsame.1]
    change Equiv.swap current target current = target
    simp
  have htwo : boundary.colorWord C' 2 = boundary.colorWord C 2 := by
    by_cases hselectedTwo :
        boundary.colorWord C 2 = current ∨
          boundary.colorWord C 2 = target
    · have hnotMeetsTwo :
          ¬ boundary.KempeComponentMeetsPort C current target K 2 :=
        data.not_kempeComponentMeetsPort_two_of_meetsPort_zero
          hcubic hnotColorable C hC hab K (Or.inl rfl) hselectedTwo
            hmeetsZero
      exact boundary.colorWord_swapOnKempeComponent_of_not_meetsPort
        C K 2 hnotMeetsTwo
    · by_cases hmeetsTwo :
          boundary.KempeComponentMeetsPort C current target K 2
      · rw [boundary.colorWord_swapOnKempeComponent_of_meetsPort
          C hab K 2 hmeetsTwo]
        simp only [not_or] at hselectedTwo
        rw [Equiv.swap_apply_def, if_neg hselectedTwo.1,
          if_neg hselectedTwo.2]
      · exact boundary.colorWord_swapOnKempeComponent_of_not_meetsPort
          C K 2 hmeetsTwo
  have hsame' :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data hcubic hnotColorable C' hC'
  have hthree : boundary.colorWord C' 3 = boundary.colorWord C 3 := by
    calc
      boundary.colorWord C' 3 = boundary.colorWord C' 2 := hsame'.2.symm
      _ = boundary.colorWord C 2 := htwo
      _ = boundary.colorWord C 3 := hsame.2
  refine ⟨C', ?_, hC', hzero, hone, htwo, hthree⟩
  exact deleted.lineGraph.mem_kempeClosure_of_mem_of_step
    (deleted.lineGraph.mem_kempeClosure_self C) current target K

/-- The second same-side request can independently be changed to any
nonzero color while the first side remains fixed. -/
theorem exists_kempeClosure_recolor_secondSide
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (target : Color) (htarget : target ≠ 0) :
    ∃ C' : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).EdgeColoring Color,
      C' ∈ (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).lineGraph.KempeClosure C ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C' ∧
      data.degreeTwoBoundaryData.colorWord C' 2 = target ∧
      data.degreeTwoBoundaryData.colorWord C' 3 = target ∧
      data.degreeTwoBoundaryData.colorWord C' 0 =
        data.degreeTwoBoundaryData.colorWord C 0 ∧
      data.degreeTwoBoundaryData.colorWord C' 1 =
        data.degreeTwoBoundaryData.colorWord C 1 := by
  let deleted := DeletedAdjacentPairGraph G data.firstVertex data.secondVertex
  let boundary := data.degreeTwoBoundaryData
  have hwell := data.degreeTwoBoundaryData_wellFormed hcubic
  have hsame :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data hcubic hnotColorable C hC
  let current := boundary.colorWord C 2
  by_cases hcurrentTarget : current = target
  · refine ⟨C, deleted.lineGraph.mem_kempeClosure_self C, hC,
      hcurrentTarget, ?_, rfl, rfl⟩
    exact hsame.2.symm.trans hcurrentTarget
  have hcurrentNonzero : current ≠ 0 :=
    boundary.colorWord_ne_zero hwell C 2
  have hab : ValidColorPair current target :=
    ⟨hcurrentNonzero, htarget, hcurrentTarget⟩
  rcases boundary.exists_kempeComponentMeetsPort_of_colorWord_selected
    hwell C hab 2 (Or.inl rfl) with ⟨K, hmeetsTwo⟩
  have hmeetsThree : boundary.KempeComponentMeetsPort C current target K 3 :=
    (data.kempeComponentMeetsPort_two_iff_three_of_selected_request
      hcubic hnotColorable C hC hab K (Or.inl rfl)).1 hmeetsTwo
  let C' := C.swapOnKempeComponent current target K
  have hC' : IsTaitEdgeColoring deleted C' :=
    isTaitEdgeColoring_swapOnKempeComponent hC hab K
  have htwo : boundary.colorWord C' 2 = target := by
    change boundary.colorWord
      (C.swapOnKempeComponent current target K) 2 = target
    rw [boundary.colorWord_swapOnKempeComponent_of_meetsPort
      C hab K 2 hmeetsTwo]
    simp [current]
  have hthree : boundary.colorWord C' 3 = target := by
    change boundary.colorWord
      (C.swapOnKempeComponent current target K) 3 = target
    rw [boundary.colorWord_swapOnKempeComponent_of_meetsPort
      C hab K 3 hmeetsThree, ← hsame.2]
    change Equiv.swap current target current = target
    simp
  have hzero : boundary.colorWord C' 0 = boundary.colorWord C 0 := by
    by_cases hselectedZero :
        boundary.colorWord C 0 = current ∨
          boundary.colorWord C 0 = target
    · have hnotMeetsZero :
          ¬ boundary.KempeComponentMeetsPort C current target K 0 :=
        data.not_kempeComponentMeetsPort_zero_of_meetsPort_two
          hcubic hnotColorable C hC hab K hselectedZero (Or.inl rfl)
            hmeetsTwo
      exact boundary.colorWord_swapOnKempeComponent_of_not_meetsPort
        C K 0 hnotMeetsZero
    · by_cases hmeetsZero :
          boundary.KempeComponentMeetsPort C current target K 0
      · rw [boundary.colorWord_swapOnKempeComponent_of_meetsPort
          C hab K 0 hmeetsZero]
        simp only [not_or] at hselectedZero
        rw [Equiv.swap_apply_def, if_neg hselectedZero.1,
          if_neg hselectedZero.2]
      · exact boundary.colorWord_swapOnKempeComponent_of_not_meetsPort
          C K 0 hmeetsZero
  have hsame' :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data hcubic hnotColorable C' hC'
  have hone : boundary.colorWord C' 1 = boundary.colorWord C 1 := by
    calc
      boundary.colorWord C' 1 = boundary.colorWord C' 0 := hsame'.1.symm
      _ = boundary.colorWord C 0 := hzero
      _ = boundary.colorWord C 1 := hsame.1
  refine ⟨C', ?_, hC', htwo, hthree, hzero, hone⟩
  exact deleted.lineGraph.mem_kempeClosure_of_mem_of_step
    (deleted.lineGraph.mem_kempeClosure_self C) current target K

/-- The Kempe closure realizes every one of the nine nonzero same-side
boundary words, with the two side colors prescribed independently. -/
theorem exists_kempeClosure_coloring_with_sameSide_requests
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (firstTarget secondTarget : Color)
    (hfirstTarget : firstTarget ≠ 0)
    (hsecondTarget : secondTarget ≠ 0) :
    ∃ C' : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).EdgeColoring Color,
      C' ∈ (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).lineGraph.KempeClosure C ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C' ∧
      data.degreeTwoBoundaryData.colorWord C' 0 = firstTarget ∧
      data.degreeTwoBoundaryData.colorWord C' 1 = firstTarget ∧
      data.degreeTwoBoundaryData.colorWord C' 2 = secondTarget ∧
      data.degreeTwoBoundaryData.colorWord C' 3 = secondTarget := by
  let deleted := DeletedAdjacentPairGraph G data.firstVertex data.secondVertex
  rcases data.exists_kempeClosure_recolor_firstSide
    hcubic hnotColorable C hC firstTarget hfirstTarget with
    ⟨C1, hclosure1, hC1, hzero1, hone1, _htwo1, _hthree1⟩
  rcases data.exists_kempeClosure_recolor_secondSide
    hcubic hnotColorable C1 hC1 secondTarget hsecondTarget with
    ⟨C2, hclosure2, hC2, htwo2, hthree2, hzero2, hone2⟩
  refine ⟨C2, ?_, hC2, hzero2.trans hzero1,
    hone2.trans hone1, htwo2, hthree2⟩
  exact deleted.lineGraph.kempeClosure_subset_of_mem hclosure1 hclosure2

/-- In particular, every nonzero constant four-port word occurs in the
same Kempe closure. -/
theorem exists_kempeClosure_coloring_with_constant_colorWord
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (target : Color) (htarget : target ≠ 0) :
    ∃ C' : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).EdgeColoring Color,
      C' ∈ (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).lineGraph.KempeClosure C ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C' ∧
      ∀ port : Fin 4,
        data.degreeTwoBoundaryData.colorWord C' port = target := by
  rcases data.exists_kempeClosure_coloring_with_sameSide_requests
    hcubic hnotColorable C hC target target htarget htarget with
    ⟨C', hclosure, hC', hzero, hone, htwo, hthree⟩
  refine ⟨C', hclosure, hC', ?_⟩
  intro port
  fin_cases port
  · exact hzero
  · exact hone
  · exact htwo
  · exact hthree

/-- There are exactly nine ordered pairs of nonzero Tait colors. -/
theorem card_orderedNonzeroColorPairs :
    Fintype.card
      ({color : Color // color ≠ 0} × {color : Color // color ≠ 0}) = 9 := by
  have hcolor : Fintype.card Color = 4 := by decide
  have hnonzero : Fintype.card {color : Color // color ≠ 0} = 3 := by
    rw [Fintype.card_subtype_compl (fun color : Color => color = 0),
      Fintype.card_subtype_eq, hcolor]
  rw [Fintype.card_prod, hnonzero]

/-- The nine prescribed same-side words can be chosen simultaneously as
nine distinct Tait colorings in one Kempe closure. -/
theorem exists_injective_nineState_sameSide_boundaryOrbit
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    ∃ orbit :
        ({color : Color // color ≠ 0} × {color : Color // color ≠ 0}) →
          (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).EdgeColoring Color,
      Function.Injective orbit ∧
      ∀ target,
        orbit target ∈
          (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).lineGraph.KempeClosure C ∧
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          (orbit target) ∧
        data.degreeTwoBoundaryData.colorWord (orbit target) 0 =
          target.1.1 ∧
        data.degreeTwoBoundaryData.colorWord (orbit target) 1 =
          target.1.1 ∧
        data.degreeTwoBoundaryData.colorWord (orbit target) 2 =
          target.2.1 ∧
        data.degreeTwoBoundaryData.colorWord (orbit target) 3 =
          target.2.1 := by
  classical
  have hexists : ∀ target :
      ({color : Color // color ≠ 0} × {color : Color // color ≠ 0}),
      ∃ C' : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).EdgeColoring Color,
        C' ∈ (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).lineGraph.KempeClosure C ∧
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C' ∧
        data.degreeTwoBoundaryData.colorWord C' 0 = target.1.1 ∧
        data.degreeTwoBoundaryData.colorWord C' 1 = target.1.1 ∧
        data.degreeTwoBoundaryData.colorWord C' 2 = target.2.1 ∧
        data.degreeTwoBoundaryData.colorWord C' 3 = target.2.1 := by
    intro target
    exact data.exists_kempeClosure_coloring_with_sameSide_requests
      hcubic hnotColorable C hC target.1.1 target.2.1
        target.1.2 target.2.2
  choose orbit horbit using hexists
  refine ⟨orbit, ?_, horbit⟩
  intro first second heq
  rcases horbit first with
    ⟨_firstClosure, _firstTait, hfirstZero, _hfirstOne,
      hfirstTwo, _hfirstThree⟩
  rcases horbit second with
    ⟨_secondClosure, _secondTait, hsecondZero, _hsecondOne,
      hsecondTwo, _hsecondThree⟩
  apply Prod.ext
  · apply Subtype.ext
    calc
      first.1.1 = data.degreeTwoBoundaryData.colorWord (orbit first) 0 :=
        hfirstZero.symm
      _ = data.degreeTwoBoundaryData.colorWord (orbit second) 0 :=
        congrArg (fun coloring =>
          data.degreeTwoBoundaryData.colorWord coloring 0) heq
      _ = second.1.1 := hsecondZero
  · apply Subtype.ext
    calc
      first.2.1 = data.degreeTwoBoundaryData.colorWord (orbit first) 2 :=
        hfirstTwo.symm
      _ = data.degreeTwoBoundaryData.colorWord (orbit second) 2 :=
        congrArg (fun coloring =>
          data.degreeTwoBoundaryData.colorWord coloring 2) heq
      _ = second.2.1 := hsecondTwo

/-- In a graph-backed minimal counterexample, every cyclic profile reaches a
constant nonzero four-port word inside its deleted-graph Kempe closure. -/
theorem CyclicKempeProfile.exists_kempeClosure_coloring_with_constant_colorWord_of_minimal
    {graphData : SimpleGraphDartRotation.Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    (profile : CyclicKempeProfile graphData data)
    (target : Color) (htarget : target ≠ 0) :
    ∃ C' : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).EdgeColoring Color,
      C' ∈ (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).lineGraph.KempeClosure profile.coloring ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C' ∧
      ∀ port : Fin 4,
        data.degreeTwoBoundaryData.colorWord C' port = target := by
  have hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal
  exact data.exists_kempeClosure_coloring_with_constant_colorWord
    hcubic hnotColorable profile.coloring profile.isTaitColoring
      target htarget

/-- Every adjacent pair in a graph-backed minimal counterexample can be
rotation-ordered so that its deletion has a Tait coloring whose Kempe closure
contains a prescribed constant nonzero boundary word. -/
theorem exists_rotationOrdered_constantBoundaryWord_of_minimal
    (graphData : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (target : Color) (htarget : target ≠ 0) :
    ∃ ordered : AdjacentPairData G,
      ordered.firstVertex = data.firstVertex ∧
      ordered.secondVertex = data.secondVertex ∧
      ∃ C C' : (DeletedAdjacentPairGraph G ordered.firstVertex
          ordered.secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G ordered.firstVertex
            ordered.secondVertex) C ∧
        C' ∈ (DeletedAdjacentPairGraph G ordered.firstVertex
            ordered.secondVertex).lineGraph.KempeClosure C ∧
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G ordered.firstVertex
            ordered.secondVertex) C' ∧
        ∀ port : Fin 4,
          ordered.degreeTwoBoundaryData.colorWord C' port = target := by
  rcases data.exists_rotationOrdered_cyclicKempeProfile graphData minimal with
    ⟨ordered, hfirst, hsecond, ⟨profile⟩⟩
  rcases profile.exists_kempeClosure_coloring_with_constant_colorWord_of_minimal
    minimal target htarget with ⟨C', hclosure, hC', hconstant⟩
  exact ⟨ordered, hfirst, hsecond, profile.coloring, C',
    profile.isTaitColoring, hclosure, hC', hconstant⟩

end


end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
