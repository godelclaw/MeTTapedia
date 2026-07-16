import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeTerminalProfile

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24AdjacentPairBoundary
open GoertzelV24FramedTrail

namespace GoertzelV24FourDefectBoundary

/-- Swap a selected color pair exactly on a finite set of boundary ports. -/
def boundaryKempeSwap {portCount : Nat}
    (a b : Color) (support : Finset (Fin portCount))
    (word : Fin portCount → Color) : Fin portCount → Color :=
  fun port =>
    if port ∈ support then Equiv.swap a b (word port) else word port

@[simp] theorem boundaryKempeSwap_apply_of_mem {portCount : Nat}
    (a b : Color) (support : Finset (Fin portCount))
    (word : Fin portCount → Color) {port : Fin portCount}
    (hport : port ∈ support) :
    boundaryKempeSwap a b support word port = Equiv.swap a b (word port) := by
  simp [boundaryKempeSwap, hport]

@[simp] theorem boundaryKempeSwap_apply_of_not_mem {portCount : Nat}
    (a b : Color) (support : Finset (Fin portCount))
    (word : Fin portCount → Color) {port : Fin portCount}
    (hport : port ∉ support) :
    boundaryKempeSwap a b support word port = word port := by
  simp [boundaryKempeSwap, hport]

/-- A boundary Kempe switch is an involution. -/
@[simp] theorem boundaryKempeSwap_involutive {portCount : Nat}
    (a b : Color) (support : Finset (Fin portCount))
    (word : Fin portCount → Color) :
    boundaryKempeSwap a b support
        (boundaryKempeSwap a b support word) = word := by
  funext port
  by_cases hport : port ∈ support <;>
    simp [boundaryKempeSwap, hport]

/-- Boundary switches of the same color pair commute, even when their
supports overlap. -/
theorem boundaryKempeSwap_commute {portCount : Nat}
    (a b : Color) (first second : Finset (Fin portCount))
    (word : Fin portCount → Color) :
    boundaryKempeSwap a b first (boundaryKempeSwap a b second word) =
      boundaryKempeSwap a b second (boundaryKempeSwap a b first word) := by
  funext port
  by_cases hfirst : port ∈ first <;>
    by_cases hsecond : port ∈ second <;>
      simp [boundaryKempeSwap, hfirst, hsecond]

/-- Switching the two disjoint same-side supports is the global relabeling
of the selected color pair on all four ports. -/
theorem boundaryKempeSwap_sameSides_eq_global
    (a b : Color) (word : Fin 4 → Color) :
    boundaryKempeSwap a b {0, 1}
        (boundaryKempeSwap a b {2, 3} word) =
      fun port => Equiv.swap a b (word port) := by
  funext port
  fin_cases port <;> simp [boundaryKempeSwap]

namespace DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance sideSwitchGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The support of a graph-level component is exactly the support of its
induced action on the boundary color word. -/
theorem colorWord_swapOnKempeComponent_eq_boundaryKempeSwap
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    data.colorWord (C.swapOnKempeComponent a b K) =
      boundaryKempeSwap a b (data.kempePortSupport C a b K)
        (data.colorWord C) := by
  funext port
  by_cases hmeets : data.KempeComponentMeetsPort C a b K port
  · rw [data.colorWord_swapOnKempeComponent_of_meetsPort
      C hab K port hmeets]
    exact (boundaryKempeSwap_apply_of_mem a b
      (data.kempePortSupport C a b K) (data.colorWord C)
      ((data.mem_kempePortSupport_iff C a b K port).2 hmeets)).symm
  · rw [data.colorWord_swapOnKempeComponent_of_not_meetsPort
      C K port hmeets]
    exact (boundaryKempeSwap_apply_of_not_mem a b
      (data.kempePortSupport C a b K) (data.colorWord C)
      (fun hport => hmeets
        ((data.mem_kempePortSupport_iff C a b K port).1 hport))).symm

/-- A component meeting a selected boundary request produces a genuinely
different edge coloring. -/
theorem swapOnKempeComponent_ne_of_meetsPort_of_selected
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (port : Fin portCount)
    (hmeets : data.KempeComponentMeetsPort C a b K port)
    (hselected : data.colorWord C port = a ∨
      data.colorWord C port = b) :
    C.swapOnKempeComponent a b K ≠ C := by
  intro heq
  have hwordEq :
      data.colorWord (C.swapOnKempeComponent a b K) port =
        data.colorWord C port :=
    congrArg (fun coloring => data.colorWord coloring port) heq
  rw [data.colorWord_swapOnKempeComponent_of_meetsPort
    C hab K port hmeets] at hwordEq
  exact (equivSwap_ne_self_of_validColorPair hab hselected) hwordEq

/-- An exact two-component cut yields the two precise same-side boundary
switch actions. -/
theorem exists_two_sameSide_kempeSwitchActions
    (data : DegreeTwoBoundaryData G 4)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (hprofile : data.HasTwoSameSideKempeCutProfile C a b) :
    ∃ K01 K23 : (C.bicoloredSubgraph a b).ConnectedComponent,
      K01 ≠ K23 ∧
      data.colorWord (C.swapOnKempeComponent a b K01) =
        boundaryKempeSwap a b {0, 1} (data.colorWord C) ∧
      data.colorWord (C.swapOnKempeComponent a b K23) =
        boundaryKempeSwap a b {2, 3} (data.colorWord C) := by
  rcases hprofile with
    ⟨K01, K23, hne, hsupport01, hsupport23, _hexhaust⟩
  refine ⟨K01, K23, hne, ?_, ?_⟩
  · rw [data.colorWord_swapOnKempeComponent_eq_boundaryKempeSwap
      C hab K01, hsupport01]
  · rw [data.colorWord_swapOnKempeComponent_eq_boundaryKempeSwap
      C hab K23, hsupport23]

/-- The two exact same-side components give two pairwise distinct genuine
Tait successors of the original coloring, with their boundary actions made
explicit. -/
theorem exists_two_distinct_sameSide_kempeSwitchColorings
    (data : DegreeTwoBoundaryData G 4)
    (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C) {a b : Color}
    (hab : ValidColorPair a b)
    (hselected : ∀ port : Fin 4,
      data.colorWord C port = a ∨ data.colorWord C port = b)
    (hprofile : data.HasTwoSameSideKempeCutProfile C a b) :
    ∃ K01 K23 : (C.bicoloredSubgraph a b).ConnectedComponent,
      K01 ≠ K23 ∧
      IsTaitEdgeColoring G (C.swapOnKempeComponent a b K01) ∧
      IsTaitEdgeColoring G (C.swapOnKempeComponent a b K23) ∧
      C.swapOnKempeComponent a b K01 ≠ C ∧
      C.swapOnKempeComponent a b K23 ≠ C ∧
      C.swapOnKempeComponent a b K01 ≠
        C.swapOnKempeComponent a b K23 ∧
      data.colorWord (C.swapOnKempeComponent a b K01) =
        boundaryKempeSwap a b {0, 1} (data.colorWord C) ∧
      data.colorWord (C.swapOnKempeComponent a b K23) =
        boundaryKempeSwap a b {2, 3} (data.colorWord C) := by
  rcases hprofile with
    ⟨K01, K23, hne, hsupport01, hsupport23, hexhaust⟩
  have hmeet01zero :
      data.KempeComponentMeetsPort C a b K01 0 := by
    apply (data.mem_kempePortSupport_iff C a b K01 0).1
    rw [hsupport01]
    simp
  have hnotMeet23zero :
      ¬ data.KempeComponentMeetsPort C a b K23 0 := by
    intro hmeet
    have hmem := (data.mem_kempePortSupport_iff C a b K23 0).2 hmeet
    rw [hsupport23] at hmem
    simp at hmem
  have hmeet23two :
      data.KempeComponentMeetsPort C a b K23 2 := by
    apply (data.mem_kempePortSupport_iff C a b K23 2).1
    rw [hsupport23]
    simp
  have hne01 : C.swapOnKempeComponent a b K01 ≠ C :=
    data.swapOnKempeComponent_ne_of_meetsPort_of_selected
      C hab K01 0 hmeet01zero (hselected 0)
  have hne23 : C.swapOnKempeComponent a b K23 ≠ C :=
    data.swapOnKempeComponent_ne_of_meetsPort_of_selected
      C hab K23 2 hmeet23two (hselected 2)
  have hswitchNe :
      C.swapOnKempeComponent a b K01 ≠
        C.swapOnKempeComponent a b K23 := by
    intro heq
    apply equivSwap_ne_self_of_validColorPair hab (hselected 0)
    calc
      Equiv.swap a b (data.colorWord C 0) =
          data.colorWord (C.swapOnKempeComponent a b K01) 0 :=
        (data.colorWord_swapOnKempeComponent_of_meetsPort
          C hab K01 0 hmeet01zero).symm
      _ = data.colorWord (C.swapOnKempeComponent a b K23) 0 :=
        congrArg (fun coloring => data.colorWord coloring 0) heq
      _ = data.colorWord C 0 :=
        data.colorWord_swapOnKempeComponent_of_not_meetsPort
          C K23 0 hnotMeet23zero
  refine ⟨K01, K23, hne,
    isTaitEdgeColoring_swapOnKempeComponent hC hab K01,
    isTaitEdgeColoring_swapOnKempeComponent hC hab K23,
    hne01, hne23, hswitchNe, ?_, ?_⟩
  · rw [data.colorWord_swapOnKempeComponent_eq_boundaryKempeSwap
      C hab K01, hsupport01]
  · rw [data.colorWord_swapOnKempeComponent_eq_boundaryKempeSwap
      C hab K23, hsupport23]

end

end DegreeTwoBoundaryData

end GoertzelV24FourDefectBoundary

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cyclicSideSwitchGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet := Subtype.instDecidableEq

local instance cyclicSideSwitchRetainedVertexSetFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance cyclicSideSwitchRetainedVertexSetDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- Every one of the four cyclic-profile requests belongs to the selected
color pair. -/
theorem CyclicKempeProfile.allRequestsSelected
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    (profile : CyclicKempeProfile graphData data) :
    ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord profile.coloring port =
          profile.firstColor ∨
        data.degreeTwoBoundaryData.colorWord profile.coloring port =
          profile.secondColor := by
  have hsame :
      data.degreeTwoBoundaryData.colorWord profile.coloring 0 =
          data.degreeTwoBoundaryData.colorWord profile.coloring 1 ∧
        data.degreeTwoBoundaryData.colorWord profile.coloring 2 =
          data.degreeTwoBoundaryData.colorWord profile.coloring 3 := by
    simpa [SquareReductionSide.Compatible,
      SquareReductionSide.join01_23] using profile.reductionCompatible
  intro port
  fin_cases port
  · exact profile.firstRequestSelected
  · rcases profile.firstRequestSelected with hfirst | hsecond
    · exact Or.inl (hsame.1.symm.trans hfirst)
    · exact Or.inr (hsame.1.symm.trans hsecond)
  · exact profile.secondRequestSelected
  · rcases profile.secondRequestSelected with hfirst | hsecond
    · exact Or.inl (hsame.2.symm.trans hfirst)
    · exact Or.inr (hsame.2.symm.trans hsecond)

/-- A cyclic adjacent-pair profile supplies two pairwise distinct genuine
Tait successors, one switching each side of the cyclic four-port cut. -/
theorem CyclicKempeProfile.exists_two_distinct_sameSide_kempeSwitchColorings
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    (profile : CyclicKempeProfile graphData data) :
    ∃ K01 K23 :
        (profile.coloring.bicoloredSubgraph
          profile.firstColor profile.secondColor).ConnectedComponent,
      K01 ≠ K23 ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        (profile.coloring.swapOnKempeComponent
          profile.firstColor profile.secondColor K01) ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        (profile.coloring.swapOnKempeComponent
          profile.firstColor profile.secondColor K23) ∧
      profile.coloring.swapOnKempeComponent
          profile.firstColor profile.secondColor K01 ≠ profile.coloring ∧
      profile.coloring.swapOnKempeComponent
          profile.firstColor profile.secondColor K23 ≠ profile.coloring ∧
      profile.coloring.swapOnKempeComponent
          profile.firstColor profile.secondColor K01 ≠
        profile.coloring.swapOnKempeComponent
          profile.firstColor profile.secondColor K23 ∧
      data.degreeTwoBoundaryData.colorWord
          (profile.coloring.swapOnKempeComponent
            profile.firstColor profile.secondColor K01) =
        GoertzelV24FourDefectBoundary.boundaryKempeSwap
          profile.firstColor profile.secondColor {0, 1}
            (data.degreeTwoBoundaryData.colorWord profile.coloring) ∧
      data.degreeTwoBoundaryData.colorWord
          (profile.coloring.swapOnKempeComponent
            profile.firstColor profile.secondColor K23) =
        GoertzelV24FourDefectBoundary.boundaryKempeSwap
          profile.firstColor profile.secondColor {2, 3}
            (data.degreeTwoBoundaryData.colorWord profile.coloring) :=
  data.degreeTwoBoundaryData.exists_two_distinct_sameSide_kempeSwitchColorings
    profile.coloring profile.isTaitColoring profile.validPair
      profile.allRequestsSelected profile.hasTwoSameSideKempeCutProfile

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
