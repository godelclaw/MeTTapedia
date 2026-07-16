import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairInsertion
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedTrail

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary
open GoertzelV24FramedTrail

theorem equivSwap_add_of_validColorPair :
    ∀ a b : Color, ValidColorPair a b →
      ∀ x y : Color,
        Equiv.swap a b (x + y) =
          Equiv.swap a b x + Equiv.swap a b y := by
  intro a b hab x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y
  all_goals
    first
    | exact (hab.1 rfl).elim
    | exact (hab.2.1 rfl).elim
    | exact (hab.2.2 rfl).elim
    | decide

/-- Swapping a valid pair moves either member of the pair. -/
theorem equivSwap_ne_self_of_validColorPair
    {a b x : Color} (hab : ValidColorPair a b)
    (hx : x = a ∨ x = b) :
    Equiv.swap a b x ≠ x := by
  rcases hx with rfl | rfl
  · simpa using (Ne.symm hab.2.2)
  · simpa using hab.2.2

/-- Any two nonzero Klein-four colors, equal or distinct, lie in some valid
two-color Kempe pair. -/
theorem exists_validColorPair_containing_of_ne_zero
    {x y : Color} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a b : Color,
      ValidColorPair a b ∧ (x = a ∨ x = b) ∧ (y = a ∨ y = b) := by
  by_cases hxy : x = y
  · subst y
    by_cases hred : x = red
    · subst x
      exact ⟨red, blue, ⟨red_ne_zero, blue_ne_zero, red_ne_blue⟩,
        Or.inl rfl, Or.inl rfl⟩
    · exact ⟨x, red, ⟨hx, red_ne_zero, hred⟩,
        Or.inl rfl, Or.inl rfl⟩
  · exact ⟨x, y, ⟨hx, hy, hxy⟩, Or.inl rfl, Or.inr rfl⟩

/-- Swapping two distinct nonzero Tait colors is an additive symmetry of the
Klein four color group. -/
def validColorPairSwapAddEquiv (a b : Color) (hab : ValidColorPair a b) :
    Color ≃+ Color where
  toEquiv := Equiv.swap a b
  map_add' := equivSwap_add_of_validColorPair a b hab

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A selected two-color component touches a boundary port when it contains
one of the two graph edges incident to that defect vertex. -/
def KempeComponentMeetsPort {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (port : Fin portCount) : Prop :=
  ∃ edge : G.edgeSet,
    edge ∈ incidentEdgeFinset G (data.defectVertex port) ∧
      edge ∈ C.kempeComponentSet a b K

theorem edge_mem_kempeComponent_of_meetsPort_of_incident_of_bicolored
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) {a b : Color}
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    {port : Fin portCount}
    (hmeets : data.KempeComponentMeetsPort C a b K port)
    {edge : G.edgeSet}
    (hincident : edge ∈ incidentEdgeFinset G (data.defectVertex port))
    (hcolor : C edge = a ∨ C edge = b) :
    edge ∈ C.kempeComponentSet a b K := by
  rcases hmeets with ⟨seed, hseedIncident, hseed⟩
  by_cases hedge : edge = seed
  · simpa [hedge] using hseed
  · apply C.mem_kempeComponentSet_of_adj hseed
    · apply (SimpleGraph.lineGraph_adj_iff_exists).2
      refine ⟨Ne.symm hedge, data.defectVertex port, ?_, ?_⟩
      · simpa [incidentEdgeFinset] using hseedIncident
      · simpa [incidentEdgeFinset] using hincident
    · exact hcolor

theorem swapOnKempeComponent_apply_incident_of_meetsPort
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) {a b : Color}
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    {port : Fin portCount}
    (hmeets : data.KempeComponentMeetsPort C a b K port)
    {edge : G.edgeSet}
    (hincident : edge ∈ incidentEdgeFinset G (data.defectVertex port)) :
    C.swapOnKempeComponent a b K edge = Equiv.swap a b (C edge) := by
  by_cases hcolor : C edge = a ∨ C edge = b
  · rw [C.swapOnKempeComponent_apply_of_mem]
    exact data.edge_mem_kempeComponent_of_meetsPort_of_incident_of_bicolored
      C K hmeets hincident hcolor
  · have hnot : edge ∉ C.kempeComponentSet a b K := by
      intro hmem
      exact hcolor (C.mem_bicoloredSet_of_mem_kempeComponentSet hmem)
    rw [C.swapOnKempeComponent_apply_of_not_mem hnot]
    simp only [not_or] at hcolor
    simp [Equiv.swap_apply_def, hcolor.1, hcolor.2]

theorem swapOnKempeComponent_apply_incident_of_not_meetsPort
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) {a b : Color}
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    {port : Fin portCount}
    (hnot : ¬ data.KempeComponentMeetsPort C a b K port)
    {edge : G.edgeSet}
    (hincident : edge ∈ incidentEdgeFinset G (data.defectVertex port)) :
    C.swapOnKempeComponent a b K edge = C edge := by
  apply C.swapOnKempeComponent_apply_of_not_mem
  intro hmem
  exact hnot ⟨edge, hincident, hmem⟩

/-- At a touched degree-two port, a Kempe-component switch swaps the port's
missing color. -/
theorem colorWord_swapOnKempeComponent_of_meetsPort
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (port : Fin portCount)
    (hmeets : data.KempeComponentMeetsPort C a b K port) :
    data.colorWord (C.swapOnKempeComponent a b K) port =
      Equiv.swap a b (data.colorWord C port) := by
  classical
  unfold colorWord vertexKirchhoffSum
  calc
    (∑ edge ∈ incidentEdgeFinset G (data.defectVertex port),
        C.swapOnKempeComponent a b K edge) =
      ∑ edge ∈ incidentEdgeFinset G (data.defectVertex port),
        validColorPairSwapAddEquiv a b hab (C edge) := by
          apply Finset.sum_congr rfl
          intro edge hedge
          exact data.swapOnKempeComponent_apply_incident_of_meetsPort
            C K hmeets hedge
    _ = validColorPairSwapAddEquiv a b hab
        (∑ edge ∈ incidentEdgeFinset G (data.defectVertex port), C edge) := by
          rw [map_sum]

/-- At an untouched degree-two port, a Kempe-component switch fixes the
port's missing color. -/
theorem colorWord_swapOnKempeComponent_of_not_meetsPort
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) {a b : Color}
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (port : Fin portCount)
    (hnot : ¬ data.KempeComponentMeetsPort C a b K port) :
    data.colorWord (C.swapOnKempeComponent a b K) port =
      data.colorWord C port := by
  classical
  unfold colorWord vertexKirchhoffSum
  apply Finset.sum_congr rfl
  intro edge hedge
  exact data.swapOnKempeComponent_apply_incident_of_not_meetsPort
    C K hnot hedge

/-- If two selected-color boundary requests are equal before and after a
component switch, then the component touches the two ports together. -/
theorem kempeComponentMeetsPort_iff_of_equal_colorWords
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (left right : Fin portCount)
    (hword : data.colorWord C left = data.colorWord C right)
    (hselected : data.colorWord C left = a ∨ data.colorWord C left = b)
    (hswapped :
      data.colorWord (C.swapOnKempeComponent a b K) left =
        data.colorWord (C.swapOnKempeComponent a b K) right) :
    data.KempeComponentMeetsPort C a b K left ↔
      data.KempeComponentMeetsPort C a b K right := by
  constructor
  · intro hleft
    by_contra hright
    have hleftAction :=
      data.colorWord_swapOnKempeComponent_of_meetsPort
        C hab K left hleft
    have hrightAction :=
      data.colorWord_swapOnKempeComponent_of_not_meetsPort
        C K right hright
    apply equivSwap_ne_self_of_validColorPair hab hselected
    calc
      Equiv.swap a b (data.colorWord C left) =
          data.colorWord (C.swapOnKempeComponent a b K) left :=
        hleftAction.symm
      _ = data.colorWord (C.swapOnKempeComponent a b K) right := hswapped
      _ = data.colorWord C right := hrightAction
      _ = data.colorWord C left := hword.symm
  · intro hright
    by_contra hleft
    have hleftAction :=
      data.colorWord_swapOnKempeComponent_of_not_meetsPort
        C K left hleft
    have hrightAction :=
      data.colorWord_swapOnKempeComponent_of_meetsPort
        C hab K right hright
    apply equivSwap_ne_self_of_validColorPair hab hselected
    calc
      Equiv.swap a b (data.colorWord C left) =
          Equiv.swap a b (data.colorWord C right) := congrArg _ hword
      _ = data.colorWord (C.swapOnKempeComponent a b K) right :=
        hrightAction.symm
      _ = data.colorWord (C.swapOnKempeComponent a b K) left := hswapped.symm
      _ = data.colorWord C left := hleftAction

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- In an uncolorable cubic graph, a Kempe component whose two colors
include the first-side boundary request touches ports `0` and `1` together. -/
theorem kempeComponentMeetsPort_zero_iff_one_of_selected_request
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
    (hselected :
      data.degreeTwoBoundaryData.colorWord C 0 = a ∨
        data.degreeTwoBoundaryData.colorWord C 0 = b) :
    data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K 0 ↔
      data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K 1 := by
  have hbefore :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data hcubic hnotColorable C hC
  have hC' :=
    GoertzelV24FramedTrail.isTaitEdgeColoring_swapOnKempeComponent hC hab K
  have hafter :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data hcubic hnotColorable (C.swapOnKempeComponent a b K) hC'
  exact data.degreeTwoBoundaryData.kempeComponentMeetsPort_iff_of_equal_colorWords
      C hab K 0 1 hbefore.1 hselected hafter.1

/-- In an uncolorable cubic graph, a Kempe component whose two colors
include the second-side boundary request touches ports `2` and `3` together. -/
theorem kempeComponentMeetsPort_two_iff_three_of_selected_request
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
    (hselected :
      data.degreeTwoBoundaryData.colorWord C 2 = a ∨
        data.degreeTwoBoundaryData.colorWord C 2 = b) :
    data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K 2 ↔
      data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K 3 := by
  have hbefore :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data hcubic hnotColorable C hC
  have hC' :=
    GoertzelV24FramedTrail.isTaitEdgeColoring_swapOnKempeComponent hC hab K
  have hafter :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data hcubic hnotColorable (C.swapOnKempeComponent a b K) hC'
  exact data.degreeTwoBoundaryData.kempeComponentMeetsPort_iff_of_equal_colorWords
      C hab K 2 3 hbefore.2 hselected hafter.2

/-- Exact adjacent-pair Kempe profile forced by uncolorability: there is one
valid color pair containing both same-side boundary requests, and every
component for that pair touches each same-side port pair together. -/
theorem exists_validColorPair_all_kempeComponents_meet_sameSidePorts_together
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    ∃ a b : Color,
      ValidColorPair a b ∧
        (data.degreeTwoBoundaryData.colorWord C 0 = a ∨
          data.degreeTwoBoundaryData.colorWord C 0 = b) ∧
        (data.degreeTwoBoundaryData.colorWord C 2 = a ∨
          data.degreeTwoBoundaryData.colorWord C 2 = b) ∧
        ∀ K : (C.bicoloredSubgraph a b).ConnectedComponent,
          (data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K 0 ↔
            data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K 1) ∧
          (data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K 2 ↔
            data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K 3) := by
  have hwell := data.degreeTwoBoundaryData_wellFormed hcubic
  have hzero : data.degreeTwoBoundaryData.colorWord C 0 ≠ 0 :=
    data.degreeTwoBoundaryData.colorWord_ne_zero hwell C 0
  have htwo : data.degreeTwoBoundaryData.colorWord C 2 ≠ 0 :=
    data.degreeTwoBoundaryData.colorWord_ne_zero hwell C 2
  rcases exists_validColorPair_containing_of_ne_zero hzero htwo with
    ⟨a, b, hab, hselectedZero, hselectedTwo⟩
  refine ⟨a, b, hab, hselectedZero, hselectedTwo, ?_⟩
  intro K
  exact ⟨
    data.kempeComponentMeetsPort_zero_iff_one_of_selected_request
      hcubic hnotColorable C hC hab K hselectedZero,
    data.kempeComponentMeetsPort_two_iff_three_of_selected_request
      hcubic hnotColorable C hC hab K hselectedTwo⟩

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
