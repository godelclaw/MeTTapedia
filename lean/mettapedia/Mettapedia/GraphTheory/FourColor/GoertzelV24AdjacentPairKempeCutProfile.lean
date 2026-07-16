import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCyclicKempeProfile

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

/-- The sum of two colors selected from a valid pair is not itself selected. -/
theorem validColorPair_add_not_selected_of_summands_selected :
    ∀ a b : Color, ValidColorPair a b →
      ∀ x y : Color,
        (x = a ∨ x = b) → (y = a ∨ y = b) →
          x + y ≠ a ∧ x + y ≠ b := by
  intro a b hab x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y
  all_goals
    first
    | exact (hab.1 rfl).elim
    | exact (hab.2.1 rfl).elim
    | exact (hab.2.2 rfl).elim
    | decide

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cutProfileGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Two Kempe-component labels containing the same selected edge are equal. -/
theorem kempeComponent_eq_of_common_edge
    (C : G.EdgeColoring Color) {a b : Color}
    {K L : (C.bicoloredSubgraph a b).ConnectedComponent}
    {edge : G.edgeSet}
    (hK : edge ∈ C.kempeComponentSet a b K)
    (hL : edge ∈ C.kempeComponentSet a b L) :
    K = L := by
  rcases hK with ⟨hcolorK, hcomponentK⟩
  rcases hL with ⟨hcolorL, hcomponentL⟩
  have hedge :
      (⟨edge, hcolorK⟩ : C.bicoloredSet a b) = ⟨edge, hcolorL⟩ := by
    rfl
  calc
    K = (C.bicoloredSubgraph a b).connectedComponentMk
        ⟨edge, hcolorK⟩ := hcomponentK.symm
    _ = (C.bicoloredSubgraph a b).connectedComponentMk
        ⟨edge, hcolorL⟩ := congrArg _ hedge
    _ = L := hcomponentL

/-- A selected missing-color request makes the component touching that
degree-two port unique. -/
theorem kempeComponent_eq_of_meetsPort_of_colorWord_selected
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (port : Fin portCount)
    (hselected : data.colorWord C port = a ∨ data.colorWord C port = b)
    {K L : (C.bicoloredSubgraph a b).ConnectedComponent}
    (hK : data.KempeComponentMeetsPort C a b K port)
    (hL : data.KempeComponentMeetsPort C a b L port) :
    K = L := by
  rcases hK with ⟨first, hfirstIncident, hfirstK⟩
  rcases hL with ⟨second, hsecondIncident, hsecondL⟩
  have hfirstColor := C.mem_bicoloredSet_of_mem_kempeComponentSet hfirstK
  have hsecondColor := C.mem_bicoloredSet_of_mem_kempeComponentSet hsecondL
  have hedges : first = second := by
    by_contra hne
    have hpairSubset :
        ({first, second} : Finset G.edgeSet) ⊆
          incidentEdgeFinset G (data.defectVertex port) := by
      intro edge hedge
      simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
      rcases hedge with rfl | rfl
      · exact hfirstIncident
      · exact hsecondIncident
    have hpairCard : ({first, second} : Finset G.edgeSet).card = 2 := by
      simp [hne]
    have hincidentCard :
        (incidentEdgeFinset G (data.defectVertex port)).card = 2 :=
      hdata.2.1 port
    have hpair :
        ({first, second} : Finset G.edgeSet) =
          incidentEdgeFinset G (data.defectVertex port) := by
      apply Finset.eq_of_subset_of_card_le hpairSubset
      omega
    have hsumSelected :
        C first + C second = a ∨ C first + C second = b := by
      simpa [colorWord, vertexKirchhoffSum, ← hpair, hne] using hselected
    have hnot := validColorPair_add_not_selected_of_summands_selected
      a b hab (C first) (C second) hfirstColor hsecondColor
    exact hsumSelected.elim hnot.1 hnot.2
  subst second
  exact kempeComponent_eq_of_common_edge C hfirstK hsecondL

/-- The ports met by one Kempe component. -/
noncomputable def kempePortSupport {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    Finset (Fin portCount) := by
  classical
  exact Finset.univ.filter fun port =>
    data.KempeComponentMeetsPort C a b K port

@[simp]
theorem mem_kempePortSupport_iff {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (port : Fin portCount) :
    port ∈ data.kempePortSupport C a b K ↔
      data.KempeComponentMeetsPort C a b K port := by
  classical
  simp [kempePortSupport]

/-- The exact one-or-two boundary-component alternatives for a four-port
Kempe cut. -/
def HasExactSameSideKempeCutProfile
    (data : DegreeTwoBoundaryData G 4)
    (C : G.EdgeColoring Color) (a b : Color) : Prop :=
  (∃ K : (C.bicoloredSubgraph a b).ConnectedComponent,
    data.kempePortSupport C a b K = Finset.univ ∧
    ∀ L : (C.bicoloredSubgraph a b).ConnectedComponent,
      (data.kempePortSupport C a b L).Nonempty → L = K) ∨
  ∃ K01 K23 : (C.bicoloredSubgraph a b).ConnectedComponent,
    K01 ≠ K23 ∧
    data.kempePortSupport C a b K01 = {0, 1} ∧
    data.kempePortSupport C a b K23 = {2, 3} ∧
    ∀ L : (C.bicoloredSubgraph a b).ConnectedComponent,
      (data.kempePortSupport C a b L).Nonempty →
        L = K01 ∨ L = K23

/-- Exact four-port cut profile for one selected Kempe family. Paired
incidence and selected requests force either one all-port boundary component
or exactly two boundary components with supports `01` and `23`. -/
theorem exists_one_allPort_or_two_sameSide_kempeComponents
    (data : DegreeTwoBoundaryData G 4)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (hselected : ∀ port : Fin 4,
      data.colorWord C port = a ∨ data.colorWord C port = b)
    (hpaired : ∀ K : (C.bicoloredSubgraph a b).ConnectedComponent,
      (data.KempeComponentMeetsPort C a b K 0 ↔
        data.KempeComponentMeetsPort C a b K 1) ∧
      (data.KempeComponentMeetsPort C a b K 2 ↔
        data.KempeComponentMeetsPort C a b K 3)) :
    data.HasExactSameSideKempeCutProfile C a b := by
  classical
  unfold HasExactSameSideKempeCutProfile
  rcases data.exists_kempeComponentMeetsPort_of_colorWord_selected
      hdata C hab 0 (hselected 0) with ⟨K01, hK01zero⟩
  rcases data.exists_kempeComponentMeetsPort_of_colorWord_selected
      hdata C hab 2 (hselected 2) with ⟨K23, hK23two⟩
  have hK01one := (hpaired K01).1.1 hK01zero
  have hK23three := (hpaired K23).2.1 hK23two
  by_cases heq : K01 = K23
  · subst K23
    left
    refine ⟨K01, ?_, ?_⟩
    · ext port
      fin_cases port <;>
        simp [kempePortSupport, hK01zero, hK01one, hK23two, hK23three]
    · intro L hL
      rcases hL with ⟨port, hport⟩
      have hLmeets : data.KempeComponentMeetsPort C a b L port :=
        (data.mem_kempePortSupport_iff C a b L port).1 hport
      have hKmeets : data.KempeComponentMeetsPort C a b K01 port := by
        fin_cases port
        · exact hK01zero
        · exact hK01one
        · exact hK23two
        · exact hK23three
      exact data.kempeComponent_eq_of_meetsPort_of_colorWord_selected
        hdata C hab port (hselected port) hLmeets hKmeets
  · right
    have hK01notTwo :
        ¬ data.KempeComponentMeetsPort C a b K01 2 := by
      intro hmeet
      exact heq (data.kempeComponent_eq_of_meetsPort_of_colorWord_selected
        hdata C hab 2 (hselected 2) hmeet hK23two)
    have hK01notThree :
        ¬ data.KempeComponentMeetsPort C a b K01 3 := by
      intro hmeet
      exact hK01notTwo ((hpaired K01).2.2 hmeet)
    have hK23notZero :
        ¬ data.KempeComponentMeetsPort C a b K23 0 := by
      intro hmeet
      exact heq (data.kempeComponent_eq_of_meetsPort_of_colorWord_selected
        hdata C hab 0 (hselected 0) hK01zero hmeet)
    have hK23notOne :
        ¬ data.KempeComponentMeetsPort C a b K23 1 := by
      intro hmeet
      exact hK23notZero ((hpaired K23).1.2 hmeet)
    refine ⟨K01, K23, heq, ?_, ?_, ?_⟩
    · ext port
      fin_cases port <;>
        simp [kempePortSupport, hK01zero, hK01one,
          hK01notTwo, hK01notThree]
    · ext port
      fin_cases port <;>
        simp [kempePortSupport, hK23notZero, hK23notOne,
          hK23two, hK23three]
    · intro L hL
      rcases hL with ⟨port, hport⟩
      have hLmeets : data.KempeComponentMeetsPort C a b L port :=
        (data.mem_kempePortSupport_iff C a b L port).1 hport
      fin_cases port
      · exact Or.inl
          (data.kempeComponent_eq_of_meetsPort_of_colorWord_selected
            hdata C hab 0 (hselected 0) hLmeets hK01zero)
      · exact Or.inl
          (data.kempeComponent_eq_of_meetsPort_of_colorWord_selected
            hdata C hab 1 (hselected 1) hLmeets hK01one)
      · exact Or.inr
          (data.kempeComponent_eq_of_meetsPort_of_colorWord_selected
            hdata C hab 2 (hselected 2) hLmeets hK23two)
      · exact Or.inr
          (data.kempeComponent_eq_of_meetsPort_of_colorWord_selected
            hdata C hab 3 (hselected 3) hLmeets hK23three)

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24AdjacentPairBoundary
open GoertzelV24FourDefectBoundary

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance exactCutGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance exactCutRetainedVertexSetFintype (first second : V) :
    Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance exactCutRetainedVertexSetDecidableEq (first second : V) :
    DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- The bundled cyclic profile has the exact one-or-two component cut
classification as soon as its canonical boundary is exposed as well formed. -/
theorem CyclicKempeProfile.hasExactSameSideKempeCutProfile
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    (profile : CyclicKempeProfile graphData data) :
    data.degreeTwoBoundaryData.HasExactSameSideKempeCutProfile
      profile.coloring profile.firstColor profile.secondColor := by
  have hsame :
      data.degreeTwoBoundaryData.colorWord profile.coloring 0 =
          data.degreeTwoBoundaryData.colorWord profile.coloring 1 ∧
        data.degreeTwoBoundaryData.colorWord profile.coloring 2 =
          data.degreeTwoBoundaryData.colorWord profile.coloring 3 := by
    simpa [SquareReductionSide.Compatible,
      SquareReductionSide.join01_23] using profile.reductionCompatible
  have hselected : ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord profile.coloring port =
          profile.firstColor ∨
        data.degreeTwoBoundaryData.colorWord profile.coloring port =
          profile.secondColor := by
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
  exact data.degreeTwoBoundaryData.exists_one_allPort_or_two_sameSide_kempeComponents
      profile.boundaryWellFormed profile.coloring profile.validPair hselected
        profile.componentProfile

end


end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
