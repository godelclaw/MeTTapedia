import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarTerminalAlternation
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorPumping

/-! Companion-color transfer along an intrinsic singleton discrepancy trail. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24CorridorPumping
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- The finite color state carried by one edge of a selected scalar
discrepancy support.  Exactly one of the two genuine Tait colorings uses the
distinguished zero-coordinate color. -/
def ScalarDiscrepancyColorState (coordinate : Bool) :=
  {colors : Color × Color //
    colors.1 ≠ 0 ∧ colors.2 ≠ 0 ∧
      ((colors.1 = crossFaceZeroColor coordinate ∧
          colors.2 ≠ crossFaceZeroColor coordinate) ∨
        (colors.1 ≠ crossFaceZeroColor coordinate ∧
          colors.2 = crossFaceZeroColor coordinate))}

instance (coordinate : Bool) :
    DecidableEq (ScalarDiscrepancyColorState coordinate) :=
  Subtype.instDecidableEq

@[reducible] def scalarDiscrepancyColorStateFintype (coordinate : Bool) :
    Fintype (ScalarDiscrepancyColorState coordinate) :=
  Fintype.ofFinset
    ((Finset.univ : Finset (Color × Color)).filter
      (fun colors : Color × Color =>
        colors.1 ≠ 0 ∧ colors.2 ≠ 0 ∧
          ((colors.1 = crossFaceZeroColor coordinate ∧
              colors.2 ≠ crossFaceZeroColor coordinate) ∨
            (colors.1 ≠ crossFaceZeroColor coordinate ∧
              colors.2 = crossFaceZeroColor coordinate)))) (by
      intro state
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl)

instance (priority := 2000) (coordinate : Bool) :
    Fintype (ScalarDiscrepancyColorState coordinate) :=
  scalarDiscrepancyColorStateFintype coordinate

/-- There are two choices of owner and two choices of the other nonzero
color. -/
theorem card_scalarDiscrepancyColorState (coordinate : Bool) :
    @Fintype.card (ScalarDiscrepancyColorState coordinate)
      (scalarDiscrepancyColorStateFintype coordinate) = 4 := by
  cases coordinate <;> decide

namespace ScalarDiscrepancyColorState

variable {coordinate : Bool}

/-- Color supplied by the source coloring. -/
def sourceColor (state : ScalarDiscrepancyColorState coordinate) : Color :=
  state.1.1

/-- Color supplied by the target coloring. -/
def targetColor (state : ScalarDiscrepancyColorState coordinate) : Color :=
  state.1.2

@[simp]
theorem sourceColor_ne_zero
    (state : ScalarDiscrepancyColorState coordinate) :
    state.sourceColor ≠ 0 :=
  state.2.1

@[simp]
theorem targetColor_ne_zero
    (state : ScalarDiscrepancyColorState coordinate) :
    state.targetColor ≠ 0 :=
  state.2.2.1

theorem exactlyOne_zeroColor
    (state : ScalarDiscrepancyColorState coordinate) :
    (state.sourceColor = crossFaceZeroColor coordinate ∧
        state.targetColor ≠ crossFaceZeroColor coordinate) ∨
      (state.sourceColor ≠ crossFaceZeroColor coordinate ∧
        state.targetColor = crossFaceZeroColor coordinate) :=
  state.2.2.2

theorem targetColor_ne_zeroColor_of_sourceColor_eq
    (state : ScalarDiscrepancyColorState coordinate)
    (hsource : state.sourceColor = crossFaceZeroColor coordinate) :
    state.targetColor ≠ crossFaceZeroColor coordinate := by
  rcases state.exactlyOne_zeroColor with hsourceState | htargetState
  · exact hsourceState.2
  · exact False.elim (htargetState.1 hsource)

theorem sourceColor_ne_zeroColor_of_targetColor_eq
    (state : ScalarDiscrepancyColorState coordinate)
    (htarget : state.targetColor = crossFaceZeroColor coordinate) :
    state.sourceColor ≠ crossFaceZeroColor coordinate := by
  rcases state.exactlyOne_zeroColor with hsourceState | htargetState
  · exact False.elim (hsourceState.2 htarget)
  · exact htargetState.1

theorem targetColor_eq_zeroColor_of_sourceColor_ne
    (state : ScalarDiscrepancyColorState coordinate)
    (hsource : state.sourceColor ≠ crossFaceZeroColor coordinate) :
    state.targetColor = crossFaceZeroColor coordinate := by
  rcases state.exactlyOne_zeroColor with hsourceState | htargetState
  · exact False.elim (hsource hsourceState.1)
  · exact htargetState.2

theorem sourceColor_eq_zeroColor_of_targetColor_ne
    (state : ScalarDiscrepancyColorState coordinate)
    (htarget : state.targetColor ≠ crossFaceZeroColor coordinate) :
    state.sourceColor = crossFaceZeroColor coordinate := by
  rcases state.exactlyOne_zeroColor with hsourceState | htargetState
  · exact hsourceState.1
  · exact False.elim (htarget htargetState.2)

/-- The non-distinguished color on a scalar-support edge. -/
def companionColor
    (state : ScalarDiscrepancyColorState coordinate) : Color :=
  if state.sourceColor = crossFaceZeroColor coordinate then
    state.targetColor
  else
    state.sourceColor

@[simp]
theorem companionColor_of_sourceColor_eq
    (state : ScalarDiscrepancyColorState coordinate)
    (hsource : state.sourceColor = crossFaceZeroColor coordinate) :
    state.companionColor = state.targetColor := by
  simp [companionColor, hsource]

@[simp]
theorem companionColor_of_sourceColor_ne
    (state : ScalarDiscrepancyColorState coordinate)
    (hsource : state.sourceColor ≠ crossFaceZeroColor coordinate) :
    state.companionColor = state.sourceColor := by
  simp [companionColor, hsource]

@[simp]
theorem companionColor_ne_zero
    (state : ScalarDiscrepancyColorState coordinate) :
    state.companionColor ≠ 0 := by
  by_cases hsource :
      state.sourceColor = crossFaceZeroColor coordinate
  · rw [state.companionColor_of_sourceColor_eq hsource]
    exact state.targetColor_ne_zero
  · rw [state.companionColor_of_sourceColor_ne hsource]
    exact state.sourceColor_ne_zero

@[simp]
theorem companionColor_ne_zeroColor
    (state : ScalarDiscrepancyColorState coordinate) :
    state.companionColor ≠ crossFaceZeroColor coordinate := by
  by_cases hsource :
      state.sourceColor = crossFaceZeroColor coordinate
  · rw [state.companionColor_of_sourceColor_eq hsource]
    exact state.targetColor_ne_zeroColor_of_sourceColor_eq hsource
  · rw [state.companionColor_of_sourceColor_ne hsource]
    exact hsource

end ScalarDiscrepancyColorState

/-- Successive scalar-support edges alternate which coloring owns the
distinguished color. -/
def ScalarDiscrepancyColorTransition {coordinate : Bool}
    (first second : ScalarDiscrepancyColorState coordinate) : Prop :=
  (first.sourceColor = crossFaceZeroColor coordinate ∧
      second.targetColor = crossFaceZeroColor coordinate) ∨
    (first.targetColor = crossFaceZeroColor coordinate ∧
      second.sourceColor = crossFaceZeroColor coordinate)

/-- The discrepancy emitted through the third edge at a cubic junction. -/
def scalarDiscrepancyTransverseEmission {coordinate : Bool}
    (first second : ScalarDiscrepancyColorState coordinate) : Color :=
  (first.sourceColor + second.sourceColor) +
    (first.targetColor + second.targetColor)

/-- At an alternating junction, cancellation of the two distinguished
colors leaves exactly the sum of the two companion colors. -/
theorem scalarDiscrepancyTransverseEmission_eq_companion_add
    {coordinate : Bool}
    {first second : ScalarDiscrepancyColorState coordinate}
    (htransition : ScalarDiscrepancyColorTransition first second) :
    scalarDiscrepancyTransverseEmission first second =
      first.companionColor + second.companionColor := by
  rcases htransition with hsourceTarget | htargetSource
  · have hsecondSource :=
      second.sourceColor_ne_zeroColor_of_targetColor_eq hsourceTarget.2
    rw [first.companionColor_of_sourceColor_eq hsourceTarget.1,
      second.companionColor_of_sourceColor_ne hsecondSource]
    unfold scalarDiscrepancyTransverseEmission
    rw [hsourceTarget.1, hsourceTarget.2]
    calc
      (crossFaceZeroColor coordinate + second.sourceColor) +
          (first.targetColor + crossFaceZeroColor coordinate) =
          (crossFaceZeroColor coordinate +
              crossFaceZeroColor coordinate) +
            (first.targetColor + second.sourceColor) := by abel
      _ = first.targetColor + second.sourceColor := by simp
  · have hfirstSource :=
      first.sourceColor_ne_zeroColor_of_targetColor_eq htargetSource.1
    rw [first.companionColor_of_sourceColor_ne hfirstSource,
      second.companionColor_of_sourceColor_eq htargetSource.2]
    unfold scalarDiscrepancyTransverseEmission
    rw [htargetSource.1, htargetSource.2]
    calc
      (first.sourceColor + crossFaceZeroColor coordinate) +
          (crossFaceZeroColor coordinate + second.targetColor) =
          (crossFaceZeroColor coordinate +
              crossFaceZeroColor coordinate) +
            (first.sourceColor + second.targetColor) := by abel
      _ = first.sourceColor + second.targetColor := by simp

/-- A straight companion transition emits no transverse discrepancy. -/
theorem scalarDiscrepancyTransverseEmission_eq_zero_iff_companion_eq
    {coordinate : Bool}
    {first second : ScalarDiscrepancyColorState coordinate}
    (htransition : ScalarDiscrepancyColorTransition first second) :
    scalarDiscrepancyTransverseEmission first second = 0 ↔
      first.companionColor = second.companionColor := by
  rw [scalarDiscrepancyTransverseEmission_eq_companion_add htransition]
  exact add_eq_zero_iff_eq _ _

/-- A changed companion emits the distinguished color into the transverse
coordinate. -/
theorem scalarDiscrepancyTransverseEmission_eq_zeroColor_of_companion_ne
    {coordinate : Bool}
    {first second : ScalarDiscrepancyColorState coordinate}
    (htransition : ScalarDiscrepancyColorTransition first second)
    (hcompanion : first.companionColor ≠ second.companionColor) :
    scalarDiscrepancyTransverseEmission first second =
      crossFaceZeroColor coordinate := by
  rw [scalarDiscrepancyTransverseEmission_eq_companion_add htransition]
  exact (color_eq_add_of_three_distinct_nonzero
    (crossFaceZeroColor_ne_zero coordinate)
    first.companionColor_ne_zero second.companionColor_ne_zero
    (Ne.symm first.companionColor_ne_zeroColor)
    (Ne.symm second.companionColor_ne_zeroColor)
    hcompanion).symm

/-- The exact local transfer dichotomy: a junction is either a straight
fixed-companion segment or emits one transverse distinguished discrepancy. -/
theorem scalarDiscrepancyTransverseEmission_dichotomy
    {coordinate : Bool}
    {first second : ScalarDiscrepancyColorState coordinate}
    (htransition : ScalarDiscrepancyColorTransition first second) :
    (first.companionColor = second.companionColor ∧
        scalarDiscrepancyTransverseEmission first second = 0) ∨
      (first.companionColor ≠ second.companionColor ∧
        scalarDiscrepancyTransverseEmission first second =
          crossFaceZeroColor coordinate) := by
  by_cases hcompanion : first.companionColor = second.companionColor
  · exact Or.inl ⟨hcompanion,
      (scalarDiscrepancyTransverseEmission_eq_zero_iff_companion_eq
        htransition).2 hcompanion⟩
  · exact Or.inr ⟨hcompanion,
      scalarDiscrepancyTransverseEmission_eq_zeroColor_of_companion_ne
        htransition hcompanion⟩

/-- A nonempty chain in a relational transfer system is an exact transfer
between its first and last states. -/
theorem exactRelationalTransfer_of_isChain
    {Profile : Type*} {oneStep : Profile → Profile → Prop}
    {states : List Profile} (hnonempty : states ≠ [])
    (hchain : states.IsChain oneStep) :
    ExactRelationalTransfer oneStep (states.length - 1)
      (states.head hnonempty) (states.getLast hnonempty) := by
  induction states with
  | nil => exact False.elim (hnonempty rfl)
  | cons first tail ih =>
      cases tail with
      | nil =>
          simpa using ExactRelationalTransfer.zero (oneStep := oneStep) first
      | cons second rest =>
          have hfirstSecond : oneStep first second := hchain.rel_head
          have htail := ih (by simp) hchain.tail
          have hstep := ExactRelationalTransfer.succ hfirstSecond htail
          simpa using hstep

variable {W : Type*} {H : SimpleGraph W}

/-- Extract the finite state carried by an actual scalar-support edge of two
Tait colorings. -/
def scalarDiscrepancyColorStateOf
    (firstColoring secondColoring : H.EdgeColoring Color)
    (hfirstTait : IsTaitEdgeColoring H firstColoring)
    (hsecondTait : IsTaitEdgeColoring H secondColoring)
    (coordinate : Bool) (edge : H.edgeSet)
    (hsupport : crossFaceCoordinate coordinate
      (firstColoring edge + secondColoring edge) ≠ 0) :
    ScalarDiscrepancyColorState coordinate :=
  ⟨(firstColoring edge, secondColoring edge),
    hfirstTait edge, hsecondTait edge,
    (crossFaceCoordinate_add_ne_zero_iff_exactlyOne_zeroColor
      coordinate (firstColoring edge) (secondColoring edge)
      (hfirstTait edge) (hsecondTait edge)).1 hsupport⟩

@[simp]
theorem scalarDiscrepancyColorStateOf_sourceColor
    (firstColoring secondColoring : H.EdgeColoring Color)
    (hfirstTait : IsTaitEdgeColoring H firstColoring)
    (hsecondTait : IsTaitEdgeColoring H secondColoring)
    (coordinate : Bool) (edge : H.edgeSet)
    (hsupport : crossFaceCoordinate coordinate
      (firstColoring edge + secondColoring edge) ≠ 0) :
    (scalarDiscrepancyColorStateOf firstColoring secondColoring
      hfirstTait hsecondTait coordinate edge hsupport).sourceColor =
        firstColoring edge := rfl

@[simp]
theorem scalarDiscrepancyColorStateOf_targetColor
    (firstColoring secondColoring : H.EdgeColoring Color)
    (hfirstTait : IsTaitEdgeColoring H firstColoring)
    (hsecondTait : IsTaitEdgeColoring H secondColoring)
    (coordinate : Bool) (edge : H.edgeSet)
    (hsupport : crossFaceCoordinate coordinate
      (firstColoring edge + secondColoring edge) ≠ 0) :
    (scalarDiscrepancyColorStateOf firstColoring secondColoring
      hfirstTait hsecondTait coordinate edge hsupport).targetColor =
        secondColoring edge := rfl

/-- Adjacent actual scalar-support edges satisfy the finite transfer
relation. -/
theorem scalarDiscrepancyColorTransition_of_adjacent
    (firstColoring secondColoring : H.EdgeColoring Color)
    (hfirstTait : IsTaitEdgeColoring H firstColoring)
    (hsecondTait : IsTaitEdgeColoring H secondColoring)
    (coordinate : Bool) {firstEdge secondEdge : H.edgeSet}
    (hadjacent : H.lineGraph.Adj firstEdge secondEdge)
    (hfirstSupport : crossFaceCoordinate coordinate
      (firstColoring firstEdge + secondColoring firstEdge) ≠ 0)
    (hsecondSupport : crossFaceCoordinate coordinate
      (firstColoring secondEdge + secondColoring secondEdge) ≠ 0) :
    ScalarDiscrepancyColorTransition
      (scalarDiscrepancyColorStateOf firstColoring secondColoring
        hfirstTait hsecondTait coordinate firstEdge hfirstSupport)
      (scalarDiscrepancyColorStateOf firstColoring secondColoring
        hfirstTait hsecondTait coordinate secondEdge hsecondSupport) := by
  rcases discrepancySupport_adjacent_edges_alternate
      firstColoring secondColoring hfirstTait hsecondTait coordinate
      hadjacent hfirstSupport hsecondSupport with hsourceTarget | htargetSource
  · exact Or.inl ⟨hsourceTarget.1, hsourceTarget.2.2.2⟩
  · exact Or.inr ⟨htargetSource.2.1, htargetSource.2.2.1⟩

/-- At a cubic junction of two support edges, the discrepancy on the third
edge is the finite state's transverse emission. -/
theorem thirdEdge_discrepancy_eq_transverseEmission
    (firstColoring secondColoring : H.EdgeColoring Color)
    (hfirstTait : IsTaitEdgeColoring H firstColoring)
    (hsecondTait : IsTaitEdgeColoring H secondColoring)
    (coordinate : Bool) {firstEdge secondEdge thirdEdge : H.edgeSet}
    (hfirstSecond : H.lineGraph.Adj firstEdge secondEdge)
    (hfirstThird : H.lineGraph.Adj firstEdge thirdEdge)
    (hsecondThird : H.lineGraph.Adj secondEdge thirdEdge)
    (hfirstSupport : crossFaceCoordinate coordinate
      (firstColoring firstEdge + secondColoring firstEdge) ≠ 0)
    (hsecondSupport : crossFaceCoordinate coordinate
      (firstColoring secondEdge + secondColoring secondEdge) ≠ 0) :
    firstColoring thirdEdge + secondColoring thirdEdge =
      scalarDiscrepancyTransverseEmission
        (scalarDiscrepancyColorStateOf firstColoring secondColoring
          hfirstTait hsecondTait coordinate firstEdge hfirstSupport)
        (scalarDiscrepancyColorStateOf firstColoring secondColoring
          hfirstTait hsecondTait coordinate secondEdge hsecondSupport) := by
  have hfirstThirdColor : firstColoring thirdEdge =
      firstColoring firstEdge + firstColoring secondEdge :=
    color_eq_add_of_three_distinct_nonzero
      (hfirstTait thirdEdge) (hfirstTait firstEdge) (hfirstTait secondEdge)
      (firstColoring.valid hfirstThird).symm
      (firstColoring.valid hsecondThird).symm
      (firstColoring.valid hfirstSecond)
  have hsecondThirdColor : secondColoring thirdEdge =
      secondColoring firstEdge + secondColoring secondEdge :=
    color_eq_add_of_three_distinct_nonzero
      (hsecondTait thirdEdge) (hsecondTait firstEdge) (hsecondTait secondEdge)
      (secondColoring.valid hfirstThird).symm
      (secondColoring.valid hsecondThird).symm
      (secondColoring.valid hfirstSecond)
  rw [hfirstThirdColor, hsecondThirdColor]
  rfl

/-- Equality on the third edge is equivalent to straight companion
transport on the two scalar-support edges. -/
theorem thirdEdge_color_eq_iff_companionColor_eq
    (firstColoring secondColoring : H.EdgeColoring Color)
    (hfirstTait : IsTaitEdgeColoring H firstColoring)
    (hsecondTait : IsTaitEdgeColoring H secondColoring)
    (coordinate : Bool) {firstEdge secondEdge thirdEdge : H.edgeSet}
    (hfirstSecond : H.lineGraph.Adj firstEdge secondEdge)
    (hfirstThird : H.lineGraph.Adj firstEdge thirdEdge)
    (hsecondThird : H.lineGraph.Adj secondEdge thirdEdge)
    (hfirstSupport : crossFaceCoordinate coordinate
      (firstColoring firstEdge + secondColoring firstEdge) ≠ 0)
    (hsecondSupport : crossFaceCoordinate coordinate
      (firstColoring secondEdge + secondColoring secondEdge) ≠ 0) :
    firstColoring thirdEdge = secondColoring thirdEdge ↔
      (scalarDiscrepancyColorStateOf firstColoring secondColoring
        hfirstTait hsecondTait coordinate firstEdge hfirstSupport).companionColor =
      (scalarDiscrepancyColorStateOf firstColoring secondColoring
        hfirstTait hsecondTait coordinate secondEdge hsecondSupport).companionColor := by
  let firstState := scalarDiscrepancyColorStateOf firstColoring secondColoring
    hfirstTait hsecondTait coordinate firstEdge hfirstSupport
  let secondState := scalarDiscrepancyColorStateOf firstColoring secondColoring
    hfirstTait hsecondTait coordinate secondEdge hsecondSupport
  have htransition : ScalarDiscrepancyColorTransition firstState secondState :=
    scalarDiscrepancyColorTransition_of_adjacent
      firstColoring secondColoring hfirstTait hsecondTait coordinate
      hfirstSecond hfirstSupport hsecondSupport
  rw [← add_eq_zero_iff_eq]
  rw [thirdEdge_discrepancy_eq_transverseEmission
    firstColoring secondColoring hfirstTait hsecondTait coordinate
    hfirstSecond hfirstThird hsecondThird hfirstSupport hsecondSupport]
  exact scalarDiscrepancyTransverseEmission_eq_zero_iff_companion_eq
    htransition

/-- A companion change is witnessed by the distinguished discrepancy on the
third edge. -/
theorem thirdEdge_discrepancy_eq_zeroColor_of_companionColor_ne
    (firstColoring secondColoring : H.EdgeColoring Color)
    (hfirstTait : IsTaitEdgeColoring H firstColoring)
    (hsecondTait : IsTaitEdgeColoring H secondColoring)
    (coordinate : Bool) {firstEdge secondEdge thirdEdge : H.edgeSet}
    (hfirstSecond : H.lineGraph.Adj firstEdge secondEdge)
    (hfirstThird : H.lineGraph.Adj firstEdge thirdEdge)
    (hsecondThird : H.lineGraph.Adj secondEdge thirdEdge)
    (hfirstSupport : crossFaceCoordinate coordinate
      (firstColoring firstEdge + secondColoring firstEdge) ≠ 0)
    (hsecondSupport : crossFaceCoordinate coordinate
      (firstColoring secondEdge + secondColoring secondEdge) ≠ 0)
    (hcompanion :
      (scalarDiscrepancyColorStateOf firstColoring secondColoring
        hfirstTait hsecondTait coordinate firstEdge hfirstSupport).companionColor ≠
      (scalarDiscrepancyColorStateOf firstColoring secondColoring
        hfirstTait hsecondTait coordinate secondEdge hsecondSupport).companionColor) :
    firstColoring thirdEdge + secondColoring thirdEdge =
      crossFaceZeroColor coordinate := by
  let firstState := scalarDiscrepancyColorStateOf firstColoring secondColoring
    hfirstTait hsecondTait coordinate firstEdge hfirstSupport
  let secondState := scalarDiscrepancyColorStateOf firstColoring secondColoring
    hfirstTait hsecondTait coordinate secondEdge hsecondSupport
  have htransition : ScalarDiscrepancyColorTransition firstState secondState :=
    scalarDiscrepancyColorTransition_of_adjacent
      firstColoring secondColoring hfirstTait hsecondTait coordinate
      hfirstSecond hfirstSupport hsecondSupport
  rw [thirdEdge_discrepancy_eq_transverseEmission
    firstColoring secondColoring hfirstTait hsecondTait coordinate
    hfirstSecond hfirstThird hsecondThird hfirstSupport hsecondSupport]
  exact scalarDiscrepancyTransverseEmission_eq_zeroColor_of_companion_ne
    htransition hcompanion

/-- The finite transfer-state word read along a scalar-support trail. -/
def scalarDiscrepancyColorStateWord
    (firstColoring secondColoring : H.EdgeColoring Color)
    (hfirstTait : IsTaitEdgeColoring H firstColoring)
    (hsecondTait : IsTaitEdgeColoring H secondColoring)
    (coordinate : Bool) {start finish : W} (path : H.Walk start finish)
    (hsupport : ∀ edge ∈ path.edgeSubtypeSupport,
      crossFaceCoordinate coordinate
        (firstColoring edge + secondColoring edge) ≠ 0) :
    List (ScalarDiscrepancyColorState coordinate) :=
  List.pmap
    (fun edge hedge =>
      scalarDiscrepancyColorStateOf firstColoring secondColoring
        hfirstTait hsecondTait coordinate edge hedge)
    path.edgeSubtypeSupport hsupport

@[simp]
theorem scalarDiscrepancyColorStateWord_length
    (firstColoring secondColoring : H.EdgeColoring Color)
    (hfirstTait : IsTaitEdgeColoring H firstColoring)
    (hsecondTait : IsTaitEdgeColoring H secondColoring)
    (coordinate : Bool) {start finish : W} (path : H.Walk start finish)
    (hsupport : ∀ edge ∈ path.edgeSubtypeSupport,
      crossFaceCoordinate coordinate
        (firstColoring edge + secondColoring edge) ≠ 0) :
    (scalarDiscrepancyColorStateWord firstColoring secondColoring
      hfirstTait hsecondTait coordinate path hsupport).length = path.length := by
  simp [scalarDiscrepancyColorStateWord]

/-- A real scalar-support trail is an exact word in the four-state transfer
system. -/
theorem scalarDiscrepancyColorStateWord_isChain
    (firstColoring secondColoring : H.EdgeColoring Color)
    (hfirstTait : IsTaitEdgeColoring H firstColoring)
    (hsecondTait : IsTaitEdgeColoring H secondColoring)
    (coordinate : Bool) {start finish : W} {path : H.Walk start finish}
    (htrail : path.IsTrail)
    (hsupport : ∀ edge ∈ path.edgeSubtypeSupport,
      crossFaceCoordinate coordinate
        (firstColoring edge + secondColoring edge) ≠ 0) :
    (scalarDiscrepancyColorStateWord firstColoring secondColoring
      hfirstTait hsecondTait coordinate path hsupport).IsChain
        ScalarDiscrepancyColorTransition := by
  unfold scalarDiscrepancyColorStateWord
  apply List.isChain_pmap_of_isChain
      (R := H.lineGraph.Adj)
      (H := fun firstEdge secondEdge hfirstSupport hsecondSupport hadjacent =>
        scalarDiscrepancyColorTransition_of_adjacent
          firstColoring secondColoring hfirstTait hsecondTait coordinate
          hadjacent hfirstSupport hsecondSupport)
      htrail.edgeSubtypeSupport_isChain hsupport

/-- A positive scalar-support trail is an exact relational transfer of one
fewer steps than its number of primal edges. -/
theorem scalarDiscrepancyColorStateWord_exactTransfer
    (firstColoring secondColoring : H.EdgeColoring Color)
    (hfirstTait : IsTaitEdgeColoring H firstColoring)
    (hsecondTait : IsTaitEdgeColoring H secondColoring)
    (coordinate : Bool) {start finish : W} {path : H.Walk start finish}
    (htrail : path.IsTrail) (hpositive : 0 < path.length)
    (hsupport : ∀ edge ∈ path.edgeSubtypeSupport,
      crossFaceCoordinate coordinate
        (firstColoring edge + secondColoring edge) ≠ 0) :
    let word := scalarDiscrepancyColorStateWord
      firstColoring secondColoring hfirstTait hsecondTait
        coordinate path hsupport
    ExactRelationalTransfer ScalarDiscrepancyColorTransition
      (path.length - 1)
      (word.head (by
        intro hnil
        have hlength := congrArg List.length hnil
        rw [scalarDiscrepancyColorStateWord_length] at hlength
        exact (Nat.ne_of_gt hpositive) hlength))
      (word.getLast (by
        intro hnil
        have hlength := congrArg List.length hnil
        rw [scalarDiscrepancyColorStateWord_length] at hlength
        exact (Nat.ne_of_gt hpositive) hlength)) := by
  dsimp only
  let word := scalarDiscrepancyColorStateWord
    firstColoring secondColoring hfirstTait hsecondTait
      coordinate path hsupport
  have hwordLength : word.length = path.length :=
    scalarDiscrepancyColorStateWord_length
      firstColoring secondColoring hfirstTait hsecondTait
        coordinate path hsupport
  have hwordNonempty : word ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    rw [hwordLength] at hlength
    exact (Nat.ne_of_gt hpositive) hlength
  have hchain : word.IsChain ScalarDiscrepancyColorTransition :=
    scalarDiscrepancyColorStateWord_isChain
      firstColoring secondColoring hfirstTait hsecondTait coordinate
        htrail hsupport
  simpa [word, hwordLength] using
    exactRelationalTransfer_of_isChain hwordNonempty hchain

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
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

/-- An intrinsic singleton collar's actual source--target colorings, packaged
as a nonempty path in the four-state companion transfer system. -/
structure SingletonCompanionTransferPath
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) where
  coordinate : Bool
  targetPort : Fin 4
  finish : collar.commonPortVertexFinset
  path : collar.commonCore.Walk
    (collar.targetPortInCommonCore targetPort) finish.1
  singletonInside :
    boundaryDeletedVertex collar.targetData targetPort ∈
      collar.singletonCutProfile.component.supp
  finish_ne_start : finish ≠ collar.targetPortCommonTerminal targetPort
  path_isPath : path.IsPath
  path_positive : 0 < path.length
  support : ∀ edge ∈ path.edgeSubtypeSupport,
    crossFaceCoordinate coordinate
      (collar.sourceCommonColoring sourceEscape edge +
        collar.targetCommonColoring edge) ≠ 0

namespace SingletonCompanionTransferPath

variable {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}
  (transfer : SingletonCompanionTransferPath collar sourceEscape)

/-- The canonical finite transfer word carried by the singleton trail. -/
noncomputable def stateWord :
    List (ScalarDiscrepancyColorState transfer.coordinate) :=
  scalarDiscrepancyColorStateWord
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    transfer.coordinate transfer.path transfer.support

@[simp]
theorem stateWord_length :
    transfer.stateWord.length = transfer.path.length := by
  exact scalarDiscrepancyColorStateWord_length
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    transfer.coordinate transfer.path transfer.support

theorem stateWord_ne_nil : transfer.stateWord ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  rw [transfer.stateWord_length] at hlength
  exact (Nat.ne_of_gt transfer.path_positive) hlength

/-- Consecutive states of the graph-extracted word satisfy the exact finite
transfer relation. -/
theorem stateWord_isChain :
    transfer.stateWord.IsChain ScalarDiscrepancyColorTransition := by
  exact scalarDiscrepancyColorStateWord_isChain
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    transfer.coordinate transfer.path_isPath.isTrail transfer.support

/-- The actual finite state on an edge of the singleton support trail. -/
noncomputable def stateOfEdge
    (edge : collar.commonCore.edgeSet)
    (hedge : edge ∈ transfer.path.edgeSubtypeSupport) :
    ScalarDiscrepancyColorState transfer.coordinate :=
  scalarDiscrepancyColorStateOf
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    transfer.coordinate edge (transfer.support edge hedge)

/-- At every cubic junction traversed by the singleton trail, either the
companion color continues unchanged and the transverse edge agrees in the two
colorings, or the companion changes and the transverse edge carries exactly
the distinguished discrepancy. -/
theorem junction_dichotomy
    {firstEdge secondEdge thirdEdge : collar.commonCore.edgeSet}
    (hfirstMem : firstEdge ∈ transfer.path.edgeSubtypeSupport)
    (hsecondMem : secondEdge ∈ transfer.path.edgeSubtypeSupport)
    (hfirstSecond : collar.commonCore.lineGraph.Adj firstEdge secondEdge)
    (hfirstThird : collar.commonCore.lineGraph.Adj firstEdge thirdEdge)
    (hsecondThird : collar.commonCore.lineGraph.Adj secondEdge thirdEdge) :
    (transfer.stateOfEdge firstEdge hfirstMem).companionColor =
          (transfer.stateOfEdge secondEdge hsecondMem).companionColor ∧
        collar.sourceCommonColoring sourceEscape thirdEdge =
          collar.targetCommonColoring thirdEdge ∨
      (transfer.stateOfEdge firstEdge hfirstMem).companionColor ≠
          (transfer.stateOfEdge secondEdge hsecondMem).companionColor ∧
        collar.sourceCommonColoring sourceEscape thirdEdge +
            collar.targetCommonColoring thirdEdge =
          crossFaceZeroColor transfer.coordinate := by
  by_cases hcompanion :
      (transfer.stateOfEdge firstEdge hfirstMem).companionColor =
        (transfer.stateOfEdge secondEdge hsecondMem).companionColor
  · apply Or.inl
    refine ⟨hcompanion, ?_⟩
    exact (thirdEdge_color_eq_iff_companionColor_eq
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      transfer.coordinate hfirstSecond hfirstThird hsecondThird
      (transfer.support firstEdge hfirstMem)
      (transfer.support secondEdge hsecondMem)).2 hcompanion
  · apply Or.inr
    refine ⟨hcompanion, ?_⟩
    exact thirdEdge_discrepancy_eq_zeroColor_of_companionColor_ne
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      transfer.coordinate hfirstSecond hfirstThird hsecondThird
      (transfer.support firstEdge hfirstMem)
      (transfer.support secondEdge hsecondMem) hcompanion

/-- Initial finite state of the graph-extracted word. -/
noncomputable def initialState :
    ScalarDiscrepancyColorState transfer.coordinate :=
  transfer.stateWord.head transfer.stateWord_ne_nil

/-- Terminal finite state of the graph-extracted word. -/
noncomputable def terminalState :
    ScalarDiscrepancyColorState transfer.coordinate :=
  transfer.stateWord.getLast transfer.stateWord_ne_nil

/-- The singleton trail is an exact transfer between its canonical endpoint
states. -/
theorem exactTransfer :
    ExactRelationalTransfer ScalarDiscrepancyColorTransition
      (transfer.path.length - 1) transfer.initialState transfer.terminalState := by
  simpa [initialState, terminalState, stateWord] using
    scalarDiscrepancyColorStateWord_exactTransfer
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      transfer.coordinate transfer.path_isPath.isTrail
      transfer.path_positive transfer.support

end SingletonCompanionTransferPath

/-- Every intrinsic singleton collar supplies a nonempty exact path in the
four-state companion transfer system. -/
theorem nonempty_singletonCompanionTransferPath
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    Nonempty (SingletonCompanionTransferPath collar sourceEscape) := by
  rcases collar.exists_singletonTerminal_alternatingSupportPath sourceEscape with
    ⟨coordinate, targetPort, finish, path, hinside, hfinishNe,
      hpath, _hstartDegree, _hfinishDegree, _hdegreeBound,
      hedgeClass, _halternation⟩
  have hendsNe :
      collar.targetPortInCommonCore targetPort ≠ finish.1 := by
    intro heq
    apply hfinishNe
    apply Subtype.ext
    simpa [targetPortCommonTerminal] using heq.symm
  have hpositive : 0 < path.length := by
    by_contra hnot
    have hzero : path.length = 0 := Nat.eq_zero_of_not_pos hnot
    exact hendsNe (path.eq_of_length_eq_zero hzero)
  have hsupport : ∀ edge ∈ path.edgeSubtypeSupport,
      crossFaceCoordinate coordinate
        (collar.sourceCommonColoring sourceEscape edge +
          collar.targetCommonColoring edge) ≠ 0 := by
    intro edge hedge
    have hedgePath : (edge : Sym2 collar.commonCoreVertex) ∈ path.edges := by
      rw [← path.edgeSubtypeSupport_map_val]
      exact List.mem_map.mpr ⟨edge, hedge, rfl⟩
    exact (crossFaceCoordinate_add_ne_zero_iff_exactlyOne_zeroColor
      coordinate
      (collar.sourceCommonColoring sourceEscape edge)
      (collar.targetCommonColoring edge)
      (collar.sourceCommonColoring_isTait sourceEscape edge)
      (collar.targetCommonColoring_isTait edge)).2
        (hedgeClass edge hedgePath)
  exact ⟨{
    coordinate := coordinate
    targetPort := targetPort
    finish := finish
    path := path
    singletonInside := hinside
    finish_ne_start := hfinishNe
    path_isPath := hpath
    path_positive := hpositive
    support := hsupport
  }⟩

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
