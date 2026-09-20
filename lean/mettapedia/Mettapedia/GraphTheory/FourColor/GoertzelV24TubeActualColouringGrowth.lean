import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeSeedMultiplicity
import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeCorridorLineGraph

/-!
# Distinct routed histories give distinct proper tube colourings

The older doubling theorem counts fully-routed *history certificates*.
This file makes their physical meaning precise: each history determines a
specific proper colouring of the canonical corridor line graph, and two
different histories cannot induce the same edge-colour function.  The
injection uses the fact that the middle-edge colours determine each ring's
five split choices.

This is still an open corridor graph.  It is not an identification of the
source's global Count functor or a theorem about arbitrary planar caps.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeActualColouringGrowth

open GoertzelV24TubeRingTransfer
open GoertzelV24WindingClassification

/-- Construct the corridor from the history's *own* ordered choices, rather
than choosing some existence witness for each transfer endpoint. -/
noncomputable def canonicalCorridor :
    {rings : Nat} → {source : RecurrentTubeProfile} →
      FullyRoutedTubeHistory rings source →
      Σ target : RecurrentTubeProfile,
        TubeCorridorTaitColoring rings
          (recurrentProfileState source) (recurrentProfileState target)
  | 0, source, _history =>
      ⟨source, {
        frontierState := fun _ => recurrentProfileState source
        ringChoice := Fin.elim0
        first_state := rfl
        last_state := rfl
        successor := fun ring => Fin.elim0 ring
      }⟩
  | rings + 1, source, ⟨choice, tail⟩ =>
      let tailCorridor := canonicalCorridor tail
      ⟨tailCorridor.1, {
        frontierState := Fin.cases (recurrentProfileState source)
          tailCorridor.2.frontierState
        ringChoice := Fin.cases choice tailCorridor.2.ringChoice
        first_state := rfl
        last_state := by
          change tailCorridor.2.frontierState (Fin.last rings) =
            recurrentProfileState tailCorridor.1
          exact tailCorridor.2.last_state
        successor := by
          intro ring
          refine Fin.cases ?_ (fun index => ?_) ring
          · change IsTubeRingSuccessor
              (recurrentProfileState source)
              (tailCorridor.2.frontierState 0) choice
            rw [tailCorridor.2.first_state]
            exact fullyRoutedNextProfile_isSuccessor source choice
          · exact tailCorridor.2.successor index
      }⟩

/-- The constructed corridor retains the history's original choice at every
ring. -/
theorem canonicalCorridor_choiceVector :
    ∀ {rings : Nat} {source : RecurrentTubeProfile}
      (history : FullyRoutedTubeHistory rings source),
      (canonicalCorridor history).2.ringChoice = history.choiceVector := by
  intro rings
  induction rings with
  | zero =>
      intro source history
      funext ring
      exact Fin.elim0 ring
  | succ rings ih =>
      intro source history
      rcases history with ⟨choice, tail⟩
      funext ring
      refine Fin.cases ?_ (fun index => ?_) ring
      · rfl
      · exact congrFun (ih tail) index

/-- The actual proper colouring of the corridor's line graph induced by a
history. -/
noncomputable def historyLineColouring
    {rings : Nat} {source : RecurrentTubeProfile}
    (history : FullyRoutedTubeHistory rings source) :
    (tubeCorridorLineGraph rings).Coloring StrandColor :=
  (canonicalCorridor history).2.toLineColoring

theorem historyLineColouring_injective
    (rings : Nat) (source : RecurrentTubeProfile) :
    Function.Injective
      (@historyLineColouring rings source) := by
  intro left right hcoloring
  apply FullyRoutedTubeHistory.choiceVector_injective rings source
  let leftCorridor := (canonicalCorridor left).2
  let rightCorridor := (canonicalCorridor right).2
  have hedge : leftCorridor.edgeColor = rightCorridor.edgeColor := by
    exact congrArg
      (fun coloring : (tubeCorridorLineGraph rings).Coloring StrandColor =>
        (coloring : TubeCorridorEdge rings → StrandColor)) hcoloring
  funext ring
  have hsource :
      (leftCorridor.frontierState ring.castSucc).color =
        (rightCorridor.frontierState ring.castSucc).color := by
    funext position
    exact congrFun hedge (.inl (ring.castSucc, position))
  have hmiddle :
      middleColor (leftCorridor.frontierState ring.castSucc)
        (leftCorridor.ringChoice ring) =
      middleColor (rightCorridor.frontierState ring.castSucc)
        (rightCorridor.ringChoice ring) := by
    funext edge
    exact congrFun hedge (.inr (ring, edge))
  have hsameSource (choice : TubeRingChoice) :
      middleColor (leftCorridor.frontierState ring.castSucc) choice =
        middleColor (rightCorridor.frontierState ring.castSucc) choice := by
    funext edge
    simp only [middleColor, hsource]
  have hchoice :
      leftCorridor.ringChoice ring = rightCorridor.ringChoice ring :=
    middleColor_choice_injective
      (leftCorridor.frontierState ring.castSucc)
      (hmiddle.trans (hsameSource _).symm)
  simpa only [← canonicalCorridor_choiceVector left,
    ← canonicalCorridor_choiceVector right] using hchoice

/-- Proper graph colourings with the prescribed five incoming boundary
colours. The terminal labels are not part of this type. -/
abbrev FixedStartColouring (rings : Nat)
    (source : RecurrentTubeProfile) :=
  {coloring : (tubeCorridorLineGraph rings).Coloring StrandColor //
    ∀ position : Fin 5,
      coloring (.inl ((0 : Fin (rings + 1)), position)) =
        (recurrentProfileState source).color position}

noncomputable def historyFixedStartColouring
    {rings : Nat} {source : RecurrentTubeProfile}
    (history : FullyRoutedTubeHistory rings source) :
    FixedStartColouring rings source := by
  refine ⟨historyLineColouring history, ?_⟩
  intro position
  change ((canonicalCorridor history).2.frontierState 0).color position =
    (recurrentProfileState source).color position
  exact congrArg (fun state : TubeFrontierState => state.color position)
    (canonicalCorridor history).2.first_state

theorem historyFixedStartColouring_injective
    (rings : Nat) (source : RecurrentTubeProfile) :
    Function.Injective (@historyFixedStartColouring rings source) := by
  intro left right heq
  apply historyLineColouring_injective rings source
  exact congrArg Subtype.val heq

/-- The canonical open tube graph has at least exponentially many genuinely
different proper edge-colour functions with the prescribed recurrent start.
This strengthens the old count of certificates to a count of graph
colourings. -/
theorem card_lineColourings_ge_two_pow
    (rings : Nat) (source : RecurrentTubeProfile) :
    2 ^ rings ≤
      Fintype.card ((tubeCorridorLineGraph rings).Coloring StrandColor) := by
  classical
  rw [← fullyRoutedTubeHistory_card rings source]
  exact Fintype.card_le_of_injective
    (@historyLineColouring rings source)
    (historyLineColouring_injective rings source)

/-- Even after the input boundary colours are fixed, the number of proper
open-corridor graph colourings grows at least as `2^rings`. -/
theorem card_fixedStartColourings_ge_two_pow
    (rings : Nat) (source : RecurrentTubeProfile) :
    2 ^ rings ≤ Fintype.card (FixedStartColouring rings source) := by
  classical
  rw [← fullyRoutedTubeHistory_card rings source]
  exact Fintype.card_le_of_injective
    (@historyFixedStartColouring rings source)
    (historyFixedStartColouring_injective rings source)

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeActualColouringGrowth
