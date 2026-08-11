import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutSerialOpenTangle
import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialOpenTangleSupportPumping

/-!
# Source-ordered `Count` support for cut-open pieces

An ordered cut carries a canonical `Fin n` coordinate supplied by the source
transversal.  This file transports literal boundary color words to that
coordinate and specializes serial `Count` composition to certified
`OrderedCutSidesData`.  Consequently all intermediate words live on the
source order, even though the geometric boundary-dart carriers of successive
pieces are distinct dependent types.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SpliceUnification.OrderedCutSidesData

open GoertzelV24OpenTangleComposition
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
  {RS : RotationSystem V E}
  {n leftTerminalCount leftFaceFragmentCount
    rightTerminalCount rightFaceFragmentCount
    middleTerminalCount middleFaceFragmentCount : Nat}

noncomputable section

/-- Read a source-coordinate word on the left geometric boundary carrier. -/
noncomputable def leftBoundaryWord
    (data : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (word : Fin n → Color) :
    BoundaryDartOn RS data.keep (orderedCut data.left.crossingEdge) → Color :=
  fun dart => word ((orderedBoundaryDartEquiv RS data.keep
    data.left.crossingEdge data.leftCrosses data.leftInjective).symm dart)

/-- Read a source-coordinate word on the right geometric boundary carrier. -/
noncomputable def rightBoundaryWord
    (data : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (word : Fin n → Color) :
    BoundaryDartOn RS data.keep (orderedCut data.right.crossingEdge) → Color :=
  fun dart => word ((orderedBoundaryDartEquiv RS data.keep
    data.right.crossingEdge data.rightCrosses data.rightInjective).symm dart)

@[simp]
theorem leftBoundaryWord_orderedBoundaryDart
    (data : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (word : Fin n → Color) (step : Fin n) :
    data.leftBoundaryWord word
        (orderedBoundaryDart RS data.keep data.left.crossingEdge
          data.leftCrosses step) = word step := by
  let equiv := orderedBoundaryDartEquiv RS data.keep
    data.left.crossingEdge data.leftCrosses data.leftInjective
  change word (equiv.symm (equiv step)) = word step
  rw [equiv.symm_apply_apply]

@[simp]
theorem rightBoundaryWord_orderedBoundaryDart
    (data : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (word : Fin n → Color) (step : Fin n) :
    data.rightBoundaryWord word
        (orderedBoundaryDart RS data.keep data.right.crossingEdge
          data.rightCrosses step) = word step := by
  let equiv := orderedBoundaryDartEquiv RS data.keep
    data.right.crossingEdge data.rightCrosses data.rightInjective
  change word (equiv.symm (equiv step)) = word step
  rw [equiv.symm_apply_apply]

/-- Literal support of one ordered-cut piece in the common source
coordinates. -/
def AcceptsOrderedBoundaryWords
    (data : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (leftWord rightWord : Fin n → Color) : Prop :=
  data.toTwoSidedOpenTangle.AcceptsBoundaryWords
    (data.leftBoundaryWord leftWord) (data.rightBoundaryWord rightWord)

/-- Literal support of the serial composite of two source-ordered pieces. -/
def SerialAcceptsOrderedBoundaryWords
    (left : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (right : OrderedCutSidesData RS n rightTerminalCount
      rightFaceFragmentCount)
    (leftWord rightWord : Fin n → Color) : Prop :=
  (left.serialCompose right).AcceptsBoundaryWords
    (left.leftBoundaryWord leftWord) (right.rightBoundaryWord rightWord)

private theorem right_input_word_eq
    (left : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (right : OrderedCutSidesData RS n rightTerminalCount
      rightFaceFragmentCount)
    (word : Fin n → Color) :
    (fun dart => left.rightBoundaryWord word
      ((rightToLeftBoundaryMatching left right).symm dart)) =
      right.leftBoundaryWord word := by
  funext dart
  let rightEquiv := orderedBoundaryDartEquiv RS right.keep
    right.left.crossingEdge right.leftCrosses right.leftInjective
  let step := rightEquiv.symm dart
  have hdart : rightEquiv step = dart := rightEquiv.apply_symm_apply dart
  rw [← hdart]
  change left.rightBoundaryWord word
      ((rightToLeftBoundaryMatching left right).symm
        (orderedBoundaryDart RS right.keep right.left.crossingEdge
          right.leftCrosses step)) =
    right.leftBoundaryWord word
      (orderedBoundaryDart RS right.keep right.left.crossingEdge
        right.leftCrosses step)
  rw [rightToLeftBoundaryMatching_symm_orderedBoundaryDart]
  simp

private theorem transported_output_word_eq
    (left : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (loop : OrderedCutSidesData RS n middleTerminalCount
      middleFaceFragmentCount)
    (right : OrderedCutSidesData RS n rightTerminalCount
      rightFaceFragmentCount)
    (word : Fin n → Color) :
    (fun output => left.rightBoundaryWord word
      ((rightToLeftBoundaryMatching left right).symm
        (rightToLeftBoundaryMatching loop right output))) =
      loop.rightBoundaryWord word := by
  funext dart
  let loopEquiv := orderedBoundaryDartEquiv RS loop.keep
    loop.right.crossingEdge loop.rightCrosses loop.rightInjective
  let step := loopEquiv.symm dart
  have hdart : loopEquiv step = dart := loopEquiv.apply_symm_apply dart
  rw [← hdart]
  change left.rightBoundaryWord word
      ((rightToLeftBoundaryMatching left right).symm
        (rightToLeftBoundaryMatching loop right
          (orderedBoundaryDart RS loop.keep loop.right.crossingEdge
            loop.rightCrosses step))) =
    loop.rightBoundaryWord word
      (orderedBoundaryDart RS loop.keep loop.right.crossingEdge
        loop.rightCrosses step)
  rw [rightToLeftBoundaryMatching_orderedBoundaryDart,
    rightToLeftBoundaryMatching_symm_orderedBoundaryDart]
  simp

/-- Source-coordinate form of support-level matrix multiplication. -/
theorem serialAcceptsOrderedBoundaryWords_iff
    (left : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (right : OrderedCutSidesData RS n rightTerminalCount
      rightFaceFragmentCount)
    (leftWord rightWord : Fin n → Color) :
    left.SerialAcceptsOrderedBoundaryWords right leftWord rightWord ↔
      ∃ middle : Fin n → Color,
        left.AcceptsOrderedBoundaryWords leftWord middle ∧
        right.AcceptsOrderedBoundaryWords middle rightWord := by
  unfold SerialAcceptsOrderedBoundaryWords
  unfold GoertzelV24SpliceUnification.OrderedCutSidesData.serialCompose
  rw [TwoSidedOpenTangleData.serialCompose_acceptsBoundaryWords_iff]
  constructor
  · rintro ⟨rawMiddle, hleft, hright⟩
    let middle : Fin n → Color := fun step =>
      rawMiddle (orderedBoundaryDart RS left.keep left.right.crossingEdge
        left.rightCrosses step)
    have hraw : left.rightBoundaryWord middle = rawMiddle := by
      funext dart
      let equiv := orderedBoundaryDartEquiv RS left.keep
        left.right.crossingEdge left.rightCrosses left.rightInjective
      have hdart : equiv (equiv.symm dart) = dart := equiv.apply_symm_apply dart
      change rawMiddle (equiv (equiv.symm dart)) = rawMiddle dart
      exact congrArg rawMiddle hdart
    refine ⟨middle, ?_, ?_⟩
    · unfold AcceptsOrderedBoundaryWords
      rwa [hraw]
    · unfold AcceptsOrderedBoundaryWords
      rw [← right_input_word_eq left right middle]
      rwa [hraw]
  · rintro ⟨middle, hleft, hright⟩
    refine ⟨left.rightBoundaryWord middle, ?_, ?_⟩
    · exact hleft
    · rw [right_input_word_eq left right middle]
      exact hright

/-- A source tile realizes identity support on the boundary words relevant
to the surrounding counterexample species. -/
def SupportsOrderedIdentityOn
    (data : OrderedCutSidesData RS n middleTerminalCount
      middleFaceFragmentCount)
    (Relevant : (Fin n → Color) → Prop) : Prop :=
  ∀ word : Fin n → Color,
    Relevant word → data.AcceptsOrderedBoundaryWords word word

/-- Strong specialization in which every source-coordinate word is
relevant.  The corridor proof should normally use
`SupportsOrderedIdentityOn`; this version is convenient only when universal
identity support is genuinely available. -/
def SupportsOrderedIdentity
    (data : OrderedCutSidesData RS n middleTerminalCount
      middleFaceFragmentCount) : Prop :=
  data.SupportsOrderedIdentityOn (fun _ => True)

/-- Source-coordinate pumping on relevant boundary words.  The relevance of
the seam word is derived from the two factors of the short composite, then
the local L2 witness inserts the middle tile. -/
theorem serialSupport_pump_of_orderedIdentityOn
    (left : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (loop : OrderedCutSidesData RS n middleTerminalCount
      middleFaceFragmentCount)
    (right : OrderedCutSidesData RS n rightTerminalCount
      rightFaceFragmentCount)
    (Relevant : (Fin n → Color) → Prop)
    (hloop : loop.SupportsOrderedIdentityOn Relevant)
    (leftWord rightWord : Fin n → Color)
    (hrelevant : ∀ middle : Fin n → Color,
      left.AcceptsOrderedBoundaryWords leftWord middle →
      right.AcceptsOrderedBoundaryWords middle rightWord →
      Relevant middle)
    (hshort : left.SerialAcceptsOrderedBoundaryWords right leftWord rightWord) :
    (TwoSidedOpenTangleData.serialCompose (left.serialCompose loop)
        right.toTwoSidedOpenTangle (rightToLeftBoundaryMatching loop right))
      |>.AcceptsBoundaryWords
        (left.leftBoundaryWord leftWord) (right.rightBoundaryWord rightWord) := by
  apply TwoSidedOpenTangleData.serialCompose_acceptsBoundaryWords_of_transportedIdentityOn
    left.toTwoSidedOpenTangle loop.toTwoSidedOpenTangle
    right.toTwoSidedOpenTangle
    (rightToLeftBoundaryMatching left loop)
    (rightToLeftBoundaryMatching loop right)
    (rightToLeftBoundaryMatching left right)
    (fun raw => Relevant (fun step =>
      raw (orderedBoundaryDart RS left.keep left.right.crossingEdge
        left.rightCrosses step)))
  · intro word hwordRelevant
    let sourceWord : Fin n → Color := fun step =>
      word (orderedBoundaryDart RS left.keep left.right.crossingEdge
        left.rightCrosses step)
    have hword : left.rightBoundaryWord sourceWord = word := by
      funext dart
      let equiv := orderedBoundaryDartEquiv RS left.keep
        left.right.crossingEdge left.rightCrosses left.rightInjective
      have hdart : equiv (equiv.symm dart) = dart := equiv.apply_symm_apply dart
      change word (equiv (equiv.symm dart)) = word dart
      exact congrArg word hdart
    have hsourceRelevant : Relevant sourceWord := by
      exact hwordRelevant
    have hrealized := hloop sourceWord hsourceRelevant
    unfold AcceptsOrderedBoundaryWords at hrealized
    have hinput := right_input_word_eq left loop sourceWord
    have houtput := transported_output_word_eq left loop right sourceWord
    rw [hword] at hinput houtput
    rw [hinput, houtput]
    exact hrealized
  · intro word hleft hright
    let sourceWord : Fin n → Color := fun step =>
      word (orderedBoundaryDart RS left.keep left.right.crossingEdge
        left.rightCrosses step)
    have hword : left.rightBoundaryWord sourceWord = word := by
      funext dart
      let equiv := orderedBoundaryDartEquiv RS left.keep
        left.right.crossingEdge left.rightCrosses left.rightInjective
      have hdart : equiv (equiv.symm dart) = dart := equiv.apply_symm_apply dart
      change word (equiv (equiv.symm dart)) = word dart
      exact congrArg word hdart
    apply hrelevant sourceWord
    · unfold AcceptsOrderedBoundaryWords
      rwa [hword]
    · unfold AcceptsOrderedBoundaryWords
      rw [← right_input_word_eq left right sourceWord]
      rwa [hword]
  · exact hshort

/-- Inserting a source-ordered identity tile preserves a positive exterior
support entry.  All geometric boundary transports are discharged by the
canonical transversal order. -/
theorem serialSupport_pump_of_orderedIdentity
    (left : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (loop : OrderedCutSidesData RS n middleTerminalCount
      middleFaceFragmentCount)
    (right : OrderedCutSidesData RS n rightTerminalCount
      rightFaceFragmentCount)
    (hloop : loop.SupportsOrderedIdentity)
    (leftWord rightWord : Fin n → Color)
    (hshort : left.SerialAcceptsOrderedBoundaryWords right leftWord rightWord) :
    (TwoSidedOpenTangleData.serialCompose (left.serialCompose loop)
        right.toTwoSidedOpenTangle (rightToLeftBoundaryMatching loop right))
      |>.AcceptsBoundaryWords
        (left.leftBoundaryWord leftWord) (right.rightBoundaryWord rightWord) := by
  apply TwoSidedOpenTangleData.serialCompose_acceptsBoundaryWords_of_transportedIdentity
    left.toTwoSidedOpenTangle loop.toTwoSidedOpenTangle right.toTwoSidedOpenTangle
    (rightToLeftBoundaryMatching left loop)
    (rightToLeftBoundaryMatching loop right)
    (rightToLeftBoundaryMatching left right)
  · intro word
    let sourceWord : Fin n → Color := fun step =>
      word (orderedBoundaryDart RS left.keep left.right.crossingEdge
        left.rightCrosses step)
    have hword : left.rightBoundaryWord sourceWord = word := by
      funext dart
      let equiv := orderedBoundaryDartEquiv RS left.keep
        left.right.crossingEdge left.rightCrosses left.rightInjective
      have hdart : equiv (equiv.symm dart) = dart := equiv.apply_symm_apply dart
      change word (equiv (equiv.symm dart)) = word dart
      exact congrArg word hdart
    have hrealized := hloop sourceWord trivial
    unfold AcceptsOrderedBoundaryWords at hrealized
    have hinput := right_input_word_eq left loop sourceWord
    have houtput := transported_output_word_eq left loop right sourceWord
    rw [hword] at hinput houtput
    rw [hinput, houtput]
    exact hrealized
  · exact hshort

end

end GoertzelV24SpliceUnification.OrderedCutSidesData

end Mettapedia.GraphTheory.FourColor
