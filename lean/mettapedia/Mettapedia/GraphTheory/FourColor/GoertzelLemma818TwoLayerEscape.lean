import Mettapedia.GraphTheory.FourColor.GoertzelLemma814

namespace Mettapedia.GraphTheory.FourColor

/-!
# Section 9.2 two-layer ambient escape probe

This module records the concrete finite counterexample class exposed by the
two-layer ambient execution lab: a Kempe switch that is valid in the tested
outer collar alone, but whose ambient component in a downstream one-gadget
layer leaves the collar, reaches the fixed outer-input side, and therefore
does not restrict to the certified collar move.
-/

namespace GoertzelLemma818TwoLayerEscape

open GoertzelLemma814

private def ce (occ : Nat) (edge : TauEdge) : ChainEdge :=
  { occ := occ, edge := edge }

def twoLayerEscapeOuterWord : List TauOrient :=
  [TauOrient.normal, TauOrient.normal]

def twoLayerEscapeInnerWord : List TauOrient :=
  [TauOrient.normal]

def twoLayerEscapeAmbientWord : List TauOrient :=
  twoLayerEscapeOuterWord ++ twoLayerEscapeInnerWord

def twoLayerEscapeCollarSource : List TauState :=
  [stateAt 114, stateAt 54]

def twoLayerEscapeCollarTarget : List TauState :=
  [stateAt 114, stateAt 53]

def twoLayerEscapeAmbientSource : List TauState :=
  [stateAt 114, stateAt 54, stateAt 112]

def twoLayerEscapeMove : ChainMove :=
  { a := LColor.r
    c := LColor.p
    seed := { occ := 1, edge := TauEdge.B5 } }

def twoLayerEscapeCollarComponent : List ChainEdge :=
  chainComponent twoLayerEscapeOuterWord twoLayerEscapeCollarSource
    twoLayerEscapeMove.a twoLayerEscapeMove.c twoLayerEscapeMove.seed

def twoLayerEscapeAmbientComponent : List ChainEdge :=
  [ ce 1 TauEdge.B5
  , ce 1 TauEdge.F4F5
  , ce 2 TauEdge.F1F0
  , ce 1 TauEdge.B4
  , ce 1 TauEdge.B7
  , ce 1 TauEdge.F2F3
  , ce 2 TauEdge.F2F3
  , ce 1 TauEdge.F0F2
  , ce 2 TauEdge.F2F4
  , ce 1 TauEdge.F1F0
  , ce 2 TauEdge.B7
  , ce 0 TauEdge.B5
  , ce 0 TauEdge.F4F5
  , ce 0 TauEdge.F2F4
  , ce 0 TauEdge.F2F3
  , ce 0 TauEdge.B3
  ]

private def twoLayerEscapeActualAmbientComponent : List ChainEdge :=
  chainComponent twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
    twoLayerEscapeMove.a twoLayerEscapeMove.c twoLayerEscapeMove.seed

def twoLayerEscapeAmbientOuterComponent : List ChainEdge :=
  twoLayerEscapeAmbientComponent.filter fun ge =>
    decide (ge.occ < twoLayerEscapeOuterWord.length)

def twoLayerComponentLeavesOuterLayer : Bool :=
  twoLayerEscapeAmbientComponent.any fun ge =>
    decide (twoLayerEscapeOuterWord.length ≤ ge.occ)

def twoLayerComponentHitsOuterInput : Bool :=
  twoLayerEscapeAmbientComponent.any fun ge =>
    (chainOuterInputEdges twoLayerEscapeOuterWord).contains ge

def twoLayerAmbientRestrictionDiffers : Bool :=
  !(twoLayerEscapeAmbientOuterComponent == twoLayerEscapeCollarComponent)

private def twoLayerEscapeAmbientSeen0 : List ChainEdge :=
  [ce 1 TauEdge.B5]

private def twoLayerEscapeAmbientLayer0 : List ChainEdge :=
  [ce 1 TauEdge.F4F5, ce 2 TauEdge.F1F0]

private def twoLayerEscapeAmbientSeen1 : List ChainEdge :=
  twoLayerEscapeAmbientSeen0 ++ twoLayerEscapeAmbientLayer0

private def twoLayerEscapeAmbientLayer1 : List ChainEdge :=
  [ce 1 TauEdge.B4, ce 1 TauEdge.B7]

private def twoLayerEscapeAmbientSeen2 : List ChainEdge :=
  twoLayerEscapeAmbientSeen1 ++ twoLayerEscapeAmbientLayer1

private def twoLayerEscapeAmbientLayer2 : List ChainEdge :=
  [ce 1 TauEdge.F2F3, ce 2 TauEdge.F2F3]

private def twoLayerEscapeAmbientSeen3 : List ChainEdge :=
  twoLayerEscapeAmbientSeen2 ++ twoLayerEscapeAmbientLayer2

private def twoLayerEscapeAmbientLayer3 : List ChainEdge :=
  [ce 1 TauEdge.F0F2, ce 2 TauEdge.F2F4]

private def twoLayerEscapeAmbientSeen4 : List ChainEdge :=
  twoLayerEscapeAmbientSeen3 ++ twoLayerEscapeAmbientLayer3

private def twoLayerEscapeAmbientLayer4 : List ChainEdge :=
  [ce 1 TauEdge.F1F0, ce 2 TauEdge.B7]

private def twoLayerEscapeAmbientSeen5 : List ChainEdge :=
  twoLayerEscapeAmbientSeen4 ++ twoLayerEscapeAmbientLayer4

private def twoLayerEscapeAmbientLayer5 : List ChainEdge :=
  [ce 0 TauEdge.B5]

private def twoLayerEscapeAmbientSeen6 : List ChainEdge :=
  twoLayerEscapeAmbientSeen5 ++ twoLayerEscapeAmbientLayer5

private def twoLayerEscapeAmbientLayer6 : List ChainEdge :=
  [ce 0 TauEdge.F4F5]

private def twoLayerEscapeAmbientSeen7 : List ChainEdge :=
  twoLayerEscapeAmbientSeen6 ++ twoLayerEscapeAmbientLayer6

private def twoLayerEscapeAmbientLayer7 : List ChainEdge :=
  [ce 0 TauEdge.F2F4]

private def twoLayerEscapeAmbientSeen8 : List ChainEdge :=
  twoLayerEscapeAmbientSeen7 ++ twoLayerEscapeAmbientLayer7

private def twoLayerEscapeAmbientLayer8 : List ChainEdge :=
  [ce 0 TauEdge.F2F3]

private def twoLayerEscapeAmbientSeen9 : List ChainEdge :=
  twoLayerEscapeAmbientSeen8 ++ twoLayerEscapeAmbientLayer8

private def twoLayerEscapeAmbientLayer9 : List ChainEdge :=
  [ce 0 TauEdge.B3]

private def twoLayerEscapeAmbientSeen10 : List ChainEdge :=
  twoLayerEscapeAmbientSeen9 ++ twoLayerEscapeAmbientLayer9

private theorem closeChainComponent_succ_eq
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (seen layer : List ChainEdge) (n : Nat)
    (hlayer : nextChainComponentLayer orients states a c seen = layer) :
    closeChainComponent orients states a c (n + 1) seen =
      closeChainComponent orients states a c n (appendFresh seen layer) := by
  simp [closeChainComponent, hlayer]

private theorem closeChainComponent_eq_self_of_layer_nil
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (seen : List ChainEdge)
    (hlayer : nextChainComponentLayer orients states a c seen = []) :
    ∀ n, closeChainComponent orients states a c n seen = seen
  | 0 => rfl
  | n + 1 => by
      rw [closeChainComponent_succ_eq
        orients states a c seen [] n hlayer]
      simpa [appendFresh] using
        closeChainComponent_eq_self_of_layer_nil
          orients states a c seen hlayer n

private theorem twoLayerEscapeAmbient_layer0 :
    nextChainComponentLayer twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
      twoLayerEscapeMove.a twoLayerEscapeMove.c twoLayerEscapeAmbientSeen0 =
        twoLayerEscapeAmbientLayer0 := by
  decide

private theorem twoLayerEscapeAmbient_seen1 :
    appendFresh twoLayerEscapeAmbientSeen0 twoLayerEscapeAmbientLayer0 =
      twoLayerEscapeAmbientSeen1 := by
  decide

private theorem twoLayerEscapeAmbient_layer1 :
    nextChainComponentLayer twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
      twoLayerEscapeMove.a twoLayerEscapeMove.c twoLayerEscapeAmbientSeen1 =
        twoLayerEscapeAmbientLayer1 := by
  decide

private theorem twoLayerEscapeAmbient_seen2 :
    appendFresh twoLayerEscapeAmbientSeen1 twoLayerEscapeAmbientLayer1 =
      twoLayerEscapeAmbientSeen2 := by
  decide

private theorem twoLayerEscapeAmbient_layer2 :
    nextChainComponentLayer twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
      twoLayerEscapeMove.a twoLayerEscapeMove.c twoLayerEscapeAmbientSeen2 =
        twoLayerEscapeAmbientLayer2 := by
  decide

private theorem twoLayerEscapeAmbient_seen3 :
    appendFresh twoLayerEscapeAmbientSeen2 twoLayerEscapeAmbientLayer2 =
      twoLayerEscapeAmbientSeen3 := by
  decide

private theorem twoLayerEscapeAmbient_layer3 :
    nextChainComponentLayer twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
      twoLayerEscapeMove.a twoLayerEscapeMove.c twoLayerEscapeAmbientSeen3 =
        twoLayerEscapeAmbientLayer3 := by
  decide

private theorem twoLayerEscapeAmbient_seen4 :
    appendFresh twoLayerEscapeAmbientSeen3 twoLayerEscapeAmbientLayer3 =
      twoLayerEscapeAmbientSeen4 := by
  decide

private theorem twoLayerEscapeAmbient_layer4 :
    nextChainComponentLayer twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
      twoLayerEscapeMove.a twoLayerEscapeMove.c twoLayerEscapeAmbientSeen4 =
        twoLayerEscapeAmbientLayer4 := by
  decide

private theorem twoLayerEscapeAmbient_seen5 :
    appendFresh twoLayerEscapeAmbientSeen4 twoLayerEscapeAmbientLayer4 =
      twoLayerEscapeAmbientSeen5 := by
  decide

private theorem twoLayerEscapeAmbient_layer5 :
    nextChainComponentLayer twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
      twoLayerEscapeMove.a twoLayerEscapeMove.c twoLayerEscapeAmbientSeen5 =
        twoLayerEscapeAmbientLayer5 := by
  decide

private theorem twoLayerEscapeAmbient_seen6 :
    appendFresh twoLayerEscapeAmbientSeen5 twoLayerEscapeAmbientLayer5 =
      twoLayerEscapeAmbientSeen6 := by
  decide

private theorem twoLayerEscapeAmbient_layer6 :
    nextChainComponentLayer twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
      twoLayerEscapeMove.a twoLayerEscapeMove.c twoLayerEscapeAmbientSeen6 =
        twoLayerEscapeAmbientLayer6 := by
  decide

private theorem twoLayerEscapeAmbient_seen7 :
    appendFresh twoLayerEscapeAmbientSeen6 twoLayerEscapeAmbientLayer6 =
      twoLayerEscapeAmbientSeen7 := by
  decide

private theorem twoLayerEscapeAmbient_layer7 :
    nextChainComponentLayer twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
      twoLayerEscapeMove.a twoLayerEscapeMove.c twoLayerEscapeAmbientSeen7 =
        twoLayerEscapeAmbientLayer7 := by
  decide

private theorem twoLayerEscapeAmbient_seen8 :
    appendFresh twoLayerEscapeAmbientSeen7 twoLayerEscapeAmbientLayer7 =
      twoLayerEscapeAmbientSeen8 := by
  decide

private theorem twoLayerEscapeAmbient_layer8 :
    nextChainComponentLayer twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
      twoLayerEscapeMove.a twoLayerEscapeMove.c twoLayerEscapeAmbientSeen8 =
        twoLayerEscapeAmbientLayer8 := by
  decide

private theorem twoLayerEscapeAmbient_seen9 :
    appendFresh twoLayerEscapeAmbientSeen8 twoLayerEscapeAmbientLayer8 =
      twoLayerEscapeAmbientSeen9 := by
  decide

private theorem twoLayerEscapeAmbient_layer9 :
    nextChainComponentLayer twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
      twoLayerEscapeMove.a twoLayerEscapeMove.c twoLayerEscapeAmbientSeen9 =
        twoLayerEscapeAmbientLayer9 := by
  decide

private theorem twoLayerEscapeAmbient_seen10 :
    appendFresh twoLayerEscapeAmbientSeen9 twoLayerEscapeAmbientLayer9 =
      twoLayerEscapeAmbientSeen10 := by
  decide

private theorem twoLayerEscapeAmbient_layer10 :
    nextChainComponentLayer twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
      twoLayerEscapeMove.a twoLayerEscapeMove.c twoLayerEscapeAmbientSeen10 = [] := by
  decide

theorem twoLayerEscape_actualAmbientComponent :
    twoLayerEscapeActualAmbientComponent = twoLayerEscapeAmbientComponent := by
  unfold twoLayerEscapeActualAmbientComponent chainComponent
  have hseed :
      chainEdgeInPair twoLayerEscapeAmbientSource
        twoLayerEscapeMove.a twoLayerEscapeMove.c twoLayerEscapeMove.seed = true := by
    decide
  simp only [hseed, ↓reduceIte]
  change
    closeChainComponent twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
      twoLayerEscapeMove.a twoLayerEscapeMove.c 31 twoLayerEscapeAmbientSeen0 =
        twoLayerEscapeAmbientComponent
  rw [closeChainComponent_succ_eq
    twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
    twoLayerEscapeMove.a twoLayerEscapeMove.c
    twoLayerEscapeAmbientSeen0 twoLayerEscapeAmbientLayer0 _
    twoLayerEscapeAmbient_layer0]
  rw [twoLayerEscapeAmbient_seen1]
  rw [closeChainComponent_succ_eq
    twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
    twoLayerEscapeMove.a twoLayerEscapeMove.c
    twoLayerEscapeAmbientSeen1 twoLayerEscapeAmbientLayer1 _
    twoLayerEscapeAmbient_layer1]
  rw [twoLayerEscapeAmbient_seen2]
  rw [closeChainComponent_succ_eq
    twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
    twoLayerEscapeMove.a twoLayerEscapeMove.c
    twoLayerEscapeAmbientSeen2 twoLayerEscapeAmbientLayer2 _
    twoLayerEscapeAmbient_layer2]
  rw [twoLayerEscapeAmbient_seen3]
  rw [closeChainComponent_succ_eq
    twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
    twoLayerEscapeMove.a twoLayerEscapeMove.c
    twoLayerEscapeAmbientSeen3 twoLayerEscapeAmbientLayer3 _
    twoLayerEscapeAmbient_layer3]
  rw [twoLayerEscapeAmbient_seen4]
  rw [closeChainComponent_succ_eq
    twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
    twoLayerEscapeMove.a twoLayerEscapeMove.c
    twoLayerEscapeAmbientSeen4 twoLayerEscapeAmbientLayer4 _
    twoLayerEscapeAmbient_layer4]
  rw [twoLayerEscapeAmbient_seen5]
  rw [closeChainComponent_succ_eq
    twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
    twoLayerEscapeMove.a twoLayerEscapeMove.c
    twoLayerEscapeAmbientSeen5 twoLayerEscapeAmbientLayer5 _
    twoLayerEscapeAmbient_layer5]
  rw [twoLayerEscapeAmbient_seen6]
  rw [closeChainComponent_succ_eq
    twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
    twoLayerEscapeMove.a twoLayerEscapeMove.c
    twoLayerEscapeAmbientSeen6 twoLayerEscapeAmbientLayer6 _
    twoLayerEscapeAmbient_layer6]
  rw [twoLayerEscapeAmbient_seen7]
  rw [closeChainComponent_succ_eq
    twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
    twoLayerEscapeMove.a twoLayerEscapeMove.c
    twoLayerEscapeAmbientSeen7 twoLayerEscapeAmbientLayer7 _
    twoLayerEscapeAmbient_layer7]
  rw [twoLayerEscapeAmbient_seen8]
  rw [closeChainComponent_succ_eq
    twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
    twoLayerEscapeMove.a twoLayerEscapeMove.c
    twoLayerEscapeAmbientSeen8 twoLayerEscapeAmbientLayer8 _
    twoLayerEscapeAmbient_layer8]
  rw [twoLayerEscapeAmbient_seen9]
  rw [closeChainComponent_succ_eq
    twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
    twoLayerEscapeMove.a twoLayerEscapeMove.c
    twoLayerEscapeAmbientSeen9 twoLayerEscapeAmbientLayer9 _
    twoLayerEscapeAmbient_layer9]
  rw [twoLayerEscapeAmbient_seen10]
  rw [closeChainComponent_eq_self_of_layer_nil
    twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource
    twoLayerEscapeMove.a twoLayerEscapeMove.c
    twoLayerEscapeAmbientSeen10 twoLayerEscapeAmbient_layer10]
  decide

/--
The finite obstruction class for Section 9.2 Step 4: a collar-certified
switch can be input-avoiding before ambient execution, yet the corresponding
ambient component can escape through the shared inner side, hit the fixed
outer input side, and induce a different restriction on the collar.
-/
def Section92Step4TwoLayerCounterexampleClass : Prop :=
  compatibleChainStates twoLayerEscapeOuterWord twoLayerEscapeCollarSource = true ∧
  compatibleChainStates twoLayerEscapeOuterWord twoLayerEscapeCollarTarget = true ∧
  compatibleChainStates twoLayerEscapeAmbientWord twoLayerEscapeAmbientSource = true ∧
  chainSpecifiedKempeStep twoLayerEscapeOuterWord
    twoLayerEscapeCollarSource twoLayerEscapeCollarTarget
    twoLayerEscapeMove = true ∧
  twoLayerEscapeActualAmbientComponent = twoLayerEscapeAmbientComponent ∧
  chainComponentAvoidsInputs twoLayerEscapeOuterWord
    twoLayerEscapeCollarComponent = true ∧
  twoLayerComponentLeavesOuterLayer = true ∧
  twoLayerComponentHitsOuterInput = true ∧
  chainComponentAvoidsInputs twoLayerEscapeAmbientWord
    twoLayerEscapeAmbientComponent = false ∧
  twoLayerAmbientRestrictionDiffers = true

theorem twoLayerEscape_outerSourceCompatible :
    compatibleChainStates twoLayerEscapeOuterWord
      twoLayerEscapeCollarSource = true := by
  decide

theorem twoLayerEscape_outerTargetCompatible :
    compatibleChainStates twoLayerEscapeOuterWord
      twoLayerEscapeCollarTarget = true := by
  decide

theorem twoLayerEscape_ambientSourceCompatible :
    compatibleChainStates twoLayerEscapeAmbientWord
      twoLayerEscapeAmbientSource = true := by
  decide

theorem twoLayerEscape_certifiedCollarStep :
    chainSpecifiedKempeStep twoLayerEscapeOuterWord
      twoLayerEscapeCollarSource twoLayerEscapeCollarTarget
      twoLayerEscapeMove = true := by
  decide

theorem twoLayerEscape_collarComponentAvoidsInputs :
    chainComponentAvoidsInputs twoLayerEscapeOuterWord
      twoLayerEscapeCollarComponent = true := by
  decide

theorem twoLayerEscape_componentLeavesOuterLayer :
    twoLayerComponentLeavesOuterLayer = true := by
  decide

theorem twoLayerEscape_componentHitsOuterInput :
    twoLayerComponentHitsOuterInput = true := by
  decide

theorem twoLayerEscape_ambientComponentDoesNotAvoidInputs :
    chainComponentAvoidsInputs twoLayerEscapeAmbientWord
      twoLayerEscapeAmbientComponent = false := by
  decide

theorem twoLayerEscape_ambientRestrictionDiffers :
    twoLayerAmbientRestrictionDiffers = true := by
  decide

theorem section92Step4TwoLayerCounterexampleClass :
    Section92Step4TwoLayerCounterexampleClass := by
  exact
    ⟨twoLayerEscape_outerSourceCompatible,
      twoLayerEscape_outerTargetCompatible,
      twoLayerEscape_ambientSourceCompatible,
      twoLayerEscape_certifiedCollarStep,
      twoLayerEscape_actualAmbientComponent,
      twoLayerEscape_collarComponentAvoidsInputs,
      twoLayerEscape_componentLeavesOuterLayer,
      twoLayerEscape_componentHitsOuterInput,
      twoLayerEscape_ambientComponentDoesNotAvoidInputs,
      twoLayerEscape_ambientRestrictionDiffers⟩

end GoertzelLemma818TwoLayerEscape

end Mettapedia.GraphTheory.FourColor
