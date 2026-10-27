import Mettapedia.TypeTheory.BubbleElaboration

/-!
# Fibre-local reindexing of conversion trees and naturality of elaboration

`BubbleElaboration.Hom` moves every judgment fibre at once: its reindexing is a total map of
indices. A substitution along a typed context morphism, or a weakening, is not of that kind.
It exists between the two fibres the morphism connects, and only there. This module gives
the fibre-local notion and proves that elaboration commutes with it.

* **Fibre maps** (`FibreMap`): between two fibres `i` and `j` of one bubble, a map of states
  and a map of declared steps between the moved endpoints. They act on conversion trees
  (`FibreMap.mapConv`), functorially (`mapConv_identity`, `mapConv_comp`), and keep the
  recorded work (`stepCount_mapConv`).
* **Receipt actions** (`ReceiptAction`): a map of receipts over a fibre map that preserves
  reflexivity, symmetry and transitivity on the nose.
* **Naturality** (`sound_mapConv`): when the justification is coherent with the fibre map on
  declared steps, elaborating a moved tree is moving the elaborated receipt. Coherence is
  checked on generators only.
* **Families of fibre maps** (`Reindexing`): arrows between indices act by fibre maps. A
  justification coherent on the generators along every arrow makes elaboration commute with
  every arrow, into any receipt family with a compatible action (`Reindexing.sound_natural`).

The control `Controls.incoherent_breaks_naturality` shows coherence is needed: with counting
receipts, a fibre map that is coherent for the justification by one is not coherent for a
justification that counts a moved step twice, and the receipts differ.

Nothing here decides conversion, proves preservation of typing by the moved steps, or
supplies the justification; each is a separate obligation of a concrete presentation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleReindexing

open FreeConversion JudgmentalEquality BubbleConversion BubbleElaboration

universe uIndex uState uBubble uStep uTarget uArrow

variable {Index : Type uIndex}

/-! ## Fibre maps -/

/-- A map from fibre `source` to fibre `target` of one bubble: states and declared steps. -/
structure FibreMap (B : Bubbles.{uIndex, uState, uBubble, uStep} Index) (b : B.Bubble)
    (source target : Index) where
  state : B.State source → B.State target
  step : ∀ {x y : B.State source}, B.Step b x y → B.Step b (state x) (state y)

namespace FibreMap

variable {B : Bubbles.{uIndex, uState, uBubble, uStep} Index} {b : B.Bubble}

/-- The action of a fibre map on conversion trees. -/
def mapConv {i j : Index} (σ : FibreMap B b i j) :
    {x y : B.State i} → B.Conv b x y → B.Conv b (index := j) (σ.state x) (σ.state y)
  | _, _, .step s => .step (σ.step s)
  | _, _, .refl x => .refl (computation := computation B.State (B.Step b)) (σ.state x)
  | _, _, .symm path => .symm (σ.mapConv path)
  | _, _, .trans first second => .trans (σ.mapConv first) (σ.mapConv second)

/-- The identity fibre map. -/
def identity (i : Index) : FibreMap B b i i where
  state x := x
  step s := s

/-- Composition of fibre maps. -/
def comp {i j k : Index} (τ : FibreMap B b j k) (σ : FibreMap B b i j) : FibreMap B b i k where
  state x := τ.state (σ.state x)
  step s := τ.step (σ.step s)

theorem mapConv_identity {i : Index} :
    ∀ {x y : B.State i} (path : B.Conv b x y), (identity (B := B) (b := b) i).mapConv path = path
  | _, _, .step _ => rfl
  | _, _, .refl _ => rfl
  | _, _, .symm path => by
      simp only [mapConv]
      rw [mapConv_identity path]
      rfl
  | _, _, .trans first second => by
      simp only [mapConv]
      rw [mapConv_identity first, mapConv_identity second]
      rfl

theorem mapConv_comp {i j k : Index} (τ : FibreMap B b j k) (σ : FibreMap B b i j) :
    ∀ {x y : B.State i} (path : B.Conv b x y),
      (τ.comp σ).mapConv path = τ.mapConv (σ.mapConv path)
  | _, _, .step _ => rfl
  | _, _, .refl _ => rfl
  | _, _, .symm path => by
      simp only [mapConv]
      rw [mapConv_comp τ σ path]
      rfl
  | _, _, .trans first second => by
      simp only [mapConv]
      rw [mapConv_comp τ σ first, mapConv_comp τ σ second]
      rfl

/-- **A fibre map keeps the recorded work.** -/
theorem stepCount_mapConv {i j : Index} (σ : FibreMap B b i j) :
    ∀ {x y : B.State i} (path : B.Conv b x y), stepCount (σ.mapConv path) = stepCount path
  | _, _, .step _ => by simp only [mapConv, stepCount_step]
  | _, _, .refl _ => by simp only [mapConv, stepCount_refl]
  | _, _, .symm path => by
      simp only [mapConv, stepCount_symm]
      exact stepCount_mapConv σ path
  | _, _, .trans first second => by
      simp only [mapConv, stepCount_trans]
      rw [stepCount_mapConv σ first, stepCount_mapConv σ second]

end FibreMap

/-! ## Receipt actions and naturality -/

/-- A map of receipts over a fibre map, preserving the three operations on the nose. -/
structure ReceiptAction {B : Bubbles.{uIndex, uState, uBubble, uStep} Index} {b : B.Bubble}
    (G : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget}) {i j : Index}
    (σ : FibreMap B b i j) where
  map : ∀ {x y : B.State i}, G.Eq x y → G.Eq (σ.state x) (σ.state y)
  map_refl : ∀ x : B.State i, map (G.refl x) = G.refl (σ.state x)
  map_symm : ∀ {x y : B.State i} (receipt : G.Eq x y), map (G.symm receipt) = G.symm (map receipt)
  map_trans : ∀ {x y z : B.State i} (first : G.Eq x y) (second : G.Eq y z),
    map (G.trans first second) = G.trans (map first) (map second)

section Natural

variable {B : Bubbles.{uIndex, uState, uBubble, uStep} Index} {b : B.Bubble}
  {G : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget}}

/-- **Elaboration commutes with a fibre map**, given coherence of the justification on the
declared steps. -/
theorem sound_mapConv {i j : Index} (σ : FibreMap B b i j) (act : ReceiptAction G σ)
    (justify : ∀ {index : Index} {x y : B.State index}, B.Step b x y → G.Eq x y)
    (coherent : ∀ {x y : B.State i} (s : B.Step b x y), justify (σ.step s) = act.map (justify s)) :
    ∀ {x y : B.State i} (path : B.Conv b x y),
      B.sound G justify (σ.mapConv path) = act.map (B.sound G justify path)
  | _, _, .step s => by
      simp only [FibreMap.mapConv, sound_step]
      exact coherent s
  | _, _, .refl x => by
      simp only [FibreMap.mapConv, sound_refl]
      exact (act.map_refl x).symm
  | _, _, .symm path => by
      simp only [FibreMap.mapConv, sound_symm]
      rw [sound_mapConv σ act justify coherent path, act.map_symm]
  | _, _, .trans first second => by
      simp only [FibreMap.mapConv, sound_trans]
      rw [sound_mapConv σ act justify coherent first,
        sound_mapConv σ act justify coherent second, act.map_trans]

end Natural

/-! ## Families of fibre maps indexed by arrows -/

set_option linter.checkUnivs false in
/-- Arrows between indices acting on one bubble by fibre maps. A typed substitution calculus
is the motivating instance: indices are judgments over contexts, arrows are context
morphisms, and composites of arrows act by composites of fibre maps
(`FibreMap.mapConv_comp`). -/
structure Reindexing (B : Bubbles.{uIndex, uState, uBubble, uStep} Index) (b : B.Bubble) where
  Arrow : Index → Index → Type uArrow
  act : ∀ {i j}, Arrow i j → FibreMap B b i j

namespace Reindexing

variable {B : Bubbles.{uIndex, uState, uBubble, uStep} Index} {b : B.Bubble}
  {G : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget}}

/-- **Elaboration is natural in every arrow** once the justification is coherent on the
generators along every arrow. -/
theorem sound_natural (R : Reindexing.{uIndex, uState, uBubble, uStep, uArrow} B b)
    (act : ∀ {i j} (σ : R.Arrow i j), ReceiptAction G (R.act σ))
    (justify : ∀ {index : Index} {x y : B.State index}, B.Step b x y → G.Eq x y)
    (coherent : ∀ {i j} (σ : R.Arrow i j) {x y : B.State i} (s : B.Step b x y),
      justify ((R.act σ).step s) = (act σ).map (justify s))
    {i j : Index} (σ : R.Arrow i j) {x y : B.State i} (path : B.Conv b x y) :
    B.sound G justify ((R.act σ).mapConv path) = (act σ).map (B.sound G justify path) :=
  sound_mapConv (R.act σ) (act σ) justify (coherent σ) path

/-- Moving along an arrow keeps the recorded work. -/
theorem stepCount_natural (R : Reindexing.{uIndex, uState, uBubble, uStep, uArrow} B b)
    {i j : Index} (σ : R.Arrow i j) {x y : B.State i} (path : B.Conv b x y) :
    stepCount ((R.act σ).mapConv path) = stepCount path :=
  (R.act σ).stepCount_mapConv path

end Reindexing

/-! ## Controls -/

namespace Controls

/-- Two fibres, each with one state, and one declared loop step in each. -/
abbrev twoFibres : Bubbles.{0, 0, 0, 0} Bool where
  State _ := Unit
  Bubble := Unit
  Step _ {_} _ _ := Unit

/-- The fibre map from fibre `false` to fibre `true`. -/
def shift : FibreMap twoFibres () false true where
  state _ := ()
  step _ := ()

/-- Counting receipts do not move. -/
def countAction : ReceiptAction (countEquality twoFibres) shift where
  map receipt := receipt
  map_refl _ := rfl
  map_symm _ := rfl
  map_trans _ _ := rfl

/-- **Positive control**: the justification by one is coherent, and the receipt of every
moved tree is the receipt of the tree. -/
theorem coherent_counts (path : twoFibres.Conv () (index := false) () ()) :
    twoFibres.sound (countEquality twoFibres) (fun _ => (1 : ℕ)) (shift.mapConv path) =
      twoFibres.sound (countEquality twoFibres) (fun _ => (1 : ℕ)) path :=
  sound_mapConv shift countAction (fun _ => (1 : ℕ)) (fun _ => rfl) path

/-- A justification that counts the steps of fibre `true` twice. -/
def doubleOnTrue : ∀ {index : Bool} {x y : twoFibres.State index},
    twoFibres.Step () x y → (countEquality twoFibres).Eq x y
  | false, _, _, _ => (1 : ℕ)
  | true, _, _, _ => (2 : ℕ)

/-- **Coherence is needed**: for the justification `doubleOnTrue` the moved one-step tree
has receipt two, while moving the receipt of the original tree gives one. -/
theorem incoherent_breaks_naturality :
    twoFibres.sound (countEquality twoFibres) doubleOnTrue
        (shift.mapConv (.step () : twoFibres.Conv () (index := false) () ())) ≠
      countAction.map
        (twoFibres.sound (countEquality twoFibres) doubleOnTrue
          (.step () : twoFibres.Conv () (index := false) () ())) := by
  simp only [FibreMap.mapConv, sound_step, countAction, doubleOnTrue]
  decide

end Controls

/-! ## Axiom audit -/

#print axioms FibreMap.mapConv_identity
#print axioms FibreMap.mapConv_comp
#print axioms FibreMap.stepCount_mapConv
#print axioms sound_mapConv
#print axioms Reindexing.sound_natural
#print axioms Reindexing.stepCount_natural
#print axioms Controls.coherent_counts
#print axioms Controls.incoherent_breaks_naturality

end Mettapedia.TypeTheory.BubbleReindexing
