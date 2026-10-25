import Mettapedia.TypeTheory.BubbleConversion

/-!
# Elaborating bubble conversions: naturality in the parameters and recorded work

A kernel with a conversion bubble accepts certificates that leave conversions
implicit. `BubbleConversion.Bubbles.sound` turns every conversion tree of a
bubble into a receipt of a chosen global equality, given a receipt for each
declared step. When the global equality is the equality judgment of a small
explicit checker, that fold is the elaboration of the bubble's conversions
into the checker's certificates. This module answers two questions about it:
does the elaboration commute with the maps between kernel parameters, and
what does an elaborated receipt cost?

* **Morphisms of presentations** (`Hom`). A morphism moves states along a
  reindexing of judgment fibres, bubbles to bubbles, and declared steps to
  declared steps. An embedding into a presentation with more formers, or a
  substitution, is a morphism exactly when it carries every declared step to a
  declared step. The action on conversion trees is functorial
  (`Hom.mapConv_identity`, `Hom.mapConv_comp`).
* **Naturality** (`sound_natural`, `sound_widen`). If receipts move along a map
  that preserves reflexivity, symmetry and transitivity, and the two
  justifications agree along the morphism, then elaborating a moved tree is
  moving the elaborated receipt. Widening a bubble inside one presentation is
  the case where neither states nor receipts move. Without coherent
  justifications widening can change the receipt
  (`Controls.incoherent_justification_breaks_naturality`).
* **Recorded work** (`stepCount`, `countEquality`, `sound_count`). The number
  of declared steps written in a tree is itself an elaboration, into receipts
  that count. Pairing it with any other elaboration (`prodEquality`,
  `sound_prod`, `gradedSound_eq`) grades each receipt by the work it records.
  Morphisms and widening preserve the grade (`stepCount_mapConv`,
  `stepCount_widen`).
* **Receipts at least as large as the work, for tree receipts**
  (`stepCount_le_size`). If a receipt size never shrinks under symmetry or
  transitivity and every step receipt has size at least one, every elaborated
  receipt is at least as large as the work it records. Both hypotheses are
  needed. Receipts that keep only their endpoints admit no such size
  (`Controls.endpoint_no_treeAdditiveSize`), although the work they stand for
  is unbounded (`Controls.stepCount_doubling`). A size by height is not
  tree-additive and falls below the work (`Controls.height_below_work`).

Nothing here decides a bubble's conversion: a decision procedure for a bubble
or for a join of bubbles is a separate property.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleElaboration

open FreeConversion JudgmentalEquality BubbleConversion

universe uIndex uState uBubble uStep uTarget uTarget'
  uIndex' uState' uBubble' uStep' uIndex'' uState'' uBubble'' uStep''

/-! ## Recorded work -/

section Work

variable {Index : Type uIndex} {State : Index → Type uState}
  {Step : {index : Index} → State index → State index → Type uStep}

/-- The number of declared steps written in a conversion tree. Reflexivity
writes none, symmetry reuses its tree, and transitivity writes both of its
trees. -/
def stepCount : {index : Index} → {source target : State index} →
    Path State Step source target → ℕ
  | _, _, _, .step _ => 1
  | _, _, _, .refl _ => 0
  | _, _, _, .symm path => stepCount path
  | _, _, _, .trans first second => stepCount first + stepCount second

@[simp] theorem stepCount_step {index : Index} {source target : State index}
    (evidence : Step source target) :
    stepCount (State := State) (Step := Step) (.step evidence) = 1 := by
  simp [stepCount]

@[simp] theorem stepCount_refl {index : Index} (state : State index) :
    stepCount (ConversionEvidence.refl (computation := computation State Step) state) = 0 := by
  simp [stepCount]

@[simp] theorem stepCount_symm {index : Index} {source target : State index}
    (path : Path State Step source target) :
    stepCount (.symm path) = stepCount path := by
  simp [stepCount]

@[simp] theorem stepCount_trans {index : Index} {source middle target : State index}
    (first : Path State Step source middle) (second : Path State Step middle target) :
    stepCount (.trans first second) = stepCount first + stepCount second := by
  simp [stepCount]

end Work

/-! ## The fold on each constructor -/

section Sound

variable {Index : Type uIndex} (B : Bubbles.{uIndex, uState, uBubble, uStep} Index)
  (G : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget}) {bubble : B.Bubble}
  (justify : ∀ {index : Index} {source target : B.State index},
    B.Step bubble source target → G.Eq source target)

@[simp] theorem sound_step {index : Index} {source target : B.State index}
    (step : B.Step bubble source target) :
    B.sound G justify (.step step) = justify step := by
  simp [Bubbles.sound]

@[simp] theorem sound_refl {index : Index} (state : B.State index) :
    B.sound G justify
        (ConversionEvidence.refl (computation := computation B.State (B.Step bubble)) state) =
      G.refl state := by
  simp [Bubbles.sound]

@[simp] theorem sound_symm {index : Index} {source target : B.State index}
    (path : B.Conv bubble source target) :
    B.sound G justify (.symm path) = G.symm (B.sound G justify path) := by
  simp [Bubbles.sound]

@[simp] theorem sound_trans {index : Index} {source middle target : B.State index}
    (first : B.Conv bubble source middle) (second : B.Conv bubble middle target) :
    B.sound G justify (.trans first second) =
      G.trans (B.sound G justify first) (B.sound G justify second) := by
  simp [Bubbles.sound]

end Sound

/-! ## Widening a bubble -/

section Widen

variable {Index : Type uIndex} (B : Bubbles.{uIndex, uState, uBubble, uStep} Index)
  (G : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget})
  {small large : B.Bubble}
  (embed : ∀ {index : Index} {source target : B.State index},
    B.Step small source target → B.Step large source target)

/-- **Elaboration commutes with widening a bubble.** When the larger bubble
justifies every embedded step as the smaller bubble does, elaborating a
widened tree gives the receipt of the original tree. -/
theorem sound_widen
    (justifySmall : ∀ {index : Index} {source target : B.State index},
      B.Step small source target → G.Eq source target)
    (justifyLarge : ∀ {index : Index} {source target : B.State index},
      B.Step large source target → G.Eq source target)
    (coherent : ∀ {index : Index} {source target : B.State index}
      (step : B.Step small source target), justifyLarge (embed step) = justifySmall step) :
    ∀ {index : Index} {source target : B.State index} (path : B.Conv small source target),
      B.sound G justifyLarge (B.widen embed path) = B.sound G justifySmall path
  | _, _, _, .step step => by
      simp only [Bubbles.widen_step, sound_step, coherent]
  | _, _, _, .refl state => by
      simp only [Bubbles.widen_reflexive, sound_refl]
  | _, _, _, .symm path => by
      simp only [Bubbles.widen_symm, sound_symm,
        sound_widen justifySmall justifyLarge coherent path]
  | _, _, _, .trans first second => by
      simp only [Bubbles.widen_trans, sound_trans,
        sound_widen justifySmall justifyLarge coherent first,
        sound_widen justifySmall justifyLarge coherent second]

/-- Widening keeps the recorded work. -/
theorem stepCount_widen :
    ∀ {index : Index} {source target : B.State index} (path : B.Conv small source target),
      stepCount (B.widen embed path) = stepCount path
  | _, _, _, .step _ => by simp only [Bubbles.widen_step, stepCount_step]
  | _, _, _, .refl _ => by simp only [Bubbles.widen_reflexive, stepCount_refl]
  | _, _, _, .symm path => by
      simp only [Bubbles.widen_symm, stepCount_symm, stepCount_widen path]
  | _, _, _, .trans first second => by
      simp only [Bubbles.widen_trans, stepCount_trans, stepCount_widen first,
        stepCount_widen second]

end Widen

/-! ## Morphisms of presentations -/

set_option linter.checkUnivs false in
/-- A morphism of bubble presentations: a reindexing of judgment fibres with a
map of states, a map of bubbles, and a map of declared steps between the moved
endpoints. -/
structure Hom {Index : Type uIndex} {Index' : Type uIndex'}
    (B : Bubbles.{uIndex, uState, uBubble, uStep} Index)
    (B' : Bubbles.{uIndex', uState', uBubble', uStep'} Index') where
  reindex : Index → Index'
  state : ∀ {index : Index}, B.State index → B'.State (reindex index)
  bubble : B.Bubble → B'.Bubble
  step : ∀ {b : B.Bubble} {index : Index} {source target : B.State index},
    B.Step b source target → B'.Step (bubble b) (state source) (state target)

namespace Hom

variable {Index : Type uIndex} {Index' : Type uIndex'} {Index'' : Type uIndex''}
  {B : Bubbles.{uIndex, uState, uBubble, uStep} Index}
  {B' : Bubbles.{uIndex', uState', uBubble', uStep'} Index'}
  {B'' : Bubbles.{uIndex'', uState'', uBubble'', uStep''} Index''}

/-- The action of a morphism on conversion trees. -/
def mapConv (h : Hom B B') (b : B.Bubble) :
    ∀ {index : Index} {source target : B.State index},
      B.Conv b source target →
        B'.Conv (h.bubble b) (index := h.reindex index) (h.state source) (h.state target) :=
  fun path => Algebra.fold
    (Target := fun {index} (source target : B.State index) =>
      B'.Conv (h.bubble b) (index := h.reindex index) (h.state source) (h.state target))
    { onStep := fun step => .step (h.step step)
      onRefl := fun state => ConversionEvidence.refl
        (computation := computation B'.State (B'.Step (h.bubble b))) (h.state state)
      onSymm := fun converted => .symm converted
      onTrans := fun first second => .trans first second } path

section MapConvEquations

variable (h : Hom B B') (b : B.Bubble) {index : Index}

@[simp] theorem mapConv_step {source target : B.State index} (step : B.Step b source target) :
    h.mapConv b (.step step) = .step (h.step step) := by
  simp [mapConv]

@[simp] theorem mapConv_refl (state : B.State index) :
    h.mapConv b (ConversionEvidence.refl (computation := computation B.State (B.Step b)) state) =
      ConversionEvidence.refl (computation := computation B'.State (B'.Step (h.bubble b)))
        (h.state state) := by
  simp [mapConv]

@[simp] theorem mapConv_symm {source target : B.State index} (path : B.Conv b source target) :
    h.mapConv b (.symm path) = .symm (h.mapConv b path) := by
  simp [mapConv]

@[simp] theorem mapConv_trans {source middle target : B.State index}
    (first : B.Conv b source middle) (second : B.Conv b middle target) :
    h.mapConv b (.trans first second) = .trans (h.mapConv b first) (h.mapConv b second) := by
  simp [mapConv]

end MapConvEquations

/-- The identity morphism. -/
def identity (B : Bubbles.{uIndex, uState, uBubble, uStep} Index) : Hom B B where
  reindex index := index
  state source := source
  bubble b := b
  step step := step

/-- Composition of morphisms. -/
def comp (second : Hom B' B'') (first : Hom B B') : Hom B B'' where
  reindex index := second.reindex (first.reindex index)
  state source := second.state (first.state source)
  bubble b := second.bubble (first.bubble b)
  step step := second.step (first.step step)

/-- The identity morphism acts as the identity on conversion trees. -/
theorem mapConv_identity (b : B.Bubble) :
    ∀ {index : Index} {source target : B.State index} (path : B.Conv b source target),
      (identity B).mapConv b path = path
  | _, _, _, .step _ => by simp only [mapConv_step]; rfl
  | _, _, _, .refl _ => by simp only [mapConv_refl]; rfl
  | _, _, _, .symm path => by
      simp only [mapConv_symm]
      exact congrArg ConversionEvidence.symm (mapConv_identity b path)
  | _, _, _, .trans first second => by
      simp only [mapConv_trans]
      exact congrArg₂ ConversionEvidence.trans (mapConv_identity b first)
        (mapConv_identity b second)

/-- Acting by a composite is acting twice. -/
theorem mapConv_comp (second : Hom B' B'') (first : Hom B B') (b : B.Bubble) :
    ∀ {index : Index} {source target : B.State index} (path : B.Conv b source target),
      (second.comp first).mapConv b path =
        second.mapConv (first.bubble b) (first.mapConv b path)
  | _, _, _, .step _ => by simp only [mapConv_step]; rfl
  | _, _, _, .refl _ => by simp only [mapConv_refl]; rfl
  | _, _, _, .symm path => by
      simp only [mapConv_symm]
      exact congrArg ConversionEvidence.symm (mapConv_comp second first b path)
  | _, _, _, .trans first' second' => by
      simp only [mapConv_trans]
      exact congrArg₂ ConversionEvidence.trans (mapConv_comp second first b first')
        (mapConv_comp second first b second')

/-- Morphisms keep the recorded work. -/
theorem stepCount_mapConv (h : Hom B B') (b : B.Bubble) :
    ∀ {index : Index} {source target : B.State index} (path : B.Conv b source target),
      stepCount (h.mapConv b path) = stepCount path
  | _, _, _, .step _ => by simp only [mapConv_step, stepCount_step]
  | _, _, _, .refl _ => by simp only [mapConv_refl, stepCount_refl]
  | _, _, _, .symm path => by
      simp only [mapConv_symm, stepCount_symm]
      exact stepCount_mapConv h b path
  | _, _, _, .trans first second => by
      simp only [mapConv_trans, stepCount_trans]
      exact congrArg₂ (· + ·) (stepCount_mapConv h b first) (stepCount_mapConv h b second)

end Hom

/-! ## Receipt maps and naturality -/

set_option linter.checkUnivs false in
/-- A map of receipts along a morphism of presentations that preserves
reflexivity, symmetry and transitivity on the nose. -/
structure EqualityHom {Index : Type uIndex} {Index' : Type uIndex'}
    {B : Bubbles.{uIndex, uState, uBubble, uStep} Index}
    {B' : Bubbles.{uIndex', uState', uBubble', uStep'} Index'} (h : Hom B B')
    (G : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget})
    (G' : B'.GlobalEquality.{uIndex', uState', uBubble', uStep', uTarget'}) where
  map : ∀ {index : Index} {source target : B.State index},
    G.Eq source target → G'.Eq (h.state source) (h.state target)
  map_refl : ∀ {index : Index} (state : B.State index),
    map (G.refl state) = G'.refl (h.state state)
  map_symm : ∀ {index : Index} {source target : B.State index} (receipt : G.Eq source target),
    map (G.symm receipt) = G'.symm (map receipt)
  map_trans : ∀ {index : Index} {source middle target : B.State index}
    (first : G.Eq source middle) (second : G.Eq middle target),
    map (G.trans first second) = G'.trans (map first) (map second)

/-- The identity map of receipts over the identity morphism. -/
def EqualityHom.identity {Index : Type uIndex} {B : Bubbles.{uIndex, uState, uBubble, uStep} Index}
    (G : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget}) :
    EqualityHom (Hom.identity B) G G where
  map receipt := receipt
  map_refl _ := rfl
  map_symm _ := rfl
  map_trans _ _ := rfl

section Natural

variable {Index : Type uIndex} {Index' : Type uIndex'}
  {B : Bubbles.{uIndex, uState, uBubble, uStep} Index}
  {B' : Bubbles.{uIndex', uState', uBubble', uStep'} Index'}

/-- **Elaboration is natural in the presentation.** Along a morphism of
presentations with a structure-preserving map of receipts, elaborating the
moved tree with a coherent justification is moving the elaborated receipt. -/
theorem sound_natural (h : Hom B B')
    {G : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget}}
    {G' : B'.GlobalEquality.{uIndex', uState', uBubble', uStep', uTarget'}}
    (receipts : EqualityHom h G G') (b : B.Bubble)
    (justify : ∀ {index : Index} {source target : B.State index},
      B.Step b source target → G.Eq source target)
    (justify' : ∀ {index : Index'} {source target : B'.State index},
      B'.Step (h.bubble b) source target → G'.Eq source target)
    (coherent : ∀ {index : Index} {source target : B.State index}
      (step : B.Step b source target), justify' (h.step step) = receipts.map (justify step)) :
    ∀ {index : Index} {source target : B.State index} (path : B.Conv b source target),
      B'.sound G' justify' (h.mapConv b path) = receipts.map (B.sound G justify path)
  | _, _, _, .step step => by
      rw [Hom.mapConv_step, sound_step, sound_step, coherent]
  | _, _, _, .refl state => by
      rw [Hom.mapConv_refl, sound_refl, sound_refl, receipts.map_refl]
  | _, _, _, .symm path => by
      rw [Hom.mapConv_symm, sound_symm, sound_symm, receipts.map_symm,
        sound_natural h receipts b justify justify' coherent path]
  | _, _, _, .trans first second => by
      rw [Hom.mapConv_trans, sound_trans, sound_trans, receipts.map_trans,
        sound_natural h receipts b justify justify' coherent first,
        sound_natural h receipts b justify justify' coherent second]

end Natural

/-! ## Graded receipts -/

section Grade

variable {Index : Type uIndex} (B : Bubbles.{uIndex, uState, uBubble, uStep} Index)

/-- Receipts that count: reflexivity counts nothing, symmetry keeps the count,
and transitivity adds the counts. -/
abbrev countEquality : B.GlobalEquality.{uIndex, uState, uBubble, uStep, 0} where
  Eq _ _ := ℕ
  refl _ := 0
  symm receipt := receipt
  trans first second := first + second

/-- **The recorded work is an elaboration**: counting one per declared step. -/
theorem sound_count {b : B.Bubble} :
    ∀ {index : Index} {source target : B.State index} (path : B.Conv b source target),
      B.sound (countEquality B) (fun _ => (1 : ℕ)) path = stepCount path
  | _, _, _, .step _ => by rw [sound_step, stepCount_step]
  | _, _, _, .refl _ => by rw [sound_refl, stepCount_refl]
  | _, _, _, .symm path => by
      rw [sound_symm, stepCount_symm]
      exact sound_count path
  | _, _, _, .trans first second => by
      rw [sound_trans, stepCount_trans]
      exact congrArg₂ (· + ·) (sound_count first) (sound_count second)

/-- Two receipts for the same pair of endpoints, composed componentwise. -/
abbrev prodEquality (G : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget})
    (H : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget'}) :
    B.GlobalEquality.{uIndex, uState, uBubble, uStep, max uTarget uTarget'} where
  Eq source target := G.Eq source target × H.Eq source target
  refl state := (G.refl state, H.refl state)
  symm receipt := (G.symm receipt.1, H.symm receipt.2)
  trans first second := (G.trans first.1 second.1, H.trans first.2 second.2)

/-- Elaborating into a pair of global equalities is the pair of
elaborations. -/
theorem sound_prod (G : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget})
    (H : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget'}) {b : B.Bubble}
    (justify : ∀ {index : Index} {source target : B.State index},
      B.Step b source target → G.Eq source target)
    (justify' : ∀ {index : Index} {source target : B.State index},
      B.Step b source target → H.Eq source target) :
    ∀ {index : Index} {source target : B.State index} (path : B.Conv b source target),
      B.sound (prodEquality B G H) (fun step => (justify step, justify' step)) path =
        (B.sound G justify path, B.sound H justify' path)
  | _, _, _, .step step => by rw [sound_step, sound_step, sound_step]
  | _, _, _, .refl state => by rw [sound_refl, sound_refl, sound_refl]
  | _, _, _, .symm path => by
      rw [sound_symm, sound_symm, sound_symm, sound_prod G H justify justify' path]
  | _, _, _, .trans first second => by
      rw [sound_trans, sound_trans, sound_trans, sound_prod G H justify justify' first,
        sound_prod G H justify justify' second]

/-- Elaborate a conversion tree and grade its receipt by the recorded work. -/
def gradedSound (G : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget}) {b : B.Bubble}
    (justify : ∀ {index : Index} {source target : B.State index},
      B.Step b source target → G.Eq source target)
    {index : Index} {source target : B.State index} (path : B.Conv b source target) :
    G.Eq source target × ℕ :=
  B.sound (prodEquality B G (countEquality B)) (fun step => (justify step, (1 : ℕ))) path

/-- The graded receipt is the receipt together with the number of declared
steps it records. -/
theorem gradedSound_eq (G : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget})
    {b : B.Bubble}
    (justify : ∀ {index : Index} {source target : B.State index},
      B.Step b source target → G.Eq source target)
    {index : Index} {source target : B.State index} (path : B.Conv b source target) :
    gradedSound B G justify path = (B.sound G justify path, stepCount path) := by
  rw [gradedSound, sound_prod B G (countEquality B) justify (fun _ => (1 : ℕ)) path,
    sound_count B path]

/-! ### Tree receipts are at least as large as the work -/

/-- A receipt size is tree-additive when symmetry never shrinks a receipt and
transitivity is at least as large as its two parts together. -/
structure TreeAdditiveSize (G : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget}) where
  size : ∀ {index : Index} {source target : B.State index}, G.Eq source target → ℕ
  symm_ge : ∀ {index : Index} {source target : B.State index} (receipt : G.Eq source target),
    size receipt ≤ size (G.symm receipt)
  trans_ge : ∀ {index : Index} {source middle target : B.State index}
    (first : G.Eq source middle) (second : G.Eq middle target),
    size first + size second ≤ size (G.trans first second)

/-- **A tree receipt is at least as large as the work it records.** -/
theorem stepCount_le_size {G : B.GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget}}
    (sized : TreeAdditiveSize B G) {b : B.Bubble}
    (justify : ∀ {index : Index} {source target : B.State index},
      B.Step b source target → G.Eq source target)
    (positive : ∀ {index : Index} {source target : B.State index}
      (step : B.Step b source target), 1 ≤ sized.size (justify step)) :
    ∀ {index : Index} {source target : B.State index} (path : B.Conv b source target),
      stepCount path ≤ sized.size (B.sound G justify path)
  | _, _, _, .step step => by
      rw [stepCount_step, sound_step]
      exact positive step
  | _, _, _, .refl _ => by
      rw [stepCount_refl]
      exact Nat.zero_le _
  | _, _, _, .symm path => by
      rw [stepCount_symm, sound_symm]
      exact Nat.le_trans (stepCount_le_size sized justify positive path) (sized.symm_ge _)
  | _, _, _, .trans first second => by
      rw [stepCount_trans, sound_trans]
      exact Nat.le_trans (Nat.add_le_add (stepCount_le_size sized justify positive first)
        (stepCount_le_size sized justify positive second)) (sized.trans_ge _ _)

/-- Counting receipts are tree-additive, with equality. -/
def countSize : TreeAdditiveSize B (countEquality B) where
  size receipt := receipt
  symm_ge _ := Nat.le_refl _
  trans_ge _ _ := Nat.le_refl _

end Grade

/-! ## Controls -/

namespace Controls

/-- One state with one declared loop step. -/
abbrev loop : Bubbles.{0, 0, 0, 0} Unit where
  State _ := Unit
  Bubble := Unit
  Step _ {_} _ _ := Unit

/-- The one-step tree of the loop. -/
def oneStep : loop.Conv () (index := ()) () () := .step ()

/-- **Coherence of justifications is needed for naturality.** Widening the loop
bubble into itself with counting receipts, a larger bubble that justifies the
loop step by two instead of one changes the elaborated receipt of the one-step
tree. -/
theorem incoherent_justification_breaks_naturality :
    loop.sound (countEquality loop) (fun _ => (2 : ℕ))
        (loop.widen (small := ()) (large := ()) (fun step => step) oneStep) ≠
      loop.sound (countEquality loop) (fun _ => (1 : ℕ)) oneStep := by
  rw [oneStep, Bubbles.widen_step, sound_step, sound_step]
  decide

/-- The doubling family: the tree for `n + 1` composes the tree for `n` with
itself. -/
def doubling : ℕ → loop.Conv () (index := ()) () ()
  | 0 => .step ()
  | n + 1 => .trans (doubling n) (doubling n)

/-- The doubling trees record exponentially many steps. -/
theorem stepCount_doubling : ∀ n : ℕ, stepCount (doubling n) = 2 ^ n
  | 0 => by rw [doubling, stepCount_step]
  | n + 1 => by
      rw [doubling, stepCount_trans, stepCount_doubling n, Nat.pow_succ]
      omega

/-- Positive control: counting receipts meet the lower bound with equality. -/
theorem count_receipts_meet_work (n : ℕ) :
    stepCount (doubling n) ≤ (countSize loop).size
      (loop.sound (countEquality loop) (fun _ => (1 : ℕ)) (doubling n)) ∧
    loop.sound (countEquality loop) (fun _ => (1 : ℕ)) (doubling n) = 2 ^ n :=
  ⟨stepCount_le_size loop (countSize loop) (fun _ => (1 : ℕ)) (fun _ => Nat.le_refl _) (doubling n),
    (sound_count loop (doubling n)).trans (stepCount_doubling n)⟩

/-- Receipts that record only that their endpoints are related. -/
abbrev endpointEquality : loop.GlobalEquality.{0, 0, 0, 0, 0} where
  Eq _ _ := Unit
  refl _ := ()
  symm _ := ()
  trans _ _ := ()

/-- **Endpoint receipts admit no tree-additive size with positive step
receipts.** Such a size would be one number `c` with `1 ≤ c` and `c + c ≤ c`. -/
theorem endpoint_no_treeAdditiveSize :
    ¬ ∃ sized : TreeAdditiveSize loop endpointEquality,
      sized.size (index := ()) (source := ()) (target := ()) () ≥ 1 := by
  rintro ⟨sized, positive⟩
  have additive := sized.trans_ge (index := ()) (source := ()) (middle := ()) (target := ()) () ()
  change sized.size (index := ()) (source := ()) (target := ()) () +
      sized.size (index := ()) (source := ()) (target := ()) () ≤
    sized.size (index := ()) (source := ()) (target := ()) () at additive
  omega

/-- Receipts measured by height: transitivity is one more than the larger part. -/
abbrev heightEquality : loop.GlobalEquality.{0, 0, 0, 0, 0} where
  Eq _ _ := ℕ
  refl _ := 0
  symm receipt := receipt
  trans first second := max first second + 1

theorem height_doubling : ∀ n : ℕ,
    loop.sound heightEquality (fun _ => (1 : ℕ)) (doubling n) = n + 1
  | 0 => by rw [doubling, sound_step]
  | n + 1 => by
      rw [doubling, sound_trans, height_doubling n]
      change max (n + 1) (n + 1) + 1 = n + 1 + 1
      rw [Nat.max_self]

/-- **Height is not tree-additive and falls below the work.** On the doubling
family the height of the receipt is `n + 1` while the work is `2 ^ n`; already
at `n = 2` the work exceeds the height. -/
theorem height_below_work :
    (∀ n : ℕ, loop.sound heightEquality (fun _ => (1 : ℕ)) (doubling n) = n + 1 ∧
      stepCount (doubling n) = 2 ^ n) ∧
    ¬ (∀ n : ℕ, stepCount (doubling n) ≤
      loop.sound heightEquality (fun _ => (1 : ℕ)) (doubling n)) := by
  refine ⟨fun n => ⟨height_doubling n, stepCount_doubling n⟩, fun bounded => ?_⟩
  have atTwo := bounded 2
  rw [stepCount_doubling, height_doubling] at atTwo
  omega

end Controls

/-! ## Axiom audit -/

#print axioms sound_widen
#print axioms stepCount_widen
#print axioms Hom.mapConv_identity
#print axioms Hom.mapConv_comp
#print axioms Hom.stepCount_mapConv
#print axioms sound_natural
#print axioms sound_count
#print axioms sound_prod
#print axioms gradedSound_eq
#print axioms stepCount_le_size
#print axioms Controls.incoherent_justification_breaks_naturality
#print axioms Controls.stepCount_doubling
#print axioms Controls.count_receipts_meet_work
#print axioms Controls.endpoint_no_treeAdditiveSize
#print axioms Controls.height_below_work

end Mettapedia.TypeTheory.BubbleElaboration
