import Mettapedia.Languages.MM0.PeanoEquationalFragment
import Mettapedia.TypeTheory.BubbleElaboration

/-!
# A justified rewriting conversion over Peano terms, as a rung on MM0

A kernel with a conversion bubble accepts `t ≡ u` when the two terms are
related by rewriting with declared rules, at any position, in any number of
steps and in either direction. This module puts such a kernel over the MM0
root of `PeanoEquationalFragment`, for every finite rule set, and proves what
it may then claim.

* **Rules and steps** (`Rule`, `Step`, `bubbles`). A rule is a pair of Peano
  patterns over its own variables. A step records the rule, the substitution
  and the position. Rule sets are the bubbles of a `BubbleConversion.Bubbles`
  presentation whose fibres are the numbers of free variables, so
  `bubbles.Conv rules t u` is the free conversion of the steps.
* **Justification** (`Justification`). Each rule of the set is mapped to a
  table position whose declaration is exactly the rule's equation
  (`Rule.declaration`).
* **Receipt mode** (`elaborate`, `elaborate_accepted`). The fold of the
  justifications over a conversion tree is an MM0 proof witness of `t = u`
  that the kernel model's checker accepts. Its grade is the number of
  recorded steps (`gradedReceipt_eq`), which its size bounds from below
  (`stepCount_le_nodeCount`); the size is exactly a fold of step costs
  (`nodeCount_elaborate`).
* **Rung mode** (`rung_sound`). Proved once: every conversion of a justified
  rule set is derivable in the root. Applying it costs no certificate.
* **An executable rewriting checker** (`checkTrace`). It replays a list of
  rewrite steps, checking each subterm against the rule instance, and builds
  no root certificate. Every accepted trace is sound (`checkTrace_sound`),
  receipt mode accepts exactly the same traces (`checkTrace_iff_receipt`), and
  the grade of the receipt is the length of the trace
  (`stepCount_traceConv`).
* **Widening** (`elaborate_widen`). Adding rules with the same
  justifications changes no receipt of a tree of the smaller set.
* **Controls.** A justification is a table lookup, so an unjustified rule
  gets no rung: the lying rule `a + 0 ↦ 0` has no justification in the root
  (`Controls.lying_rule_unjustified`), because its conversion would derive
  `1 + 0 = 0`, which the standard model refutes. The collapsing rule `a ↦ 0`
  converts any two terms (`Controls.collapse_converts_all`); justified by an
  added axiom, it makes the root derive every formula
  (`Controls.collapse_derives_every_formula`): false is the top.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.RewriteRung

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.MM0.PeanoEquationalFragment
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.FreeConversion
open Mettapedia.TypeTheory.JudgmentalEquality
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleElaboration

/-! ## Rules and rewrite steps -/

/-- A rewrite rule over `arity` pattern variables. -/
structure Rule where
  arity : Nat
  lhs : PTerm arity
  rhs : PTerm arity
  deriving DecidableEq, Repr

/-- The MM0 statement that justifies a rule: its equation over its pattern
variables. -/
abbrev Rule.declaration (rule : Rule) : TheoremDecl :=
  ⟨natContext rule.arity, [], eqn (encode rule.lhs) (encode rule.rhs)⟩

/-- One rewrite step of a rule set: a rule instance at some position. -/
inductive Step (rules : List Rule) {n : Nat} : PTerm n → PTerm n → Type where
  | root {rule : Rule} (member : rule ∈ rules) (σ : Fin rule.arity → PTerm n) :
      Step rules (rule.lhs.subst σ) (rule.rhs.subst σ)
  | succ {t u : PTerm n} : Step rules t u → Step rules (.succ t) (.succ u)
  | addLeft {t u : PTerm n} (w : PTerm n) : Step rules t u → Step rules (.add t w) (.add u w)
  | addRight {t u : PTerm n} (w : PTerm n) : Step rules t u → Step rules (.add w t) (.add w u)
  | mulLeft {t u : PTerm n} (w : PTerm n) : Step rules t u → Step rules (.mul t w) (.mul u w)
  | mulRight {t u : PTerm n} (w : PTerm n) : Step rules t u → Step rules (.mul w t) (.mul w u)

/-- Rule sets as bubbles over Peano terms: the fibre `n` holds the terms over
`n` variables. -/
abbrev bubbles : Bubbles.{0, 0, 0, 0} Nat where
  State n := PTerm n
  Bubble := List Rule
  Step rules {_} t u := Step rules t u

/-- The conversion of a rule set: free conversion trees of its steps. -/
abbrev Conv (rules : List Rule) {n : Nat} (t u : PTerm n) : Type :=
  bubbles.Conv rules (index := n) t u

/-! ## Justifications -/

/-- A justification of a rule set in the root `table extra`: a table position
for every rule, holding exactly the rule's equation. -/
structure Justification (extra : List Entry) (rules : List Rule) where
  index : Rule → Nat
  lookup : ∀ rule ∈ rules, table extra (index rule) = some rule.declaration

/-! ## Receipt mode -/

section Receipts

variable {extra : List Entry} {rules : List Rule}

/-- The witness of one step: the rule's table entry at the substitution,
wrapped in one congruence per position above it. -/
def stepWitness (J : Justification extra rules) {n : Nat} :
    {t u : PTerm n} → Step rules t u → ProofWitness
  | _, _, .root (rule := rule) _ σ =>
      .theoremApp (J.index rule) (List.ofFn fun i => encode (σ i)) []
  | _, _, .succ (t := t) (u := u) step => sucW (encode t) (encode u) (stepWitness J step)
  | _, _, .addLeft (t := t) (u := u) w step =>
      addW (encode t) (encode u) (encode w) (encode w) (stepWitness J step) (reflW (encode w))
  | _, _, .addRight (t := t) (u := u) w step =>
      addW (encode w) (encode w) (encode t) (encode u) (reflW (encode w)) (stepWitness J step)
  | _, _, .mulLeft (t := t) (u := u) w step =>
      mulW (encode t) (encode u) (encode w) (encode w) (stepWitness J step) (reflW (encode w))
  | _, _, .mulRight (t := t) (u := u) w step =>
      mulW (encode w) (encode w) (encode t) (encode u) (reflW (encode w)) (stepWitness J step)

/-- **The witness of every step is accepted** for the step's equation. -/
theorem stepWitness_checks (J : Justification extra rules) {n : Nat} :
    ∀ {t u : PTerm n} (step : Step rules t u),
      Checks extra n (stepWitness J step) (eqn (encode t) (encode u))
  | _, _, .root member σ => checks_instance (J.lookup _ member) σ
  | _, _, .succ step =>
      checks_suc (encode_typed _) (encode_typed _) (stepWitness_checks J step)
  | _, _, .addLeft w step =>
      checks_add (encode_typed _) (encode_typed _) (encode_typed w) (encode_typed w)
        (stepWitness_checks J step) (checks_refl (encode_typed w))
  | _, _, .addRight w step =>
      checks_add (encode_typed w) (encode_typed w) (encode_typed _) (encode_typed _)
        (checks_refl (encode_typed w)) (stepWitness_checks J step)
  | _, _, .mulLeft w step =>
      checks_mul (encode_typed _) (encode_typed _) (encode_typed w) (encode_typed w)
        (stepWitness_checks J step) (checks_refl (encode_typed w))
  | _, _, .mulRight w step =>
      checks_mul (encode_typed w) (encode_typed w) (encode_typed _) (encode_typed _)
        (checks_refl (encode_typed w)) (stepWitness_checks J step)

/-- The number of congruence nodes above a step: two for each `suc`, four for
each sum or product (two modus ponens, the congruence axiom and a reflexivity
for the other side). -/
def Step.congruenceCost {n : Nat} : {t u : PTerm n} → Step rules t u → Nat
  | _, _, .root _ _ => 0
  | _, _, .succ step => step.congruenceCost + 2
  | _, _, .addLeft _ step => step.congruenceCost + 4
  | _, _, .addRight _ step => step.congruenceCost + 4
  | _, _, .mulLeft _ step => step.congruenceCost + 4
  | _, _, .mulRight _ step => step.congruenceCost + 4

theorem nodeCount_stepWitness (J : Justification extra rules) {n : Nat} :
    ∀ {t u : PTerm n} (step : Step rules t u),
      nodeCount (stepWitness J step) = step.congruenceCost + 1
  | _, _, .root _ _ => by simp [stepWitness, Step.congruenceCost]
  | _, _, .succ step => by
      simp only [stepWitness, Step.congruenceCost, nodeCount_suc, nodeCount_stepWitness J step]
  | _, _, .addLeft _ step => by
      simp only [stepWitness, Step.congruenceCost, nodeCount_add, nodeCount_refl,
        nodeCount_stepWitness J step]
  | _, _, .addRight _ step => by
      simp only [stepWitness, Step.congruenceCost, nodeCount_add, nodeCount_refl,
        nodeCount_stepWitness J step]
      omega
  | _, _, .mulLeft _ step => by
      simp only [stepWitness, Step.congruenceCost, nodeCount_mul, nodeCount_refl,
        nodeCount_stepWitness J step]
  | _, _, .mulRight _ step => by
      simp only [stepWitness, Step.congruenceCost, nodeCount_mul, nodeCount_refl,
        nodeCount_stepWitness J step]
      omega

variable (extra) in
/-- Receipts: proof witnesses of the equation that the kernel model accepts.
Reflexivity, symmetry and transitivity are the root's `rung_eqid`,
`rung_eqcom` and `rung_eqtr` under modus ponens. -/
def receipts : bubbles.GlobalEquality.{0, 0, 0, 0, 0} where
  Eq {n} t u := {witness : ProofWitness // Checks extra n witness (eqn (encode t) (encode u))}
  refl t := ⟨reflW (encode t), checks_refl (encode_typed t)⟩
  symm {_} {t u} receipt :=
    ⟨symmW (encode t) (encode u) receipt.1,
      checks_symm (encode_typed t) (encode_typed u) receipt.2⟩
  trans {_} {t m u} first second :=
    ⟨transW (encode t) (encode m) (encode u) first.1 second.1,
      checks_trans (encode_typed t) (encode_typed m) (encode_typed u) first.2 second.2⟩

/-- The receipt of a step. -/
def stepReceipt (J : Justification extra rules) {n : Nat} {t u : PTerm n}
    (step : Step rules t u) : (receipts extra).Eq t u :=
  ⟨stepWitness J step, stepWitness_checks J step⟩

/-- **Receipt mode**: the explicit elaboration of a conversion tree into an
MM0 proof witness, the fold of the justifications. -/
def elaborate (J : Justification extra rules) {n : Nat} {t u : PTerm n}
    (path : Conv rules t u) : (receipts extra).Eq t u :=
  bubbles.sound (receipts extra) (stepReceipt J) path

/-- **Every elaborated receipt is accepted by the kernel model's checker**, for
the exact equation. -/
theorem elaborate_accepted (J : Justification extra rules) {n : Nat} {t u : PTerm n}
    (path : Conv rules t u) :
    ProofWitness.check terms definitions (table extra) (natContext n) []
      (elaborate J path).1 (eqn (encode t) (encode u)) = true :=
  (ProofWitness.check_iff _ _ _ _ _ _ _).mpr (elaborate J path).2

/-- A graded receipt: the receipt with the number of rewrite steps it records. -/
def gradedReceipt (J : Justification extra rules) {n : Nat} {t u : PTerm n}
    (path : Conv rules t u) : (receipts extra).Eq t u × ℕ :=
  gradedSound bubbles (receipts extra) (stepReceipt J) path

theorem gradedReceipt_eq (J : Justification extra rules) {n : Nat} {t u : PTerm n}
    (path : Conv rules t u) :
    gradedReceipt J path = (elaborate J path, stepCount path) :=
  gradedSound_eq bubbles (receipts extra) (stepReceipt J) path

variable (extra) in
/-- Receipt size is tree-additive: symmetry adds two nodes, transitivity three. -/
def receiptSize : TreeAdditiveSize bubbles (receipts extra) where
  size receipt := nodeCount receipt.1
  symm_ge receipt := by
    change nodeCount receipt.1 ≤ nodeCount (symmW _ _ receipt.1)
    rw [nodeCount_symm]
    omega
  trans_ge first second := by
    change nodeCount first.1 + nodeCount second.1 ≤ nodeCount (transW _ _ _ first.1 second.1)
    rw [nodeCount_trans]
    omega

/-- **A receipt is at least as large as the work it records.** -/
theorem stepCount_le_nodeCount (J : Justification extra rules) {n : Nat} {t u : PTerm n}
    (path : Conv rules t u) : stepCount path ≤ nodeCount (elaborate J path).1 :=
  stepCount_le_size bubbles (receiptSize extra) (stepReceipt J)
    (fun step => by
      change 1 ≤ nodeCount (stepWitness J step)
      rw [nodeCount_stepWitness]
      omega)
    path

/-- Sizes: reflexivity one node, symmetry two more, transitivity three more. -/
abbrev sizeEquality : bubbles.GlobalEquality.{0, 0, 0, 0, 0} where
  Eq _ _ := ℕ
  refl _ := 1
  symm size := size + 2
  trans first second := first + second + 3

variable (extra) in
/-- Forgetting a receipt to its size preserves the three operations. -/
def sizeMap : EqualityHom (Hom.identity bubbles) (receipts extra) sizeEquality where
  map receipt := nodeCount receipt.1
  map_refl _ := nodeCount_refl _
  map_symm receipt := nodeCount_symm _ _ receipt.1
  map_trans first second := nodeCount_trans _ _ _ first.1 second.1

/-- **The exact size of a receipt** is the fold of its step costs: each step
costs one node plus its congruence nodes; each reflexivity one, each
symmetry two and each transitivity three more. Proved by naturality of the
elaboration along the size map. -/
theorem nodeCount_elaborate (J : Justification extra rules) {n : Nat} {t u : PTerm n}
    (path : Conv rules t u) :
    nodeCount (elaborate J path).1 =
      bubbles.sound sizeEquality (fun step => step.congruenceCost + 1) path := by
  have natural := sound_natural (Hom.identity bubbles) (sizeMap extra) rules (stepReceipt J)
    (fun step => step.congruenceCost + 1)
    (fun step => (nodeCount_stepWitness J step).symm) path
  rw [Hom.mapConv_identity] at natural
  exact natural.symm

end Receipts

/-! ## Rung mode -/

section Rung

variable {extra : List Entry} {rules : List Rule}

variable (extra) in
/-- Derivability in the root, as a global equality. -/
def derivability : bubbles.GlobalEquality.{0, 0, 0, 0, 0} where
  Eq {n} t u :=
    PLift (Derives terms definitions (table extra) (natContext n) [] (eqn (encode t) (encode u)))
  refl t := ⟨(checks_refl (encode_typed t)).derives⟩
  symm {_} {t u} derived :=
    ⟨by
      obtain ⟨witness, checked⟩ := derived.down.certificate_exists
      exact (checks_symm (encode_typed t) (encode_typed u) checked).derives⟩
  trans {_} {t m u} first second :=
    ⟨by
      obtain ⟨witness, checked⟩ := first.down.certificate_exists
      obtain ⟨witness', checked'⟩ := second.down.certificate_exists
      exact (checks_trans (encode_typed t) (encode_typed m) (encode_typed u) checked
        checked').derives⟩

/-- **The rung theorem.** If every rule of a rule set is justified by a table
position holding its equation, every conversion of the rule set, by rewriting
under congruence in any number of steps, is derivable in the root. -/
theorem rung_sound (J : Justification extra rules) {n : Nat} {t u : PTerm n}
    (path : Conv rules t u) :
    Derives terms definitions (table extra) (natContext n) [] (eqn (encode t) (encode u)) :=
  (bubbles.sound (derivability extra) (fun step => ⟨(stepWitness_checks J step).derives⟩)
    path).down

/-- The rung asks only for the existence of a conversion. -/
theorem rung_sound_of_nonempty (J : Justification extra rules) {n : Nat} {t u : PTerm n}
    (convertible : Nonempty (Conv rules t u)) :
    Derives terms definitions (table extra) (natContext n) [] (eqn (encode t) (encode u)) :=
  convertible.elim (rung_sound J)

/-- **Rung mode and receipt mode accept the same judgments.** A pair is
convertible exactly when some tree has a receipt the root accepts. -/
theorem rung_iff_receipt (J : Justification extra rules) {n : Nat} (t u : PTerm n) :
    Nonempty (Conv rules t u) ↔
      ∃ path : Conv rules t u,
        ProofWitness.check terms definitions (table extra) (natContext n) []
          (elaborate J path).1 (eqn (encode t) (encode u)) = true :=
  ⟨fun ⟨path⟩ => ⟨path, elaborate_accepted J path⟩, fun ⟨path, _⟩ => ⟨path⟩⟩

end Rung

/-! ## Widening -/

section Widen

variable {extra : List Entry}

/-- Steps of a smaller rule set are steps of a larger one. -/
def Step.widen {small large : List Rule} (included : ∀ rule ∈ small, rule ∈ large) {n : Nat} :
    {t u : PTerm n} → Step small t u → Step large t u
  | _, _, .root member σ => .root (included _ member) σ
  | _, _, .succ step => .succ (step.widen included)
  | _, _, .addLeft w step => .addLeft w (step.widen included)
  | _, _, .addRight w step => .addRight w (step.widen included)
  | _, _, .mulLeft w step => .mulLeft w (step.widen included)
  | _, _, .mulRight w step => .mulRight w (step.widen included)

theorem stepWitness_widen {small large : List Rule} (included : ∀ rule ∈ small, rule ∈ large)
    (J : Justification extra small) (J' : Justification extra large)
    (coherent : ∀ rule ∈ small, J'.index rule = J.index rule) {n : Nat} :
    ∀ {t u : PTerm n} (step : Step small t u),
      stepWitness J' (step.widen included) = stepWitness J step
  | _, _, .root member σ => by
      simp only [Step.widen, stepWitness, coherent _ member]
  | _, _, .succ step => by
      simp only [Step.widen, stepWitness, stepWitness_widen included J J' coherent step]
  | _, _, .addLeft w step => by
      simp only [Step.widen, stepWitness, stepWitness_widen included J J' coherent step]
  | _, _, .addRight w step => by
      simp only [Step.widen, stepWitness, stepWitness_widen included J J' coherent step]
  | _, _, .mulLeft w step => by
      simp only [Step.widen, stepWitness, stepWitness_widen included J J' coherent step]
  | _, _, .mulRight w step => by
      simp only [Step.widen, stepWitness, stepWitness_widen included J J' coherent step]

/-- **Widening changes no receipt.** If the larger rule set justifies the
rules of the smaller one by the same table positions, a tree of the smaller
set and its widening have the same receipt. -/
theorem elaborate_widen {small large : List Rule} (included : ∀ rule ∈ small, rule ∈ large)
    (J : Justification extra small) (J' : Justification extra large)
    (coherent : ∀ rule ∈ small, J'.index rule = J.index rule) {n : Nat} {t u : PTerm n}
    (path : Conv small t u) :
    (elaborate J' (bubbles.widen (fun step => step.widen included) path)).1 =
      (elaborate J path).1 :=
  congrArg Subtype.val (sound_widen bubbles (receipts extra) (fun step => step.widen included)
    (stepReceipt J) (stepReceipt J')
    (fun step => Subtype.ext (stepWitness_widen included J J' coherent step)) path)

end Widen

/-! ## An executable rewriting checker -/

section Trace

/-- A direction into a term. -/
inductive Direction where
  | succ
  | addLeft
  | addRight
  | mulLeft
  | mulRight
  deriving DecidableEq, Repr

/-- One step of a rewriting trace: the rule, its substitution, the position of
the redex, and whether the rule is used from left to right. -/
structure TraceStep (n : Nat) where
  rule : Rule
  substitution : List (PTerm n)
  position : List Direction
  forward : Bool
  deriving Repr

/-- The substitution of a trace step, padded with `0`. -/
def TraceStep.σ {n : Nat} (s : TraceStep n) : Fin s.rule.arity → PTerm n :=
  fun i => s.substitution.getD i.val .zero

variable {rules : List Rule} {n : Nat}

/-- Conversion trees under `suc`. -/
def mapSucc : {t u : PTerm n} → Conv rules t u → Conv rules (.succ t) (.succ u)
  | _, _, .step step => .step (.succ step)
  | _, _, .refl t => ConversionEvidence.refl (computation := computation bubbles.State
      (bubbles.Step rules)) (PTerm.succ t)
  | _, _, .symm path => .symm (mapSucc path)
  | _, _, .trans first second => .trans (mapSucc first) (mapSucc second)

/-- Conversion trees on the left of a sum. -/
def mapAddLeft (w : PTerm n) : {t u : PTerm n} → Conv rules t u → Conv rules (.add t w) (.add u w)
  | _, _, .step step => .step (.addLeft w step)
  | _, _, .refl t => ConversionEvidence.refl (computation := computation bubbles.State
      (bubbles.Step rules)) (PTerm.add t w)
  | _, _, .symm path => .symm (mapAddLeft w path)
  | _, _, .trans first second => .trans (mapAddLeft w first) (mapAddLeft w second)

/-- Conversion trees on the right of a sum. -/
def mapAddRight (w : PTerm n) : {t u : PTerm n} → Conv rules t u → Conv rules (.add w t) (.add w u)
  | _, _, .step step => .step (.addRight w step)
  | _, _, .refl t => ConversionEvidence.refl (computation := computation bubbles.State
      (bubbles.Step rules)) (PTerm.add w t)
  | _, _, .symm path => .symm (mapAddRight w path)
  | _, _, .trans first second => .trans (mapAddRight w first) (mapAddRight w second)

/-- Conversion trees on the left of a product. -/
def mapMulLeft (w : PTerm n) : {t u : PTerm n} → Conv rules t u → Conv rules (.mul t w) (.mul u w)
  | _, _, .step step => .step (.mulLeft w step)
  | _, _, .refl t => ConversionEvidence.refl (computation := computation bubbles.State
      (bubbles.Step rules)) (PTerm.mul t w)
  | _, _, .symm path => .symm (mapMulLeft w path)
  | _, _, .trans first second => .trans (mapMulLeft w first) (mapMulLeft w second)

/-- Conversion trees on the right of a product. -/
def mapMulRight (w : PTerm n) : {t u : PTerm n} → Conv rules t u → Conv rules (.mul w t) (.mul w u)
  | _, _, .step step => .step (.mulRight w step)
  | _, _, .refl t => ConversionEvidence.refl (computation := computation bubbles.State
      (bubbles.Step rules)) (PTerm.mul w t)
  | _, _, .symm path => .symm (mapMulRight w path)
  | _, _, .trans first second => .trans (mapMulRight w first) (mapMulRight w second)

theorem stepCount_mapSucc : ∀ {t u : PTerm n} (path : Conv rules t u),
    stepCount (mapSucc path) = stepCount path
  | _, _, .step _ => by simp only [mapSucc, stepCount_step]
  | _, _, .refl _ => by simp only [mapSucc, stepCount_refl]
  | _, _, .symm path => by
      simp only [mapSucc, stepCount_symm, stepCount_mapSucc path]
  | _, _, .trans first second => by
      simp only [mapSucc, stepCount_trans, stepCount_mapSucc first, stepCount_mapSucc second]

theorem stepCount_mapAddLeft (w : PTerm n) : ∀ {t u : PTerm n} (path : Conv rules t u),
    stepCount (mapAddLeft w path) = stepCount path
  | _, _, .step _ => by simp only [mapAddLeft, stepCount_step]
  | _, _, .refl _ => by simp only [mapAddLeft, stepCount_refl]
  | _, _, .symm path => by
      simp only [mapAddLeft, stepCount_symm, stepCount_mapAddLeft w path]
  | _, _, .trans first second => by
      simp only [mapAddLeft, stepCount_trans, stepCount_mapAddLeft w first,
        stepCount_mapAddLeft w second]

theorem stepCount_mapAddRight (w : PTerm n) : ∀ {t u : PTerm n} (path : Conv rules t u),
    stepCount (mapAddRight w path) = stepCount path
  | _, _, .step _ => by simp only [mapAddRight, stepCount_step]
  | _, _, .refl _ => by simp only [mapAddRight, stepCount_refl]
  | _, _, .symm path => by
      simp only [mapAddRight, stepCount_symm, stepCount_mapAddRight w path]
  | _, _, .trans first second => by
      simp only [mapAddRight, stepCount_trans, stepCount_mapAddRight w first,
        stepCount_mapAddRight w second]

theorem stepCount_mapMulLeft (w : PTerm n) : ∀ {t u : PTerm n} (path : Conv rules t u),
    stepCount (mapMulLeft w path) = stepCount path
  | _, _, .step _ => by simp only [mapMulLeft, stepCount_step]
  | _, _, .refl _ => by simp only [mapMulLeft, stepCount_refl]
  | _, _, .symm path => by
      simp only [mapMulLeft, stepCount_symm, stepCount_mapMulLeft w path]
  | _, _, .trans first second => by
      simp only [mapMulLeft, stepCount_trans, stepCount_mapMulLeft w first,
        stepCount_mapMulLeft w second]

theorem stepCount_mapMulRight (w : PTerm n) : ∀ {t u : PTerm n} (path : Conv rules t u),
    stepCount (mapMulRight w path) = stepCount path
  | _, _, .step _ => by simp only [mapMulRight, stepCount_step]
  | _, _, .refl _ => by simp only [mapMulRight, stepCount_refl]
  | _, _, .symm path => by
      simp only [mapMulRight, stepCount_symm, stepCount_mapMulRight w path]
  | _, _, .trans first second => by
      simp only [mapMulRight, stepCount_trans, stepCount_mapMulRight w first,
        stepCount_mapMulRight w second]

/-- Replace the subterm `old` at a position by `new`, carrying a conversion of
the two along the context. -/
def replaceAt {old new : PTerm n} (conversion : Conv rules old new) :
    List Direction → (t : PTerm n) → Option (Σ u : PTerm n, Conv rules t u)
  | [], t => if h : t = old then some ⟨new, h ▸ conversion⟩ else none
  | .succ :: position, .succ t =>
      (replaceAt conversion position t).map fun result => ⟨.succ result.1, mapSucc result.2⟩
  | .addLeft :: position, .add t w =>
      (replaceAt conversion position t).map fun result =>
        ⟨.add result.1 w, mapAddLeft w result.2⟩
  | .addRight :: position, .add w t =>
      (replaceAt conversion position t).map fun result =>
        ⟨.add w result.1, mapAddRight w result.2⟩
  | .mulLeft :: position, .mul t w =>
      (replaceAt conversion position t).map fun result =>
        ⟨.mul result.1 w, mapMulLeft w result.2⟩
  | .mulRight :: position, .mul w t =>
      (replaceAt conversion position t).map fun result =>
        ⟨.mul w result.1, mapMulRight w result.2⟩
  | _, _ => none

/-- Apply one trace step: the rule must belong to the set, and the subterm at
the position must be the rule's instance. -/
def applyTraceStep (rules : List Rule) (s : TraceStep n) (t : PTerm n) :
    Option (Σ u : PTerm n, Conv rules t u) :=
  if member : s.rule ∈ rules then
    if s.forward then replaceAt (.step (.root member s.σ)) s.position t
    else replaceAt (.symm (.step (.root member s.σ))) s.position t
  else none

/-- Run a trace from a term: the result and the conversion tree recorded. -/
def runTrace (rules : List Rule) : List (TraceStep n) → (t : PTerm n) →
    Option (Σ u : PTerm n, Conv rules t u)
  | [], t => some ⟨t, ConversionEvidence.refl (computation := computation bubbles.State
      (bubbles.Step rules)) t⟩
  | [s], t => applyTraceStep rules s t
  | s :: rest, t =>
      match applyTraceStep rules s t with
      | none => none
      | some ⟨m, first⟩ =>
          match runTrace rules rest m with
          | none => none
          | some ⟨u, second⟩ => some ⟨u, .trans first second⟩

/-- The conversion tree a trace records from `t`, when it ends at `u`. -/
def traceConv? (rules : List Rule) (t u : PTerm n) (trace : List (TraceStep n)) :
    Option (Conv rules t u) :=
  match runTrace rules trace t with
  | some result => if same : result.1 = u then some (same ▸ result.2) else none
  | none => none

/-- **The executable rewriting checker.** It accepts `t ≡ u` when the trace
leads from `t` to `u`. No root certificate is built. -/
def checkTrace (rules : List Rule) (t u : PTerm n) (trace : List (TraceStep n)) : Bool :=
  (traceConv? rules t u trace).isSome

/-- The conversion tree of an accepted trace. -/
def traceConv (rules : List Rule) {t u : PTerm n} (trace : List (TraceStep n))
    (accepted : checkTrace rules t u trace = true) : Conv rules t u :=
  (traceConv? rules t u trace).get accepted

theorem stepCount_replaceAt {old new : PTerm n} (conversion : Conv rules old new) :
    ∀ (position : List Direction) (t : PTerm n) (result : Σ u : PTerm n, Conv rules t u),
      replaceAt conversion position t = some result →
        stepCount result.2 = stepCount conversion
  | [], t, result, found => by
      unfold replaceAt at found
      split at found
      · rename_i same
        subst same
        cases found
        rfl
      · cases found
  | .succ :: position, .succ t, result, found => by
      simp only [replaceAt, Option.map_eq_some_iff] at found
      obtain ⟨inner, innerFound, rfl⟩ := found
      simp only [stepCount_mapSucc, stepCount_replaceAt conversion position t inner innerFound]
  | .addLeft :: position, .add t w, result, found => by
      simp only [replaceAt, Option.map_eq_some_iff] at found
      obtain ⟨inner, innerFound, rfl⟩ := found
      simp only [stepCount_mapAddLeft, stepCount_replaceAt conversion position t inner innerFound]
  | .addRight :: position, .add w t, result, found => by
      simp only [replaceAt, Option.map_eq_some_iff] at found
      obtain ⟨inner, innerFound, rfl⟩ := found
      simp only [stepCount_mapAddRight, stepCount_replaceAt conversion position t inner innerFound]
  | .mulLeft :: position, .mul t w, result, found => by
      simp only [replaceAt, Option.map_eq_some_iff] at found
      obtain ⟨inner, innerFound, rfl⟩ := found
      simp only [stepCount_mapMulLeft, stepCount_replaceAt conversion position t inner innerFound]
  | .mulRight :: position, .mul w t, result, found => by
      simp only [replaceAt, Option.map_eq_some_iff] at found
      obtain ⟨inner, innerFound, rfl⟩ := found
      simp only [stepCount_mapMulRight, stepCount_replaceAt conversion position t inner innerFound]
  | .succ :: _, .var _, _, found => by cases found
  | .succ :: _, .zero, _, found => by cases found
  | .succ :: _, .add _ _, _, found => by cases found
  | .succ :: _, .mul _ _, _, found => by cases found
  | .addLeft :: _, .var _, _, found => by cases found
  | .addLeft :: _, .zero, _, found => by cases found
  | .addLeft :: _, .succ _, _, found => by cases found
  | .addLeft :: _, .mul _ _, _, found => by cases found
  | .addRight :: _, .var _, _, found => by cases found
  | .addRight :: _, .zero, _, found => by cases found
  | .addRight :: _, .succ _, _, found => by cases found
  | .addRight :: _, .mul _ _, _, found => by cases found
  | .mulLeft :: _, .var _, _, found => by cases found
  | .mulLeft :: _, .zero, _, found => by cases found
  | .mulLeft :: _, .succ _, _, found => by cases found
  | .mulLeft :: _, .add _ _, _, found => by cases found
  | .mulRight :: _, .var _, _, found => by cases found
  | .mulRight :: _, .zero, _, found => by cases found
  | .mulRight :: _, .succ _, _, found => by cases found
  | .mulRight :: _, .add _ _, _, found => by cases found

theorem stepCount_applyTraceStep (rules : List Rule) (s : TraceStep n) (t : PTerm n)
    (result : Σ u : PTerm n, Conv rules t u) (found : applyTraceStep rules s t = some result) :
    stepCount result.2 = 1 := by
  unfold applyTraceStep at found
  split at found
  · split at found
    · exact (stepCount_replaceAt _ _ _ _ found).trans (stepCount_step _)
    · exact (stepCount_replaceAt _ _ _ _ found).trans
        ((stepCount_symm _).trans (stepCount_step _))
  · cases found

theorem stepCount_runTrace (rules : List Rule) :
    ∀ (trace : List (TraceStep n)) (t : PTerm n) (result : Σ u : PTerm n, Conv rules t u),
      runTrace rules trace t = some result → stepCount result.2 = trace.length
  | [], t, result, found => by
      simp only [runTrace, Option.some.injEq] at found
      subst found
      simp only [stepCount_refl, List.length_nil]
  | [s], t, result, found => by
      simp only [runTrace] at found
      exact stepCount_applyTraceStep rules s t result found
  | s :: s' :: rest, t, result, found => by
      simp only [runTrace] at found
      split at found
      · cases found
      · rename_i m first firstFound
        split at found
        · cases found
        · rename_i u second secondFound
          cases found
          simp only [stepCount_trans, stepCount_applyTraceStep rules s t ⟨m, first⟩ firstFound,
            stepCount_runTrace rules (s' :: rest) m ⟨u, second⟩ secondFound, List.length_cons]
          omega

theorem stepCount_traceConv? (rules : List Rule) {t u : PTerm n} (trace : List (TraceStep n))
    (path : Conv rules t u) (found : traceConv? rules t u trace = some path) :
    stepCount path = trace.length := by
  unfold traceConv? at found
  split at found
  · rename_i result run
    split at found
    · rename_i same
      rw [← Option.some.inj found]
      obtain ⟨u', recorded⟩ := result
      simp only at same
      subst same
      exact stepCount_runTrace rules trace t ⟨u', recorded⟩ run
    · cases found
  · cases found

/-- **The grade of an accepted trace is its length**: one recorded step per
trace step. -/
theorem stepCount_traceConv (rules : List Rule) {t u : PTerm n} (trace : List (TraceStep n))
    (accepted : checkTrace rules t u trace = true) :
    stepCount (traceConv rules trace accepted) = trace.length :=
  stepCount_traceConv? rules trace _ (Option.some_get accepted).symm

variable {extra : List Entry}

/-- **The rewriting checker is sound**: an accepted trace of a justified rule
set yields a root derivation of the equation. -/
theorem checkTrace_sound (J : Justification extra rules) {t u : PTerm n}
    (trace : List (TraceStep n)) (accepted : checkTrace rules t u trace = true) :
    Derives terms definitions (table extra) (natContext n) [] (eqn (encode t) (encode u)) :=
  rung_sound J (traceConv rules trace accepted)

/-- The receipt of an accepted trace. -/
def traceReceipt (J : Justification extra rules) {t u : PTerm n} (trace : List (TraceStep n))
    (accepted : checkTrace rules t u trace = true) : ProofWitness :=
  (elaborate J (traceConv rules trace accepted)).1

/-- **The checker and receipt mode accept the same traces**: a trace is
accepted exactly when it yields a receipt the root's checker accepts for the
equation. -/
theorem checkTrace_iff_receipt (J : Justification extra rules) {t u : PTerm n}
    (trace : List (TraceStep n)) :
    checkTrace rules t u trace = true ↔
      ∃ accepted : checkTrace rules t u trace = true,
        ProofWitness.check terms definitions (table extra) (natContext n) []
          (traceReceipt J trace accepted) (eqn (encode t) (encode u)) = true :=
  ⟨fun accepted => ⟨accepted, elaborate_accepted J _⟩, fun ⟨accepted, _⟩ => accepted⟩

/-- A receipt of an accepted trace records exactly as many steps as the trace
has, and has at least that many nodes. -/
theorem traceReceipt_grade (J : Justification extra rules) {t u : PTerm n}
    (trace : List (TraceStep n)) (accepted : checkTrace rules t u trace = true) :
    (gradedReceipt J (traceConv rules trace accepted)).2 = trace.length ∧
      trace.length ≤ nodeCount (traceReceipt J trace accepted) := by
  refine ⟨?_, ?_⟩
  · rw [gradedReceipt_eq, stepCount_traceConv]
  · rw [← stepCount_traceConv rules trace accepted]
    exact stepCount_le_nodeCount J _

end Trace

/-! ## Controls -/

namespace Controls

/-- The lying rule `a + 0 ↦ 0`. -/
def lyingRule : Rule := ⟨1, .add (.var 0) .zero, .zero⟩

/-- Its conversion relates `1 + 0` and `0`. -/
def lyingConv : Conv [lyingRule] (n := 0) (.add (.succ .zero) .zero) .zero :=
  .step (Step.root (rule := lyingRule) (List.mem_singleton_self _) fun _ => .succ .zero)

/-- **The lying rule has no justification in the root**: a justification
would make the root derive `1 + 0 = 0`, which fails in the standard model. -/
theorem lying_rule_unjustified : IsEmpty (Justification [] [lyingRule]) :=
  ⟨fun J => not_derives_one_add_zero_eq_zero (rung_sound J lyingConv)⟩

/-- The collapsing rule `a ↦ 0`. -/
def collapseRule : Rule := ⟨1, .var 0, .zero⟩

/-- **The collapsing rule converts any two terms**: its conversion is the top
relation. -/
def collapse_converts_all {n : Nat} (t u : PTerm n) : Conv [collapseRule] t u :=
  .trans (.step (Step.root (rule := collapseRule) (List.mem_singleton_self _) fun _ => t))
    (.symm (.step (Step.root (rule := collapseRule) (List.mem_singleton_self _) fun _ => u)))

/-- The collapsing rule has no justification in the root either: it would
derive `suc 0 = 0`. -/
theorem collapse_rule_unjustified : IsEmpty (Justification [] [collapseRule]) :=
  ⟨fun J => not_derives_suc_zero_eq_zero
    (rung_sound J (collapse_converts_all (n := 0) (.succ .zero) .zero))⟩

/-- The root extended by the collapsing equation as an axiom. -/
def collapseEntry : Entry := ⟨"collapse", true, collapseRule.declaration⟩

/-- In the extended root the collapsing rule is justified, by the new axiom. -/
def collapseJustification : Justification [collapseEntry] [collapseRule] where
  index _ := baseEntries.length
  lookup rule member := by
    rw [List.mem_singleton.mp member]
    rfl

/-- **False is the top.** With the collapsing rule justified by an axiom, the
root derives every formula: from `suc 0 = 0` and `~ suc 0 = 0` by the axioms
`ax_1` and `ax_3`. -/
theorem collapse_derives_every_formula {n : Nat} {formula : Preterm}
    (typed : WffTyped n formula) :
    Derives terms definitions (table [collapseEntry]) (natContext n) [] formula := by
  have collapsed : Derives terms definitions (table [collapseEntry]) (natContext n) []
      (eqn (sucE zeroE) zeroE) :=
    rung_sound collapseJustification (collapse_converts_all (.succ .zero) .zero)
  obtain ⟨equalWitness, equalChecked⟩ := collapsed.certificate_exists
  let p := eqn (sucE zeroE) zeroE
  have pTyped : WffTyped n p := eqn_typed (sucE_typed zeroE_typed) zeroE_typed
  have negated : Checks [collapseEntry] n (.theoremApp sucNeZeroIndex [zeroE] []) (neg p) :=
    .theoremApp (lookup_sucNeZero _)
      (instantiates (hypotheses := []) (allRegular_natContext 1) (.cons (.regular zeroE_typed) .nil)
        rfl rfl) .nil
  have weakened : Checks [collapseEntry] n
      (mpW (neg p) (imp (neg formula) (neg p))
        (.theoremApp ax1Index [neg p, neg formula] []) (.theoremApp sucNeZeroIndex [zeroE] []))
      (imp (neg formula) (neg p)) :=
    checks_mp (neg_typed pTyped) (imp_typed (neg_typed typed) (neg_typed pTyped))
      (.theoremApp (lookup_ax1 _)
        (instantiates (hypotheses := []) allRegular_wff2
          (.cons (.regular (neg_typed pTyped)) (.cons (.regular (neg_typed typed)) .nil)) rfl rfl)
        .nil)
      negated
  have contraposed := checks_mp (imp_typed (neg_typed typed) (neg_typed pTyped))
    (imp_typed pTyped typed)
    (.theoremApp (lookup_ax3 _)
      (instantiates (hypotheses := []) allRegular_wff2
        (.cons (.regular typed) (.cons (.regular pTyped) .nil)) rfl rfl) .nil)
    weakened
  exact (checks_mp pTyped typed contraposed equalChecked).derives

end Controls

/-! ## Axiom audit -/

#print axioms stepWitness_checks
#print axioms elaborate_accepted
#print axioms gradedReceipt_eq
#print axioms stepCount_le_nodeCount
#print axioms nodeCount_elaborate
#print axioms rung_sound
#print axioms rung_iff_receipt
#print axioms elaborate_widen
#print axioms stepCount_traceConv
#print axioms checkTrace_sound
#print axioms checkTrace_iff_receipt
#print axioms traceReceipt_grade
#print axioms Controls.lying_rule_unjustified
#print axioms Controls.collapse_rule_unjustified
#print axioms Controls.collapse_derives_every_formula

end Mettapedia.Languages.MM0.RewriteRung
