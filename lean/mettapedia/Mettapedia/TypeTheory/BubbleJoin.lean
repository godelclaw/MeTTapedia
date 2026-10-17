import Mettapedia.TypeTheory.BubbleConversion

/-!
# Joins of bubbles

A program that uses two bubbles needs the definitional equalities of both at
once.  The **join** of two bubbles declares the steps of both.  Which of a
bubble's good properties survive the join?

* **What composes.**
  - Each bubble's conversion is a conversion of the join
    (`convertible_join_left`, `convertible_join_right`).
  - The join is the least upper bound of the two in the conversion order: a
    bubble that has both conversions has every conversion of the join
    (`convertible_join_least`).  In particular a join of two bubbles that are
    sound for one global equality is sound for it.
  - Stability under substitution composes (`join_stable`).
* **What does not compose: decisions.**  The conversion of a join is not the
  union of the two conversions.  A conversion can be *emergent*: in the join
  but in neither bubble.  The arithmetic control below joins the recursion
  equations of addition with the step `t + 0 ↦ 0 + t`, which moves a zero
  summand to the left.  Neither bubble converts `x` with `0 + x`
  (`rule_not_conv`, `zeroSwap_not_conv`); their join does (`join_conv`).  So no
  decision procedure assembled from the two bubbles' own normal forms decides
  the join.
* **When decisions compose.**  If each bubble is normalized by its own
  function and the first function sends conversions of the second bubble to
  conversions of the second bubble, the join is decided by the composite
  (`join_normalizedBy`).  The respect condition is the obligation a join has to
  discharge; in the control it fails (`norm_false_not_respects_zeroSwap`).
  It holds for a logical bubble beside arithmetic: every bubble that is rigid
  and compatible for arithmetic satisfies it
  (`BubbleJoinDisjoint.join_rule_normalizedBy_of_rigid`), and `¬⊤ ↦ ⊥` is such
  a bubble, so the join of the two is normalized by the composite normal form
  (`Arith.arith_notTop_normalizedBy`, `Arith.arith_notTop_conv_iff`, stated in
  `Mettapedia.TypeTheory.BubbleJoinDisjoint`).
* **Completion recovers a decision here.**  The emergent equation is the
  left-unit equation `0 + t = t`, the critical pair of the two step sets.  The
  join has exactly the conversion of the bubble that adds it
  (`join_conv_iff_plus`), so it is decided by that bubble's normal form
  (`join_conv_iff_norm`): a third normal form, found by completion, not built
  from the two given ones.

A join of decided bubbles is therefore decided only when completion of the
combined steps succeeds; deciding a join is a property of the join, proved
for it, never inherited from its parts.

Being normalized by a function is a property of that function, not by itself
a decision procedure: every bubble is normalized by some function that picks
representatives of its conversion classes
(`BubbleJoinCongruence.CongruenceClosure.exists_normalizedBy`).  Conversion is
decided when the normalizing function is computable and equality of its
values is decidable, as for the normal forms of this module.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleConversion

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Join

variable {Base : Type u} {Const : Ty Base → Type v}

/-- **The join of two bubbles** declares the steps of both. -/
def join (first second : Expr Base Const → Expr Base Const → Prop) :
    Expr Base Const → Expr Base Const → Prop :=
  fun left right => first left right ∨ second left right

/-- Conversion is a congruence for every expression former whose steps lift. -/
theorem convertible_context {rules : Expr Base Const → Expr Base Const → Prop}
    (context : Expr Base Const → Expr Base Const)
    (lift : ∀ {a a' : Expr Base Const}, Rewrite rules a a' → Rewrite rules (context a) (context a'))
    {a a' : Expr Base Const} (converted : Convertible rules a a') :
    Convertible rules (context a) (context a') := by
  induction converted with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ (lift step)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

/-- A rewrite step of one bubble is a conversion of another once every root
rule of the first is a conversion of the second. -/
theorem rewrite_into {small large : Expr Base Const → Expr Base Const → Prop}
    (into : ∀ left right, small left right → Convertible large left right)
    {e e' : Expr Base Const} (step : Rewrite small e e') : Convertible large e e' := by
  induction step with
  | root rule => exact into _ _ rule
  | @piDomain A A' B _ ih => exact convertible_context (fun X => pi X B) (fun s => .piDomain s) ih
  | @piBody A B B' _ ih => exact convertible_context (fun X => pi A X) (fun s => .piBody s) ih
  | @lamDomain A A' b _ ih => exact convertible_context (fun X => lam X b) (fun s => .lamDomain s) ih
  | @lamBody A b b' _ ih => exact convertible_context (fun X => lam A X) (fun s => .lamBody s) ih
  | @appFunction f f' a _ ih =>
      exact convertible_context (fun X => app X a) (fun s => .appFunction s) ih
  | @appArgument f a a' _ ih =>
      exact convertible_context (fun X => app f X) (fun s => .appArgument s) ih
  | @andLeft p p' q _ ih => exact convertible_context (fun X => Expr.and X q) (fun s => .andLeft s) ih
  | @andRight p q q' _ ih =>
      exact convertible_context (fun X => Expr.and p X) (fun s => .andRight s) ih
  | @orLeft p p' q _ ih => exact convertible_context (fun X => Expr.or X q) (fun s => .orLeft s) ih
  | @orRight p q q' _ ih => exact convertible_context (fun X => Expr.or p X) (fun s => .orRight s) ih
  | @impLeft p p' q _ ih => exact convertible_context (fun X => imp X q) (fun s => .impLeft s) ih
  | @impRight p q q' _ ih => exact convertible_context (fun X => imp p X) (fun s => .impRight s) ih
  | @notBody p p' _ ih => exact convertible_context (fun X => Expr.not X) (fun s => .notBody s) ih
  | @eqLeft a a' b _ ih => exact convertible_context (fun X => Expr.eq X b) (fun s => .eqLeft s) ih
  | @eqRight a b b' _ ih => exact convertible_context (fun X => Expr.eq a X) (fun s => .eqRight s) ih
  | @allDomain A A' b _ ih => exact convertible_context (fun X => all X b) (fun s => .allDomain s) ih
  | @allBody A b b' _ ih => exact convertible_context (fun X => all A X) (fun s => .allBody s) ih
  | @exDomain A A' b _ ih => exact convertible_context (fun X => ex X b) (fun s => .exDomain s) ih
  | @exBody A b b' _ ih => exact convertible_context (fun X => ex A X) (fun s => .exBody s) ih

/-- Conversions of one bubble are conversions of another once every root rule
of the first is a conversion of the second. -/
theorem convertible_into {small large : Expr Base Const → Expr Base Const → Prop}
    (into : ∀ left right, small left right → Convertible large left right)
    {e e' : Expr Base Const} (converted : Convertible small e e') : Convertible large e e' := by
  induction converted with
  | rel _ _ step => exact rewrite_into into step
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

variable {first second : Expr Base Const → Expr Base Const → Prop}

theorem convertible_join_left {e e' : Expr Base Const} (converted : Convertible first e e') :
    Convertible (join first second) e e' :=
  convertible_mono (fun _ _ rule => Or.inl rule) converted

theorem convertible_join_right {e e' : Expr Base Const} (converted : Convertible second e e') :
    Convertible (join first second) e e' :=
  convertible_mono (fun _ _ rule => Or.inr rule) converted

/-- **The join is the least upper bound in the conversion order**: a bubble
that has both conversions has every conversion of the join.  Read with a
global bubble, this is soundness of the join from soundness of its parts. -/
theorem convertible_join_least {large : Expr Base Const → Expr Base Const → Prop}
    (fromFirst : ∀ {e e' : Expr Base Const}, Convertible first e e' → Convertible large e e')
    (fromSecond : ∀ {e e' : Expr Base Const}, Convertible second e e' → Convertible large e e')
    {e e' : Expr Base Const} (converted : Convertible (join first second) e e') :
    Convertible large e e' :=
  convertible_into
    (fun _ _ rule => rule.elim
      (fun inFirst => fromFirst (Relation.EqvGen.rel _ _ (.root inFirst)))
      (fun inSecond => fromSecond (Relation.EqvGen.rel _ _ (.root inSecond))))
    converted

/-- **Stability under substitution composes.** -/
theorem join_stable (stableFirst : SubstitutionStable first)
    (stableSecond : SubstitutionStable second) : SubstitutionStable (join first second) :=
  fun left right rule depth replacement => rule.elim
    (fun inFirst => Or.inl (stableFirst left right inFirst depth replacement))
    (fun inSecond => Or.inr (stableSecond left right inSecond depth replacement))

/-- Typing in the join extends typing in each bubble. -/
theorem hasTypeIn_join_left {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    (typed : HasTypeIn first Γ e A) : HasTypeIn (join first second) Γ e A :=
  hasTypeIn_mono (fun _ _ rule => Or.inl rule) typed

theorem hasTypeIn_join_right {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    (typed : HasTypeIn second Γ e A) : HasTypeIn (join first second) Γ e A :=
  hasTypeIn_mono (fun _ _ rule => Or.inr rule) typed

/-! ### When decisions compose -/

/-- A bubble is **normalized by** a function when every expression converts to
its image and conversion keeps the image. -/
def NormalizedBy (rules : Expr Base Const → Expr Base Const → Prop)
    (normal : Expr Base Const → Expr Base Const) : Prop :=
  (∀ e, Convertible rules e (normal e)) ∧
    ∀ e e', Convertible rules e e' → normal e = normal e'

/-- In a bubble normalized by a function, conversion is equality of images.
This decides conversion when the function is computable. -/
theorem NormalizedBy.conv_iff {rules : Expr Base Const → Expr Base Const → Prop}
    {normal : Expr Base Const → Expr Base Const} (normalized : NormalizedBy rules normal)
    {e e' : Expr Base Const} : Convertible rules e e' ↔ normal e = normal e' :=
  ⟨normalized.2 e e', fun equal => Relation.EqvGen.trans _ _ _ (normalized.1 e)
    (Relation.EqvGen.symm _ _ (equal ▸ normalized.1 e'))⟩

/-- A rewrite step of the join is a conversion of one of the two bubbles. -/
theorem rewrite_join_cases {e e' : Expr Base Const} (step : Rewrite (join first second) e e') :
    Convertible first e e' ∨ Convertible second e e' := by
  induction step with
  | root rule =>
      exact rule.imp (fun r => Relation.EqvGen.rel _ _ (Rewrite.root r))
        (fun r => Relation.EqvGen.rel _ _ (Rewrite.root r))
  | @piDomain A A' B _ ih =>
      exact ih.imp (convertible_context (fun X => pi X B) (fun s => .piDomain s))
        (convertible_context (fun X => pi X B) (fun s => .piDomain s))
  | @piBody A B B' _ ih =>
      exact ih.imp (convertible_context (fun X => pi A X) (fun s => .piBody s))
        (convertible_context (fun X => pi A X) (fun s => .piBody s))
  | @lamDomain A A' b _ ih =>
      exact ih.imp (convertible_context (fun X => lam X b) (fun s => .lamDomain s))
        (convertible_context (fun X => lam X b) (fun s => .lamDomain s))
  | @lamBody A b b' _ ih =>
      exact ih.imp (convertible_context (fun X => lam A X) (fun s => .lamBody s))
        (convertible_context (fun X => lam A X) (fun s => .lamBody s))
  | @appFunction f f' a _ ih =>
      exact ih.imp (convertible_context (fun X => app X a) (fun s => .appFunction s))
        (convertible_context (fun X => app X a) (fun s => .appFunction s))
  | @appArgument f a a' _ ih =>
      exact ih.imp (convertible_context (fun X => app f X) (fun s => .appArgument s))
        (convertible_context (fun X => app f X) (fun s => .appArgument s))
  | @andLeft p p' q _ ih =>
      exact ih.imp (convertible_context (fun X => Expr.and X q) (fun s => .andLeft s))
        (convertible_context (fun X => Expr.and X q) (fun s => .andLeft s))
  | @andRight p q q' _ ih =>
      exact ih.imp (convertible_context (fun X => Expr.and p X) (fun s => .andRight s))
        (convertible_context (fun X => Expr.and p X) (fun s => .andRight s))
  | @orLeft p p' q _ ih =>
      exact ih.imp (convertible_context (fun X => Expr.or X q) (fun s => .orLeft s))
        (convertible_context (fun X => Expr.or X q) (fun s => .orLeft s))
  | @orRight p q q' _ ih =>
      exact ih.imp (convertible_context (fun X => Expr.or p X) (fun s => .orRight s))
        (convertible_context (fun X => Expr.or p X) (fun s => .orRight s))
  | @impLeft p p' q _ ih =>
      exact ih.imp (convertible_context (fun X => imp X q) (fun s => .impLeft s))
        (convertible_context (fun X => imp X q) (fun s => .impLeft s))
  | @impRight p q q' _ ih =>
      exact ih.imp (convertible_context (fun X => imp p X) (fun s => .impRight s))
        (convertible_context (fun X => imp p X) (fun s => .impRight s))
  | @notBody p p' _ ih =>
      exact ih.imp (convertible_context (fun X => Expr.not X) (fun s => .notBody s))
        (convertible_context (fun X => Expr.not X) (fun s => .notBody s))
  | @eqLeft a a' b _ ih =>
      exact ih.imp (convertible_context (fun X => Expr.eq X b) (fun s => .eqLeft s))
        (convertible_context (fun X => Expr.eq X b) (fun s => .eqLeft s))
  | @eqRight a b b' _ ih =>
      exact ih.imp (convertible_context (fun X => Expr.eq a X) (fun s => .eqRight s))
        (convertible_context (fun X => Expr.eq a X) (fun s => .eqRight s))
  | @allDomain A A' b _ ih =>
      exact ih.imp (convertible_context (fun X => all X b) (fun s => .allDomain s))
        (convertible_context (fun X => all X b) (fun s => .allDomain s))
  | @allBody A b b' _ ih =>
      exact ih.imp (convertible_context (fun X => all A X) (fun s => .allBody s))
        (convertible_context (fun X => all A X) (fun s => .allBody s))
  | @exDomain A A' b _ ih =>
      exact ih.imp (convertible_context (fun X => ex X b) (fun s => .exDomain s))
        (convertible_context (fun X => ex X b) (fun s => .exDomain s))
  | @exBody A b b' _ ih =>
      exact ih.imp (convertible_context (fun X => ex A X) (fun s => .exBody s))
        (convertible_context (fun X => ex A X) (fun s => .exBody s))

/-- **Decisions compose when the first normal form respects the second
bubble.**  If each bubble is normalized by its own function, and the first
function sends conversions of the second bubble to conversions of the second
bubble, the join is normalized, hence decided, by the composite. -/
theorem join_normalizedBy {normalFirst normalSecond : Expr Base Const → Expr Base Const}
    (byFirst : NormalizedBy first normalFirst) (bySecond : NormalizedBy second normalSecond)
    (respects : ∀ e e', Convertible second e e' →
      Convertible second (normalFirst e) (normalFirst e')) :
    NormalizedBy (join first second) (fun e => normalSecond (normalFirst e)) := by
  refine ⟨fun e => Relation.EqvGen.trans _ _ _ (convertible_join_left (byFirst.1 e))
    (convertible_join_right (bySecond.1 (normalFirst e))), ?_⟩
  intro e e' converted
  induction converted with
  | rel _ _ step =>
      rcases rewrite_join_cases step with inFirst | inSecond
      · exact congrArg normalSecond (byFirst.2 _ _ inFirst)
      · exact bySecond.2 _ _ (respects _ _ inSecond)
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

end Join

/-! ## Control: an emergent conversion, and completion -/

namespace Arith

/-- Moving a zero summand to the left: `t + 0 ↦ 0 + t`.  The step is true in
the standard model. -/
inductive ZeroSwap : AExpr → AExpr → Prop where
  | swap (t : AExpr) : ZeroSwap (addE t zeroE) (addE zeroE t)

/-- The number of nodes of an expression. -/
def nodes : AExpr → Nat
  | .bvar _ => 1
  | .univ => 1
  | .prop => 1
  | .base _ => 1
  | .pi A B => nodes A + nodes B + 1
  | .lam A b => nodes A + nodes b + 1
  | .app f a => nodes f + nodes a + 1
  | .const _ _ => 1
  | .tyFam _ => 1
  | .top => 1
  | .bot => 1
  | .and p q => nodes p + nodes q + 1
  | .or p q => nodes p + nodes q + 1
  | .imp p q => nodes p + nodes q + 1
  | .not p => nodes p + 1
  | .eq a b => nodes a + nodes b + 1
  | .all A b => nodes A + nodes b + 1
  | .ex A b => nodes A + nodes b + 1

/-- Moving a zero summand keeps the number of nodes, at every position. -/
theorem rewrite_zeroSwap_nodes {e e' : AExpr} (step : Rewrite ZeroSwap e e') :
    nodes e = nodes e' := by
  induction step with
  | root rule =>
      cases rule with
      | swap t => simp only [addE, zeroE, nodes]; omega
  | piDomain _ ih => simp only [nodes, ih]
  | piBody _ ih => simp only [nodes, ih]
  | lamDomain _ ih => simp only [nodes, ih]
  | lamBody _ ih => simp only [nodes, ih]
  | appFunction _ ih => simp only [nodes, ih]
  | appArgument _ ih => simp only [nodes, ih]
  | andLeft _ ih => simp only [nodes, ih]
  | andRight _ ih => simp only [nodes, ih]
  | orLeft _ ih => simp only [nodes, ih]
  | orRight _ ih => simp only [nodes, ih]
  | impLeft _ ih => simp only [nodes, ih]
  | impRight _ ih => simp only [nodes, ih]
  | notBody _ ih => simp only [nodes, ih]
  | eqLeft _ ih => simp only [nodes, ih]
  | eqRight _ ih => simp only [nodes, ih]
  | allDomain _ ih => simp only [nodes, ih]
  | allBody _ ih => simp only [nodes, ih]
  | exDomain _ ih => simp only [nodes, ih]
  | exBody _ ih => simp only [nodes, ih]

theorem convertible_zeroSwap_nodes {e e' : AExpr} (converted : Convertible ZeroSwap e e') :
    nodes e = nodes e' := by
  induction converted with
  | rel _ _ step => exact rewrite_zeroSwap_nodes step
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- A variable, and the sum of zero and that variable. -/
def x : AExpr := bvar 0

/-- **The recursion bubble does not convert `x` with `0 + x`.** -/
theorem rule_not_conv : ¬ Convertible Rule x (addE zeroE x) := by
  intro converted
  have equal := (conv_iff_norm false).mp converted
  simp [x, norm, addE, zeroE, appNorm, addNorm] at equal

/-- **The zero-swap bubble does not convert `x` with `0 + x`**: it keeps the
number of nodes. -/
theorem zeroSwap_not_conv : ¬ Convertible ZeroSwap x (addE zeroE x) := by
  intro converted
  have equal := convertible_zeroSwap_nodes converted
  simp [x, nodes, addE, zeroE] at equal

/-- **Their join does**: `x ← x + 0 ↦ 0 + x`, an emergent conversion. -/
theorem join_conv : Convertible (join Rule ZeroSwap) x (addE zeroE x) :=
  Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (.root (Or.inl (Rule.addZero x)))))
    (Relation.EqvGen.rel _ _ (.root (Or.inr (ZeroSwap.swap x))))

/-- So the join's conversion is not the union of the two conversions. -/
theorem join_conv_emergent :
    Convertible (join Rule ZeroSwap) x (addE zeroE x) ∧
      ¬ Convertible Rule x (addE zeroE x) ∧ ¬ Convertible ZeroSwap x (addE zeroE x) :=
  ⟨join_conv, rule_not_conv, zeroSwap_not_conv⟩

/-- **Completion**: the join has exactly the conversion of the bubble that adds
the left-unit equation, the critical pair of the two step sets. -/
theorem join_conv_iff_plus {e e' : AExpr} :
    Convertible (join Rule ZeroSwap) e e' ↔ Convertible RulePlus e e' := by
  constructor
  · exact convertible_into fun _ _ rule => rule.elim
      (fun recursion => Relation.EqvGen.rel _ _ (.root (RulePlus.recursion recursion)))
      (fun swapped => by
        cases swapped with
        | swap t =>
            exact Relation.EqvGen.trans _ _ _
              (Relation.EqvGen.rel _ _ (.root (RulePlus.recursion (Rule.addZero t))))
              (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (.root (RulePlus.zeroAdd t)))))
  · exact convertible_into fun _ _ rule => by
      cases rule with
      | recursion recursion => exact Relation.EqvGen.rel _ _ (.root (Or.inl recursion))
      | zeroAdd _ =>
          exact Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (.root (Or.inr (ZeroSwap.swap _)))))
            (Relation.EqvGen.rel _ _ (.root (Or.inl (Rule.addZero _))))

/-- **The join is decided, by a third normal form**: the normal form of the
completed bubble, not one assembled from the two given bubbles. -/
theorem join_conv_iff_norm {e e' : AExpr} :
    Convertible (join Rule ZeroSwap) e e' ↔ norm true e = norm true e' :=
  join_conv_iff_plus.trans (conv_iff_norm true)

/-- The recursion bubble is normalized by its normal form. -/
theorem rule_normalizedBy : NormalizedBy Rule (norm false) :=
  ⟨fun e => norm_reachable false e, fun _ _ converted => (conv_iff_norm false).mp converted⟩

/-- **The respect condition fails here**, as it must: the recursion normal form
sends the zero-swap conversion `x + 0 ~ 0 + x` to `x` and `0 + x`, which the
zero-swap bubble does not convert. -/
theorem norm_false_not_respects_zeroSwap :
    ¬ ∀ e e', Convertible ZeroSwap e e' → Convertible ZeroSwap (norm false e) (norm false e') := by
  intro respects
  have converted := respects (addE x zeroE) (addE zeroE x)
    (Relation.EqvGen.rel _ _ (.root (ZeroSwap.swap x)))
  have left : norm false (addE x zeroE) = x := by simp [x, norm, addE, zeroE, appNorm, addNorm]
  have right : norm false (addE zeroE x) = addE zeroE x := by
    simp [x, norm, addE, zeroE, appNorm, addNorm]
  rw [left, right] at converted
  exact zeroSwap_not_conv converted

/-- The recursion bubble's own normal form does not decide the join. -/
theorem norm_false_not_decides_join :
    ¬ ∀ e e' : AExpr, Convertible (join Rule ZeroSwap) e e' → norm false e = norm false e' := by
  intro decides
  exact rule_not_conv ((conv_iff_norm false).mpr (decides _ _ join_conv))

/-! ### Positive control: a logical bubble beside arithmetic -/

/-- Negation of truth: `¬⊤ ↦ ⊥`, a step on the logical formers alone. -/
inductive NotTop : AExpr → AExpr → Prop where
  | notTop : NotTop (.not .top) .bot

/-- Negation, with `¬⊤` contracted. -/
def negNorm : AExpr → AExpr
  | .top => .bot
  | p => .not p

/-- The normal form of the logical bubble: every `¬⊤` contracted, compositionally. -/
def normNot : AExpr → AExpr
  | .bvar i => .bvar i
  | .univ => .univ
  | .prop => .prop
  | .base b => .base b
  | .pi A B => .pi (normNot A) (normNot B)
  | .lam A b => .lam (normNot A) (normNot b)
  | .app f a => .app (normNot f) (normNot a)
  | .const τ c => .const τ c
  | .tyFam b => .tyFam b
  | .top => .top
  | .bot => .bot
  | .and p q => .and (normNot p) (normNot q)
  | .or p q => .or (normNot p) (normNot q)
  | .imp p q => .imp (normNot p) (normNot q)
  | .not p => negNorm (normNot p)
  | .eq a b => .eq (normNot a) (normNot b)
  | .all A b => .all (normNot A) (normNot b)
  | .ex A b => .ex (normNot A) (normNot b)

theorem rewrite_notTop_normNot {e e' : AExpr} (step : Rewrite NotTop e e') :
    normNot e = normNot e' := by
  induction step with
  | root rule => cases rule; rfl
  | piDomain _ ih => simp only [normNot, ih]
  | piBody _ ih => simp only [normNot, ih]
  | lamDomain _ ih => simp only [normNot, ih]
  | lamBody _ ih => simp only [normNot, ih]
  | appFunction _ ih => simp only [normNot, ih]
  | appArgument _ ih => simp only [normNot, ih]
  | andLeft _ ih => simp only [normNot, ih]
  | andRight _ ih => simp only [normNot, ih]
  | orLeft _ ih => simp only [normNot, ih]
  | orRight _ ih => simp only [normNot, ih]
  | impLeft _ ih => simp only [normNot, ih]
  | impRight _ ih => simp only [normNot, ih]
  | notBody _ ih => simp only [normNot, ih]
  | eqLeft _ ih => simp only [normNot, ih]
  | eqRight _ ih => simp only [normNot, ih]
  | allDomain _ ih => simp only [normNot, ih]
  | allBody _ ih => simp only [normNot, ih]
  | exDomain _ ih => simp only [normNot, ih]
  | exBody _ ih => simp only [normNot, ih]

theorem negNorm_reachable (p : AExpr) : Convertible NotTop (.not p) (negNorm p) := by
  cases p with
  | top => exact Relation.EqvGen.rel _ _ (.root NotTop.notTop)
  | _ => exact Relation.EqvGen.refl _

/-- **The logical bubble is normalized by its normal form.** -/
theorem notTop_normalizedBy : NormalizedBy NotTop normNot := by
  refine ⟨fun e => ?_, fun e e' converted => ?_⟩
  · induction e with
    | app f a ihf iha =>
        exact convertible_two app (fun step => .appFunction step) (fun step => .appArgument step) ihf iha
    | pi A B ihA ihB =>
        exact convertible_two pi (fun step => .piDomain step) (fun step => .piBody step) ihA ihB
    | lam A b ihA ihb =>
        exact convertible_two lam (fun step => .lamDomain step) (fun step => .lamBody step) ihA ihb
    | and p q ihp ihq =>
        exact convertible_two Expr.and (fun step => .andLeft step) (fun step => .andRight step) ihp ihq
    | or p q ihp ihq =>
        exact convertible_two Expr.or (fun step => .orLeft step) (fun step => .orRight step) ihp ihq
    | imp p q ihp ihq =>
        exact convertible_two imp (fun step => .impLeft step) (fun step => .impRight step) ihp ihq
    | not p ihp =>
        exact Relation.EqvGen.trans _ _ _ (convertible_lift Expr.not (fun step => .notBody step) ihp)
          (negNorm_reachable (normNot p))
    | eq a b iha ihb =>
        exact convertible_two Expr.eq (fun step => .eqLeft step) (fun step => .eqRight step) iha ihb
    | all A b ihA ihb =>
        exact convertible_two all (fun step => .allDomain step) (fun step => .allBody step) ihA ihb
    | ex A b ihA ihb =>
        exact convertible_two ex (fun step => .exDomain step) (fun step => .exBody step) ihA ihb
    | _ => exact Relation.EqvGen.refl _
  · induction converted with
    | rel _ _ step => exact rewrite_notTop_normNot step
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

end Arith

end Mettapedia.TypeTheory.BubbleConversion
