import Mettapedia.TypeTheory.BubbleJoin

/-!
# A justified rewrite is not a normalization procedure

A proved equation licenses an explicit, justified rewrite: adding it to a bubble keeps every
conversion true in the model that justifies it. Making the rewrite part of an automatic
normalization procedure has two further obligations, confluence and termination, and the
justification supplies neither. This module separates the three properties on the
arithmetic bubbles of `BubbleConversion`.

* **The zero-swap join** (`join Rule ZeroSwap`): the recursion equations of addition on the
  second argument together with the true equation `t + 0 ↦ 0 + t`.
  - It is **sound** for the standard model of numeral terms (`zeroSwapJoin_sound`).
  - It is **not Church–Rosser** (`zeroSwapJoin_not_churchRosser`): `x + 0` reduces to `x` and
    to `0 + x`, both normal and distinct. This is the critical pair whose completion
    `BubbleJoin.join_conv_iff_plus` adds.
  - It is **not terminating** (`zeroSwapJoin_not_terminating`): `0 + 0` rewrites to itself.
* **Commutativity** (`Commute`): `t + u ↦ u + t` is sound and stable under substitution
  (`commute_sound`, `commute_stable`) and has the self-loop `x + x ↦ x + x`
  (`commute_not_terminating`).

The positive control is the recursion bubble alone: it is decided by its normal form
(`BubbleConversion.Arith.conv_iff_norm`), and so is the completed join
(`BubbleJoin.join_conv_iff_norm`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.JustifiedRewriteNotNormalizing

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr
open BubbleConversion BubbleConversion.Arith

/-! ## Reduction properties of a rule set -/

/-- Church–Rosser for the rewriting of a rule set at every position. -/
def ChurchRosser (rules : AExpr → AExpr → Prop) : Prop :=
  ∀ e e' : AExpr, Convertible rules e e' →
    ∃ common, Relation.ReflTransGen (Rewrite rules) e common ∧
      Relation.ReflTransGen (Rewrite rules) e' common

/-- An expression is normal when no rewrite step starts at it. -/
def Normal (rules : AExpr → AExpr → Prop) (e : AExpr) : Prop :=
  ∀ e', ¬ Rewrite rules e e'

/-- An expression is terminating when every rewrite sequence from it is finite. -/
def Terminating (rules : AExpr → AExpr → Prop) (e : AExpr) : Prop :=
  Acc (fun target source => Rewrite rules source target) e

theorem eq_of_normal {rules : AExpr → AExpr → Prop} {e common : AExpr}
    (normal : Normal rules e) (reduces : Relation.ReflTransGen (Rewrite rules) e common) :
    common = e := by
  rcases Relation.ReflTransGen.cases_head reduces with same | ⟨next, step, _⟩
  · exact same.symm
  · exact (normal next step).elim

/-- A rewrite step from an expression to itself makes it non-terminating. -/
theorem not_terminating_of_loop {rules : AExpr → AExpr → Prop} {e : AExpr}
    (loop : Rewrite rules e e) : ¬ Terminating rules e := by
  have claim : ∀ e', Acc (fun target source => Rewrite rules source target) e' → e' = e → False := by
    intro e' accessible
    induction accessible with
    | intro current _ ih =>
        intro same
        subst same
        exact ih current loop rfl
  exact fun terminating => claim e terminating rfl

/-! ## The zero-swap join -/

/-- The recursion equations and the zero swap `t + 0 ↦ 0 + t`. -/
abbrev zeroSwapJoin : AExpr → AExpr → Prop := join Rule ZeroSwap

/-- **Sound in the standard model**: convertible numeral terms have one value under every
valuation. -/
theorem zeroSwapJoin_sound {e e' : AExpr} (numeral : IsNumeral e) (numeral' : IsNumeral e')
    (converted : Convertible zeroSwapJoin e e') (valuation : ℕ → ℕ) :
    value valuation e = value valuation e' := by
  rw [← value_norm true valuation numeral, join_conv_iff_norm.mp converted,
    value_norm true valuation numeral']

theorem zeroSwapJoin_no_root_var (index : ℕ) (target : AExpr) :
    ¬ zeroSwapJoin (bvar index) target := by
  rintro (rule | rule) <;> cases rule

theorem zeroSwapJoin_no_root_const {τ : Ty Unit} (c : ArithConst τ) (target : AExpr) :
    ¬ zeroSwapJoin (const τ c) target := by
  rintro (rule | rule) <;> cases rule

/-- A variable is normal. -/
theorem normal_var (index : ℕ) : Normal zeroSwapJoin (bvar index) := by
  intro target step
  cases step with
  | root rule => exact zeroSwapJoin_no_root_var index target rule

/-- A constant is normal. -/
theorem normal_const {τ : Ty Unit} (c : ArithConst τ) : Normal zeroSwapJoin (const τ c) := by
  intro target step
  cases step with
  | root rule => exact zeroSwapJoin_no_root_const c target rule

/-- The partial application `add 0` is normal. -/
theorem normal_addZeroPartial : Normal zeroSwapJoin (app (const _ .add) zeroE) := by
  intro target step
  cases step with
  | root rule =>
      rcases rule with rule | rule
      · cases rule
      · cases rule
  | appFunction inner => exact normal_const _ _ inner
  | appArgument inner => exact normal_const _ _ inner

/-- **`0 + x` is normal** for a variable `x`. -/
theorem normal_zeroPlusVar (index : ℕ) : Normal zeroSwapJoin (addE zeroE (bvar index)) := by
  intro target step
  cases step with
  | root rule =>
      rcases rule with rule | rule
      · cases rule
      · cases rule
  | appFunction inner => exact normal_addZeroPartial _ inner
  | appArgument inner => exact normal_var index _ inner

/-- **Not Church–Rosser**: `x + 0` reduces to `x` and to `0 + x`, two distinct normal
forms. -/
theorem zeroSwapJoin_not_churchRosser : ¬ ChurchRosser zeroSwapJoin := by
  intro churchRosser
  have converted : Convertible zeroSwapJoin (bvar 0) (addE zeroE (bvar 0)) :=
    Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (.root (Or.inl (Rule.addZero (bvar 0))))))
      (Relation.EqvGen.rel _ _ (.root (Or.inr (ZeroSwap.swap (bvar 0)))))
  obtain ⟨common, fromVar, fromSum⟩ := churchRosser _ _ converted
  have first := eq_of_normal (normal_var 0) fromVar
  have second := eq_of_normal (normal_zeroPlusVar 0) fromSum
  have distinct : (bvar 0 : AExpr) ≠ addE zeroE (bvar 0) := by
    simp [addE, zeroE]
  exact distinct (first.symm.trans second)

/-- **Not terminating**: `0 + 0` rewrites to itself by the zero swap. -/
theorem zeroSwapJoin_not_terminating : ¬ Terminating zeroSwapJoin (addE zeroE zeroE) :=
  not_terminating_of_loop (.root (Or.inr (ZeroSwap.swap zeroE)))

/-- **Positive control**: the completed join is decided by a normal form, so its conversion
is decidable although its rewriting is neither confluent nor terminating. -/
theorem zeroSwapJoin_decided {e e' : AExpr} :
    Convertible zeroSwapJoin e e' ↔ norm true e = norm true e' :=
  join_conv_iff_norm

/-! ## Commutativity -/

/-- The commutativity of addition as a rewrite rule. -/
inductive Commute : AExpr → AExpr → Prop where
  | swap (t u : AExpr) : Commute (addE t u) (addE u t)

theorem bind_add_comm (x y : Option ℕ) :
    (x.bind fun a => y.map (a + ·)) = (y.bind fun b => x.map (b + ·)) := by
  cases x <;> cases y <;> simp [Nat.add_comm]

/-- **Sound in the standard model.** -/
theorem commute_sound {left right : AExpr} (rule : Commute left right) (valuation : ℕ → ℕ) :
    value valuation left = value valuation right := by
  cases rule with
  | swap t u => rw [value_addE, value_addE, bind_add_comm]

/-- **Stable under substitution.** -/
theorem commute_stable : SubstitutionStable Commute := by
  intro left right rule depth replacement
  cases rule with
  | swap t u => exact Commute.swap _ _

/-- **Not terminating**: `x + x ↦ x + x`. -/
theorem commute_not_terminating (t : AExpr) : ¬ Terminating Commute (addE t t) :=
  not_terminating_of_loop (.root (Commute.swap t t))

/-! ## Axiom audit -/

#print axioms zeroSwapJoin_sound
#print axioms zeroSwapJoin_not_churchRosser
#print axioms zeroSwapJoin_not_terminating
#print axioms zeroSwapJoin_decided
#print axioms commute_sound
#print axioms commute_stable
#print axioms commute_not_terminating

end Mettapedia.TypeTheory.JustifiedRewriteNotNormalizing
