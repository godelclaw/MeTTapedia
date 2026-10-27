import Mettapedia.TypeTheory.PromotionAdmission.Criterion
import Mettapedia.TypeTheory.JustifiedRewriteNotNormalizing

/-!
# The criterion on the arithmetic bubbles of the core

The admission criterion (`Convergent`) applied to the arithmetic bubbles of
`BubbleConversion`, whose steps rewrite at every position of an expression of the dependent
core, binders included.

* **The zero swap promoted into addition is refused, by both parts**
  (`zeroSwapJoin_not_locallyConfluent`, `zeroSwapJoin_not_terminating'`): the join of the
  recursion equations with `t + 0 ↦ 0 + t` has the fork `x + 0 ↦ x`, `x + 0 ↦ 0 + x` to two
  distinct normal forms, and the loop `0 + 0 ↦ 0 + 0`. The equation is true in `ℕ`
  (`JustifiedRewriteNotNormalizing.zeroSwapJoin_sound`): justification does not give the
  criterion.
* **Commutativity is confluent and refused by termination alone** (`commute_confluent`,
  `commute_not_convergent`): every commutation step can be undone, so reductions can always be
  retraced, and `x + x ↦ x + x` loops. It is true in `ℕ`
  (`JustifiedRewriteNotNormalizing.commute_sound`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PromotionAdmission.BubbleControls

open Relation
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr
open BubbleConversion BubbleConversion.Arith
open JustifiedRewriteNotNormalizing (zeroSwapJoin Commute normal_var normal_zeroPlusVar
  eq_of_normal)
open Mettapedia.Logic.Relation (Confluent)

/-- **The zero swap breaks local confluence**: `x + 0` reaches `x` and `0 + x`, both normal. -/
theorem zeroSwapJoin_not_locallyConfluent : ¬ LocallyConfluent (Rewrite zeroSwapJoin) := by
  intro lc
  obtain ⟨common, fromVar, fromSum⟩ := lc (addE (bvar 0) zeroE) (bvar 0) (addE zeroE (bvar 0))
    (.root (Or.inl (Rule.addZero (bvar 0)))) (.root (Or.inr (ZeroSwap.swap (bvar 0))))
  have first := eq_of_normal (normal_var 0) fromVar
  have second := eq_of_normal (normal_zeroPlusVar 0) fromSum
  have distinct : (bvar 0 : AExpr) ≠ addE zeroE (bvar 0) := by simp [addE, zeroE]
  exact distinct (first.symm.trans second)

/-- **The zero swap breaks termination**: `0 + 0` rewrites to itself. -/
theorem zeroSwapJoin_not_terminating' : ¬ Terminating (Rewrite zeroSwapJoin) :=
  fun terminating => JustifiedRewriteNotNormalizing.zeroSwapJoin_not_terminating
    (terminating (addE zeroE zeroE))

/-- **The zero swap fails the criterion.** -/
theorem zeroSwapJoin_not_convergent : ¬ Convergent (Rewrite zeroSwapJoin) :=
  fun convergent => zeroSwapJoin_not_locallyConfluent convergent.locallyConfluent

/-- A commutation step can be undone. -/
theorem commute_symmetric {e e' : AExpr} (step : Rewrite Commute e e') : Rewrite Commute e' e := by
  induction step with
  | root rule => cases rule with | swap t u => exact .root (.swap u t)
  | piDomain _ ih => exact .piDomain ih
  | piBody _ ih => exact .piBody ih
  | lamDomain _ ih => exact .lamDomain ih
  | lamBody _ ih => exact .lamBody ih
  | appFunction _ ih => exact .appFunction ih
  | appArgument _ ih => exact .appArgument ih
  | andLeft _ ih => exact .andLeft ih
  | andRight _ ih => exact .andRight ih
  | orLeft _ ih => exact .orLeft ih
  | orRight _ ih => exact .orRight ih
  | impLeft _ ih => exact .impLeft ih
  | impRight _ ih => exact .impRight ih
  | notBody _ ih => exact .notBody ih
  | eqLeft _ ih => exact .eqLeft ih
  | eqRight _ ih => exact .eqRight ih
  | allDomain _ ih => exact .allDomain ih
  | allBody _ ih => exact .allBody ih
  | exDomain _ ih => exact .exDomain ih
  | exBody _ ih => exact .exBody ih

/-- **Commutativity is confluent**: every reduction can be retraced. -/
theorem commute_confluent : Confluent (Rewrite Commute) := by
  intro s left right toLeft toRight
  have back : ∀ {a b : AExpr}, ReflTransGen (Rewrite Commute) a b →
      ReflTransGen (Rewrite Commute) b a := by
    intro a b steps
    induction steps with
    | refl => exact .refl
    | tail _ step ih => exact ReflTransGen.head (commute_symmetric step) ih
  exact ⟨right, (back toLeft).trans toRight, .refl⟩

/-- **Commutativity is refused by the termination part alone.** -/
theorem commute_not_convergent : ¬ Convergent (Rewrite Commute) :=
  fun convergent => JustifiedRewriteNotNormalizing.commute_not_terminating (addE (bvar 0) (bvar 0))
    (convergent.terminating _)

/-- Its local confluence holds. -/
theorem commute_locallyConfluent : LocallyConfluent (Rewrite Commute) :=
  fun a b c first second =>
    commute_confluent a b c (ReflTransGen.single first) (ReflTransGen.single second)

/-! ## Axiom audit -/

#print axioms zeroSwapJoin_not_locallyConfluent
#print axioms zeroSwapJoin_not_terminating'
#print axioms zeroSwapJoin_not_convergent
#print axioms commute_confluent
#print axioms commute_not_convergent

end Mettapedia.TypeTheory.PromotionAdmission.BubbleControls
