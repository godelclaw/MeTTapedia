import Mettapedia.GSLT.Dedukti.LeanMinusExplicitExamples

/-!
# Theorem 2 of the paper fails for one level variable; the corrected rules

Theorem 2 of Blanqui and Vaishnav: `l₁ ≃ l₂` iff `ΣU ⊢ |l₁|_c ≡ |l₂|_c`, where
`|·|_c` (Definition 2) sends the level variable numbered `i` to
`Max (cons S_code (var (nil N_code) i 0) (nil S_code))`.  Theorem 3 rests on it.
Both directions fail already for levels in one variable, for two independent
reasons, each witnessed here with the paper's rules.

* **D1, the empty guard.** Géran's normal form writes a variable as `V {α} α 0`;
  the guard holds the variable, and the comparison rule
  `cst G i ≤ var H _ j ↪ incl H G ∧ i ≤ s j` assumes it (the variable is then
  at least `1`).  With the empty guard of Definition 2, `max (succ zero) α`
  reduces to `α` (`paper_max_one_var_reduces`), although `max 1 α` and `α`
  differ at `α = 0`.  So the direction "convertible ⇒ equivalent" fails
  (`paper_theorem2_reflection_fails`).
* **D2, `add` for `Add`.** The middle branch of the rule on `Add` drops the
  dominated head and inserts the new sublevel into the rest by `add`, which
  does not test the rest for dominance.  `max (succ α) (max 2 α)` and
  `max 2 (succ α)` are equivalent and keep distinct normal forms
  (`paper_add_incomplete`), so the direction "equivalent ⇒ convertible", the
  statement of Theorem 3, fails.  With the guard corrected alone, the pair
  `max 3 (max 1 (imax 2 α))`, `max 3 α` fails in the same way
  (`guard_alone_incomplete`).

The non-convertibility statements are made in `paperLevelTheory`: `ΣU` and
`ΣP` with the paper's rules, `∧` excepted, which is given by the four rules on
literals that the paper's proof of Theorem 2 names as its orthogonal version.
That theory is orthogonal, hence confluent.

With both corrections (`leanTheoryExplicit`), each pair is separated or
joined as its semantics requires (`explicit_separates_max_one_var`,
`explicit_joins_add_pair`, `explicit_joins_guard_pair`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig lookupBody)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## The paper's rules -/

/-- The paper's rules of `ΣU` and `ΣP`, `∧` given by its four rules on
literals. -/
def paperLevelRules : List RewriteRule :=
  rulesC ++ rulesBOrthogonal ++ rulesN ++ rulesSet ++ rulesS ++ rulesE ++ rulesI ++ rulesP

/-- `ΣU` and `ΣP` with the paper's rules, `∧` orthogonal. -/
def paperLevelTheory : Theory := Theory.ofSig pureSig paperLevelRules

theorem paperLevelTheory_orthogonal : paperLevelTheory.Orthogonal :=
  orthogonal_of_check_closed paperLevelRules (fun _ member => member)
    (closedBodies_of_test paperLevelRules (by decide +kernel))
    (undefinedOnLeft_of_test (by decide +kernel)) (by decide +kernel)

theorem paperLevelTheory_confluent : Confluent (Step paperLevelTheory) :=
  confluent_of_orthogonal paperLevelTheory_orthogonal

theorem paperLevelRules_linear : ∀ rule ∈ paperLevelRules, (patternVars rule.lhs).Nodup :=
  fun rule member => paperLevelTheory_orthogonal.leftLinear rule member

theorem pureRules_linear : ∀ rule ∈ pureRules, (patternVars rule.lhs).Nodup := by
  decide +kernel

theorem pureRules_algebraic : ∀ rule ∈ pureRules, algebraic true rule.lhs = true := by
  decide +kernel

/-! ## The level variable `α` and some levels in it -/

/-- The level variable numbered `0`. -/
def alpha : LeanLevel := .param 0

/-- The closed level `n`. -/
def natLevel : Nat → LeanLevel
  | 0 => .zero
  | count + 1 => .succ (natLevel count)

theorem eval_natLevel (valuation : Nat → Nat) (count : Nat) :
    (natLevel count).eval valuation = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [natLevel, LeanLevel.eval, ih]

/-- `max 1 α`. -/
def maxOneVar : LeanLevel := .max (natLevel 1) alpha

/-! ## D1: the empty guard identifies `max 1 α` with `α` -/

/-- **`max 1 α` reduces to `α`** in the paper's `ΣU`, with the code of
Definition 2. -/
theorem paper_max_one_var_reduces : Reduces pureTheory (paperCode maxOneVar) (paperCode alpha) :=
  Reduces.of_evaluate pureRules_linear (fuel := 200) (by decide +kernel)

/-- **`max 1 α` and `α` are not equivalent**: at `α = 0` they are `1` and `0`. -/
theorem maxOneVar_not_equiv : ¬ LeanLevel.Equiv maxOneVar alpha := by
  intro equivalent
  have atZero := equivalent fun _ => 0
  simp [maxOneVar, alpha, natLevel, LeanLevel.eval] at atZero

/-- **Theorem 2 of the paper, direction "convertible ⇒ equivalent", fails**
for one level variable, with the code of Definition 2. -/
theorem paper_theorem2_reflection_fails :
    ¬ ∀ first second : LeanLevel,
        Conv pureTheory (paperCode first) (paperCode second) → LeanLevel.Equiv first second :=
  fun claimed => maxOneVar_not_equiv (claimed maxOneVar alpha paper_max_one_var_reduces.conv)

/-- The same with `Σpoly` and Definition 3, which writes the variable as
`v α 0` for a Dedukti variable `α`: the fallback rule turns it into the code of
Definition 2, and both levels reach that code.  Only the fallback fires here,
so the order of the two rules on `v` does not matter. -/
theorem paper_poly_max_one_var_joinable :
    Joinable leanTheory (paperLevel (fun _ => .var 0) maxOneVar) (paperLevel (fun _ => .var 0) alpha) := by
  have variable_ : Reduces leanTheory (ap "v" [.var 0, zeroN]) (levelVariable zeroN) :=
    .single (variableRule_step (.var 0) zeroN)
  have inner : Reduces leanTheory (paperLevel (fun _ => .var 0) maxOneVar) (paperCode maxOneVar) :=
    Reduces.app .refl variable_
  exact ⟨paperCode alpha, inner.trans (paper_max_one_var_reduces.mono pureTheory_extends), variable_⟩

/-! ## D2: `add` in place of `Add` separates equivalent levels -/

/-- `max (succ α) (max 2 α)`. -/
def addPairLeft : LeanLevel := .max (.succ alpha) (.max (natLevel 2) alpha)

/-- `max 2 (succ α)`. -/
def addPairRight : LeanLevel := .max (natLevel 2) (.succ alpha)

theorem addPair_equiv : LeanLevel.Equiv addPairLeft addPairRight := by
  intro valuation
  simp only [addPairLeft, addPairRight, alpha, LeanLevel.eval, eval_natLevel]
  omega

/-- The normal form of `|max (succ α) (max 2 α)|_c` in the paper's `ΣU`:
`Max {V ∅ α 0, V ∅ α 1}`, in which the first element is dominated. -/
def addPairLeftNormal : Term :=
  ap "Max" [ap "cons" [.con "S_code", ap "var" [ap "nil" [.con "N_code"], zeroN, zeroN],
    singletonSet (ap "var" [ap "nil" [.con "N_code"], zeroN, oneN])]]

/-- The normal form of `|max 2 (succ α)|_c` in the paper's `ΣU`:
`Max {V ∅ α 1}`. -/
def addPairRightNormal : Term :=
  ap "Max" [singletonSet (ap "var" [ap "nil" [.con "N_code"], zeroN, oneN])]

/-- **Theorem 2 of the paper, direction "equivalent ⇒ convertible", fails**
for one level variable: `max (succ α) (max 2 α)` and `max 2 (succ α)` are
equivalent, and their codes are not convertible. -/
theorem paper_add_incomplete :
    LeanLevel.Equiv addPairLeft addPairRight ∧
      ¬ Conv paperLevelTheory (paperCode addPairLeft) (paperCode addPairRight) := by
  refine ⟨addPair_equiv, fun convertible => ?_⟩
  have left : Reduces paperLevelTheory (paperCode addPairLeft) addPairLeftNormal :=
    Reduces.of_evaluate paperLevelRules_linear (fuel := 2000) (by decide +kernel)
  have right : Reduces paperLevelTheory (paperCode addPairRight) addPairRightNormal :=
    Reduces.of_evaluate paperLevelRules_linear (fuel := 2000) (by decide +kernel)
  have algebraicRules : ∀ rule ∈ paperLevelRules, algebraic true rule.lhs = true :=
    fun rule member => paperLevelTheory_orthogonal.leftAlgebraic rule member
  exact not_conv_of_normal paperLevelTheory_confluent
    (normal_of_stepOnce algebraicRules (term := addPairLeftNormal) (by decide +kernel))
    (normal_of_stepOnce algebraicRules (term := addPairRightNormal) (by decide +kernel)) (by decide)
    (.trans _ _ _ (.symm _ _ left.conv) (.trans _ _ _ convertible right.conv))

/-- `max 3 (max 1 (imax 2 α))`. -/
def guardPairLeft : LeanLevel := .max (natLevel 3) (.max (natLevel 1) (.imax (natLevel 2) alpha))

/-- `max 3 α`. -/
def guardPairRight : LeanLevel := .max (natLevel 3) alpha

theorem guardPair_equiv : LeanLevel.Equiv guardPairLeft guardPairRight := by
  intro valuation
  simp only [guardPairLeft, guardPairRight, alpha, LeanLevel.eval, eval_natLevel]
  split <;> omega

/-- The normal form of `|max 3 (max 1 (imax 2 α))|`, the guard corrected, in
the paper's `ΣU`: `Max {C ∅ 3, C {α} 2, V {α} α 0}`, in which `C {α} 2` is
dominated by `C ∅ 3`. -/
def guardPairLeftNormal : Term :=
  ap "Max" [ap "cons" [.con "S_code", ap "cst" [ap "nil" [.con "N_code"], numeral 3],
    ap "cons" [.con "S_code", ap "cst" [guardOf zeroN, numeral 2],
      singletonSet (ap "var" [guardOf zeroN, zeroN, zeroN])]]]

/-- The normal form of `|max 3 α|`: `Max {C ∅ 3, V {α} α 0}`. -/
def guardPairRightNormal : Term :=
  ap "Max" [ap "cons" [.con "S_code", ap "cst" [ap "nil" [.con "N_code"], numeral 3],
    singletonSet (ap "var" [guardOf zeroN, zeroN, zeroN])]]

/-- **The guard corrected alone does not suffice**: with the corrected code of
a variable and the paper's rule on `Add`, the equivalent levels
`max 3 (max 1 (imax 2 α))` and `max 3 α` have codes that are not
convertible. -/
theorem guard_alone_incomplete :
    LeanLevel.Equiv guardPairLeft guardPairRight ∧
      ¬ Conv paperLevelTheory (code guardPairLeft) (code guardPairRight) := by
  refine ⟨guardPair_equiv, fun convertible => ?_⟩
  have algebraicRules : ∀ rule ∈ paperLevelRules, algebraic true rule.lhs = true :=
    fun rule member => paperLevelTheory_orthogonal.leftAlgebraic rule member
  have left : Reduces paperLevelTheory (code guardPairLeft) guardPairLeftNormal :=
    Reduces.of_evaluate paperLevelRules_linear (fuel := 4000) (by decide +kernel)
  have right : Reduces paperLevelTheory (code guardPairRight) guardPairRightNormal :=
    Reduces.of_evaluate paperLevelRules_linear (fuel := 4000) (by decide +kernel)
  exact not_conv_of_normal paperLevelTheory_confluent
    (normal_of_stepOnce algebraicRules (term := guardPairLeftNormal) (by decide +kernel))
    (normal_of_stepOnce algebraicRules (term := guardPairRightNormal) (by decide +kernel))
    (by decide +kernel)
    (.trans _ _ _ (.symm _ _ left.conv) (.trans _ _ _ convertible right.conv))

/-! ## The corrected rules -/

/-- **With both corrections, `max 1 α` and `α` are separated**, as their
values at `α = 0` require (`var_maxOneVar_not_conv_explicit`, restated for the
levels of this module). -/
theorem explicit_separates_max_one_var :
    ¬ Conv leanTheoryExplicit (code maxOneVar) (code alpha) :=
  fun convertible => var_maxOneVar_not_conv_explicit (.symm _ _ convertible)

/-- The normal form of `|max 2 (succ α)|` with both corrections:
`Max {C ∅ 2, V {α} α 1}`. -/
def addPairExplicitNormal : Term :=
  ap "Max" [ap "cons" [.con "S_code", ap "cst" [ap "nil" [.con "N_code"], numeral 2],
    singletonSet (ap "var" [guardOf zeroN, zeroN, oneN])]]

/-- **With both corrections, the pair of D2 is joined.** -/
theorem explicit_joins_add_pair : Conv leanTheoryExplicit (code addPairLeft) (code addPairRight) :=
  convExplicit_of_evaluate (fuel := 4000) (fuel' := 4000) (common := addPairExplicitNormal)
    (by decide +kernel) (by decide +kernel)

/-- **With both corrections, the pair that the guard alone leaves apart is
joined.** -/
theorem explicit_joins_guard_pair : Conv leanTheoryExplicit (code guardPairLeft) (code guardPairRight) :=
  convExplicit_of_evaluate (fuel := 4000) (fuel' := 4000) (common := guardPairRightNormal)
    (by decide +kernel) (by decide +kernel)

#print axioms paperLevelTheory_orthogonal
#print axioms paperLevelTheory_confluent
#print axioms paper_max_one_var_reduces
#print axioms paper_theorem2_reflection_fails
#print axioms paper_poly_max_one_var_joinable
#print axioms paper_add_incomplete
#print axioms guard_alone_incomplete
#print axioms explicit_separates_max_one_var
#print axioms explicit_joins_add_pair
#print axioms explicit_joins_guard_pair

end Mettapedia.GSLT.Dedukti.LeanMinus
