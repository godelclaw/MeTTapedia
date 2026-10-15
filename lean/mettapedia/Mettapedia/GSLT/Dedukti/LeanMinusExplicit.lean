import Mettapedia.GSLT.Dedukti.LeanMinusExamples
import Mettapedia.GSLT.Dedukti.ConfluenceApplied
import Mettapedia.GSLT.Dedukti.Evaluator

/-!
# The Dedukti theory of Lean⁻ with explicit level substitution

`LeanMinus.leanTheory` transcribes the theory `Σ` of Blanqui and Vaishnav
(arXiv 2609.24604).  Its two rules on `v`, `v (inst l) _ ↪ l` and
`v _ i ↪ B(i)`, overlap, and under the conversion of the paper's Section 1.4
every two terms are convertible (`leanTheory_conv_all`).  This module gives a
second transcription, `leanTheoryExplicit`, in which no two rules overlap, so
that `confluent_of_orthogonal` applies (`leanTheoryExplicit_confluent`), and
`Step.subst`, `Conv.subst` apply to it unchanged.

## What replaces `Σpoly`

* A level variable of a declaration is carried as its code, a closed term:
  the variable numbered `i` is `varCode i`, Géran's sublevel `V {i} i 0`.
* A universe-polymorphic declaration takes one argument `fr : Inst`, the
  instantiation of all its level variables.  Inside it, the level `l` is
  `sub fr |l|` (`levelIn`), where `|l|` is the closed code of `l`.  Level
  arithmetic happens in `|l|`, on closed terms, by the rules of `ΣU`.
* An instantiation is the constructor `inst` applied to a list of levels;
  `sub (inst L) e ↪ dsub L e` substitutes the levels `L` into the normal form
  `e`, using the operations `Fold`, `Add`, `Incr` and `addguard` of `ΣU`.
* A free frame variable `fr` is stuck: `sub fr e` has no rule.  Nothing
  distinguishes a variable from an instance by the order of rules; `inst` is
  a constructor, and the only rule on `sub` requires it.
* A use `x[l₁ … lₙ]` is `x (inst [|l₁|, …, |lₙ|])` at the top level, and
  `x (inst [sub fr |l₁|, …])` inside a declaration with frame `fr`.  `dsub`
  returns `lookup L i` at once on the code of a single variable `i`, so a
  use whose levels are variables of the enclosing declaration has exactly the
  levels of that declaration.

## Two corrections to `ΣU`

Both are forced by kernel-checked witnesses against the paper's rules
(`LeanMinusLevels`).

* The code of a level variable has the variable in its guard.  Definition 2
  writes `var (nil N_code) i 0`, with the empty guard; with it `ΣU` reduces
  `max (succ zero) α` to `α` although the two differ at `α = 0`
  (`paper_max_one_var_reduces`).
* The middle branch of the rule on `Add` continues with `Add`, not `add`:
  when the head of the set is dominated, the remaining elements must still be
  tested.  With `add`, two equivalent levels keep distinct normal forms
  (`paper_add_incomplete`).

And `∧` is given by its four rules on literals, the orthogonal version that
the paper's proof of its Theorem 2 names.

## Contents

* `orthogonal_of_check_closed`: the test of `OrthogonalCheck` for a theory
  with closed definitions, none of which occurs on a left side.
* `leanTheoryExplicit`, `leanTheoryExplicit_orthogonal`,
  `leanTheoryExplicit_confluent`, closed definitions and closed declared types.
* Definitions 2–4 of the paper, translated: `LeanLevel`, `code`, `levelIn`,
  `explicitDecl`, `useTop`, `useIn`, and the paper's own `paperCode`,
  `paperLevel`, `paperDecl`, `paperUse`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig Decl sigT lookupType lookupBody lift subst subst0)

/-! ## Orthogonality of a theory with closed definitions -/

/-- The constants occurring in a term. -/
def constantsOf : Term → List String
  | .con name => [name]
  | .app function argument => constantsOf function ++ constantsOf argument
  | .pi domain body => constantsOf domain ++ constantsOf body
  | .lam domain body => constantsOf domain ++ constantsOf body
  | .var _ => []
  | .srt _ => []

theorem constantsOf_of_mem_subpatterns :
    ∀ {whole part : Term}, part ∈ subpatterns whole →
      ∀ name ∈ constantsOf part, name ∈ constantsOf whole := by
  intro whole
  induction whole with
  | var index => intro part member; simp [subpatterns] at member
  | srt sort => intro part member; simp [subpatterns] at member
  | con name => intro part member; simp [subpatterns] at member
  | pi domain body _ _ => intro part member; simp [subpatterns] at member
  | lam domain body _ _ => intro part member; simp [subpatterns] at member
  | app function argument ihFunction ihArgument =>
      intro part member name inPart
      simp only [subpatterns, List.mem_cons, List.mem_append] at member
      simp only [constantsOf, List.mem_append]
      rcases member with rfl | rfl | inFunction | inArgument
      · exact Or.inl inPart
      · exact Or.inr inPart
      · exact Or.inl (ihFunction inFunction name inPart)
      · exact Or.inr (ihArgument inArgument name inPart)

/-- **A theory with closed definitions, none of which occurs on a left side,
whose rules are among those of a list that passes the test, is orthogonal.** -/
theorem orthogonal_of_check_closed {theory : Theory} (rules : List RewriteRule)
    (covered : ∀ rule, theory.rule rule → rule ∈ rules)
    (closed : theory.ClosedBodies)
    (undefinedOnLeft : ∀ rule ∈ rules, ∀ name ∈ constantsOf rule.lhs, theory.body name = none)
    (checked : orthogonalCheck rules = true) : theory.Orthogonal := by
  have each : ∀ rule, theory.rule rule →
      algebraic true rule.lhs = true ∧ (patternVars rule.lhs).Nodup ∧
        usesOnly (patternVars rule.lhs) 0 rule.rhs = true ∧
        (∀ part ∈ subpatterns rule.lhs, algebraic true part = true →
          ∀ other ∈ rules, clashes part other.lhs = true) ∧
        ∀ other ∈ rules, rule = other ∨ clashes rule.lhs other.lhs = true := by
    intro rule member
    have passed := List.all_eq_true.mp checked rule (covered rule member)
    simp only [ruleChecked, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true'] at passed
    obtain ⟨⟨⟨⟨isAlgebraic, nodup⟩, uses⟩, parts⟩, roots⟩ := passed
    refine ⟨isAlgebraic, nodup, uses, fun part partMember partAlgebraic other otherMember => ?_,
      roots⟩
    rcases parts part partMember with notAlgebraic | clash
    · rw [partAlgebraic] at notAlgebraic
      cases notAlgebraic
    · exact clash other otherMember
  refine
    { closedBodies := closed
      leftAlgebraic := fun rule member => (each rule member).1
      leftLinear := fun rule member => (each rule member).2.1
      rightDetermined := fun rule member first second agree =>
        instantiate_congr_of_usesOnly agree rule.rhs 0 (each rule member).2.2.1
      leftUndefined := fun rule member name same =>
        undefinedOnLeft rule (covered rule member) name (by rw [same]; simp [constantsOf])
      rootUnique := fun first second firstMember secondMember left right same => ?_
      nonOverlapping := fun rule member part partMember partAlgebraic =>
        { undefined := fun name same =>
            undefinedOnLeft rule (covered rule member) name
              (constantsOf_of_mem_subpatterns partMember name (by rw [same]; simp [constantsOf]))
          unmatched := fun other first second otherMember =>
            ne_inst_of_clashes
              ((each rule member).2.2.2.1 part partMember partAlgebraic other
                (covered other otherMember)) first second } }
  rcases (each first firstMember).2.2.2.2 second (covered second secondMember) with equal | clash
  · exact equal
  · exact (ne_inst_of_clashes clash left right same).elim

/-- The test that no constant of a left side has a definition. -/
def undefinedOnLeftTest (signature : Sig) (rules : List RewriteRule) : Bool :=
  rules.all fun rule => (constantsOf rule.lhs).all fun name => (lookupBody signature name).isNone

theorem undefinedOnLeft_of_test {signature : Sig} {rules : List RewriteRule}
    (passed : undefinedOnLeftTest signature rules = true) :
    ∀ rule ∈ rules, ∀ name ∈ constantsOf rule.lhs,
      (Theory.ofSig signature rules).body name = none := by
  intro rule member name inLeft
  have found := List.all_eq_true.mp (List.all_eq_true.mp passed rule member) name inLeft
  exact Option.isNone_iff_eq_none.mp found

/-- The test that a declaration is closed. -/
def declClosedTest : Decl → Bool
  | .const _ type => wellScopedTest 0 type
  | .defn _ type body => wellScopedTest 0 type && wellScopedTest 0 body

/-- The test that every declaration of a signature is closed. -/
def closedSigTest (signature : Sig) : Bool := signature.all declClosedTest

theorem closedBodies_of_test {signature : Sig} (rules : List RewriteRule)
    (passed : closedSigTest signature = true) : (Theory.ofSig signature rules).ClosedBodies := by
  intro name term found
  change lookupBody signature name = some term at found
  induction signature with
  | nil => simp [lookupBody] at found
  | cons head rest ih =>
      simp only [closedSigTest, List.all_cons, Bool.and_eq_true] at passed
      cases head with
      | const declared type =>
          simp only [lookupBody] at found
          exact ih passed.2 found
      | defn declared type body =>
          simp only [lookupBody] at found
          split at found
          · obtain rfl := Option.some.inj found
            simp only [declClosedTest, Bool.and_eq_true] at passed
            exact wellScoped_of_test _ 0 passed.1.2
          · exact ih passed.2 found

theorem closedTypes_of_test {signature : Sig} (rules : List RewriteRule)
    (passed : closedSigTest signature = true) : (Theory.ofSig signature rules).ClosedTypes := by
  intro name type found
  change lookupType signature name = some type at found
  induction signature with
  | nil => simp [lookupType] at found
  | cons head rest ih =>
      simp only [closedSigTest, List.all_cons, Bool.and_eq_true] at passed
      cases head with
      | const declared declaredType =>
          simp only [lookupType] at found
          split at found
          · obtain rfl := Option.some.inj found
            exact wellScoped_of_test _ 0 passed.1
          · exact ih passed.2 found
      | defn declared declaredType body =>
          simp only [lookupType] at found
          split at found
          · obtain rfl := Option.some.inj found
            simp only [declClosedTest, Bool.and_eq_true] at passed
            exact wellScoped_of_test _ 0 passed.1.1
          · exact ih passed.2 found

end Mettapedia.GSLT.Dedukti

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig Decl sigT lookupType lookupBody lift subst subst0 Ctx)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## Two corrections to `ΣU`, and the orthogonal `∧` -/

/-- `∧` by its four rules on literals, and `if`: the orthogonal version of the
rules of `ΣB` named in the paper's proof of its Theorem 2. -/
def rulesBOrthogonal : List RewriteRule :=
  [mkRule [] (ap "and" [.con "true", .con "true"]) (.con "true"),
    mkRule [] (ap "and" [.con "true", .con "false"]) (.con "false"),
    mkRule [] (ap "and" [.con "false", .con "true"]) (.con "false"),
    mkRule [] (ap "and" [.con "false", .con "false"]) (.con "false"),
    mkRule ["w0", "x", "w1"] (ap "if" [nv "w0", .con "true", nv "x", nv "w1"]) (nv "x"),
    mkRule ["w0", "w1", "x"] (ap "if" [nv "w0", .con "false", nv "w1", nv "x"]) (nv "x")]

/-- The paper's rule `Add o (o1 :: e1)`: when `o1 ≤ o` it continues with
`add`, which does not test the rest of the set. -/
def addConsPaper : RewriteRule :=
  mkRule ["o", "w", "o1", "e1"] (ap "Add" [nv "o", ap "cons" [nv "w", nv "o1", nv "e1"]])
    (ap "if" [setOf (.con "S_code"), ap "leS" [nv "o", nv "o1"],
      ap "cons" [nv "w", nv "o1", nv "e1"],
      ap "if" [setOf (.con "S_code"), ap "leS" [nv "o1", nv "o"],
        ap "add" [.con "S_code", .con "cmpS", nv "o", nv "e1"],
        ap "add" [.con "S_code", .con "cmpS", nv "o1", ap "Add" [nv "o", nv "e1"]]]])

/-- **`Add o (o1 :: e1)`, corrected**: when `o1 ≤ o`, `o1` is dropped and `o`
is inserted into `e1` by `Add`, which keeps testing the rest. -/
def addConsCorrected : RewriteRule :=
  mkRule ["o", "w", "o1", "e1"] (ap "Add" [nv "o", ap "cons" [nv "w", nv "o1", nv "e1"]])
    (ap "if" [setOf (.con "S_code"), ap "leS" [nv "o", nv "o1"],
      ap "cons" [nv "w", nv "o1", nv "e1"],
      ap "if" [setOf (.con "S_code"), ap "leS" [nv "o1", nv "o"],
        ap "Add" [nv "o", nv "e1"],
        ap "add" [.con "S_code", .con "cmpS", nv "o1", ap "Add" [nv "o", nv "e1"]]]])

/-- The rules of `ΣE` with the corrected rule on `Add`. -/
def rulesECorrected : List RewriteRule :=
  [mkRule ["w"] (ap "Incr" [ap "nil" [nv "w"]]) (ap "nil" [.con "S_code"]),
    mkRule ["w", "o", "s1"] (ap "Incr" [ap "cons" [nv "w", nv "o", nv "s1"]])
      (ap "cons" [.con "S_code", ap "incr" [nv "o"], ap "Incr" [nv "s1"]]),
    mkRule ["o", "w"] (ap "Add" [nv "o", ap "nil" [nv "w"]])
      (ap "cons" [.con "S_code", nv "o", ap "nil" [.con "S_code"]]),
    addConsCorrected]

/-- The transcribed rules of `ΣE` are the first three rules and the paper's
rule on `Add`; only that rule is corrected. -/
theorem rulesE_eq_paper : rulesE = rulesECorrected.take 3 ++ [addConsPaper] := by
  decide

/-- The guard `{i}`. -/
def guardOf (index : Term) : Term :=
  ap "cons" [.con "N_code", index, ap "nil" [.con "N_code"]]

/-- **The code of the level variable numbered `index`**: Géran's sublevel
`V {α} α 0`, whose guard holds the variable.  Definition 2 of the paper writes
`levelVariable index`, with the empty guard. -/
def varCode (index : Term) : Term :=
  ap "Max" [ap "cons" [.con "S_code", ap "var" [guardOf index, index, zeroN],
    ap "nil" [.con "S_code"]]]

/-- The numeral of a natural number. -/
def numeral : Nat → Term
  | 0 => zeroN
  | count + 1 => ap "s" [numeral count]

/-! ## Explicit level substitution, in place of `Σpoly` -/

/-- The type of lists of levels. -/
def LS : Term := .con "LS"
/-- The type of instantiations. -/
def InstT : Term := .con "Inst"

/-- A list of levels. -/
def levelList : List Term → Term
  | [] => .con "lnil"
  | level :: rest => ap "lcons" [level, levelList rest]

/-- The instantiation of the level variables `0, 1, …` by a list of levels. -/
def instAt (levels : List Term) : Term := ap "inst" [levelList levels]

/-- The level whose code is `code`, read under the instantiation `frame`. -/
def subIn (frame code : Term) : Term := ap "sub" [frame, code]

/-- The set of sublevels of one sublevel. -/
def singletonSet (sublevel : Term) : Term :=
  ap "cons" [.con "S_code", sublevel, ap "nil" [.con "S_code"]]

/-- The substitution of `levels` into the normal form `Max (o :: e)`, by the
general construction. -/
def generalSubst (levels sublevel rest : Term) : Term :=
  ap "Max" [ap "dsubSet" [levels, ap "cons" [.con "S_code", sublevel, rest]]]

def sigmaSubst : Sig :=
  [.const "LS" typ, .const "lnil" LS, .const "lcons" (arrows [L, LS] LS),
    .const "Inst" typ, .const "inst" (arrow LS InstT),
    .const "sub" (arrows [InstT, L] L),
    .const "dsub" (arrows [LS, L] L),
    .const "dsubMax" (arrows [LS, E] L),
    .const "dsubCons" (arrows [LS, S, E] L),
    .const "dsubVar" (arrows [LS, G, N, N] L),
    .const "ifL" (arrows [B, L, L] L),
    .const "lookup" (arrows [LS, N] L),
    .const "unMax" (arrow L E),
    .const "dsubSet" (arrows [LS, E] E),
    .const "dsubSub" (arrows [LS, S] E),
    .const "guardAll" (arrows [LS, G, E] E),
    .const "IncrN" (arrows [N, E] E),
    .defn "Guard" (arrows [E, E] E)
      (lamN "e" E (lamN "f" E (ap "Fold" [ap "FoldAddguard" [nv "f"], nv "e",
        ap "nil" [.con "S_code"]])))]

/-- `sub (inst L) e ↪ dsub L e`: the only rule on `sub`. -/
def subRule : RewriteRule :=
  mkRule ["l", "e"] (ap "sub" [ap "inst" [nv "l"], nv "e"]) (ap "dsub" [nv "l", nv "e"])

def rulesSubst : List RewriteRule :=
  [subRule,
    mkRule ["l", "e"] (ap "dsub" [nv "l", ap "Max" [nv "e"]]) (ap "dsubMax" [nv "l", nv "e"]),
    mkRule ["l", "w"] (ap "dsubMax" [nv "l", ap "nil" [nv "w"]]) (ap "Max" [ap "nil" [.con "S_code"]]),
    mkRule ["l", "w", "o", "e"] (ap "dsubMax" [nv "l", ap "cons" [nv "w", nv "o", nv "e"]])
      (ap "dsubCons" [nv "l", nv "o", nv "e"]),
    mkRule ["l", "g", "c", "e"] (ap "dsubCons" [nv "l", ap "cst" [nv "g", nv "c"], nv "e"])
      (generalSubst (nv "l") (ap "cst" [nv "g", nv "c"]) (nv "e")),
    mkRule ["l", "g", "x", "k", "w"]
      (ap "dsubCons" [nv "l", ap "var" [nv "g", nv "x", nv "k"], ap "nil" [nv "w"]])
      (ap "dsubVar" [nv "l", nv "g", nv "x", nv "k"]),
    mkRule ["l", "g", "x", "k", "w", "o", "e"]
      (ap "dsubCons" [nv "l", ap "var" [nv "g", nv "x", nv "k"], ap "cons" [nv "w", nv "o", nv "e"]])
      (generalSubst (nv "l") (ap "var" [nv "g", nv "x", nv "k"]) (ap "cons" [nv "w", nv "o", nv "e"])),
    mkRule ["l", "w", "x", "k"] (ap "dsubVar" [nv "l", ap "nil" [nv "w"], nv "x", nv "k"])
      (generalSubst (nv "l") (ap "var" [ap "nil" [.con "N_code"], nv "x", nv "k"])
        (ap "nil" [.con "S_code"])),
    mkRule ["l", "w", "g", "w1", "x"]
      (ap "dsubVar" [nv "l", ap "cons" [nv "w", nv "g", ap "nil" [nv "w1"]], nv "x", zeroN])
      (ap "ifL" [ap "eqN" [nv "g", nv "x"], ap "lookup" [nv "l", nv "x"],
        generalSubst (nv "l") (ap "var" [guardOf (nv "g"), nv "x", zeroN]) (ap "nil" [.con "S_code"])]),
    mkRule ["l", "w", "g", "w1", "x", "k"]
      (ap "dsubVar" [nv "l", ap "cons" [nv "w", nv "g", ap "nil" [nv "w1"]], nv "x", ap "s" [nv "k"]])
      (generalSubst (nv "l") (ap "var" [guardOf (nv "g"), nv "x", ap "s" [nv "k"]])
        (ap "nil" [.con "S_code"])),
    mkRule ["l", "w", "g", "w1", "h", "rest", "x", "k"]
      (ap "dsubVar" [nv "l", ap "cons" [nv "w", nv "g", ap "cons" [nv "w1", nv "h", nv "rest"]],
        nv "x", nv "k"])
      (generalSubst (nv "l")
        (ap "var" [ap "cons" [.con "N_code", nv "g", ap "cons" [.con "N_code", nv "h", nv "rest"]],
          nv "x", nv "k"])
        (ap "nil" [.con "S_code"])),
    mkRule ["a", "b"] (ap "ifL" [.con "true", nv "a", nv "b"]) (nv "a"),
    mkRule ["a", "b"] (ap "ifL" [.con "false", nv "a", nv "b"]) (nv "b"),
    mkRule ["a", "l"] (ap "lookup" [ap "lcons" [nv "a", nv "l"], zeroN]) (nv "a"),
    mkRule ["a", "l", "n"] (ap "lookup" [ap "lcons" [nv "a", nv "l"], ap "s" [nv "n"]])
      (ap "lookup" [nv "l", nv "n"]),
    mkRule ["e"] (ap "unMax" [ap "Max" [nv "e"]]) (nv "e"),
    mkRule ["l", "w"] (ap "dsubSet" [nv "l", ap "nil" [nv "w"]]) (ap "nil" [.con "S_code"]),
    mkRule ["l", "w", "o", "e"] (ap "dsubSet" [nv "l", ap "cons" [nv "w", nv "o", nv "e"]])
      (ap "Fold" [.con "Add", ap "dsubSub" [nv "l", nv "o"], ap "dsubSet" [nv "l", nv "e"]]),
    mkRule ["l", "g", "c"] (ap "dsubSub" [nv "l", ap "cst" [nv "g", nv "c"]])
      (ap "guardAll" [nv "l", nv "g", singletonSet (ap "cst" [ap "nil" [.con "N_code"], nv "c"])]),
    mkRule ["l", "g", "x", "k"] (ap "dsubSub" [nv "l", ap "var" [nv "g", nv "x", nv "k"]])
      (ap "guardAll" [nv "l", nv "g", ap "IncrN" [nv "k", ap "unMax" [ap "lookup" [nv "l", nv "x"]]]]),
    mkRule ["l", "w", "e"] (ap "guardAll" [nv "l", ap "nil" [nv "w"], nv "e"]) (nv "e"),
    mkRule ["l", "w", "g", "rest", "e"] (ap "guardAll" [nv "l", ap "cons" [nv "w", nv "g", nv "rest"], nv "e"])
      (ap "guardAll" [nv "l", nv "rest", ap "Guard" [nv "e", ap "unMax" [ap "lookup" [nv "l", nv "g"]]]]),
    mkRule ["e"] (ap "IncrN" [zeroN, nv "e"]) (nv "e"),
    mkRule ["k", "e"] (ap "IncrN" [ap "s" [nv "k"], nv "e"]) (ap "Incr" [ap "IncrN" [nv "k", nv "e"]])]

/-! ## The Lean declarations, over a frame -/

/-- The frame variable of a declaration. -/
def frameVar : Term := nv "fr"

/-- `|α|`, the first level variable of a declaration, read in its frame. -/
def alphaIn : Term := subIn frameVar (varCode zeroN)

/-- `|β|`, the second level variable of a declaration, read in its frame. -/
def betaIn : Term := subIn frameVar (varCode oneN)

/-- `A → A → Prop`, at the level `level`. -/
def relationTypeIn (level code : Term) : Term := arrows [eps level code, eps level code] (U zero)

/-- `Eq[level] A x y`. -/
def eqIn (level code first second : Term) : Term := ap "Eq" [instAt [level], code, first, second]

def sigmaLeanExplicit : Sig :=
  [.const "Eq" (piN "fr" InstT (piN "A" (U alphaIn)
      (arrows [eps alphaIn (nv "A"), eps alphaIn (nv "A")] (U zero)))),
    .const "Eq_refl" (piN "fr" InstT (piN "A" (U alphaIn) (piN "a" (eps alphaIn (nv "A"))
      (eps zero (eqIn alphaIn (nv "A") (nv "a") (nv "a")))))),
    .const "Eq_rec" (piN "fr" InstT (piN "A" (U alphaIn) (piN "a" (eps alphaIn (nv "A"))
      (piN "Q" (piN "b" (eps alphaIn (nv "A"))
          (arrow (eps zero (eqIn alphaIn (nv "A") (nv "a") (nv "b"))) (U betaIn)))
        (arrow (eps betaIn (apT (nv "Q") [nv "a", ap "Eq_refl" [instAt [alphaIn], nv "A", nv "a"]]))
          (piN "b" (eps alphaIn (nv "A"))
            (piN "e" (eps zero (eqIn alphaIn (nv "A") (nv "a") (nv "b")))
              (eps betaIn (apT (nv "Q") [nv "b", nv "e"]))))))))),
    .const "PUnit" (piN "fr" InstT (U alphaIn)),
    .const "PUnit_unit" (piN "fr" InstT (eps alphaIn (ap "PUnit" [instAt [alphaIn]]))),
    .const "PUnit_rec" (piN "fr" InstT
      (piN "Q" (arrow (eps alphaIn (ap "PUnit" [instAt [alphaIn]])) (U betaIn))
        (arrow (eps betaIn (apT (nv "Q") [ap "PUnit_unit" [instAt [alphaIn]]]))
          (piN "x" (eps alphaIn (ap "PUnit" [instAt [alphaIn]]))
            (eps betaIn (apT (nv "Q") [nv "x"])))))),
    .const "Quot" (piN "fr" InstT (piN "A" (U alphaIn)
      (arrow (relationTypeIn alphaIn (nv "A")) (U alphaIn)))),
    .const "Quot_mk" (piN "fr" InstT (piN "A" (U alphaIn) (piN "R" (relationTypeIn alphaIn (nv "A"))
      (arrow (eps alphaIn (nv "A")) (eps alphaIn (ap "Quot" [instAt [alphaIn], nv "A", nv "R"])))))),
    .const "Quot_lift" (piN "fr" InstT (piN "A" (U alphaIn)
      (piN "R" (relationTypeIn alphaIn (nv "A")) (piN "B" (U betaIn)
        (piN "f" (arrow (eps alphaIn (nv "A")) (eps betaIn (nv "B")))
          (arrow (piN "x" (eps alphaIn (nv "A")) (piN "y" (eps alphaIn (nv "A"))
              (arrow (eps zero (apT (nv "R") [nv "x", nv "y"]))
                (eps zero (eqIn betaIn (nv "B") (apT (nv "f") [nv "x"]) (apT (nv "f") [nv "y"]))))))
            (arrow (eps alphaIn (ap "Quot" [instAt [alphaIn], nv "A", nv "R"]))
              (eps betaIn (nv "B"))))))))),
    .const "id" (piN "fr" InstT (piN "A" (U alphaIn)
      (arrow (eps alphaIn (nv "A")) (eps alphaIn (nv "A")))))]

/-- `Eq.rec fr A a Q h _ (Eq.refl fr' A' a') ↪ h`, linearised as in Section 6. -/
def eqRecRuleExplicit : RewriteRule :=
  mkRule ["fr", "A", "a", "Q", "h", "w", "fr1", "A1", "a1"]
    (ap "Eq_rec" [nv "fr", nv "A", nv "a", nv "Q", nv "h", nv "w",
      ap "Eq_refl" [nv "fr1", nv "A1", nv "a1"]])
    (nv "h")

/-- `PUnit.rec fr Q h x ↪ h`. -/
def punitRecRuleExplicit : RewriteRule :=
  mkRule ["fr", "Q", "h", "x"] (ap "PUnit_rec" [nv "fr", nv "Q", nv "h", nv "x"]) (nv "h")

/-- `lift fr A R B f h (class fr' A' R' a) ↪ f a`. -/
def quotLiftRuleExplicit : RewriteRule :=
  mkRule ["fr", "A", "R", "B", "f", "h", "fr1", "A1", "R1", "a"]
    (ap "Quot_lift" [nv "fr", nv "A", nv "R", nv "B", nv "f", nv "h",
      ap "Quot_mk" [nv "fr1", nv "A1", nv "R1", nv "a"]])
    (apT (nv "f") [nv "a"])

def rulesLeanExplicit : List RewriteRule :=
  [eqRecRuleExplicit, punitRecRuleExplicit, quotLiftRuleExplicit]

/-! ## The theories -/

/-- The rules of `ΣU`, corrected, and of `ΣP`. -/
def pureRulesExplicit : List RewriteRule :=
  rulesC ++ rulesBOrthogonal ++ rulesN ++ rulesSet ++ rulesS ++ rulesECorrected ++ rulesI ++ rulesP

/-- All declarations.  Those of `ΣU` and `ΣP` are the paper's, unchanged. -/
def explicitSig : Sig := pureSig ++ sigmaSubst ++ sigmaLeanExplicit

/-- All rules. -/
def explicitRules : List RewriteRule := pureRulesExplicit ++ rulesSubst ++ rulesLeanExplicit

/-- **The theory of the paper with explicit level substitution**: `ΣU`
corrected, `ΣP`, explicit substitution in place of `Σpoly`, and the
declarations of `Eq`, `PUnit`, `Quot` and `id` over a frame. -/
def leanTheoryExplicit : Theory := Theory.ofSig explicitSig explicitRules

/-- `ΣU` corrected and `ΣP`, without polymorphism. -/
def pureTheoryExplicit : Theory := Theory.ofSig pureSig pureRulesExplicit

theorem pureTheoryExplicit_extends : pureTheoryExplicit.Extends leanTheoryExplicit where
  constType := fun name type declared => by
    have here : lookupType pureSig name = some type := declared
    show lookupType (pureSig ++ sigmaSubst ++ sigmaLeanExplicit) name = some type
    rw [List.append_assoc, lookupType_append, here]
    rfl
  body := fun name term defined => by
    have here : lookupBody pureSig name = some term := defined
    show lookupBody (pureSig ++ sigmaSubst ++ sigmaLeanExplicit) name = some term
    rw [List.append_assoc, lookupBody_append, here]
    rfl
  rule := fun rule member => List.mem_append_left _ (List.mem_append_left _ member)

/-! ## Orthogonal, hence confluent -/

theorem explicitSig_closed : closedSigTest explicitSig = true := by
  decide +kernel

theorem leanTheoryExplicit_closedBodies : leanTheoryExplicit.ClosedBodies :=
  closedBodies_of_test explicitRules explicitSig_closed

theorem leanTheoryExplicit_closedTypes : leanTheoryExplicit.ClosedTypes :=
  closedTypes_of_test explicitRules explicitSig_closed

theorem explicitRules_undefinedOnLeft : undefinedOnLeftTest explicitSig explicitRules = true := by
  decide +kernel

theorem explicitRules_checked : orthogonalCheck explicitRules = true := by
  decide +kernel

/-- **The theory with explicit level substitution is orthogonal**: every rule
is left-linear and algebraic, no two left sides have a common instance, no
proper part of a left side is a redex, and the definitions are closed. -/
theorem leanTheoryExplicit_orthogonal : leanTheoryExplicit.Orthogonal :=
  orthogonal_of_check_closed explicitRules (fun _ member => member)
    leanTheoryExplicit_closedBodies (undefinedOnLeft_of_test explicitRules_undefinedOnLeft)
    explicitRules_checked

/-- **The theory with explicit level substitution is confluent.** -/
theorem leanTheoryExplicit_confluent : Confluent (Step leanTheoryExplicit) :=
  confluent_of_orthogonal leanTheoryExplicit_orthogonal

theorem pureTheoryExplicit_orthogonal : pureTheoryExplicit.Orthogonal :=
  orthogonal_of_check_closed pureRulesExplicit (fun _ member => member)
    (closedBodies_of_test pureRulesExplicit (by decide +kernel))
    (undefinedOnLeft_of_test (by decide +kernel)) (by decide +kernel)

theorem leanTheoryExplicit_headed : leanTheoryExplicit.Headed :=
  leanTheoryExplicit_orthogonal.leftAlgebraic.headed

theorem explicitRules_linear : ∀ rule ∈ explicitRules, (patternVars rule.lhs).Nodup :=
  fun rule member => leanTheoryExplicit_orthogonal.leftLinear rule member

theorem explicitRules_algebraic : ∀ rule ∈ explicitRules, algebraic true rule.lhs = true :=
  fun rule member => leanTheoryExplicit_orthogonal.leftAlgebraic rule member

/-- **Steps are stable under substitution**, by `Step.subst` unchanged. -/
theorem leanTheoryExplicit_step_subst {source target : Term}
    (step : Step leanTheoryExplicit source target) (index : Nat) (replacement : Term) :
    Step leanTheoryExplicit (subst index replacement source) (subst index replacement target) :=
  step.subst leanTheoryExplicit_closedBodies index replacement

/-- **Conversion is stable under substitution**, by `Conv.subst` unchanged. -/
theorem leanTheoryExplicit_conv_subst {source target : Term}
    (convertible : Conv leanTheoryExplicit source target) (index : Nat) (replacement : Term) :
    Conv leanTheoryExplicit (subst index replacement source) (subst index replacement target) :=
  convertible.subst leanTheoryExplicit_closedBodies index replacement

/-- A computed reduction of the theory, as a reduction. -/
theorem reducesExplicit_of_evaluate {fuel : Nat} {source target : Term}
    (computed : evaluate explicitSig explicitRules fuel source = target) :
    Reduces leanTheoryExplicit source target :=
  Reduces.of_evaluate explicitRules_linear computed

/-- A term on which the evaluator computes nothing is normal. -/
theorem normalExplicit_of_stepOnce {term : Term}
    (computed : stepOnce explicitSig explicitRules term = none) :
    IsNormal (Step leanTheoryExplicit) term :=
  normal_of_stepOnce explicitRules_algebraic computed

/-! ## Definitions 2–4 of the paper, translated -/

/-- The universe levels of Lean, with level variables numbered from `0`. -/
inductive LeanLevel where
  | zero
  | succ (level : LeanLevel)
  | max (first second : LeanLevel)
  | imax (first second : LeanLevel)
  | param (index : Nat)
  deriving DecidableEq, Repr

namespace LeanLevel

/-- The value of a level when the variables take the values `valuation`. -/
def eval (valuation : Nat → Nat) : LeanLevel → Nat
  | zero => 0
  | succ level => eval valuation level + 1
  | max first second => Max.max (eval valuation first) (eval valuation second)
  | imax first second =>
      if eval valuation second = 0 then 0 else Max.max (eval valuation first) (eval valuation second)
  | param index => valuation index

/-- **Lean's equivalence of levels**: equal values at every valuation of the
level variables. -/
def Equiv (first second : LeanLevel) : Prop :=
  ∀ valuation : Nat → Nat, eval valuation first = eval valuation second

/-- The level has no variable. -/
def IsClosed : LeanLevel → Bool
  | zero => true
  | succ level => IsClosed level
  | max first second => IsClosed first && IsClosed second
  | imax first second => IsClosed first && IsClosed second
  | param _ => false

/-- The only variable of the level, if any, is the variable `0`. -/
def OneVariable : LeanLevel → Bool
  | zero => true
  | succ level => OneVariable level
  | max first second => OneVariable first && OneVariable second
  | imax first second => OneVariable first && OneVariable second
  | param index => index == 0

end LeanLevel

/-- **Definition 2 of the paper**, as written: the variable numbered `i` is
`Max (cons S_code (var (nil N_code) i 0) (nil S_code))`, with the empty
guard. -/
def paperCode : LeanLevel → Term
  | .zero => zero
  | .succ level => succ (paperCode level)
  | .max first second => ap "max" [paperCode first, paperCode second]
  | .imax first second => imax (paperCode first) (paperCode second)
  | .param index => levelVariable (numeral index)

/-- **Definition 2, corrected**: the closed code `|l|` of a level, the
variable numbered `i` being `varCode i`, with its guard. -/
def code : LeanLevel → Term
  | .zero => zero
  | .succ level => succ (code level)
  | .max first second => ap "max" [code first, code second]
  | .imax first second => imax (code first) (code second)
  | .param index => varCode (numeral index)

/-- **Definition 3 of the paper**: inside a declaration whose level variables
are the Dedukti variables `parameter i`, the variable `α_i` is `v α_i i`. -/
def paperLevel (parameter : Nat → Term) : LeanLevel → Term
  | .zero => zero
  | .succ level => succ (paperLevel parameter level)
  | .max first second => ap "max" [paperLevel parameter first, paperLevel parameter second]
  | .imax first second => imax (paperLevel parameter first) (paperLevel parameter second)
  | .param index => ap "v" [parameter index, numeral index]

/-- **Definition 3, with explicit substitution**: inside a declaration with
frame `frame`, the level `l` is `sub frame |l|`. -/
def levelIn (frame : Term) (level : LeanLevel) : Term := subIn frame (code level)

/-- **Definition 4 of the paper**, declarations: `x[α₁ … αₙ] : A` becomes
`x : Π α₁ … αₙ : L, ‖A‖`. -/
def paperDecl : Nat → Term → Term
  | 0, type => type
  | count + 1, type => .pi L (paperDecl count type)

/-- **Definition 4 of the paper**, uses: `x[l₁ … lₙ]` becomes
`x (inst |l₁|) … (inst |lₙ|)`. -/
def paperUse (name : String) (levels : List Term) : Term :=
  apT (.con name) (levels.map instOf)

/-- **Definition 4, with explicit substitution**, declarations: `x[α⃗] : A`
becomes `x : Π fr : Inst, ‖A‖`, the levels of `‖A‖` read in `fr`. -/
def explicitDecl (type : Term) : Term := .pi InstT type

/-- **Definition 4, with explicit substitution**, uses at the top level:
`x[l₁ … lₙ]` becomes `x (inst [|l₁|, …, |lₙ|])`. -/
def useTop (name : String) (levels : List LeanLevel) : Term :=
  ap name [instAt (levels.map code)]

/-- **Definition 4, with explicit substitution**, uses inside a declaration
with frame `frame`: `x[l₁ … lₙ]` becomes `x (inst [sub frame |l₁|, …])`. -/
def useIn (frame : Term) (name : String) (levels : List LeanLevel) : Term :=
  ap name [instAt (levels.map (levelIn frame))]

/-- The variables of the declarations are written by Definition 3. -/
theorem alphaIn_eq : alphaIn = levelIn frameVar (.param 0) := rfl

theorem betaIn_eq : betaIn = levelIn frameVar (.param 1) := rfl

/-- The uses inside the declarations are written by Definition 4. -/
theorem eqIn_alpha (code first second : Term) :
    eqIn alphaIn code first second =
      apT (useIn frameVar "Eq" [.param 0]) [code, first, second] := rfl

/-- **The declared types are `v`-free**: no declaration of the theory
mentions `v`. -/
theorem explicitSig_v_free :
    (explicitSig.all fun declaration => match declaration with
      | .const _ type => !(constantsOf type).contains "v"
      | .defn _ type body => !(constantsOf type).contains "v" && !(constantsOf body).contains "v") =
      true := by
  decide +kernel

#print axioms orthogonal_of_check_closed
#print axioms rulesE_eq_paper
#print axioms leanTheoryExplicit_orthogonal
#print axioms leanTheoryExplicit_confluent
#print axioms leanTheoryExplicit_closedBodies
#print axioms leanTheoryExplicit_closedTypes
#print axioms leanTheoryExplicit_headed
#print axioms leanTheoryExplicit_step_subst
#print axioms leanTheoryExplicit_conv_subst
#print axioms pureTheoryExplicit_orthogonal
#print axioms explicitSig_v_free

end Mettapedia.GSLT.Dedukti.LeanMinus
