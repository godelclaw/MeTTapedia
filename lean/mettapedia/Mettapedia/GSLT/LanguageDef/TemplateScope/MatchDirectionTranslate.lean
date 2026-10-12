import Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionCoverExamples

/-!
# Template scope: from rule M with both sides to lexical fresh with pattern-only

`toLexical` keeps the matching direction (`runDir_toLexical`): rule M with both
sides goes, exactly, to lexical fresh with both sides.  This module asks for
more: lexical fresh with *pattern-only*, each value-side filling written out.

## The extension

`Src.fillUnify` rewrites a plain `let` or a `unify` whose pattern is data
(nothing to bind on the pattern side) and whose value is open data (it
evaluates to itself, and the text shows its shape) as `unify` with the sides
exchanged.  `toLexicalFill` is `toLexical` after it.  The rewriting is the law
`stepDir_let_data_exchange`, one unfolding at a time.

## Results

* `fill_valueSide`, `fill_through_parameter` — on the first-order row, and on a
  `let` whose value arrives through a parameter, rule M with both sides and
  lexical fresh with pattern-only on the translation give the same bag.  A
  crossing set spells it too (`crossing_spelling`).
* `not_run_toLexicalFill` — **the statement of `run_toLexical` for it is false**:
  `mixedFill` is a `let` that must fill a name on each side at once, with the
  value arriving through a parameter.  Rule M with both sides answers
  `(Got 0 a)`; lexical fresh with pattern-only answers nothing on the
  translation, and on the `let` with its sides exchanged
  (`mixedFill_no_patternOnly_spelling`).  Pattern-only writes no store name when
  the value is not ground (`letCont_nonground_store`), and here neither side is.
* `let_is_not_unify_LF` — under lexical fresh a `let` is not `unify`, at either
  direction; under rule M it is (`answersDirCfg_letToUnify`).
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v

variable {S : Type u} {X : Type v}

namespace Src

/-- Data: symbols and data application. -/
def isData : Src S X → Bool
  | .sym _ => true
  | .app f a => f.isData && a.isData
  | _ => false

/-- Open data: symbols, store names, parameters, and data application of such
under a symbol.  It evaluates to itself, and the text shows its shape.  `head`
is true on the function side of an application, where only a symbol-headed
spine is data. -/
def openDataAt (head : Bool) : Src S X → Bool
  | .sym _ => true
  | .sv _ => !head
  | .par _ => !head
  | .app f a => openDataAt true f && openDataAt false a
  | _ => false

/-- **Write each value-side filling the text shows as a `unify` with the sides
exchanged**: a plain `let`, or a `unify`, whose pattern is data and whose value
is open data.  Every other form is kept. -/
def fillUnify : Src S X → Src S X
  | .lam z xs b => .lam z xs (fillUnify b)
  | .app f a => .app (fillUnify f) (fillUnify a)
  | .letS p w b none =>
      if p.isData && w.openDataAt false then .unify w p (fillUnify b)
      else .letS p (fillUnify w) (fillUnify b) none
  | .letS p w b (some sh) => .letS p (fillUnify w) (fillUnify b) (some sh)
  | .unify p w b =>
      if p.isData && w.openDataAt false then .unify w p (fillUnify b)
      else .unify p (fillUnify w) (fillUnify b)
  | .alt t₁ t₂ => .alt (fillUnify t₁) (fillUnify t₂)
  | .new ys b => .new ys (fillUnify b)
  | .form z b => .form z (fillUnify b)
  | t => t

end Src

variable [DecidableEq X]

/-- **The extended translator**: value-side fillings written as `unify`, then
rule M's binding structure written into lexical fresh. -/
def toLexicalFill (t : Src S X) : Src S X := toLexical (Src.fillUnify t)

/-- The extended translation of a program's equations. -/
def toLexicalFillProg (cl : S → Option (Src S X)) : S → Option (Src S X) :=
  toLexicalProg fun F => (cl F).map Src.fillUnify

end Mettapedia.GSLT.LanguageDef.TemplateScope

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionExamples

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot

/-- Lexical fresh with pattern-only on the extended translation, in the identity
model. -/
def fillLF (cl : DSym → Option A) (t : A) : Option (List (Tm DSym (BId DSp))) :=
  answers .static (progLF .u .unit (toLexicalFillProg cl)) 80 (elabLFFormAt [] (toLexicalFill t))

/-! ## Where the text shows the filling -/

/-- **The first-order row.**  The extension writes
`(let (f a) (f $x) (Got $x))` as `(unify (f $x) (f a) (Got $x))`.  Rule M with
both sides on the source, and lexical fresh with pattern-only on the
translation, give `(Got a)`, in both models. -/
theorem fill_valueSide :
    toLexicalFill valueSide = unifyPattern ∧
      idM .bothSides noCl valueSide = some [gotA] ∧ fillLF noCl valueSide = some [gotA] ∧
      slotAns cfgM.bothSides noCl valueSide = some [gotA] ∧
      slotAns cfgLF.patternOnly (toLexicalFillProg noCl) (toLexicalFill valueSide) =
        some [gotA] := by
  and_intros <;> decide +kernel

/-- `(let (f $x) (f a) (Got $x)){$x}`: a `let` whose crossing set shares `$x`. -/
def crossLet : A := .letS (fOf (nm .x)) (fOf (k .a)) (got1 (nm .x)) (some [.x])

/-- **A crossing set spells it too**: under lexical fresh and pattern-only, the
`let` with the sides exchanged and `$x` in its crossing set gives `(Got a)`. -/
theorem crossing_spelling :
    slotAns cfgLF.patternOnly noCl crossLet = some [gotA] ∧
      idLF .patternOnly noCl crossLet = some [gotA] := by
  and_intros <;> decide +kernel

/-- `((lam w (let (f a) w (Got $x))) (f $x))`: the value of the `let` arrives
through the parameter `w`. -/
def throughPar : A :=
  ap (.lam .w none (.letS (fOf (k .a)) (.par .w) (got1 (nm .x)) none)) (fOf (nm .x))

/-- **A value that arrives through a parameter**, against a data pattern: the
extension exchanges the sides inside the lambda, and the two runs agree. -/
theorem fill_through_parameter :
    Src.fillUnify throughPar =
        ap (.lam .w none (.unify (.par .w) (fOf (k .a)) (got1 (nm .x)))) (fOf (nm .x)) ∧
      idM .bothSides noCl throughPar = some [gotA] ∧ fillLF noCl throughPar = some [gotA] ∧
      idM .patternOnly noCl throughPar = some [] := by
  and_intros <;> decide +kernel

/-! ## Where it does not -/

/-- `(Got 0 a)`. -/
def got0A {Y : Type} : Tm DSym Y := .app (.app (.sym .Got) (.sym .n0)) (.sym .a)

/-- `((lam w (let (pair $x a) w (Got $x $y))) (pair 0 $y))`: the `let` must bind
`$x` from the value and `$y` from the pattern, and its value arrives through a
parameter. -/
def mixedFill : A :=
  ap (.lam .w none (.letS (pairOf (nm .x) (k .a)) (.par .w) (got2 (nm .x) (nm .y)) none))
    (pairOf (k .n0) (nm .y))

/-- The same with the sides of the `let` exchanged. -/
def mixedFillExchanged : A :=
  ap (.lam .w none (.unify (.par .w) (pairOf (nm .x) (k .a)) (got2 (nm .x) (nm .y))))
    (pairOf (k .n0) (nm .y))

theorem mixedFill_admissible : mixedFill.Admissible := by decide +kernel

/-- The extension leaves it as written: its pattern is not data. -/
theorem fillUnify_mixedFill : Src.fillUnify mixedFill = mixedFill := by decide +kernel

/-- **Both sides fills a name on each side**: `(Got 0 a)`, in both models. -/
theorem mixedFill_bothSides :
    slotAns cfgM.bothSides noCl mixedFill = some [got0A] ∧
      idM .bothSides noCl mixedFill = some [got0A] := by
  and_intros <;> decide +kernel

/-- **Pattern-only has no spelling of it at the `let`.**  As written, and with
the sides exchanged, under rule M and under lexical fresh: no answer.  At the
match neither side is ground, and pattern-only writes no store name when the
value is not ground (`letCont_nonground_store`). -/
theorem mixedFill_no_patternOnly_spelling :
    slotAns cfgM.patternOnly noCl mixedFill = some [] ∧
      slotAns cfgLF.patternOnly noCl mixedFill = some [] ∧
    slotAns cfgM.patternOnly noCl mixedFillExchanged = some [] ∧
      slotAns cfgLF.patternOnly noCl mixedFillExchanged = some [] := by
  and_intros <;> decide +kernel

/-- **The statement of `run_toLexical` for the extended translator is false.**
The goal that fails: for every query, rule M with both sides on the source and
lexical fresh with pattern-only on the extended translation have the same
answers.  On `mixedFill` the first is `(Got 0 a)` and the second is empty. -/
theorem not_run_toLexicalFill :
    ¬ ∀ (t : A) (n : ℕ),
      answersDir .bothSides .static (progM .u .unit noCl) n (elabMFormAt [] t) =
        answers .static (progLF .u .unit (toLexicalFillProg noCl)) n
          (elabLFFormAt [] (toLexicalFill t)) := by
  intro h
  have h80 := h mixedFill 80
  have e₁ : answersDir .bothSides .static (progM .u .unit noCl) 80 (elabMFormAt [] mixedFill) =
      some [got0A] := by decide +kernel
  have e₂ : answers .static (progLF .u .unit (toLexicalFillProg noCl)) 80
      (elabLFFormAt [] (toLexicalFill mixedFill)) = some [] := by decide +kernel
  rw [e₁, e₂] at h80
  exact absurd h80 (by decide)

/-! ## `let` and `unify` under lexical fresh -/

/-- `(let $x a (let $x 0 ok))`. -/
def letTwice : A := .letS (nm .x) (k .a) (.letS (nm .x) (k .n0) (k .ok) none) none

/-- `(let $x a (unify $x 0 ok))`. -/
def letThenUnify : A := .letS (nm .x) (k .a) (.unify (nm .x) (k .n0) (k .ok)) none

/-- **Under lexical fresh a `let` is not `unify`**, at either direction: the
inner `let` introduces a new `$x` and answers `ok`; the inner `unify` refines
the `$x` in scope, which holds `a`, and answers nothing.  Under rule M both
answer nothing: there a plain `let` is `unify`. -/
theorem let_is_not_unify_LF :
    slotAns cfgLF.patternOnly noCl letTwice = some [.sym .ok] ∧
      slotAns cfgLF.patternOnly noCl letThenUnify = some [] ∧
    slotAns cfgLF.bothSides noCl letTwice = some [.sym .ok] ∧
      slotAns cfgLF.bothSides noCl letThenUnify = some [] ∧
    slotAns cfgM.patternOnly noCl letTwice = some [] ∧
      slotAns cfgM.patternOnly noCl letThenUnify = some [] ∧
    slotAns cfgM.bothSides noCl letTwice = some [] ∧
      slotAns cfgM.bothSides noCl letThenUnify = some [] ∧
    Src.letToUnify letTwice = .unify (nm .x) (k .a) (.unify (nm .x) (k .n0) (k .ok)) := by
  and_intros <;> decide +kernel

end Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionExamples
