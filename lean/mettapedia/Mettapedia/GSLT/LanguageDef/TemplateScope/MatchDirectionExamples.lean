import Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionFrame
import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotExamples

/-!
# Template scope: the two matching directions on examples

Kernel-checked answers under pattern-only and under both sides, in the slot
model and in the identity model, under rule M and under lexical fresh.

* `valueSide_patternOnly`, `valueSide_bothSides` —
  `(let (f a) (f $x) (Got $x))`: no answer under pattern-only, `(Got a)` under
  both sides.
* `patternSide_agree` — `(let (f $x) (f a) (Got $x))`: `(Got a)` under both.
* `leak_patternOnly_eq`, `leak_bothSides`, `leak_never_bare` —
  `(let (quote (lam w w)) (quote (lam z $hole)) (Got escaped $hole))`: no answer
  under pattern-only (the shipped `leak_answers`), `(Got escaped (quote z (z)))`
  under both sides, and never the bare `(Got escaped z)`.  `act_var_ne_pvar`: no
  store name ever reads as a bare parameter.
* `holeFill_part`, `holeFill_ground`, `holeFill_reads_store`,
  `holeFill_refuses_unbound` — what a hole of value code takes: the aligned
  pattern part as contextual code, a ground part as it is, a part read under
  the store, and nothing when a store name of the part is unbound.
* `different_nonempty_bags`, `bags_eq_of_length_eq` — a program on which the two
  readings give different non-empty bags; and, in general, two bags of the same
  length are equal.
* `twoNames_no_answer`, `oneName_substitutes`, `order_of_components` — two
  unbound names: no match when nested, substitution when the pattern is one
  name; and the order of the components decides whether a both-sides match
  over ground stores succeeds.
* `unify_patternOnly_one_sided` — the model's `unify` is one-sided under
  pattern-only.
* `frame_fails_bothSides`, `frame_needs_no_parameter`,
  `frame_needs_no_quotation_hole` — the frame of a `let`: its failure under both
  sides, and the two side conditions of `let_frame_LF_introduced`.
* `rebind_no_answer`, `rebind_never_substitutes` — under rule M, a `let` whose
  pattern is one name that already holds a value, against a value that is not
  ground, is a match of the stored value against the new one.  On
  `(let $x a (let $x (f $y) (Got $x)))` there is no answer under either
  reading, and `(Got (f $y))` is the answer at no fuel.
* `rebindFill_answers`, `rebindLam_no_answer`, `lamTwice_no_answer`,
  `aliasThenGround_answers`, `sameTwice_answers`, `lamThenGround_no_answer`,
  `openThenGround_answers` — seven more rows on a name that is bound twice.
  The two readings differ on one: `(let $x (f a) (let $x (f $y) (Got $x $y)))`
  gives no answer under pattern-only and `(Got (f a) a)` under both sides.
* `rebindCross_no_answer`, `rebindLamCross_no_answer`,
  `openThenGroundCross_answers` — under lexical fresh, with the name in the
  crossing set of the inner `let`.  `rebind_lexicalFresh_own_name` — with no
  crossing set the inner `let` has its own name, unbound, and substitutes.
* `not_run_letP_lam_any_store`, `not_step_letP_some_any_store`,
  `not_run_elabTopM_inline_any_store` — the three statements that held before
  the correction without the hypothesis that the `let`'s name is unbound are
  false: `$f` holds `1`, `(let $f (lam z z) (Got ($f 2)))` gives no answer, and
  the substituted body answers `(Got 2)`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionExamples

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotExamples
open Mettapedia.GSLT.LanguageDef.TemplateScope.Bridge

/-- Symbols of the examples; `unit` is the clause wrapper's argument. -/
inductive DSym where
  | f | a | pair | Got | ok | n0 | n1 | n2 | unit | F
  deriving DecidableEq, Repr

/-- Spellings of the examples; `u` is the clause wrapper's parameter. -/
inductive DSp where
  | x | y | z | w | m | h | f | u
  deriving DecidableEq, Repr

/-- Authored text of the examples. -/
abbrev A := Src DSym DSp

/-- No equations. -/
def noCl : DSym → Option A := fun _ => none

def k (s : DSym) : A := .sym s
def nm (v : DSp) : A := .sv v
def ap (g a : A) : A := .app g a
def fOf (a : A) : A := ap (k .f) a
def got1 (a : A) : A := ap (k .Got) a
def got2 (a b : A) : A := ap (ap (k .Got) a) b
def pairOf (a b : A) : A := ap (ap (k .pair) a) b

/-- Answers in the slot model, under a configuration and its direction. -/
def slotAns (c : DirConfig) (cl : DSym → Option A) (t : A) :
    Option (List (Tm DSym (Slot DSp))) :=
  answersDirCfg c (progSlot c.scope .u .unit cl) 80 t

/-- Answers in the identity model, rule M. -/
def idM (dir : Direction) (cl : DSym → Option A) (t : A) : Option (List (Tm DSym (BId DSp))) :=
  answersDir dir .static (progM .u .unit cl) 80 (elabMFormAt [] t)

/-- Answers in the identity model, lexical fresh. -/
def idLF (dir : Direction) (cl : DSym → Option A) (t : A) : Option (List (Tm DSym (BId DSp))) :=
  answersDir dir .static (progLF .u .unit cl) 80 (elabLFFormAt [] t)

/-- At pattern-only, `slotAns` is the shipped `answersCfg`. -/
theorem slotAns_patternOnly (c : Config) (cl : DSym → Option A) (t : A) :
    slotAns c.patternOnly cl t = answersCfg c (progSlot c .u .unit cl) 80 t :=
  answersDirCfg_patternOnly c _ 80 t

/-- `(Got a)`. -/
def gotA {Y : Type} : Tm DSym Y := .app (.sym .Got) (.sym .a)

/-! ## The first-order rows -/

/-- `(let (f a) (f $x) (Got $x))`: the unbound name is on the value side. -/
def valueSide : A := .letS (fOf (k .a)) (fOf (nm .x)) (got1 (nm .x)) none

/-- `(let (f $x) (f a) (Got $x))`: the unbound name is on the pattern side. -/
def patternSide : A := .letS (fOf (nm .x)) (fOf (k .a)) (got1 (nm .x)) none

/-- **Pattern-only does not fill the value side**: no answer, in both models,
under rule M and under lexical fresh. -/
theorem valueSide_patternOnly :
    slotAns cfgM.patternOnly noCl valueSide = some [] ∧
      slotAns cfgLF.patternOnly noCl valueSide = some [] ∧
      idM .patternOnly noCl valueSide = some [] ∧ idLF .patternOnly noCl valueSide = some [] := by
  and_intros <;> decide +kernel

/-- **Both sides fills it**: `(Got a)`, in both models, under rule M and under
lexical fresh. -/
theorem valueSide_bothSides :
    slotAns cfgM.bothSides noCl valueSide = some [gotA] ∧
      slotAns cfgLF.bothSides noCl valueSide = some [gotA] ∧
      idM .bothSides noCl valueSide = some [gotA] ∧ idLF .bothSides noCl valueSide = some [gotA] := by
  and_intros <;> decide +kernel

/-- **A name on the pattern side is bound under both readings**: `(Got a)`. -/
theorem patternSide_agree :
    slotAns cfgM.patternOnly noCl patternSide = some [gotA] ∧
      slotAns cfgLF.patternOnly noCl patternSide = some [gotA] ∧
      idM .patternOnly noCl patternSide = some [gotA] ∧
      idLF .patternOnly noCl patternSide = some [gotA] ∧
    slotAns cfgM.bothSides noCl patternSide = some [gotA] ∧
      slotAns cfgLF.bothSides noCl patternSide = some [gotA] ∧
      idM .bothSides noCl patternSide = some [gotA] ∧
      idLF .bothSides noCl patternSide = some [gotA] := by
  and_intros <;> decide +kernel

/-! ## The code row -/

/-- The leak, in the slot model, under a configuration and its direction. -/
def leakSlot (c : DirConfig) : Option (List (Tm LeakSym (Slot LeakSp))) :=
  answersDirCfg c (progSlot c.scope .u .unit noLeak) 80 leak

/-- The leak, in the identity model, rule M. -/
def leakIdMDir (dir : Direction) : Option (List (Tm LeakSym (BId LeakSp))) :=
  answersDir dir .static (progM .u .unit noLeak) 80 (elabMFormAt [] leak)

/-- The leak, in the identity model, lexical fresh. -/
def leakIdLFDir (dir : Direction) : Option (List (Tm LeakSym (BId LeakSp))) :=
  answersDir dir .static (progLF .u .unit noLeak) 80 (elabLFFormAt [] leak)

/-- `(Got escaped (quote z (z)))`: the hole holds the code `z` under the
binder `z` of the value. -/
def leakCtx : SExp (SAtom LeakSym LeakSp) :=
  .list [.atom (.sym .Got), .atom (.sym .escaped),
    .list [.atom (.kw .quote), .atom (.par .z), .list [.atom (.par .z)]]]

/-- **The shipped renderer spells that answer as the C text.** -/
theorem leakCtx_text :
    (leakCtx.render leakAtom (fun _ => false)).toList =
      "(Got escaped (quote z (z)))".toList := by
  simp [leakCtx, SExp.render, SExp.renderList, SExp.renderSeq, leakAtom, leakSymText,
    leakSpText, kwText]

/-- At pattern-only these are the shipped runs of the leak, which answer nothing
(`leak_answers`) and so not the bare name (`leak_not_bare`). -/
theorem leak_patternOnly_eq :
    leakSlot cfgM.patternOnly = leakSlotM ∧ leakSlot cfgLF.patternOnly = leakSlotLF ∧
      leakIdMDir .patternOnly = leakIdM ∧ leakIdLFDir .patternOnly = leakIdLF :=
  ⟨answersDirCfg_patternOnly _ _ _ _, answersDirCfg_patternOnly _ _ _ _,
    answersDir_patternOnly _ _ _ _, answersDir_patternOnly _ _ _ _⟩

/-- **Both sides fills it with contextual code**: `(Got escaped (quote z (z)))`,
in both models, under rule M and under lexical fresh. -/
theorem leak_bothSides :
    (leakSlot cfgM.bothSides).map (List.map leakPrintSlot) = some [leakCtx] ∧
      (leakSlot cfgLF.bothSides).map (List.map leakPrintSlot) = some [leakCtx] ∧
      (leakIdMDir .bothSides).map (List.map leakPrintId) = some [leakCtx] ∧
      (leakIdLFDir .bothSides).map (List.map leakPrintId) = some [leakCtx] := by
  and_intros <;> decide +kernel

/-- **Not the bare name under both sides either**: in neither model, under
neither profile, is the answer `(Got escaped z)`. -/
theorem leak_never_bare :
    (leakSlot cfgM.bothSides).map (List.map leakPrintSlot) ≠ some [leakBare] ∧
      (leakSlot cfgLF.bothSides).map (List.map leakPrintSlot) ≠ some [leakBare] ∧
      (leakIdMDir .bothSides).map (List.map leakPrintId) ≠ some [leakBare] ∧
      (leakIdLFDir .bothSides).map (List.map leakPrintId) ≠ some [leakBare] := by
  and_intros <;> decide +kernel

/-- **No store name reads as a bare parameter**, whatever the store: a cell
holds a ground value, and a parameter is not one.  A hole is therefore never
answered by the bare name of a binder. -/
theorem act_var_ne_pvar {S X : Type} [DecidableEq X] (σ : GStore S X) (n x : Nm X) :
    act σ (.var n) ≠ .pvar x := by
  rw [act_var]
  cases σ n with
  | none => simp
  | some g => cases g <;> simp [GVal.toTm]

/-! ## What a hole of value code takes -/

/-- The value's binder `z`, as the slot model names it. -/
def zS : Nm (Slot DSp) := .src (codeBinder [], .z)

/-- `(let (quote (lam w (f w))) (quote (lam z $h)) (Got $h))`. -/
def fillPart : A :=
  .letS (.pquote (.lam .w none (fOf (.par .w)))) (.quote (.lam .z none (nm .h)))
    (got1 (nm .h)) none

/-- `(let (quote (lam w a)) (quote (lam z $h)) (Got $h))`. -/
def fillGround : A :=
  .letS (.pquote (.lam .w none (k .a))) (.quote (.lam .z none (nm .h))) (got1 (nm .h)) none

/-- `(let (quote (lam w (pair w $x))) (quote (lam z $h)) (Got $h))`: the pattern
part has the store name `$x`. -/
def fillOpen : A :=
  .letS (.pquote (.lam .w none (pairOf (.par .w) (nm .x)))) (.quote (.lam .z none (nm .h)))
    (got1 (nm .h)) none

/-- `(let $x a …)` around it: `$x` holds `a` when the hole is filled. -/
def fillRead : A := .letS (nm .x) (k .a) fillOpen none

/-- **The aligned pattern part, as contextual code**: the hole takes `(f w)`
read along the value's binder, `(quote (f z) (z))`. -/
theorem holeFill_part :
    slotAns cfgM.bothSides noCl fillPart =
        some [.app (.sym .Got) (.ctx [zS] (.app (.sym .f) (.pvar zS)))] ∧
      slotAns cfgLF.bothSides noCl fillPart =
        some [.app (.sym .Got) (.ctx [zS] (.app (.sym .f) (.pvar zS)))] ∧
      slotAns cfgM.patternOnly noCl fillPart = some [] := by
  and_intros <;> decide +kernel

/-- **A ground part, as it is**: the hole takes `a`. -/
theorem holeFill_ground :
    slotAns cfgM.bothSides noCl fillGround = some [gotA] ∧
      idM .bothSides noCl fillGround = some [gotA] ∧
      slotAns cfgM.patternOnly noCl fillGround = some [] := by
  and_intros <;> decide +kernel

/-- **A part is read under the store**: with `$x` holding `a`, the hole takes
`(quote (pair z a) (z))`. -/
theorem holeFill_reads_store :
    slotAns cfgM.bothSides noCl fillRead =
        some [.app (.sym .Got) (.ctx [zS] (.app (.app (.sym .pair) (.pvar zS)) (.sym .a)))] ∧
      slotAns cfgLF.bothSides noCl fillRead =
        some [.app (.sym .Got) (.ctx [zS] (.app (.app (.sym .pair) (.pvar zS)) (.sym .a)))] := by
  and_intros <;> decide +kernel

/-- **A part with an unbound store name is refused**: no answer.  A cell holds
no store name, in code or out of it. -/
theorem holeFill_refuses_unbound :
    slotAns cfgM.bothSides noCl fillOpen = some [] ∧
      slotAns cfgLF.bothSides noCl fillOpen = some [] ∧
      idM .bothSides noCl fillOpen = some [] ∧ idLF .bothSides noCl fillOpen = some [] := by
  and_intros <;> decide +kernel

/-! ## Different non-empty bags -/

/-- `(superpose ((let (f a) (f $x) (Got $x)) ok))`. -/
def altRow : A := .alt valueSide (k .ok)

/-- **A program on which the two readings give different non-empty bags**:
`[ok]` under pattern-only, `[(Got a), ok]` under both sides. -/
theorem different_nonempty_bags :
    slotAns cfgM.patternOnly noCl altRow = some [.sym .ok] ∧
      slotAns cfgM.bothSides noCl altRow = some [gotA, .sym .ok] ∧
    slotAns cfgLF.patternOnly noCl altRow = some [.sym .ok] ∧
      slotAns cfgLF.bothSides noCl altRow = some [gotA, .sym .ok] := by
  and_intros <;> decide +kernel

/-- **Two bags of the same length are equal.**  Both sides only adds answers
(`answers_sublist_answersDir`), so the readings never give two different bags
of one size. -/
theorem bags_eq_of_length_eq {S X : Type} [DecidableEq S] [DecidableEq X] [CodeId X]
    (d : Disc) (prog : S → Option (Tm S X)) (n : ℕ) (t : Tm S X) {bag bag' : List (Tm S X)}
    (h : answers d prog n t = some bag) (h' : answersDir .bothSides d prog n t = some bag')
    (hl : bag.length = bag'.length) : bag = bag' :=
  (answers_sublist_answersDir d prog n t h h').eq_of_length hl

/-! ## Two unbound names -/

/-- `(let (f $x) (f $y) (Got $x $y))`: two unbound names inside a pattern. -/
def twoNames : A := .letS (fOf (nm .x)) (fOf (nm .y)) (got2 (nm .x) (nm .y)) none

/-- **Two unbound names inside a pattern do not match**, under either reading:
no ground binding relates them. -/
theorem twoNames_no_answer :
    slotAns cfgM.patternOnly noCl twoNames = some [] ∧
      slotAns cfgLF.patternOnly noCl twoNames = some [] ∧
    slotAns cfgM.bothSides noCl twoNames = some [] ∧
      slotAns cfgLF.bothSides noCl twoNames = some [] ∧
      idM .bothSides noCl twoNames = some [] ∧ idLF .bothSides noCl twoNames = some [] := by
  and_intros <;> decide +kernel

/-- `(let $x $y (Got $x))`: the pattern is one name, the value an unbound
name. -/
def oneName : A := .letS (nm .x) (nm .y) (got1 (nm .x)) none

/-- **A pattern that is one name, unbound in the store, takes a value that is
not ground by substitution**, under either reading: `(Got $y)`. -/
theorem oneName_substitutes :
    slotAns cfgM.patternOnly noCl oneName = some [.app (.sym .Got) (.var (.src ([], .y)))] ∧
      slotAns cfgLF.patternOnly noCl oneName = some [.app (.sym .Got) (.var (.src ([], .y)))] ∧
    slotAns cfgM.bothSides noCl oneName = some [.app (.sym .Got) (.var (.src ([], .y)))] ∧
      slotAns cfgLF.bothSides noCl oneName = some [.app (.sym .Got) (.var (.src ([], .y)))] := by
  and_intros <;> decide +kernel

/-- `(let (pair $x a) (pair $y $x) (Got $x $y))`. -/
def orderFirst : A :=
  .letS (pairOf (nm .x) (k .a)) (pairOf (nm .y) (nm .x)) (got2 (nm .x) (nm .y)) none

/-- `(let (pair a $x) (pair $x $y) (Got $x $y))`: the same two equations, the
components in the other order. -/
def orderSecond : A :=
  .letS (pairOf (k .a) (nm .x)) (pairOf (nm .x) (nm .y)) (got2 (nm .x) (nm .y)) none

/-- **The order of the components decides.**  Under rule M and both sides, the
equations `x = y`, `x = a` in that order give no answer: the first meets two
unbound names.  In the other order they give `(Got a a)`.  A pattern-only match
is a refinement run of ground steps (`matchT_eq_refineRun`), which no order
changes (`run_empty_perm`); a both-sides match over ground stores is not. -/
theorem order_of_components :
    slotAns cfgM.bothSides noCl orderFirst = some [] ∧
      slotAns cfgM.bothSides noCl orderSecond =
        some [.app (.app (.sym .Got) (.sym .a)) (.sym .a)] ∧
    idM .bothSides noCl orderFirst = some [] ∧
      idM .bothSides noCl orderSecond = some [.app (.app (.sym .Got) (.sym .a)) (.sym .a)] ∧
    slotAns cfgM.patternOnly noCl orderFirst = some [] ∧
      slotAns cfgM.patternOnly noCl orderSecond = some [] := by
  and_intros <;> decide +kernel

/-! ## `unify` -/

/-- `(unify (f a) (f $x) (Got $x))`. -/
def unifyValue : A := .unify (fOf (k .a)) (fOf (nm .x)) (got1 (nm .x))

/-- `(unify (f $x) (f a) (Got $x))`. -/
def unifyPattern : A := .unify (fOf (nm .x)) (fOf (k .a)) (got1 (nm .x))

/-- **The model's `unify` is one-sided under pattern-only.**  With the unbound
name on the value side it gives no answer; with the sides exchanged it gives
`(Got a)`.  Under both sides both give `(Got a)`. -/
theorem unify_patternOnly_one_sided :
    slotAns cfgM.patternOnly noCl unifyValue = some [] ∧
      slotAns cfgLF.patternOnly noCl unifyValue = some [] ∧
    slotAns cfgM.patternOnly noCl unifyPattern = some [gotA] ∧
      slotAns cfgLF.patternOnly noCl unifyPattern = some [gotA] ∧
    slotAns cfgM.bothSides noCl unifyValue = some [gotA] ∧
      slotAns cfgLF.bothSides noCl unifyValue = some [gotA] ∧
    slotAns cfgM.bothSides noCl unifyPattern = some [gotA] ∧
      slotAns cfgLF.bothSides noCl unifyPattern = some [gotA] := by
  and_intros <;> decide +kernel

/-! ## The frame of a `let` -/

/-- **The pattern-only frame fails under both sides.**  Under lexical fresh
and both sides, `(let (f a) (f $x) (Got $x))` leaves the query's `$x` bound to
`a`.  Its pattern `(f a)` introduces nothing and writes no store name. -/
theorem frame_fails_bothSides :
    (runDir .bothSides .static (progSlot cfgLF .u .unit noCl) 80 [] Store.empty
        (elabCfg cfgLF [] valueSide)).map (List.map fun r => r.2 (.src ([], .x))) =
      some [some (.sym .a)] ∧
    lfIntro none (fOf (k .a)) ([] : List DSp) = [] ∧ Src.direct (fOf (k .a)) = [] := by
  and_intros <;> decide +kernel

/-- `((lam z (let (f z) (f a) (Got z))) $m)`: the pattern writes a parameter,
and the call passes the unbound name `$m` for it. -/
def parWrite : A :=
  ap (.lam .z none (.letS (fOf (.par .z)) (fOf (k .a)) (got1 (.par .z)) none)) (nm .m)

/-- **A parameter in a pattern carries a name in.**  Under lexical fresh and
pattern-only, the `let` inside the lambda leaves the caller's `$m` bound to
`a`.  Its pattern `(f z)` introduces nothing and writes no store name: the name
arrives as the value of the parameter `z`.  So the frame statement needs "no
parameter of the pattern is instantiated". -/
theorem frame_needs_no_parameter :
    (run .static (progSlot cfgLF .u .unit noCl) 80 [] Store.empty
        (elabCfg cfgLF [] parWrite)).map (List.map fun r => r.2 (.src ([], .m))) =
      some [some (.sym .a)] ∧
    lfIntro none (fOf (.par .z)) ([] : List DSp) = [] ∧ Src.direct (fOf (.par .z)) = [] ∧
    slotAns cfgLF.patternOnly noCl parWrite = some [gotA] := by
  and_intros <;> decide +kernel

/-- `(let (quote (lam z $h)) (quote (lam z a)) ok)`: the pattern is a quotation
with the hole `$h`. -/
def holeWrite : A :=
  .letS (.pquote (.lam .z none (nm .h))) (.quote (.lam .z none (k .a))) (k .ok) none

/-- **A hole of a quotation pattern is not introduced.**  Under lexical fresh
and pattern-only, the `let` leaves the query's `$h` bound to `a`.  The pattern
writes `$h` and the `let` does not introduce it: `lfIntro` reads only the names
on the pattern's data spine.  So the frame statement needs "every name the
pattern writes is introduced". -/
theorem frame_needs_no_quotation_hole :
    (run .static (progSlot cfgLF .u .unit noCl) 80 [] Store.empty
        (elabCfg cfgLF [] holeWrite)).map (List.map fun r => r.2 (.src ([], .h))) =
      some [some (.sym .a)] ∧
    lfIntro none (.pquote (.lam .z none (nm .h)) : A) ([] : List DSp) = [] ∧
    Src.direct (.pquote (.lam .z none (nm .h)) : A) = [.h] := by
  and_intros <;> decide +kernel

/-! ## A pattern that is one bound name -/

/-- `(let $x a (let $x (f $y) (Got $x)))`. -/
def rebind : A := .letS (nm .x) (k .a) (.letS (nm .x) (fOf (nm .y)) (got1 (nm .x)) none) none

/-- `$y` of the query, in the slot model. -/
def yS : Tm DSym (Slot DSp) := .var (.src ([], .y))

/-- `$y` of the query, in the identity model. -/
def yI : Tm DSym (BId DSp) := .var (.src (.slot ⟨.y, [], [], .head⟩))

/-- `(Got (f t))`. -/
def gotF {Y : Type} (t : Tm DSym Y) : Tm DSym Y := .app (.sym .Got) (.app (.sym .f) t)

/-- `(Got (f a) a)`. -/
def gotFaA {Y : Type} : Tm DSym Y :=
  .app (.app (.sym .Got) (.app (.sym .f) (.sym .a))) (.sym .a)

/-- **Under rule M the inner `let` is a match, and it fails.**  `$x` holds `a`
and the new value `(f $y)` is not ground.  Pattern-only fills no name of the
value, so it gives no answer.  Both sides matches `a` against `(f $y)`, which
has no solution.  No answer, under both readings, in both models. -/
theorem rebind_no_answer :
    slotAns cfgM.patternOnly noCl rebind = some [] ∧
      slotAns cfgM.bothSides noCl rebind = some [] ∧
    idM .patternOnly noCl rebind = some [] ∧ idM .bothSides noCl rebind = some [] := by
  and_intros <;> decide +kernel

/-- **That `let` never substitutes**: at no fuel, under neither reading, in
neither model, is the answer `(Got (f $y))`. -/
theorem rebind_never_substitutes (dir : Direction) (n : ℕ) :
    answersDirCfg ⟨cfgM, dir⟩ (progSlot cfgM .u .unit noCl) n rebind ≠ some [gotF yS] ∧
      answersDir dir .static (progM .u .unit noCl) n (elabMFormAt [] rebind) ≠ some [gotF yI] := by
  obtain ⟨hSP, hSB, hIP, hIB⟩ := rebind_no_answer
  unfold slotAns answersDirCfg at hSP hSB
  unfold idM at hIP hIB
  unfold answersDirCfg
  constructor
  · intro e
    cases dir with
    | patternOnly => exact List.cons_ne_nil _ _ (answersDir_det .patternOnly (m := 80) e hSP)
    | bothSides => exact List.cons_ne_nil _ _ (answersDir_det .bothSides (m := 80) e hSB)
  · intro e
    cases dir with
    | patternOnly => exact List.cons_ne_nil _ _ (answersDir_det .patternOnly (m := 80) e hIP)
    | bothSides => exact List.cons_ne_nil _ _ (answersDir_det .bothSides (m := 80) e hIB)

/-- `(let $x (f a) (let $x (f $y) (Got $x $y)))`. -/
def rebindFill : A :=
  .letS (nm .x) (fOf (k .a)) (.letS (nm .x) (fOf (nm .y)) (got2 (nm .x) (nm .y)) none) none

/-- **The stored value fills the new one under both sides.**  `$x` holds
`(f a)` and the new value is `(f $y)`.  Pattern-only gives no answer.  Both
sides matches the two, which binds `$y` to `a`: `(Got (f a) a)`. -/
theorem rebindFill_answers :
    slotAns cfgM.patternOnly noCl rebindFill = some [] ∧
      idM .patternOnly noCl rebindFill = some [] ∧
    slotAns cfgM.bothSides noCl rebindFill = some [gotFaA] ∧
      idM .bothSides noCl rebindFill = some [gotFaA] := by
  and_intros <;> decide +kernel

/-- `(lam v v)`: the identity, its binder spelled `v`. -/
def idLam (v : DSp) : A := .lam v none (.par v)

/-- `(let $f 1 (let $f (lam z z) (Got ($f 2))))`. -/
def rebindLam : A :=
  .letS (nm .f) (k .n1)
    (.letS (nm .f) (idLam .z) (got1 (ap (nm .f) (k .n2))) none) none

/-- **A lambda written in place, on a name that holds a value**: no answer,
under both readings, in both models. -/
theorem rebindLam_no_answer :
    slotAns cfgM.patternOnly noCl rebindLam = some [] ∧
      slotAns cfgM.bothSides noCl rebindLam = some [] ∧
    idM .patternOnly noCl rebindLam = some [] ∧ idM .bothSides noCl rebindLam = some [] := by
  and_intros <;> decide +kernel

/-- `(let $f (lam z z) (let $f (lam w w) (Got ($f 2))))`. -/
def lamTwice : A :=
  .letS (nm .f) (idLam .z)
    (.letS (nm .f) (idLam .w) (got1 (ap (nm .f) (k .n2))) none) none

/-- **Two lambdas for one name**: the first is substituted for `$f`, so the
inner `let` has a lambda as its pattern.  No answer, as before the correction. -/
theorem lamTwice_no_answer :
    slotAns cfgM.patternOnly noCl lamTwice = some [] ∧
      slotAns cfgM.bothSides noCl lamTwice = some [] ∧
    idM .patternOnly noCl lamTwice = some [] ∧ idM .bothSides noCl lamTwice = some [] := by
  and_intros <;> decide +kernel

/-- `(let $x $y (let $x a (Got $x $y)))`. -/
def aliasThenGround : A :=
  .letS (nm .x) (nm .y) (.letS (nm .x) (k .a) (got2 (nm .x) (nm .y)) none) none

/-- **A name bound by substitution is not bound in the store.**  The outer
`let` substitutes `$y` for `$x`; the inner one then binds `$y`: `(Got a a)`. -/
theorem aliasThenGround_answers :
    slotAns cfgM.patternOnly noCl aliasThenGround =
        some [.app (.app (.sym .Got) (.sym .a)) (.sym .a)] ∧
      slotAns cfgM.bothSides noCl aliasThenGround =
        some [.app (.app (.sym .Got) (.sym .a)) (.sym .a)] ∧
    idM .patternOnly noCl aliasThenGround = some [.app (.app (.sym .Got) (.sym .a)) (.sym .a)] ∧
      idM .bothSides noCl aliasThenGround =
        some [.app (.app (.sym .Got) (.sym .a)) (.sym .a)] := by
  and_intros <;> decide +kernel

/-- `(let $x a (let $x a (Got $x)))`. -/
def sameTwice : A := .letS (nm .x) (k .a) (.letS (nm .x) (k .a) (got1 (nm .x)) none) none

/-- **The same ground value twice** matches: `(Got a)`. -/
theorem sameTwice_answers :
    slotAns cfgM.patternOnly noCl sameTwice = some [gotA] ∧
      slotAns cfgM.bothSides noCl sameTwice = some [gotA] ∧
    idM .patternOnly noCl sameTwice = some [gotA] ∧ idM .bothSides noCl sameTwice = some [gotA] := by
  and_intros <;> decide +kernel

/-- `(let $f (lam z z) (let $f 1 (Got $f)))`. -/
def lamThenGround : A :=
  .letS (nm .f) (idLam .z) (.letS (nm .f) (k .n1) (got1 (nm .f)) none) none

/-- **A lambda, then a ground value**: the lambda is substituted for `$f`, and
a lambda as pattern matches no ground value.  No answer. -/
theorem lamThenGround_no_answer :
    slotAns cfgM.patternOnly noCl lamThenGround = some [] ∧
      slotAns cfgM.bothSides noCl lamThenGround = some [] ∧
    idM .patternOnly noCl lamThenGround = some [] ∧
      idM .bothSides noCl lamThenGround = some [] := by
  and_intros <;> decide +kernel

/-- `(let $x (f $y) (let $x (f a) (Got $x $y)))`. -/
def openThenGround : A :=
  .letS (nm .x) (fOf (nm .y)) (.letS (nm .x) (fOf (k .a)) (got2 (nm .x) (nm .y)) none) none

/-- **A value that is not ground, then a ground one**: `(f $y)` is substituted
for `$x`, and the inner `let` matches `(f $y)` against `(f a)`:
`(Got (f a) a)`. -/
theorem openThenGround_answers :
    slotAns cfgM.patternOnly noCl openThenGround = some [gotFaA] ∧
      slotAns cfgM.bothSides noCl openThenGround = some [gotFaA] ∧
    idM .patternOnly noCl openThenGround = some [gotFaA] ∧
      idM .bothSides noCl openThenGround = some [gotFaA] := by
  and_intros <;> decide +kernel

/-! ### The same under lexical fresh, the name in the crossing set -/

/-- `(let $x a (let $x (f $y) (Got $x)){$x})`. -/
def rebindCross : A :=
  .letS (nm .x) (k .a) (.letS (nm .x) (fOf (nm .y)) (got1 (nm .x)) (some [.x])) none

/-- **Under lexical fresh, with `$x` in force in the inner `let`**: the inner
`let` meets the name the outer one bound.  No answer, under both readings, in
both models. -/
theorem rebindCross_no_answer :
    slotAns cfgLF.patternOnly noCl rebindCross = some [] ∧
      slotAns cfgLF.bothSides noCl rebindCross = some [] ∧
    idLF .patternOnly noCl rebindCross = some [] ∧ idLF .bothSides noCl rebindCross = some [] := by
  and_intros <;> decide +kernel

/-- `(let $f 1 (let $f (lam z z) (Got ($f 2))){$f})`. -/
def rebindLamCross : A :=
  .letS (nm .f) (k .n1)
    (.letS (nm .f) (idLam .z) (got1 (ap (nm .f) (k .n2))) (some [.f])) none

/-- **A lambda written in place on the name in force**: no answer. -/
theorem rebindLamCross_no_answer :
    slotAns cfgLF.patternOnly noCl rebindLamCross = some [] ∧
      slotAns cfgLF.bothSides noCl rebindLamCross = some [] ∧
    idLF .patternOnly noCl rebindLamCross = some [] ∧
      idLF .bothSides noCl rebindLamCross = some [] := by
  and_intros <;> decide +kernel

/-- `(let $x (f $y) (let $x (f a) (Got $x $y)){$x})`. -/
def openThenGroundCross : A :=
  .letS (nm .x) (fOf (nm .y))
    (.letS (nm .x) (fOf (k .a)) (got2 (nm .x) (nm .y)) (some [.x])) none

/-- **A value that is not ground, then a ground one, on the name in force**:
`(Got (f a) a)`. -/
theorem openThenGroundCross_answers :
    slotAns cfgLF.patternOnly noCl openThenGroundCross = some [gotFaA] ∧
      slotAns cfgLF.bothSides noCl openThenGroundCross = some [gotFaA] ∧
    idLF .patternOnly noCl openThenGroundCross = some [gotFaA] ∧
      idLF .bothSides noCl openThenGroundCross = some [gotFaA] := by
  and_intros <;> decide +kernel

/-- **Under lexical fresh with no crossing set the inner `let` has its own
`$x`.**  That name is unbound, so the value is substituted for it, as before
the correction: `(Got (f $y))` on the first row and `(Got 2)` on the row with
the lambda, under both readings, in both models. -/
theorem rebind_lexicalFresh_own_name :
    slotAns cfgLF.patternOnly noCl rebind = some [gotF yS] ∧
      slotAns cfgLF.bothSides noCl rebind = some [gotF yS] ∧
    idLF .patternOnly noCl rebind = some [gotF yI] ∧ idLF .bothSides noCl rebind = some [gotF yI] ∧
    slotAns cfgLF.patternOnly noCl rebindLam = some [.app (.sym .Got) (.sym .n2)] ∧
      slotAns cfgLF.bothSides noCl rebindLam = some [.app (.sym .Got) (.sym .n2)] ∧
    idLF .patternOnly noCl rebindLam = some [.app (.sym .Got) (.sym .n2)] ∧
      idLF .bothSides noCl rebindLam = some [.app (.sym .Got) (.sym .n2)] := by
  and_intros <;> decide +kernel

/-! ## Three statements that needed the hypothesis that the name is unbound -/

/-- The store in which `$f` holds `1`. -/
def fHolds1 : GStore DSym DSp := fun n => if n = .src .f then some (.sym .n1) else none

/-- `(Got ($f 2))`, over plain spellings. -/
def gotCallF2 : Tm DSym DSp := .app (.sym .Got) (.app (.var (.src .f)) (.sym .n2))

/-- **`run_letP_lam` without its hypothesis is false.**  From the store in which
`$f` holds `1`, `(let $f (lam z z) (Got ($f 2)))` gives no answer, while the
substituted body `(Got ((lam z z) 2))` answers `(Got 2)`. -/
theorem not_run_letP_lam_any_store :
    ¬ ∀ (d : Disc) (prog : DSym → Option (Tm DSym DSp)) (n : ℕ) (π : Path)
      (σ : GStore DSym DSp) (f x : Nm DSp) (own : List DSp) (body C : Tm DSym DSp),
      run d prog (n + 1) π σ (.letP (.var f) (.lam x own body) C) =
        run d prog n π σ (subst (Sub.single f (.lam x own body)) Sub.none C) := by
  intro h
  have e := congrArg (Option.map List.length)
    (h .static (fun _ => none) 5 [] fHolds1 (.src .f) (.src .z) [] (.pvar (.src .z)) gotCallF2)
  revert e
  decide +kernel

/-- **`IdSlot.step_letP_some` without its hypothesis is false**, on the same
`let`. -/
theorem not_step_letP_some_any_store :
    ¬ ∀ (d : Disc) (P : DSym → Option (Tm DSym DSp)) (rec : Runner DSym DSp) (π : Path)
      (σ : GStore DSym DSp) (p w b : Tm DSym DSp) (f : Nm DSp), letLam? p w = some f →
      step d P rec π σ (.letP p w b) = rec π σ (subst (Sub.single f w) Sub.none b) := by
  intro h
  have e := congrArg (Option.map List.length)
    (h .static (fun _ => none) (run .static (fun _ => none) 5) [] fHolds1 (.var (.src .f))
      (.lam (.src .z) [] (.pvar (.src .z))) gotCallF2 (.src .f) rfl)
  revert e
  decide +kernel

/-- **`run_elabTopM_inline` without its hypothesis is false.**  The hygiene
hypotheses hold for `(let $f (lam z z) (Got ($f 2)))`; from the store in which
`$f` holds `1` the elaborated `let` gives no answer, and the elaborated inlined
text answers `(Got 2)`. -/
theorem not_run_elabTopM_inline_any_store :
    ¬ ∀ (prog : DSym → Option (Tm DSym DSp)) (n : ℕ) (π : Path) (σ : GStore DSym DSp)
      (fx : DSp) (x : Nm DSp) (body C : Tm DSym DSp),
      bare C = true → fx ∉ names body →
      hygM fx (names body) (elabM (direct (.letP (.var (.src fx)) (.lam x [] body) C)) C) = true →
      run .static prog (n + 1) π σ (elabTopM (.letP (.var (.src fx)) (.lam x [] body) C)) =
        run .static prog n π σ
          (elabTopM (subst (Sub.single (.src fx) (.lam x [] body)) Sub.none C)) := by
  intro h
  have e := congrArg (Option.map List.length)
    (h (fun _ => none) 5 [] fHolds1 .f (.src .z) (.pvar (.src .z)) gotCallF2
      (by decide) (by decide) (by decide))
  revert e
  decide +kernel

end Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionExamples
