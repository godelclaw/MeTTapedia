import Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionCoverExamples

/-!
# Template scope: the hole of quoted code belongs to the form that writes it

A hole of a quotation written in a form rooted at `R` is that form's head slot:
`(R, y)` in the slot model (`codeOf R`), `⟨y, R, R, .head⟩` in the identity
model (`codeI R`).  The query's own quotations keep the query's slot; an
equation's quotations (root `[5]`) get a slot of the equation's frame.

Nine rows, each a program and a query, in the slot model and the identity
model, under rule M and lexical fresh, under pattern-only and both sides
(`table`).  The C draft answers, under both of its profiles:

| Row | Program | Draft |
|---|---|---|
| 1 | `(= (F) (quote (lam z $y)))` · `(let (quote (lam w w)) (F) (Got $y))` | `(Got $y)` |
| 2 | `(= (G) (quote (lam z $x)))` · `(let (quote (lam w w)) (G) (Got $y))` | `(Got $y)` |
| 3 | `F` · `(let (quote (lam w w)) (F) (let $y 0 (Got $y)))` | `(Got 0)` |
| 4 | `F`, `(= (G) (quote (lam z (f $y))))` · two matches | `(Got twoEquations)` |
| 5 | `(= (H) (quote (lam z (f $y))))` · two calls of `H` | `(Got twoCalls)` |
| 6 | `H` · `(let (quote (lam w (f a))) (H) (Got $y))` | `(Got $y)` |
| 7 | one form, `(Got $y)` after the match | `(Got (quote z (z)))` |
| 8 | one form, an inner `let` on `$y` | `(Got 0)` |
| 9 | one form, two matches of the query's own hole | nothing |

## Main results

* `row1` … `row9`, `row5_renamed` — the eight bags of each row, kernel-checked.
  Every row is the draft's in all four, except row 8 in the slot model under
  rule M (one name for the hole and the inner `$y`).  Rows 4 and 5 need the
  per-call renaming of holes: an activation of a frame renames the frame's own
  names inside the sealed code of its body (`activate_quote`), and a clause's
  wrapper owns the holes of its sealed code (`clauseOf`, `holeSpellings`; the
  identity model's `frameSlots`).
* `hole_renamed_per_call` — two calls of one equation return its quotation with
  disjoint holes: each call copies the hole at its own activation path.
* `hole_spelling_invariant` — renaming the equation's hole changes no answer.
* `query_name_kept` — the query's `$y` is not filled by an equation's hole: a
  call's hole is not the caller's name of the same spelling.
* `codeBinder_kept` — the renaming does not enter a quotation's own binders: a
  code binder spelled like the frame's hole keeps its name.
* `closed_quote_kept` — a quotation that mentions no name of the frame comes
  back unchanged from every call.
* `patternOnly_blind` — pattern-only writes no hole.
* `hole_collected` — both models' clause wrappers list the equation's hole
  among the frame's own names: the identity model through `frameSlots`, the
  slot model through `holeSpellings` (a name written only inside a quotation is
  no root spelling).
* `transfer_stores_differ_in_copies` — the slot model's two runs of the
  translator store one quotation, copied by calls at different paths: the
  stored values differ in the copy of the hole, so the stores of
  `transfer_firstOrder` agree up to a correspondence of copies, not literally.
* `codeFwd_equation_hole`, `mapCode_codeOf_needs_scopeOwner`,
  `codeEq_codeOf_codeI_needs_scopeOwner` — negatives: an owner that is not `[]`
  is not a code owner (`codeFwd` sends the equation's hole to a slot), and the
  agreement of the two models' sealed code fails at a root that is a code
  owner, which is why those statements assume `scopeOwner R`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.QuotedHoleRows

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot

/-- Symbols of the rows; `unit` is the clause wrapper's argument. -/
inductive Sy where
  | f | a | b | Got | n0 | unit | F | G | H | twoEquations | twoCalls
  deriving DecidableEq, Repr

/-- Spellings of the rows; `u` is the clause wrapper's parameter. -/
inductive Sp where
  | x | y | z | w | u
  deriving DecidableEq, Repr

/-- Authored text of the rows. -/
abbrev A := Src Sy Sp

def k (s : Sy) : A := .sym s
def nm (v : Sp) : A := .sv v
def fOf (a : A) : A := .app (k .f) a
def got1 (a : A) : A := .app (k .Got) a
/-- `(quote (lam z b))`, a value. -/
def qz (b : A) : A := .quote (.lam .z none b)
/-- `(quote (lam w b))`, in pattern position. -/
def pw (b : A) : A := .pquote (.lam .w none b)
/-- A `let` with no crossing set. -/
def lt (p v b : A) : A := .letS p v b none

/-- Answers in the slot model, under a configuration and its direction. -/
def slotAns (c : DirConfig) (cl : Sy → Option A) (t : A) : Option (List (Tm Sy (Slot Sp))) :=
  answersDirCfg c (progSlot c.scope .u .unit cl) 80 t

/-- Answers in the identity model, rule M. -/
def idM (dir : Direction) (cl : Sy → Option A) (t : A) : Option (List (Tm Sy (BId Sp))) :=
  answersDir dir .static (progM .u .unit cl) 80 (elabMFormAt [] t)

/-- Answers in the identity model, lexical fresh. -/
def idLF (dir : Direction) (cl : Sy → Option A) (t : A) : Option (List (Tm Sy (BId Sp))) :=
  answersDir dir .static (progLF .u .unit cl) 80 (elabLFFormAt [] t)

/-- Printed answers. -/
abbrev P := SExp (SAtom Sy Sp)

/-- An answer of the slot model, every name printed by its spelling. -/
def spS (t : Tm Sy (Slot Sp)) : P :=
  printAns (fun n => .var n.spelling) (fun n => .par n.spelling) t

/-- An answer of the identity model, every name printed by its spelling. -/
def spI (t : Tm Sy (BId Sp)) : P :=
  printAns (fun n => .var (IdSlot.spellI n)) (fun n => .par (IdSlot.spellI n)) t

/-- The eight bags of a row: slot model rule M pattern-only and both sides, slot
model lexical fresh pattern-only and both sides, then the same in the identity
model. -/
def table (cl : Sy → Option A) (t : A) : List (Option (List P)) :=
  [(slotAns cfgM.patternOnly cl t).map (List.map spS),
   (slotAns cfgM.bothSides cl t).map (List.map spS),
   (slotAns cfgLF.patternOnly cl t).map (List.map spS),
   (slotAns cfgLF.bothSides cl t).map (List.map spS),
   (idM .patternOnly cl t).map (List.map spI), (idM .bothSides cl t).map (List.map spI),
   (idLF .patternOnly cl t).map (List.map spI), (idLF .bothSides cl t).map (List.map spI)]

/-! ## The programs -/

/-- No equations. -/
def noCl : Sy → Option A := fun _ => none

/-- `(= (F) (quote (lam z $y)))`. -/
def clF : Sy → Option A
  | .F => some (qz (nm .y))
  | _ => none

/-- `(= (F) (quote (lam z $x)))`: the hole of `F` spelled `x`. -/
def clFx : Sy → Option A
  | .F => some (qz (nm .x))
  | _ => none

/-- `(= (G) (quote (lam z $x)))`. -/
def clGx : Sy → Option A
  | .G => some (qz (nm .x))
  | _ => none

/-- `(= (F) (quote (lam z $y)))`, `(= (G) (quote (lam z (f $y))))`. -/
def clFG : Sy → Option A
  | .F => some (qz (nm .y))
  | .G => some (qz (fOf (nm .y)))
  | _ => none

/-- `(= (H) (quote (lam z (f $y))))`. -/
def clH : Sy → Option A
  | .H => some (qz (fOf (nm .y)))
  | _ => none

/-- `(= (H) (quote (lam z (f $x))))`: the hole of `H` spelled `x`. -/
def clHx : Sy → Option A
  | .H => some (qz (fOf (nm .x)))
  | _ => none

/-- Row 1: `(let (quote (lam w w)) (F) (Got $y))`. -/
def r1 : A := lt (pw (.par .w)) (.fn .F) (got1 (nm .y))
/-- Row 2: `(let (quote (lam w w)) (G) (Got $y))`. -/
def r2 : A := lt (pw (.par .w)) (.fn .G) (got1 (nm .y))
/-- Row 3: `(let (quote (lam w w)) (F) (let $y 0 (Got $y)))`. -/
def r3 : A := lt (pw (.par .w)) (.fn .F) (lt (nm .y) (k .n0) (got1 (nm .y)))
/-- Row 4: `(let (quote (lam w w)) (F) (let (quote (lam w (f a))) (G) (Got twoEquations)))`. -/
def r4 : A := lt (pw (.par .w)) (.fn .F) (lt (pw (fOf (k .a))) (.fn .G) (got1 (k .twoEquations)))
/-- Row 5: `(let (quote (lam w (f a))) (H) (let (quote (lam w (f b))) (H) (Got twoCalls)))`. -/
def r5 : A := lt (pw (fOf (k .a))) (.fn .H) (lt (pw (fOf (k .b))) (.fn .H) (got1 (k .twoCalls)))
/-- Row 6: `(let (quote (lam w (f a))) (H) (Got $y))`. -/
def r6 : A := lt (pw (fOf (k .a))) (.fn .H) (got1 (nm .y))
/-- Row 7: `(let (quote (lam w w)) (quote (lam z $y)) (Got $y))`. -/
def r7 : A := lt (pw (.par .w)) (qz (nm .y)) (got1 (nm .y))
/-- Row 8: `(let (quote (lam w w)) (quote (lam z $y)) (let $y 0 (Got $y)))`. -/
def r8 : A := lt (pw (.par .w)) (qz (nm .y)) (lt (nm .y) (k .n0) (got1 (nm .y)))
/-- Row 9: `(let (quote (lam w (f a))) (quote (lam z (f $y)))
(let (quote (lam w (f b))) (quote (lam z (f $y))) (Got $y)))`. -/
def r9 : A := lt (pw (fOf (k .a))) (qz (fOf (nm .y)))
  (lt (pw (fOf (k .b))) (qz (fOf (nm .y))) (got1 (nm .y)))

/-- `(Got $y)`. -/
def gotY : P := .list [.atom (.sym .Got), .atom (.var .y)]

/-- `(Got (quote z (z)))`. -/
def gotQ : P :=
  .list [.atom (.sym .Got), .list [.atom (.kw .quote), .atom (.par .z), .list [.atom (.par .z)]]]

/-- `(Got s)`. -/
def gotS (s : Sy) : P := .list [.atom (.sym .Got), .atom (.sym s)]

/-! ## The nine rows -/

/-- **Row 1, `(Got $y)` as in the draft**: under both sides the equation's hole
takes the contextual code and the query's `$y` stays unbound, in all four. -/
theorem row1 : table clF r1 =
    [some [], some [gotY], some [], some [gotY], some [], some [gotY], some [], some [gotY]] := by
  decide +kernel

/-- **Row 2, `(Got $y)` as in the draft**, in all four. -/
theorem row2 : table clGx r2 =
    [some [], some [gotY], some [], some [gotY], some [], some [gotY], some [], some [gotY]] := by
  decide +kernel

/-- **Row 3, `(Got 0)` as in the draft**, in all four: the inner `let` binds the
query's `$y`, which the equation's hole is not. -/
theorem row3 : table clF r3 =
    [some [], some [gotS .n0], some [], some [gotS .n0], some [], some [gotS .n0], some [],
      some [gotS .n0]] := by
  decide +kernel

/-- **Row 4, `(Got twoEquations)` as in the draft**, in all four under both
sides: `F` and `G` are both rooted at `[5]`, and each call copies its
equation's hole at its own path, so the two matches write two names. -/
theorem row4 : table clFG r4 =
    [some [], some [gotS .twoEquations], some [], some [gotS .twoEquations], some [],
      some [gotS .twoEquations], some [], some [gotS .twoEquations]] := by
  decide +kernel

/-- **Row 5, `(Got twoCalls)` as in the draft**, in all four under both sides:
the two calls of `H` return two copies of its hole (`hole_renamed_per_call`). -/
theorem row5 : table clH r5 =
    [some [], some [gotS .twoCalls], some [], some [gotS .twoCalls], some [],
      some [gotS .twoCalls], some [], some [gotS .twoCalls]] := by
  decide +kernel

/-- **Row 6, `(Got $y)` as in the draft**, in all four: `H`'s hole takes `a`. -/
theorem row6 : table clH r6 =
    [some [], some [gotY], some [], some [gotY], some [], some [gotY], some [], some [gotY]] := by
  decide +kernel

/-- **Row 7, `(Got (quote z (z)))` as in the draft**, in all four: the query's
own quotation shares its hole with the query's `$y`. -/
theorem row7 : table noCl r7 =
    [some [], some [gotQ], some [], some [gotQ], some [], some [gotQ], some [], some [gotQ]] := by
  decide +kernel

/-- **Row 8, `(Got 0)` as in the draft, except in the slot model under rule M**,
which has one name for the hole and the inner `$y`, and answers nothing. -/
theorem row8 : table noCl r8 =
    [some [], some [], some [], some [gotS .n0], some [], some [gotS .n0], some [],
      some [gotS .n0]] := by
  decide +kernel

/-- **Row 9, nothing as in the draft**, in all four: the query's own hole is one
name, written by the first match. -/
theorem row9 : table noCl r9 =
    [some [], some [], some [], some [], some [], some [], some [], some []] := by
  decide +kernel

/-- Row 5 with the hole of `H` spelled `$x`: `(Got twoCalls)`, in all four under
both sides. -/
theorem row5_renamed : table clHx r5 =
    [some [], some [gotS .twoCalls], some [], some [gotS .twoCalls], some [],
      some [gotS .twoCalls], some [], some [gotS .twoCalls]] := by
  decide +kernel

/-! ## Spelling, the query's names, pattern-only -/

/-- **Renaming the equation's hole changes no answer**, in all four, under both
sides: the answers of row 1 are the same terms whether `F`'s hole is spelled
`$y` or `$x`; rows 1 and 2 answer alike; row 5 answers alike with `H`'s hole
spelled `$y` or `$x`. -/
theorem hole_spelling_invariant :
    slotAns cfgM.bothSides clF r1 = slotAns cfgM.bothSides clFx r1 ∧
      slotAns cfgLF.bothSides clF r1 = slotAns cfgLF.bothSides clFx r1 ∧
      idM .bothSides clF r1 = idM .bothSides clFx r1 ∧
      idLF .bothSides clF r1 = idLF .bothSides clFx r1 ∧
      table clF r1 = table clGx r2 ∧ table clH r5 = table clHx r5 := by
  and_intros <;> decide +kernel

/-- **The query's `$y` is not filled by an equation's hole**: in row 1 the
answer still holds the query's own name, in all four. -/
theorem query_name_kept :
    (slotAns cfgM.bothSides clF r1).map (List.map Tm.vars) = some [[.src ([], .y)]] ∧
      (slotAns cfgLF.bothSides clF r1).map (List.map Tm.vars) = some [[.src ([], .y)]] ∧
      (idM .bothSides clF r1).map (List.map Tm.vars) =
        some [[.src (.slot ⟨.y, [], [], .head⟩)]] ∧
      (idLF .bothSides clF r1).map (List.map Tm.vars) =
        some [[.src (.slot ⟨.y, [], [], .head⟩)]] := by
  and_intros <;> decide +kernel

/-- **Pattern-only never writes a hole**: no answer for either spelling of the
equation's hole, in either model. -/
theorem patternOnly_blind :
    slotAns cfgM.patternOnly clF r1 = some [] ∧ slotAns cfgM.patternOnly clFx r1 = some [] ∧
      idM .patternOnly clF r1 = some [] ∧ idM .patternOnly clFx r1 = some [] := by
  and_intros <;> decide +kernel

/-! ## The equation's hole is a slot of its frame -/

/-- **The hole is a name of the equation's frame, and its wrapper owns it**:
`codeOf [5]` and `codeI [5]` write it at the root `[5]`; the identity model's
clause wrapper lists it among the frame's slots (`frameSlots`); the slot
model's wrapper lists it among the holes of its sealed code (`holeSpellings`),
although it is no root spelling. -/
theorem hole_collected :
    Tm.vars (codeOf [5] (.lam .z none (nm .y)) : Tm Sy (Slot Sp)) = [.src ([5], .y)] ∧
      Tm.vars (codeI [5] (.lam .z none (nm .y)) : Tm Sy (BId Sp)) =
        [.src (.slot ⟨.y, [5], [5], .head⟩)] ∧
      frameSlots [5] (elabMFormAt [5] (qz (nm .y))) = [.slot ⟨.y, [5], [5], .head⟩] ∧
      frameSlots [5] (elabLFFormAt [5] (qz (nm .y))) = [.slot ⟨.y, [5], [5], .head⟩] ∧
      rootSpellings (qz (nm .y)) = [] ∧
      holeSpellings [5] (elabCfg cfgM [5] (qz (nm .y))) = [.y] ∧
      holeSpellings [5] (elabCfg cfgLF [5] (qz (nm .y))) = [.y] ∧
      clauseOf cfgM [5] .u .unit (qz (nm .y)) =
        .app (.lam (.src ([5, 9], .u)) [([5], .y)] (.quote (codeOf [5] (.lam .z none (nm .y)))))
          (.sym .unit) := by
  and_intros <;> decide +kernel

/-- `H`'s quotation as the call at the activation path `ρ` returns it, in the
slot model: the hole `([5], y)` is renamed at `ρ`. -/
def callH (ρ : Path) : Tm Sy (Slot Sp) :=
  renCode ρ [([5], .y)] (codeOf [5] (.lam .z none (fOf (nm .y))))

/-- The same, in the identity model: the head slot of the equation's frame is
renamed at `ρ`. -/
def callHI (ρ : Path) : Tm Sy (BId Sp) :=
  renCode ρ [.slot ⟨.y, [5], [5], .head⟩] (codeI [5] (.lam .z none (fOf (nm .y))))

/-- **Two calls of one equation have disjoint holes**, in both models.  Each call
of `H` is an activation of the equation's frame, which owns the hole `([5], y)`
(the identity model's `⟨y, [5], [5], .head⟩`), and renames it inside the
returned quotation at the call's own activation path: the call at `[0]` returns
the copy at `[0, 0, 2]`, the call at `[1]` the copy at `[1, 0, 2]`. -/
theorem hole_renamed_per_call :
    (run .static (progSlot cfgM .u .unit clH) 4 [0] Store.empty (.fn .H)).map (List.map Prod.fst) =
        some [.quote (callH [0, 0, 2])] ∧
      (run .static (progSlot cfgM .u .unit clH) 4 [1] Store.empty (.fn .H)).map
          (List.map Prod.fst) = some [.quote (callH [1, 0, 2])] ∧
      (run .static (progM .u .unit clH) 4 [0] Store.empty (.fn .H)).map (List.map Prod.fst) =
        some [.quote (callHI [0, 0, 2])] ∧
      (run .static (progM .u .unit clH) 4 [1] Store.empty (.fn .H)).map (List.map Prod.fst) =
        some [.quote (callHI [1, 0, 2])] ∧
      codeVars (callH [0, 0, 2]) = [.inst [0, 0, 2] (.src ([5], .y))] ∧
      codeVars (callH [1, 0, 2]) = [.inst [1, 0, 2] (.src ([5], .y))] ∧
      codeVars (callHI [0, 0, 2]) = [.inst [0, 0, 2] (.src (.slot ⟨.y, [5], [5], .head⟩))] ∧
      codeVars (callHI [1, 0, 2]) = [.inst [1, 0, 2] (.src (.slot ⟨.y, [5], [5], .head⟩))] := by
  and_intros <;> decide +kernel

/-! ## What the per-call renaming leaves alone -/

/-- `(= (F) (quote (lam y (f y $y))))`: a code binder spelled like the hole. -/
def clK : Sy → Option A
  | .F => some (.quote (.lam .y none (.app (fOf (.par .y)) (nm .y))))
  | _ => none

/-- **The renaming does not enter a quotation's own binders**: the call of `F`
in `clK` renames the hole `$y` and keeps the code binder `y` and its use, in
both models.  The frame owns `([5], y)`; the binder is `([9, 1], y)`. -/
theorem codeBinder_kept :
    (run .static (progSlot cfgM .u .unit clK) 4 [0] Store.empty (.fn .F)).map (List.map Prod.fst) =
        some [.quote (.lam (.src ([9, 1], .y)) []
          (.app (.app (.sym .f) (.pvar (.src ([9, 1], .y)))) (.var (.inst [0, 0, 2] (.src ([5], .y))))))] ∧
      (run .static (progM .u .unit clK) 4 [0] Store.empty (.fn .F)).map (List.map Prod.fst) =
        some [.quote (.lam (.src (.code .y [9, 1])) []
          (.app (.app (.sym .f) (.pvar (.src (.code .y [9, 1]))))
            (.var (.inst [0, 0, 2] (.src (.slot ⟨.y, [5], [5], .head⟩))))))] := by
  and_intros <;> decide +kernel

/-- `(= (F) (quote (lam z (f z))))`: a quotation with no hole. -/
def clClosed : Sy → Option A
  | .F => some (.quote (.lam .z none (fOf (.par .z))))
  | _ => none

/-- **A quotation that mentions no name of the frame comes back unchanged**, from
every call, in both models. -/
theorem closed_quote_kept :
    (run .static (progSlot cfgM .u .unit clClosed) 4 [0] Store.empty (.fn .F)).map
        (List.map Prod.fst) = some [.quote (codeOf [5] (.lam .z none (fOf (.par .z))))] ∧
      (run .static (progSlot cfgM .u .unit clClosed) 4 [1] Store.empty (.fn .F)).map
        (List.map Prod.fst) = some [.quote (codeOf [5] (.lam .z none (fOf (.par .z))))] ∧
      (run .static (progM .u .unit clClosed) 4 [0] Store.empty (.fn .F)).map (List.map Prod.fst) =
        some [.quote (codeI [5] (.lam .z none (fOf (.par .z))))] ∧
      (run .static (progM .u .unit clClosed) 4 [1] Store.empty (.fn .F)).map (List.map Prod.fst) =
        some [.quote (codeI [5] (.lam .z none (fOf (.par .z))))] := by
  and_intros <;> decide +kernel

/-! ## The stores of the translator's two slot runs -/

/-- `((lam w (let $x (F) (Got a))) b)`: the lambda owns `$x`, so the translator
puts a `new` block around its body, and the call of `F` sits deeper in the
translation. -/
def rStore : A := .app (.lam .w none (lt (nm .x) (.fn .F) (got1 (k .a)))) (k .b)

/-- `(Got a)`. -/
def gotAT : Tm Sy (Slot Sp) := .app (.sym .Got) (.sym .a)

/-- `F`'s quotation with the hole copied at `ρ`. -/
def quoteFAt (ρ : Path) : GVal Sy (Slot Sp) :=
  .quote (.lam (.src ([9, 1], .z)) [] (.var (.inst ρ (.src ([5], .y)))))

set_option maxRecDepth 100000 in
/-- **The slot model's two runs of the translator store one quotation, copied at
different paths.**  Rule M on the source and lexical fresh on the translation
both answer `(Got a)` and bind one name, `$x`'s copy, to the quotation that
`F` returns; the two calls are activated at `[2, 0, 0, 2]` and at
`[2, 1, 0, 2]`, so the stored quotations differ in the copy of `F`'s hole, and
the value rule M stores is stored at no name by lexical fresh.  The stores of
`transfer_firstOrder` therefore agree up to a correspondence of the copies, not
literally. -/
theorem transfer_stores_differ_in_copies :
    run .static (progSlot cfgM .u .unit clF) 80 [] Store.empty (elabCfg cfgM [] rStore) =
        some [(gotAT, fun n => if n = .inst [2] (.src ([0, 0], .x)) then some (quoteFAt [2, 0, 0, 2])
          else Store.empty n)] ∧
      run .static (progSlot cfgLF .u .unit (toLexicalProg clF)) 80 [] Store.empty
          (elabCfg cfgLF [] (toLexical rStore)) =
        some [(gotAT, fun n => if n = .inst [2, 2] (.src ([0, 0, 2], .x))
          then some (quoteFAt [2, 1, 0, 2]) else Store.empty n)] ∧
      ∀ n : Nm (Slot Sp), (if n = .inst [2, 2] (.src ([0, 0, 2], .x)) then some (quoteFAt [2, 1, 0, 2])
          else Store.empty n) ≠ some (quoteFAt [2, 0, 0, 2]) := by
  refine ⟨rfl, rfl, fun n => ?_⟩
  split
  · simp only [ne_eq, Option.some.injEq]
    decide
  · simp [Store.empty]

/-! ## Negatives: the root of a form is a scope owner -/

/-- **An owner that is not `[]` need not be a code owner**: `codeFwd` sends the
hole of an equation, owner `[5]`, to the head slot of the equation's frame, not
to a code name. -/
theorem codeFwd_equation_hole :
    (codeFwd (.src ([5], Sp.y)) : Nm (BId Sp)) = .src (.slot ⟨.y, [5], [5], .head⟩) ∧
      (codeFwd (.src ([5], Sp.y)) : Nm (BId Sp)) ≠ .src (.code .y [5]) := by
  decide

/-- **`mapCode_codeOf` needs `scopeOwner R`**: at the code-binder owner `[9, 1]`
the slot model's hole is read as a code name, and the identity model's as a
slot. -/
theorem mapCode_codeOf_needs_scopeOwner :
    mapCode codeFwd (codeOf [9, 1] (.sv .y : Src Sy Sp)) ≠ codeI [9, 1] (.sv .y : Src Sy Sp) := by
  decide +kernel

/-- **`codeEq_codeOf_codeI` needs `scopeOwner R`**: at the code-binder owner
`[9, 1]`, two holes of different spellings are one binder position to the slot
model and two slots to the identity model. -/
theorem codeEq_codeOf_codeI_needs_scopeOwner :
    codeEq (codeOf [9, 1] (.sv .y : Src Sy Sp)) (codeOf [9, 1] (.sv .z)) ≠
      codeEq (codeI [9, 1] (.sv .y : Src Sy Sp)) (codeI [9, 1] (.sv .z)) := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.TemplateScope.QuotedHoleRows
