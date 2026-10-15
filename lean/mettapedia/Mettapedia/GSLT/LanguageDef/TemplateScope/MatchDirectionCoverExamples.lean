import Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionCover
import Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionUnify

/-!
# Template scope: rule M with both sides, on examples

Kernel-checked programs for `MatchDirectionCover`.

* `coveredHole_cover`, `coveredHole_names` — on
  `(let (quote (lam w w)) (quote (lam z $y)) (let $y 0 (Got $y)))`, rule M's
  cover count gives the value's quotation no occurrence of `y`, `findCover` puts
  `$y` at the inner `let`, and the identity model then names the hole (the
  root's own cell) and the inner `$y` (a pattern cell) differently, where the
  slot model has one name.
* `coveredHole_bags`, `not_renaming_M_bothSides`, `not_transfer_bothSides` — under
  both sides the slot model answers nothing and the identity model answers
  `(Got 0)`: the statements of `renaming_M` and of `transfer`, read with both
  sides, are false.
* `coveredHole_count`, `coveredHole_count_agrees` — with the count of holes inside quotations
  (`findCoverQ []`) the two models agree on that query, and so do the slot
  model's two runs of `transfer`.
* `cross_cover`, `cross_bags`, `cross_runS`, `cross_runL`, `cross_runI` — when
  the quotation with the hole is written in an equation, the query has no
  quotation and the count over the query changes nothing.  The hole is the
  equation's own cell, copied by the call of `F`, not the query's `$y`: in
  every run the call's copy of the hole takes the contextual code, the query's
  `$y` takes `0`, and the answer is `(Got 0)`.
* `cross_renaming_MQ_bothSides`, `cross_transferQ_bothSides` — on that program
  the statements of `renaming_M` and of `transfer`, read with both sides and the
  count over the query, hold: each slot result is a renaming of the identity
  result (`cross_renamed`).
* `cross_holes_agree` — with the hole spellings of the equations listed
  (`findCoverQ [y]`), the two models agree as well, on `(Got 0)`.
* `lexicalFresh_bothSides_agree`, `stress_bothSides_agree` — under lexical
  fresh and both sides the two models agree on these programs, on the rows of
  `MatchDirectionExamples`, and on eleven more programs chosen where the models
  allocate differently.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionExamples

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot

/-- `(Got 0)`. -/
def got0 {Y : Type} : Tm DSym Y := .app (.sym .Got) (.sym .n0)

/-- The slot model's run, as a function of the fuel, under a configuration and
its direction. -/
def slotRun (c : DirConfig) (cl : DSym → Option A) (t : A) (n : ℕ) :
    Option (Result DSym (Slot DSp)) :=
  runDir c.direction c.scope.disc (progSlot c.scope .u .unit cl) n [] Store.empty
    (elabCfg c.scope [] t)

/-- The identity model's rule-M run of an elaborated query, as a function of the
fuel. -/
def idRunM (dir : Direction) (cl : DSym → Option A) (q : Tm DSym (BId DSp)) (n : ℕ) :
    Option (Result DSym (BId DSp)) :=
  runDir dir .static (progM .u .unit cl) n [] Store.empty q

/-! ## One form: the hole and its cover -/

/-- `(let (quote (lam w w)) (quote (lam z $y)) (let $y 0 (Got $y)))`. -/
def coveredHole : A :=
  .letS (.pquote (.lam .w none (.par .w))) (.quote (.lam .z none (nm .y)))
    (.letS (nm .y) (k .n0) (got1 (nm .y)) none) none

theorem coveredHole_admissible : coveredHole.Admissible := by decide +kernel

/-- **Rule M's cover count gives the quotation no occurrence, and the cover is
the inner `let`.**  `occM` of the value's quotation is `0`; `findCover` returns
the position `[2]` of the inner `let`; so rule M's root environment names `y`
after that pattern, not as the root's own cell. -/
theorem coveredHole_cover :
    occM (Src.direct coveredHole) .y (.quote (.lam .z none (nm .y)) : A) = 0 ∧
      findCover (Src.direct coveredHole) DSp.y false coveredHole = some [2] ∧
      mRootEnv [] coveredHole .y = ⟨.y, [], [2], .pat⟩ ∧
      (mRootEnv [] coveredHole .y ≠ ⟨.y, [], [], .head⟩) := by
  and_intros <;> decide +kernel

/-- **One name in the slot model, two in the identity model.**  The store names
of the elaborated query, in order: the hole of the value's quotation, the inner
pattern, the body.  The slot model has the query's cell `([], y)` three times.
The identity model has the root's own cell for the hole, which is where
`codeFwd` sends the slot model's name, and a pattern cell for the other two. -/
theorem coveredHole_names :
    Tm.vars (elabCfg cfgM [] coveredHole) = [.src ([], .y), .src ([], .y), .src ([], .y)] ∧
      Tm.vars (elabMFormAt [] coveredHole) =
        [.src (.slot ⟨.y, [], [], .head⟩), .src (.slot ⟨.y, [], [2], .pat⟩),
          .src (.slot ⟨.y, [], [2], .pat⟩)] ∧
      (codeFwd (.src ([], DSp.y)) : Nm (BId DSp)) = .src (.slot ⟨.y, [], [], .head⟩) := by
  and_intros <;> decide +kernel

/-- **The two models differ under both sides.**  Pattern-only: no answer in
either.  Both sides: the slot model fills the query's `$y` with the contextual
code and the inner `let` then fails; the identity model fills the root's own
cell and the inner `let` binds another cell, so it answers `(Got 0)`. -/
theorem coveredHole_bags :
    slotAns cfgM.patternOnly noCl coveredHole = some [] ∧ idM .patternOnly noCl coveredHole = some [] ∧
      slotAns cfgM.bothSides noCl coveredHole = some [] ∧ idM .bothSides noCl coveredHole = some [got0] := by
  and_intros <;> decide +kernel

/-- **The statement of `renaming_M`, read with both sides, is false** on an
admissible query with no equations. -/
theorem not_renaming_M_bothSides :
    ¬ RenamingStatement (slotRun cfgM.bothSides noCl coveredHole)
      (idRunM .bothSides noCl (elabMFormAt [] coveredHole)) :=
  not_renamingStatement_of_length (n := 80) (m := 80) (a := 0) (b := 1) (by decide +kernel)
    (by decide +kernel) (by decide)

/-- **The statement of `transfer`, read with both sides, is false** on that
query: in the slot model itself, lexical fresh on the translation has one
answer and rule M on the source has none. -/
theorem not_transfer_bothSides :
    ¬ TransferStatement (slotRun cfgLF.bothSides (toLexicalProg noCl) (toLexical coveredHole))
      (slotRun cfgM.bothSides noCl coveredHole) (idRunM .bothSides noCl (elabMFormAt [] coveredHole)) :=
  not_transferStatement_of_length (n := 80) (n' := 80) (a := 1) (b := 0) (by decide +kernel)
    (by decide +kernel) (by decide)

/-! ## The count of holes inside quotations, over the form -/

/-- **The count finds the hole, and the cover is gone.**  The count of holes of
`y` inside quotations of the query is `1`; `findCoverQ` returns no cover; the
root environment names `y` as the root's own cell, and the identity model has
that one name three times. -/
theorem coveredHole_count :
    Src.quoteOcc DSp.y coveredHole = 1 ∧
      findCoverQ [] (Src.direct coveredHole) DSp.y false coveredHole = none ∧
      Tm.vars (elabMFormAtQ [] [] coveredHole) =
        [.src (.slot ⟨.y, [], [], .head⟩), .src (.slot ⟨.y, [], [], .head⟩),
          .src (.slot ⟨.y, [], [], .head⟩)] := by
  and_intros <;> decide +kernel

/-- **With the count the two models agree on that query**, under both sides:
no answer in the slot model, none in the identity model, and none in the slot
model's lexical-fresh run of the translation. -/
theorem coveredHole_count_agrees :
    slotAns cfgM.bothSides noCl coveredHole = some [] ∧
      answersDir .bothSides .static (progM .u .unit noCl) 80 (elabMFormAtQ [] [] coveredHole) =
        some [] ∧
      slotAns cfgLF.bothSides (toLexicalProg noCl) (toLexicalQ [] coveredHole) = some [] := by
  and_intros <;> decide +kernel

/-! ## Two forms: the hole belongs to the equation -/

/-- The equation `(= (F) (quote (lam z $y)))`. -/
def clF : DSym → Option A
  | .F => some (.quote (.lam .z none (nm .y)))
  | _ => none

/-- `(let (quote (lam w w)) (F) (let $y 0 (Got $y)))`: the quotation with the
hole is the value of the equation `F`. -/
def crossQ : A :=
  .letS (.pquote (.lam .w none (.par .w))) (.fn .F)
    (.letS (nm .y) (k .n0) (got1 (nm .y)) none) none

theorem cross_admissible :
    crossQ.Admissible ∧ ∀ s body, clF s = some body → body.Admissible := by
  refine ⟨by decide +kernel, fun s body h => ?_⟩
  cases s <;> simp only [clF, reduceCtorEq, Option.some.injEq] at h
  subst h
  decide +kernel

/-- **The query has no quotation**, so the count over the query adds nothing,
and the cover of `y` is the inner `let` again.  The hole that will be written
is in the equation, and it is the equation's own cell. -/
theorem cross_cover :
    Src.quoteOcc DSp.y crossQ = 0 ∧
      findCoverQ [] (Src.direct crossQ) DSp.y false crossQ = some [2] ∧
      findCoverQ [.y] (Src.direct crossQ) DSp.y false crossQ = none := by
  and_intros <;> decide +kernel

/-- The two models on that program, under both sides: the equation's hole takes
the contextual code and the query's `$y` takes `0`, so both answer `(Got 0)`,
as the C draft does. -/
theorem cross_bags :
    slotAns cfgM.bothSides clF crossQ = some [got0] ∧
      answersDir .bothSides .static (progM .u .unit clF) 80 (elabMFormAtQ [] [] crossQ) =
        some [got0] := by
  and_intros <;> decide +kernel

/-- The equation's hole as the call of `F` at `[0, 0]` returns it, in the slot
model: the cell `([5], y)` of the equation's frame, copied at the activation
path `[0, 0, 2]`. -/
def crossHoleS : Nm (Slot DSp) := .inst [0, 0, 2] (.src ([5], .y))

/-- The query's `$y`, in the slot model under rule M: the root's cell. -/
def crossYS : Nm (Slot DSp) := .src ([], .y)

/-- The query's `$y`, in the slot model's lexical-fresh run of the translation:
the activation copy of the inner `let`'s cell. -/
def crossYL : Nm (Slot DSp) := .inst [1, 2] (.src ([2, 2], .y))

/-- The equation's hole as the call returns it, in the identity model: the head
cell of the equation's frame, copied at `[0, 0, 2]`. -/
def crossHoleI : Nm (BId DSp) := .inst [0, 0, 2] (.src (.slot ⟨.y, [5], [5], .head⟩))

/-- The query's `$y`, in the identity model: the inner `let`'s pattern cell. -/
def crossYI : Nm (BId DSp) := .src (.slot ⟨.y, [], [2], .pat⟩)

/-- What the hole takes, in the slot model: the pattern's body read along the
value's binder, as contextual code. -/
def crossCtxS : GVal DSym (Slot DSp) := .ctx [.src ([9, 1], .z)] (.pvar (.src ([9, 1], .z)))

/-- What the hole takes, in the identity model. -/
def crossCtxI : GVal DSym (BId DSp) :=
  .ctx [.src (.code .z [9, 1])] (.pvar (.src (.code .z [9, 1])))

/-- A final store of the program in the slot model, with `q` the query's `$y`:
`q` holds `0`, the call's copy of the hole holds the contextual code, nothing
else is bound. -/
def crossStoreS (q : Nm (Slot DSp)) : GStore DSym (Slot DSp) := fun n =>
  if n = q then some (.sym .n0) else if n = crossHoleS then some crossCtxS else none

/-- The final store of the program in the identity model. -/
def crossStoreI : GStore DSym (BId DSp) := fun n =>
  if n = crossYI then some (.sym .n0) else if n = crossHoleI then some crossCtxI else none

/-- **The slot model's rule-M run** of the program, under both sides: one
result, `(Got $y)` under the store where `$y` holds `0` and the call's copy of
the equation's hole holds the contextual code.  Before the hole belonged to the
equation it had no result. -/
theorem cross_runS : slotRun cfgM.bothSides clF crossQ 80 =
    some [(.app (.sym .Got) (.var crossYS), crossStoreS crossYS)] := by rfl

/-- **The slot model's lexical-fresh run** of the translation, under both sides. -/
theorem cross_runL : slotRun cfgLF.bothSides (toLexicalProg clF) (toLexicalQ [] crossQ) 80 =
    some [(.app (.sym .Got) (.var crossYL), crossStoreS crossYL)] := by rfl

/-- **The identity model's rule-M run** of the program with the count over the
query, under both sides. -/
theorem cross_runI : idRunM .bothSides clF (elabMFormAtQ [] [] crossQ) 80 =
    some [(.app (.sym .Got) (.var crossYI), crossStoreI)] := by rfl

/-- The renaming from the slot model's names to the identity model's, with `q`
the slot name of the query's `$y`. -/
def crossRen (q : Nm (Slot DSp)) (n : Nm (Slot DSp)) : Nm (BId DSp) :=
  if n = q then crossYI else if n = crossHoleS then crossHoleI else codeFwd n

/-- **A slot result of the program is a renaming of the identity result**, with
either slot name of the query's `$y`. -/
theorem cross_renamed {q : Nm (Slot DSp)} (hq : q = crossYS ∨ q = crossYL) :
    Renamed (.app (.sym .Got) (.var q), crossStoreS q)
      (.app (.sym .Got) (.var crossYI), crossStoreI) := by
  have hq1 : crossRen q q = crossYI := by simp [crossRen]
  have hqh : q ≠ crossHoleS := by rcases hq with rfl | rfl <;> decide
  have hq2 : crossRen q crossHoleS = crossHoleI := by simp [crossRen, Ne.symm hqh]
  have hv : scVarHole q crossYI := by
    unfold scVarHole
    rcases hq with rfl | rfl <;> rfl
  have hqc : ¬ holeCopy (SC : Setting DSym (Slot DSp) (BId DSp)) q := by
    rcases hq with rfl | rfl
    · exact fun h => h
    · show ¬ (([2, 2] : Owner) = [] ∨ ([2, 2] : Owner) = [5])
      decide
  refine ⟨crossRen q, codeFwd, {q, crossHoleS}, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    have : n = q := by simpa [freeNames] using hn
    rw [this]
    exact Set.mem_insert q _
  · intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · rw [hq1, hq2] at hab; exact absurd hab (by decide)
    · rw [hq1, hq2] at hab; exact absurd hab (by decide)
    · rfl
  · intro a ha b hb hca hcb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl
    · exact absurd hca hqc
    · rcases hb with rfl | rfl
      · exact absurd hcb hqc
      · rfl
  · have h := Rel.app (C := SC) (ν := crossRen q) (μ := codeFwd) (k := .val)
      (Rel.sym (C := SC) (ν := crossRen q) (μ := codeFwd) (k := .val) DSym.Got)
      (Rel.var (C := SC) (μ := codeFwd) (k := .val) q (hq1 ▸ hv))
    rw [hq1] at h
    exact h
  · refine ⟨fun n hn => ?_, fun n h => ?_, fun m h => ?_, fun n g h => ?_⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      rcases hn with rfl | rfl
      · rw [hq1]
        simp only [crossStoreS, crossStoreI]
        exact GRel.sym _
      · rw [hq2]
        simp only [crossStoreS, crossStoreI, if_neg (Ne.symm hqh)]
        simp only [show crossHoleI ≠ crossYI by decide, if_false]
        refine GRel.ctx ⟨trivial, fun n hn => by simp [codeVars] at hn, fun n hn => ?_⟩ rfl rfl
        simp only [codeBinders, List.mem_append, List.mem_singleton, or_self] at hn
        exact ⟨_, hn⟩
    · simp only [crossStoreS] at h
      split_ifs at h with h1 h2
      · rw [h1]
        exact Set.mem_insert q _
      · rw [h2]
        exact Set.mem_insert_of_mem q rfl
      · exact absurd rfl h
    · simp only [crossStoreI] at h
      split_ifs at h with h1 h2
      · exact ⟨q, Set.mem_insert q _, hq1.trans h1.symm⟩
      · exact ⟨crossHoleS, Set.mem_insert_of_mem q rfl, hq2.trans h2.symm⟩
      · exact absurd rfl h
    · intro m hm
      simp only [crossStoreS] at h
      split_ifs at h <;> injection h with h <;> subst h <;>
        simp [crossCtxS, GVal.toTm, sealedFree, codeVars] at hm

/-- **On that program the statement of `renaming_M`, read with both sides and
the count over the query, holds.**  Before the hole belonged to the equation it
was false there: the slot model had no result and the identity model one. -/
theorem cross_renaming_MQ_bothSides :
    RenamingStatement (slotRun cfgM.bothSides clF crossQ)
      (idRunM .bothSides clF (elabMFormAtQ [] [] crossQ)) := by
  refine ⟨⟨fun _ => ⟨80, _, cross_runI⟩, fun _ => ⟨80, _, cross_runS⟩⟩, fun e₁ e₂ => ?_⟩
  obtain rfl := runDir_det _ e₁ cross_runS
  obtain rfl := runDir_det _ e₂ cross_runI
  exact .cons (cross_renamed (Or.inl rfl)) .nil

/-- **On that program the statement of `transfer`, read with both sides and the
count over the query, holds.**  Before the hole belonged to the equation it was
false there: the two slot runs had results of different lengths. -/
theorem cross_transferQ_bothSides :
    TransferStatement (slotRun cfgLF.bothSides (toLexicalProg clF) (toLexicalQ [] crossQ))
      (slotRun cfgM.bothSides clF crossQ)
      (idRunM .bothSides clF (elabMFormAtQ [] [] crossQ)) := by
  refine ⟨⟨fun _ => ⟨80, _, cross_runS⟩, fun _ => ⟨80, _, cross_runL⟩⟩, fun e₁ e₂ => ?_⟩
  obtain rfl := runDir_det _ e₁ cross_runL
  obtain rfl := runDir_det _ e₂ cross_runS
  exact ⟨80, _, cross_runI, .cons (cross_renamed (Or.inr rfl)) .nil,
    .cons (cross_renamed (Or.inl rfl)) .nil⟩

/-- **With the equations' hole spellings listed, the models agree** on that
program, under both sides: `(Got 0)` in the slot model, in the identity model,
and in the slot model's lexical-fresh run of the translation. -/
theorem cross_holes_agree :
    slotAns cfgM.bothSides clF crossQ = some [got0] ∧
      answersDir .bothSides .static (progM .u .unit clF) 80 (elabMFormAtQ [.y] [] crossQ) =
        some [got0] ∧
      slotAns cfgLF.bothSides (toLexicalProg clF) (toLexicalQ [.y] crossQ) = some [got0] := by
  and_intros <;> decide +kernel

/-! ## Lexical fresh with both sides -/

/-- **Under lexical fresh and both sides the two models agree on these
programs**: the query with the hole, the program with the equation, the
first-order rows and the mixed filling through a parameter.  (The contextual
answer of the code row is `leak_bothSides`.) -/
theorem lexicalFresh_bothSides_agree :
    slotAns cfgLF.bothSides noCl coveredHole = some [got0] ∧ idLF .bothSides noCl coveredHole = some [got0] ∧
    slotAns cfgLF.bothSides clF crossQ = some [got0] ∧ idLF .bothSides clF crossQ = some [got0] ∧
    slotAns cfgLF.bothSides noCl valueSide = some [gotA] ∧
      idLF .bothSides noCl valueSide = some [gotA] ∧
    slotAns cfgLF.bothSides noCl twoNames = some [] ∧ idLF .bothSides noCl twoNames = some [] := by
  and_intros <;> decide +kernel

/-! ## More programs, both models, both sides -/

/-- An answer of the slot model, printed with every name by its spelling. -/
def spellS (t : Tm DSym (Slot DSp)) : SExp (SAtom DSym DSp) :=
  printAns (fun n => .var n.spelling) (fun n => .par n.spelling) t

/-- An answer of the identity model, printed with every name by its spelling. -/
def spellId (t : Tm DSym (BId DSp)) : SExp (SAtom DSym DSp) :=
  printAns (fun n => .var (IdSlot.spellI n)) (fun n => .par (IdSlot.spellI n)) t

/-- The equation `(= (F) (pair $x (quote (lam z $h))))`: a name of the equation
and a hole of sealed code, both unbound in its value. -/
def clPair : DSym → Option A
  | .F => some (pairOf (nm .x) (.quote (.lam .z none (nm .h))))
  | _ => none

/-- `(quote (lam w b))`, in pattern position. -/
def pqLamW (b : A) : A := .pquote (.lam .w none b)

/-- `(quote (lam z b))`. -/
def qLamZ (b : A) : A := .quote (.lam .z none b)

/-- Programs that fill a value side in the situations where the two models
allocate differently: a name of an equation and a hole of its code; a lambda
called twice whose body fills one hole; a name a `let` introduces that is
spelled like a hole; contextual code matched again; a lambda called twice whose
body fills a name; alternatives on either side; a `new` name on the value side;
a lambda with a crossing set; a hole behind data; a hole spelled like a name a
later `let` binds. -/
def stressRows : List A :=
  [ .letS (pairOf (k .a) (pqLamW (.par .w))) (.fn .F) (got2 (nm .h) (nm .x)) none,
    .letS (nm .m)
      (.lam .y none (.letS (pqLamW (fOf (.par .w))) (qLamZ (nm .h)) (got1 (nm .h)) none))
      (pairOf (ap (nm .m) (k .a)) (ap (nm .m) (k .n0))) none,
    .letS (nm .h) (k .a) (.letS (pqLamW (.par .w)) (qLamZ (nm .h)) (got1 (nm .h)) none) none,
    .letS (pqLamW (.par .w)) (qLamZ (nm .h))
      (.letS (pqLamW (nm .x)) (qLamZ (nm .h)) (got2 (nm .h) (nm .x)) none) none,
    .letS (nm .m) (.lam .y none (.letS (fOf (.par .y)) (fOf (nm .x)) (got1 (nm .x)) none))
      (pairOf (ap (nm .m) (k .a)) (ap (nm .m) (k .n0))) none,
    .letS (fOf (.alt (k .a) (k .n0))) (fOf (nm .x)) (got1 (nm .x)) none,
    .letS (fOf (k .a)) (.alt (fOf (nm .x)) (fOf (nm .y))) (got2 (nm .x) (nm .y)) none,
    .new [.x] (.letS (fOf (k .a)) (fOf (nm .x)) (got1 (nm .x)) none),
    ap (.lam .y (some [.x])
      (.letS (pairOf (k .a) (.par .y)) (pairOf (nm .x) (nm .h)) (got2 (nm .x) (nm .h)) none))
      (k .n0),
    .letS (pqLamW (.par .w)) (ap (k .f) (.fn .F)) (k .ok) none,
    .letS (pairOf (nm .x) (pqLamW (fOf (.par .w)))) (.fn .F)
      (.letS (nm .h) (k .n0) (got2 (nm .x) (nm .h)) none) none ]

/-- **On these programs the two models agree under both sides**: every program
is admissible, and the bags print alike, names by spelling, under lexical fresh,
and under rule M with the equations' hole spelling `h` listed.  A check of
eleven programs, not a theorem about all. -/
theorem stress_bothSides_agree :
    stressRows.all (fun t =>
      decide t.Admissible &&
      decide ((slotAns cfgLF.bothSides clPair t).map (List.map spellS) =
        (idLF .bothSides clPair t).map (List.map spellId)) &&
      decide ((slotAns cfgM.bothSides clPair t).map (List.map spellS) =
        (answersDir .bothSides .static (progM .u .unit clPair) 80
          (elabMFormAtQ [.h] [] t)).map (List.map spellId))) = true := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionExamples
