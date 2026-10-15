import Mettapedia.Logic.HostingStyles.StoredPrograms.Letters
import Mettapedia.Logic.HostingStyles.StoredPrograms.SharedHost

/-!
# Comparing data by rules: the equality of data, and matching

With names written in a finite alphabet (`letterSpelling`), sixty-one rules
compare two data, constructor by constructor (`comparisonRules`).  The helper
`same` takes a mode and two data.

* In the mode `exact` it decides whether the two data are equal.  The
  primitive `nik:data-eq` of the larger host is one rule that calls it
  (`dataEqualityRule`), and it agrees with the host on all data
  (`dataEquality_realized`).
* In the mode `open` a variable of the first datum agrees with everything.
  The first datum is then a pattern, and the helper decides whether the engine
  matches the pattern against the second (`agree_open`).  This is what a
  table needs to follow the engine's first match (`Sequential.lean`).

`agree wild pattern value` is the function that the rules compute
(`same_reduces`): in the mode `exact` it is equality (`agree_exact_iff`), and
in the mode `open` it is whether `matchTerm` succeeds (`agree_open`).

The rules are complete case distinctions: for every two kinds of data there
is one rule, so with the rules of the shared host they are a stored table,
hence orthogonal (`libraryRules_stored`).  Names
are compared letter by letter and letters digit by digit; numbers by the
rules of `Naturals.lean`, and the marks of their spelling beside them, so two
literals that spell one number in two ways are different data, as for the
host.

**Why a finite alphabet.**  With a name written as one constant, a rule
mentions the constants it compares, and a finite table mentions finitely many:
no finite table decides the equality of two symbols written as constants
(`Obstruction.lean`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Host Env natural boolean dataEqualityHost matchTerm matchTerms PrimitiveResult)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces inst)
open Mettapedia.Logic.HostingStyles.AtomsReduce (RunnableEquations programTheory)

/-- Fire a rule: unfold it, compute the instance, compare. -/
macro "side" "[" names:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [$names,*]; (try instances); (try rfl)))

/-! ## The terms of the helpers -/

/-- The truth value `True`, with names in letters. -/
abbrev yes : LF.Term := truth letterSpelling true

/-- The truth value `False`, with names in letters. -/
abbrev no : LF.Term := truth letterSpelling false

/-- A cell: a first term and the cells of the rest. -/
abbrev cell (first rest : LF.Term) : LF.Term := .app (.app (.con "cons") first) rest

abbrev sameLetter (first second : LF.Term) : LF.Term := libTerm "same-letter" [first, second]
abbrev sameName (first second : LF.Term) : LF.Term := libTerm "same-name" [first, second]
abbrev sameMark (first second : LF.Term) : LF.Term := libTerm "same-mark" [first, second]
abbrev bothTerm (first second : LF.Term) : LF.Term := libTerm "both" [first, second]
abbrev sameNumber (first second : LF.Term) : LF.Term := libTerm "nat-eq" [first, second]

/-- The comparison of two data in a mode. -/
abbrev same (mode first second : LF.Term) : LF.Term := libTerm "same" [mode, first, second]

/-- The comparison of the cells of two lists of data in a mode. -/
abbrev sameItems (mode first second : LF.Term) : LF.Term :=
  libTerm "same-items" [mode, first, second]

/-- **The mode of a comparison**: `open` when a variable of the first datum
agrees with everything, `exact` otherwise. -/
def modeTerm (wild : Bool) : LF.Term := .con (if wild then "open" else "exact")

/-! ## Conjunction -/

namespace Both

def whenYes : RewriteRule := ⟨bothTerm yes (.var 0), .var 0⟩
def whenNo : RewriteRule := ⟨bothTerm no (.var 0), no⟩

end Both

/-- **The rules of the conjunction of two truth values.** -/
def bothRules : List RewriteRule := [Both.whenYes, Both.whenNo]

/-- The conjunction of two terms that reduce to truth values. -/
theorem both_reduces {theory : Theory} (holds : Holds theory bothRules) {first second : LF.Term}
    {left right : Bool} (firstReduces : Reduces theory first (truth letterSpelling left))
    (secondReduces : Reduces theory second (truth letterSpelling right)) :
    Reduces theory (bothTerm first second) (truth letterSpelling (left && right)) := by
  have start : Reduces theory (bothTerm first second) (bothTerm (truth letterSpelling left) second) :=
    reduces_libTerm "both" (.cons firstReduces (.cons .refl .nil))
  cases left with
  | true =>
      exact (start.trans (fires (rule := Both.whenYes) (holds _ (by simp [bothRules])) [second]
        (by side [Both.whenYes]) (by side [Both.whenYes]))).trans secondReduces
  | false =>
      exact start.trans (fires (rule := Both.whenNo) (holds _ (by simp [bothRules])) [second]
        (by side [Both.whenNo]) (by side [Both.whenNo]))

/-! ## Letters -/

namespace SameLetter

abbrev nought (rest : LF.Term) : LF.Term := .app (.con "nought") rest
abbrev one (rest : LF.Term) : LF.Term := .app (.con "one") rest

def endEnd : RewriteRule := ⟨sameLetter (.con "end") (.con "end"), yes⟩
def endNought : RewriteRule := ⟨sameLetter (.con "end") (nought (.var 0)), no⟩
def endOne : RewriteRule := ⟨sameLetter (.con "end") (one (.var 0)), no⟩
def noughtEnd : RewriteRule := ⟨sameLetter (nought (.var 0)) (.con "end"), no⟩
def oneEnd : RewriteRule := ⟨sameLetter (one (.var 0)) (.con "end"), no⟩
def noughtNought : RewriteRule :=
  ⟨sameLetter (nought (.var 0)) (nought (.var 1)), sameLetter (.var 0) (.var 1)⟩
def oneOne : RewriteRule := ⟨sameLetter (one (.var 0)) (one (.var 1)), sameLetter (.var 0) (.var 1)⟩
def noughtOne : RewriteRule := ⟨sameLetter (nought (.var 0)) (one (.var 1)), no⟩
def oneNought : RewriteRule := ⟨sameLetter (one (.var 0)) (nought (.var 1)), no⟩

end SameLetter

/-- **The rules that compare two letters**, digit by digit. -/
def sameLetterRules : List RewriteRule :=
  [SameLetter.endEnd, SameLetter.endNought, SameLetter.endOne, SameLetter.noughtEnd,
    SameLetter.oneEnd, SameLetter.noughtNought, SameLetter.oneOne, SameLetter.noughtOne,
    SameLetter.oneNought]

/-- **The helper decides the equality of two letters.** -/
theorem sameLetter_reduces {theory : Theory} (holds : Holds theory sameLetterRules) :
    ∀ first second : List Bool,
      Reduces theory (sameLetter (digitsTerm first) (digitsTerm second))
        (truth letterSpelling (decide (first = second)))
  | [], [] =>
      fires (rule := SameLetter.endEnd) (holds _ (by simp [sameLetterRules])) []
        (by side [SameLetter.endEnd]) (by side [SameLetter.endEnd])
  | [], false :: rest =>
      fires (rule := SameLetter.endNought) (holds _ (by simp [sameLetterRules]))
        [digitsTerm rest] (by side [SameLetter.endNought]) (by side [SameLetter.endNought])
  | [], true :: rest =>
      fires (rule := SameLetter.endOne) (holds _ (by simp [sameLetterRules])) [digitsTerm rest]
        (by side [SameLetter.endOne]) (by side [SameLetter.endOne])
  | false :: rest, [] =>
      fires (rule := SameLetter.noughtEnd) (holds _ (by simp [sameLetterRules]))
        [digitsTerm rest] (by side [SameLetter.noughtEnd]) (by side [SameLetter.noughtEnd])
  | true :: rest, [] =>
      fires (rule := SameLetter.oneEnd) (holds _ (by simp [sameLetterRules])) [digitsTerm rest]
        (by side [SameLetter.oneEnd]) (by side [SameLetter.oneEnd])
  | false :: rest, true :: others =>
      fires (rule := SameLetter.noughtOne) (holds _ (by simp [sameLetterRules]))
        [digitsTerm rest, digitsTerm others] (by side [SameLetter.noughtOne])
        (by side [SameLetter.noughtOne])
  | true :: rest, false :: others =>
      fires (rule := SameLetter.oneNought) (holds _ (by simp [sameLetterRules]))
        [digitsTerm rest, digitsTerm others] (by side [SameLetter.oneNought])
        (by side [SameLetter.oneNought])
  | false :: rest, false :: others => by
      have step : Reduces theory (sameLetter (digitsTerm (false :: rest)) (digitsTerm (false :: others)))
          (sameLetter (digitsTerm rest) (digitsTerm others)) :=
        fires (rule := SameLetter.noughtNought) (holds _ (by simp [sameLetterRules]))
          [digitsTerm rest, digitsTerm others] (by side [SameLetter.noughtNought])
          (by side [SameLetter.noughtNought])
      have same : decide (false :: rest = false :: others) = decide (rest = others) := by simp
      rw [same]
      exact step.trans (sameLetter_reduces holds rest others)
  | true :: rest, true :: others => by
      have step : Reduces theory (sameLetter (digitsTerm (true :: rest)) (digitsTerm (true :: others)))
          (sameLetter (digitsTerm rest) (digitsTerm others)) :=
        fires (rule := SameLetter.oneOne) (holds _ (by simp [sameLetterRules]))
          [digitsTerm rest, digitsTerm others] (by side [SameLetter.oneOne])
          (by side [SameLetter.oneOne])
      have same : decide (true :: rest = true :: others) = decide (rest = others) := by simp
      rw [same]
      exact step.trans (sameLetter_reduces holds rest others)

/-! ## Names -/

namespace SameName

def nilNil : RewriteRule := ⟨sameName (.con "nil") (.con "nil"), yes⟩
def nilCons : RewriteRule := ⟨sameName (.con "nil") (cell (.var 0) (.var 1)), no⟩
def consNil : RewriteRule := ⟨sameName (cell (.var 0) (.var 1)) (.con "nil"), no⟩
def consCons : RewriteRule :=
  ⟨sameName (cell (.var 0) (.var 1)) (cell (.var 2) (.var 3)),
    bothTerm (sameLetter (.var 0) (.var 2)) (sameName (.var 1) (.var 3))⟩

end SameName

/-- **The rules that compare two names**, letter by letter. -/
def sameNameRules : List RewriteRule :=
  [SameName.nilNil, SameName.nilCons, SameName.consNil, SameName.consCons]

/-- The rules of names, letters and conjunction. -/
def nameRules : List RewriteRule := sameNameRules ++ (sameLetterRules ++ bothRules)

/-- **The helper decides the equality of two lists of letters.** -/
theorem sameLetters_reduces {theory : Theory} (holds : Holds theory nameRules) :
    ∀ first second : List (List Bool),
      Reduces theory (sameName (lettersTerm first) (lettersTerm second))
        (truth letterSpelling (decide (first = second)))
  | [], [] =>
      fires (rule := SameName.nilNil) (holds.left _ (by simp [sameNameRules])) []
        (by side [SameName.nilNil]) (by side [SameName.nilNil])
  | [], letter :: rest =>
      fires (rule := SameName.nilCons) (holds.left _ (by simp [sameNameRules]))
        [digitsTerm letter, lettersTerm rest] (by side [SameName.nilCons])
        (by side [SameName.nilCons])
  | letter :: rest, [] =>
      fires (rule := SameName.consNil) (holds.left _ (by simp [sameNameRules]))
        [digitsTerm letter, lettersTerm rest] (by side [SameName.consNil])
        (by side [SameName.consNil])
  | letter :: rest, other :: others => by
      have step : Reduces theory (sameName (lettersTerm (letter :: rest)) (lettersTerm (other :: others)))
          (bothTerm (sameLetter (digitsTerm letter) (digitsTerm other))
            (sameName (lettersTerm rest) (lettersTerm others))) :=
        fires (rule := SameName.consCons) (holds.left _ (by simp [sameNameRules]))
          [digitsTerm letter, lettersTerm rest, digitsTerm other, lettersTerm others]
          (by side [SameName.consCons]) (by side [SameName.consCons])
      have same : decide (letter :: rest = other :: others) =
          (decide (letter = other) && decide (rest = others)) := by simp
      rw [same]
      exact step.trans (both_reduces holds.right.right
        (sameLetter_reduces holds.right.left letter other) (sameLetters_reduces holds rest others))

/-- **The helper decides the equality of two names.** -/
theorem sameName_reduces {theory : Theory} (holds : Holds theory nameRules) (first second : String) :
    Reduces theory (sameName (letterSpelling.write first) (letterSpelling.write second))
      (truth letterSpelling (first == second)) := by
  have same : (first == second) = decide (lettersOf first = lettersOf second) := by
    rw [Bool.eq_iff_iff]
    simp [lettersOf_injective.eq_iff]
  rw [same]
  exact sameLetters_reduces holds (lettersOf first) (lettersOf second)

/-! ## The marks of numbers -/

namespace SameMark

def canonCanon : RewriteRule := ⟨sameMark (.con "canon") (.con "canon"), yes⟩
def canonSpelled : RewriteRule := ⟨sameMark (.con "canon") (tag "spelled" (.var 0)), no⟩
def spelledCanon : RewriteRule := ⟨sameMark (tag "spelled" (.var 0)) (.con "canon"), no⟩
def spelledSpelled : RewriteRule :=
  ⟨sameMark (tag "spelled" (.var 0)) (tag "spelled" (.var 1)), sameName (.var 0) (.var 1)⟩

end SameMark

/-- **The rules that compare the marks of two numbers.** -/
def sameMarkRules : List RewriteRule :=
  [SameMark.canonCanon, SameMark.canonSpelled, SameMark.spelledCanon, SameMark.spelledSpelled]

/-- The mark of a literal that spells a number. -/
def markOf (spelling : String) (value : Nat) : LF.Term :=
  if value.repr = spelling then .con "canon" else tag "spelled" (letterSpelling.write spelling)

theorem literal_of_number {spelling : String} {value : Nat}
    (spelled : spelledNumber spelling = some value) :
    literal letterSpelling spelling = numbered (unary value) (markOf spelling value) := by
  simp only [literal, spelled, markOf]
  split <;> rfl

theorem literal_of_name {spelling : String} (spelled : spelledNumber spelling = none) :
    literal letterSpelling spelling = tag "lit" (letterSpelling.write spelling) := by
  simp only [literal, spelled]

/-- **The helper decides whether two literals of one number are one
literal.** -/
theorem sameMark_reduces {theory : Theory} (holds : Holds theory (sameMarkRules ++ nameRules))
    (first second : String) (value : Nat) :
    Reduces theory (sameMark (markOf first value) (markOf second value))
      (truth letterSpelling (first == second)) := by
  unfold markOf
  by_cases firstCanon : value.repr = first <;> by_cases secondCanon : value.repr = second
  · have equal : (first == second) = true := by simp [← firstCanon, ← secondCanon]
    rw [if_pos firstCanon, if_pos secondCanon, equal]
    exact fires (rule := SameMark.canonCanon) (holds.left _ (by simp [sameMarkRules])) []
      (by side [SameMark.canonCanon]) (by side [SameMark.canonCanon])
  · have different : (first == second) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun equal => secondCanon (equal ▸ firstCanon)
    rw [if_pos firstCanon, if_neg secondCanon, different]
    exact fires (rule := SameMark.canonSpelled) (holds.left _ (by simp [sameMarkRules]))
      [letterSpelling.write second] (by side [SameMark.canonSpelled])
      (by side [SameMark.canonSpelled])
  · have different : (first == second) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun equal => firstCanon (equal ▸ secondCanon)
    rw [if_neg firstCanon, if_pos secondCanon, different]
    exact fires (rule := SameMark.spelledCanon) (holds.left _ (by simp [sameMarkRules]))
      [letterSpelling.write first] (by side [SameMark.spelledCanon])
      (by side [SameMark.spelledCanon])
  · rw [if_neg firstCanon, if_neg secondCanon]
    exact (fires (rule := SameMark.spelledSpelled) (holds.left _ (by simp [sameMarkRules]))
      [letterSpelling.write first, letterSpelling.write second]
      (by side [SameMark.spelledSpelled]) (by side [SameMark.spelledSpelled])).trans
      (sameName_reduces holds.right first second)

/-! ## Kinds of data -/

/-- **The kinds of readings of data**: a symbol, a variable, a literal that
spells no number, a number, an expression, a list value. -/
inductive Kind where
  | sym | var | lit | num | expr | list
  deriving DecidableEq, Repr

/-- All kinds. -/
def allKinds : List Kind := [.sym, .var, .lit, .num, .expr, .list]

theorem mem_allKinds (kind : Kind) : kind ∈ allKinds := by
  cases kind <;> simp [allKinds]

/-- The pattern of a kind, with its pattern variables from a position. -/
def Kind.pattern (kind : Kind) (position : Nat) : LF.Term :=
  match kind with
  | .sym => tag "sym" (.var position)
  | .var => tag "var" (.var position)
  | .lit => tag "lit" (.var position)
  | .num => numbered (.var position) (.var (position + 1))
  | .expr => tag "expr" (.var position)
  | .list => tag "list" (.var position)

/-- The reading of a kind with a content, and a mark for a number. -/
def Kind.reading (kind : Kind) (content mark : LF.Term) : LF.Term :=
  match kind with
  | .sym => tag "sym" content
  | .var => tag "var" content
  | .lit => tag "lit" content
  | .num => numbered content mark
  | .expr => tag "expr" content
  | .list => tag "list" content

theorem Kind.inst_pattern (kind : Kind) (assignment : Nat → LF.Term) (position : Nat) :
    inst assignment (kind.pattern position) =
      kind.reading (assignment position) (assignment (position + 1)) := by
  cases kind <;> simp [Kind.pattern, Kind.reading, inst_tag, inst_numbered]

/-- **The kind of a datum.** -/
def kindOf : EngineTerm → Kind
  | .sym _ => .sym
  | .var _ => .var
  | .lit spelling => if (spelledNumber spelling).isSome then .num else .lit
  | .expr _ => .expr
  | .list _ => .list

/-- The reading of a datum is the reading of its kind. -/
theorem datum_reading (term : EngineTerm) :
    ∃ content mark, datum letterSpelling term = (kindOf term).reading content mark := by
  cases term with
  | sym name => exact ⟨_, .con "canon", rfl⟩
  | var name => exact ⟨_, .con "canon", rfl⟩
  | expr items => exact ⟨_, .con "canon", rfl⟩
  | list items => exact ⟨_, .con "canon", rfl⟩
  | lit spelling =>
      cases spelled : spelledNumber spelling with
      | none =>
          refine ⟨letterSpelling.write spelling, .con "canon", ?_⟩
          simp only [datum, literal_of_name spelled, kindOf, spelled, Option.isSome_none,
            Bool.false_eq_true, if_false, Kind.reading]
      | some value =>
          refine ⟨unary value, markOf spelling value, ?_⟩
          simp only [datum, literal_of_number spelled, kindOf, spelled, Option.isSome_some, if_true,
            Kind.reading]

/-! ## Two data of two kinds -/

/-- The rule for a first datum of one kind and a second datum of another:
they do not agree. -/
def differentKindRule (first second : Kind) : RewriteRule :=
  ⟨same (.var 0) (first.pattern 1) (second.pattern 3), no⟩

/-- **The rules for two data of two kinds**, the first no variable. -/
def differentKindRules : List RewriteRule :=
  (allKinds.filter fun first => first ≠ .var).flatMap fun first =>
    (allKinds.filter fun second => second ≠ first).map fun second => differentKindRule first second

/-- The rule for a variable and a datum of another kind, in the mode
`exact`. -/
def exactVariableRule (second : Kind) : RewriteRule :=
  ⟨same (.con "exact") (tag "var" (.var 0)) (second.pattern 1), no⟩

/-- **The rules for a variable and a datum of another kind**, in the mode
`exact`. -/
def exactVariableRules : List RewriteRule :=
  (allKinds.filter fun second => second ≠ .var).map exactVariableRule

theorem differentKinds_reduce {theory : Theory} (holds : Holds theory differentKindRules)
    {first second : Kind} (notVariable : first ≠ .var) (different : second ≠ first)
    (mode content mark otherContent otherMark : LF.Term) :
    Reduces theory (same mode (first.reading content mark) (second.reading otherContent otherMark))
      no := by
  have member : differentKindRule first second ∈ differentKindRules :=
    List.mem_flatMap.mpr ⟨first, List.mem_filter.mpr ⟨mem_allKinds first, by simpa using notVariable⟩,
      List.mem_map.mpr ⟨second, List.mem_filter.mpr ⟨mem_allKinds second, by simpa using different⟩,
        rfl⟩⟩
  exact fires (rule := differentKindRule first second) (holds _ member)
    [mode, content, mark, otherContent, otherMark]
    (by simp only [differentKindRule, inst_libTerm, List.map_cons, List.map_nil, Kind.inst_pattern,
      Dedukti.inst_var, assign, List.getD_cons_zero, List.getD_cons_succ])
    (by side [differentKindRule])

theorem exactVariable_reduces {theory : Theory} (holds : Holds theory exactVariableRules)
    {second : Kind} (different : second ≠ .var) (name content mark : LF.Term) :
    Reduces theory (same (.con "exact") (tag "var" name) (second.reading content mark)) no := by
  have member : exactVariableRule second ∈ exactVariableRules :=
    List.mem_map.mpr ⟨second, List.mem_filter.mpr ⟨mem_allKinds second, by simpa using different⟩,
      rfl⟩
  exact fires (rule := exactVariableRule second) (holds _ member) [name, content, mark]
    (by simp only [exactVariableRule, inst_libTerm, List.map_cons, List.map_nil, Kind.inst_pattern,
      inst_tag, Dedukti.inst_var, Dedukti.inst_con, assign, List.getD_cons_zero,
      List.getD_cons_succ])
    (by side [exactVariableRule])

/-! ## Two data of one kind -/

namespace Same

def symbols : RewriteRule :=
  ⟨same (.var 0) (tag "sym" (.var 1)) (tag "sym" (.var 2)), sameName (.var 1) (.var 2)⟩

def literals : RewriteRule :=
  ⟨same (.var 0) (tag "lit" (.var 1)) (tag "lit" (.var 2)), sameName (.var 1) (.var 2)⟩

def numbers : RewriteRule :=
  ⟨same (.var 0) (numbered (.var 1) (.var 2)) (numbered (.var 3) (.var 4)),
    bothTerm (sameNumber (.var 1) (.var 3)) (sameMark (.var 2) (.var 4))⟩

def expressions : RewriteRule :=
  ⟨same (.var 0) (tag "expr" (.var 1)) (tag "expr" (.var 2)), sameItems (.var 0) (.var 1) (.var 2)⟩

def lists : RewriteRule :=
  ⟨same (.var 0) (tag "list" (.var 1)) (tag "list" (.var 2)), sameItems (.var 0) (.var 1) (.var 2)⟩

def variablesExact : RewriteRule :=
  ⟨same (.con "exact") (tag "var" (.var 0)) (tag "var" (.var 1)), sameName (.var 0) (.var 1)⟩

def variableOpen : RewriteRule := ⟨same (.con "open") (tag "var" (.var 0)) (.var 1), yes⟩

def nilNil : RewriteRule := ⟨sameItems (.var 0) (.con "nil") (.con "nil"), yes⟩

def nilCons : RewriteRule := ⟨sameItems (.var 0) (.con "nil") (cell (.var 1) (.var 2)), no⟩

def consNil : RewriteRule := ⟨sameItems (.var 0) (cell (.var 1) (.var 2)) (.con "nil"), no⟩

def consCons : RewriteRule :=
  ⟨sameItems (.var 0) (cell (.var 1) (.var 2)) (cell (.var 3) (.var 4)),
    bothTerm (same (.var 0) (.var 1) (.var 3)) (sameItems (.var 0) (.var 2) (.var 4))⟩

end Same

/-- **The rules for two data of one kind**, and for the cells of two lists. -/
def sameKindRules : List RewriteRule :=
  [Same.symbols, Same.literals, Same.numbers, Same.expressions, Same.lists, Same.variablesExact,
    Same.variableOpen, Same.nilNil, Same.nilCons, Same.consNil, Same.consCons]

/-- **The rule of `nik:data-eq`**: the comparison of its two arguments in the
mode `exact`. -/
def dataEqualityRule : RewriteRule :=
  ⟨callTerm "nik:data-eq" [.var 0, .var 1], same (.con "exact") (.var 0) (.var 1)⟩

/-- **The rules that compare data**: sixty-one rules. -/
def comparisonRules : List RewriteRule :=
  dataEqualityRule :: (sameKindRules ++ (differentKindRules ++ (exactVariableRules ++
    (sameMarkRules ++ nameRules))))

theorem comparisonRules_length : comparisonRules.length = 61 := by decide

/-! ## What the rules compute -/

mutual

/-- **Whether two data agree**: constructor by constructor; with `wild`, a
variable of the first agrees with everything. -/
def agree (wild : Bool) : EngineTerm → EngineTerm → Bool
  | .var name, value =>
      wild || (match value with
        | .var other => name == other
        | _ => false)
  | .sym name, value =>
      match value with
      | .sym other => name == other
      | _ => false
  | .lit spelling, value =>
      match value with
      | .lit other => spelling == other
      | _ => false
  | .expr items, value =>
      match value with
      | .expr others => agreeList wild items others
      | _ => false
  | .list items, value =>
      match value with
      | .list others => agreeList wild items others
      | _ => false

def agreeList (wild : Bool) : List EngineTerm → List EngineTerm → Bool
  | [], values => values.isEmpty
  | first :: rest, values =>
      match values with
      | value :: others => agree wild first value && agreeList wild rest others
      | [] => false

end

mutual

theorem agree_refl : ∀ term : EngineTerm, agree false term term = true
  | .var _ => by simp [agree]
  | .sym _ => by simp [agree]
  | .lit _ => by simp [agree]
  | .expr items => by simpa [agree] using agreeList_refl items
  | .list items => by simpa [agree] using agreeList_refl items

theorem agreeList_refl : ∀ items : List EngineTerm, agreeList false items items = true
  | [] => by simp [agreeList]
  | first :: rest => by simp [agreeList, agree_refl first, agreeList_refl rest]

end

mutual

theorem eq_of_agree : ∀ (first second : EngineTerm), agree false first second = true →
    first = second
  | .var _, .var _, agreed => by simp [agree] at agreed; rw [agreed]
  | .var _, .sym _, agreed | .var _, .lit _, agreed | .var _, .expr _, agreed
  | .var _, .list _, agreed => by simp [agree] at agreed
  | .sym _, .sym _, agreed => by simp [agree] at agreed; rw [agreed]
  | .sym _, .var _, agreed | .sym _, .lit _, agreed | .sym _, .expr _, agreed
  | .sym _, .list _, agreed => by simp [agree] at agreed
  | .lit _, .lit _, agreed => by simp [agree] at agreed; rw [agreed]
  | .lit _, .var _, agreed | .lit _, .sym _, agreed | .lit _, .expr _, agreed
  | .lit _, .list _, agreed => by simp [agree] at agreed
  | .expr items, .expr others, agreed => by
      rw [eq_of_agreeList items others (by simpa [agree] using agreed)]
  | .expr _, .var _, agreed | .expr _, .sym _, agreed | .expr _, .lit _, agreed
  | .expr _, .list _, agreed => by simp [agree] at agreed
  | .list items, .list others, agreed => by
      rw [eq_of_agreeList items others (by simpa [agree] using agreed)]
  | .list _, .var _, agreed | .list _, .sym _, agreed | .list _, .lit _, agreed
  | .list _, .expr _, agreed => by simp [agree] at agreed

theorem eq_of_agreeList : ∀ (first second : List EngineTerm), agreeList false first second = true →
    first = second
  | [], [], _ => rfl
  | [], _ :: _, agreed => by simp [agreeList] at agreed
  | _ :: _, [], agreed => by simp [agreeList] at agreed
  | first :: rest, second :: others, agreed => by
      simp only [agreeList, Bool.and_eq_true] at agreed
      rw [eq_of_agree first second agreed.1, eq_of_agreeList rest others agreed.2]

end

/-- **In the mode `exact`, two data agree exactly when they are equal.** -/
theorem agree_exact_iff (first second : EngineTerm) : agree false first second = true ↔ first = second :=
  ⟨eq_of_agree first second, fun same => same ▸ agree_refl first⟩

mutual

/-- **In the mode `open`, a pattern agrees with a value exactly when the
engine matches it.** -/
theorem agree_open : ∀ (term value : EngineTerm),
    agree true term value = (matchTerm term value).isSome
  | .var _, _ => by simp [agree, matchTerm]
  | .sym name, value => by
      cases value <;> simp only [agree, matchTerm, Option.isSome_none]
      next other => by_cases same : name = other <;> simp [same]
  | .lit spelling, value => by
      cases value <;> simp only [agree, matchTerm, Option.isSome_none]
      next other => by_cases same : spelling = other <;> simp [same]
  | .expr items, value => by
      cases value <;> simp only [agree, matchTerm, Option.isSome_none]
      next others => exact agreeList_open items others
  | .list items, value => by
      cases value <;> simp only [agree, matchTerm, Option.isSome_none]
      next others => exact agreeList_open items others

theorem agreeList_open : ∀ (items values : List EngineTerm),
    agreeList true items values = (matchTerms items values).isSome
  | [], [] => by simp [agreeList, matchTerms]
  | [], _ :: _ => by simp [agreeList, matchTerms]
  | _ :: _, [] => by simp [agreeList, matchTerms]
  | first :: rest, value :: others => by
      simp only [agreeList, matchTerms, agree_open first value, agreeList_open rest others]
      cases matchTerm first value <;> cases matchTerms rest others <;> rfl

end

/-- Two data of two kinds do not agree, unless the first is a variable in the
mode `open`. -/
theorem agree_of_kind_ne {wild : Bool} {first second : EngineTerm}
    (different : kindOf second ≠ kindOf first) (notWild : kindOf first ≠ .var ∨ wild = false) :
    agree wild first second = false := by
  cases first with
  | var name =>
      have exact : wild = false := notWild.resolve_left (by simp [kindOf])
      cases second <;> simp_all [agree, kindOf]
  | sym name => cases second <;> simp_all [agree, kindOf]
  | expr items => cases second <;> simp_all [agree, kindOf]
  | list items => cases second <;> simp_all [agree, kindOf]
  | lit spelling =>
      cases second with
      | lit other =>
          simp only [agree, beq_eq_false_iff_ne, ne_eq]
          intro equal
          exact different (by rw [equal])
      | var _ => simp [agree]
      | sym _ => simp [agree]
      | expr _ => simp [agree]
      | list _ => simp [agree]

/-! ## The rules compute it -/

/-- The parts of the comparison rules that a theory holds. -/
structure HoldsComparison (theory : Theory) : Prop where
  sameKind : Holds theory sameKindRules
  different : Holds theory differentKindRules
  exactVariable : Holds theory exactVariableRules
  marks : Holds theory (sameMarkRules ++ nameRules)
  numbers : Holds theory (equalNumbersRules letterSpelling)

theorem HoldsComparison.names {theory : Theory} (holds : HoldsComparison theory) :
    Holds theory nameRules := holds.marks.right

theorem HoldsComparison.both {theory : Theory} (holds : HoldsComparison theory) :
    Holds theory bothRules := holds.marks.right.right.right

/-- Two literals, compared. -/
theorem sameLiteral_reduces {theory : Theory} (holds : HoldsComparison theory) (mode : LF.Term)
    (first second : String) :
    Reduces theory (same mode (literal letterSpelling first) (literal letterSpelling second))
      (truth letterSpelling (first == second)) := by
  cases firstSpelled : spelledNumber first with
  | none =>
      cases secondSpelled : spelledNumber second with
      | none =>
          rw [literal_of_name firstSpelled, literal_of_name secondSpelled]
          exact (fires (rule := Same.literals) (holds.sameKind _ (by simp [sameKindRules]))
            [mode, letterSpelling.write first, letterSpelling.write second]
            (by side [Same.literals]) (by side [Same.literals])).trans
            (sameName_reduces holds.names first second)
      | some value =>
          have different : (first == second) = false := by
            rw [beq_eq_false_iff_ne]
            intro equal
            rw [equal, secondSpelled] at firstSpelled
            cases firstSpelled
          rw [literal_of_name firstSpelled, literal_of_number secondSpelled, different]
          exact differentKinds_reduce holds.different (first := .lit) (second := .num) (by decide)
            (by decide) mode _ (.con "canon") _ _
  | some value =>
      cases secondSpelled : spelledNumber second with
      | none =>
          have different : (first == second) = false := by
            rw [beq_eq_false_iff_ne]
            intro equal
            rw [equal, secondSpelled] at firstSpelled
            cases firstSpelled
          rw [literal_of_number firstSpelled, literal_of_name secondSpelled, different]
          exact differentKinds_reduce holds.different (first := .num) (second := .lit) (by decide)
            (by decide) mode _ _ _ (.con "canon")
      | some other =>
          rw [literal_of_number firstSpelled, literal_of_number secondSpelled]
          have step : Reduces theory
              (same mode (numbered (unary value) (markOf first value))
                (numbered (unary other) (markOf second other)))
              (bothTerm (sameNumber (unary value) (unary other))
                (sameMark (markOf first value) (markOf second other))) :=
            fires (rule := Same.numbers) (holds.sameKind _ (by simp [sameKindRules]))
              [mode, unary value, markOf first value, unary other, markOf second other]
              (by side [Same.numbers]) (by side [Same.numbers])
          have numbers := equalNumbers_reduces letterSpelling holds.numbers value other
          by_cases sameValue : value = other
          · subst sameValue
            have conjunction := both_reduces holds.both numbers
              (sameMark_reduces holds.marks first second value)
            simpa using step.trans conjunction
          · have different : (first == second) = false := by
              rw [beq_eq_false_iff_ne]
              intro equal
              rw [equal, secondSpelled] at firstSpelled
              exact sameValue (Option.some.inj firstSpelled).symm
            have refused : Reduces theory
                (bothTerm (sameNumber (unary value) (unary other))
                  (sameMark (markOf first value) (markOf second other))) no := by
              have start : Reduces theory
                  (bothTerm (sameNumber (unary value) (unary other))
                    (sameMark (markOf first value) (markOf second other)))
                  (bothTerm no (sameMark (markOf first value) (markOf second other))) := by
                have reduced := numbers
                simp only [sameValue, decide_false] at reduced
                exact reduces_libTerm "both" (.cons reduced (.cons .refl .nil))
              exact start.trans (fires (rule := Both.whenNo) (holds.both _ (by simp [bothRules]))
                [sameMark (markOf first value) (markOf second other)] (by side [Both.whenNo])
                (by side [Both.whenNo]))
            rw [different]
            exact step.trans refused

mutual

/-- **The rules compute the agreement of two data.** -/
theorem same_reduces {theory : Theory} (holds : HoldsComparison theory) (wild : Bool) :
    ∀ (first second : EngineTerm),
      Reduces theory
        (same (modeTerm wild) (datum letterSpelling first) (datum letterSpelling second))
        (truth letterSpelling (agree wild first second))
  | .var name, second => by
      cases wild with
      | true =>
          have agreed : agree true (.var name) second = true := by simp [agree]
          rw [agreed]
          exact fires (rule := Same.variableOpen) (holds.sameKind _ (by simp [sameKindRules]))
            [letterSpelling.write name, datum letterSpelling second]
            (by side [Same.variableOpen, modeTerm, datum]) (by side [Same.variableOpen])
      | false =>
          cases second with
          | var other =>
              have agreed : agree false (.var name) (.var other) = (name == other) := by
                simp [agree]
              rw [agreed]
              exact (fires (rule := Same.variablesExact)
                (holds.sameKind _ (by simp [sameKindRules]))
                [letterSpelling.write name, letterSpelling.write other]
                (by side [Same.variablesExact, modeTerm, datum])
                (by side [Same.variablesExact])).trans (sameName_reduces holds.names name other)
          | sym other =>
              exact exactVariable_reduces holds.exactVariable (second := .sym) (by decide) _ _
                (.con "canon")
          | expr others =>
              exact exactVariable_reduces holds.exactVariable (second := .expr) (by decide) _ _
                (.con "canon")
          | list others =>
              exact exactVariable_reduces holds.exactVariable (second := .list) (by decide) _ _
                (.con "canon")
          | lit other =>
              obtain ⟨content, mark, shape⟩ := datum_reading (.lit other)
              have different : kindOf (.lit other) ≠ .var := by
                simp only [kindOf]
                split <;> decide
              have refused := exactVariable_reduces holds.exactVariable different
                (letterSpelling.write name) content mark
              have disagreed : agree false (.var name) (.lit other) = false := by simp [agree]
              rw [disagreed, shape]
              exact refused
  | .sym name, second => by
      cases second with
      | sym other =>
          have agreed : agree wild (.sym name) (.sym other) = (name == other) := by simp [agree]
          rw [agreed]
          exact (fires (rule := Same.symbols) (holds.sameKind _ (by simp [sameKindRules]))
            [modeTerm wild, letterSpelling.write name, letterSpelling.write other]
            (by side [Same.symbols, datum]) (by side [Same.symbols])).trans
            (sameName_reduces holds.names name other)
      | var other =>
          exact differentKinds_reduce holds.different (first := .sym) (second := .var) (by decide)
            (by decide) _ _ (.con "canon") _ (.con "canon")
      | expr others =>
          exact differentKinds_reduce holds.different (first := .sym) (second := .expr)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | list others =>
          exact differentKinds_reduce holds.different (first := .sym) (second := .list)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | lit other =>
          obtain ⟨content, mark, shape⟩ := datum_reading (.lit other)
          have different : kindOf (.lit other) ≠ .sym := by
            simp only [kindOf]
            split <;> decide
          have refused := differentKinds_reduce holds.different (first := .sym) (by decide)
            different (modeTerm wild) (letterSpelling.write name) (.con "canon") content mark
          have disagreed : agree wild (.sym name) (.lit other) = false := by simp [agree]
          rw [disagreed, shape]
          exact refused
  | .lit spelling, second => by
      cases second with
      | lit other =>
          have agreed : agree wild (.lit spelling) (.lit other) = (spelling == other) := by
            simp [agree]
          rw [agreed]
          exact sameLiteral_reduces holds (modeTerm wild) spelling other
      | var other =>
          obtain ⟨content, mark, shape⟩ := datum_reading (.lit spelling)
          have notVariable : kindOf (.lit spelling) ≠ .var := by
            simp only [kindOf]
            split <;> decide
          have refused := differentKinds_reduce holds.different (second := .var) notVariable
            notVariable.symm (modeTerm wild) content mark (letterSpelling.write other) (.con "canon")
          have disagreed : agree wild (.lit spelling) (.var other) = false := by simp [agree]
          rw [disagreed, shape]
          exact refused
      | sym other =>
          obtain ⟨content, mark, shape⟩ := datum_reading (.lit spelling)
          have notVariable : kindOf (.lit spelling) ≠ .var := by
            simp only [kindOf]
            split <;> decide
          have notSymbol : Kind.sym ≠ kindOf (.lit spelling) := by
            simp only [kindOf]
            split <;> decide
          have refused := differentKinds_reduce holds.different (second := .sym) notVariable
            notSymbol (modeTerm wild) content mark (letterSpelling.write other) (.con "canon")
          have disagreed : agree wild (.lit spelling) (.sym other) = false := by simp [agree]
          rw [disagreed, shape]
          exact refused
      | expr others =>
          obtain ⟨content, mark, shape⟩ := datum_reading (.lit spelling)
          have notVariable : kindOf (.lit spelling) ≠ .var := by
            simp only [kindOf]
            split <;> decide
          have notExpression : Kind.expr ≠ kindOf (.lit spelling) := by
            simp only [kindOf]
            split <;> decide
          have refused := differentKinds_reduce holds.different (second := .expr) notVariable
            notExpression (modeTerm wild) content mark (cells (data letterSpelling others))
            (.con "canon")
          have disagreed : agree wild (.lit spelling) (.expr others) = false := by simp [agree]
          rw [disagreed, shape]
          exact refused
      | list others =>
          obtain ⟨content, mark, shape⟩ := datum_reading (.lit spelling)
          have notVariable : kindOf (.lit spelling) ≠ .var := by
            simp only [kindOf]
            split <;> decide
          have notList : Kind.list ≠ kindOf (.lit spelling) := by
            simp only [kindOf]
            split <;> decide
          have refused := differentKinds_reduce holds.different (second := .list) notVariable
            notList (modeTerm wild) content mark (cells (data letterSpelling others)) (.con "canon")
          have disagreed : agree wild (.lit spelling) (.list others) = false := by simp [agree]
          rw [disagreed, shape]
          exact refused
  | .expr items, second => by
      cases second with
      | expr others =>
          have agreed : agree wild (.expr items) (.expr others) = agreeList wild items others := by
            simp [agree]
          rw [agreed]
          exact (fires (rule := Same.expressions) (holds.sameKind _ (by simp [sameKindRules]))
            [modeTerm wild, cells (data letterSpelling items), cells (data letterSpelling others)]
            (by side [Same.expressions, datum]) (by side [Same.expressions])).trans
            (sameItems_reduces holds wild items others)
      | var other =>
          exact differentKinds_reduce holds.different (first := .expr) (second := .var)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | sym other =>
          exact differentKinds_reduce holds.different (first := .expr) (second := .sym)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | list others =>
          exact differentKinds_reduce holds.different (first := .expr) (second := .list)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | lit other =>
          obtain ⟨content, mark, shape⟩ := datum_reading (.lit other)
          have different : kindOf (.lit other) ≠ .expr := by
            simp only [kindOf]
            split <;> decide
          have refused := differentKinds_reduce holds.different (first := .expr) (by decide)
            different (modeTerm wild) (cells (data letterSpelling items)) (.con "canon") content mark
          have disagreed : agree wild (.expr items) (.lit other) = false := by simp [agree]
          rw [disagreed, shape]
          exact refused
  | .list items, second => by
      cases second with
      | list others =>
          have agreed : agree wild (.list items) (.list others) = agreeList wild items others := by
            simp [agree]
          rw [agreed]
          exact (fires (rule := Same.lists) (holds.sameKind _ (by simp [sameKindRules]))
            [modeTerm wild, cells (data letterSpelling items), cells (data letterSpelling others)]
            (by side [Same.lists, datum]) (by side [Same.lists])).trans
            (sameItems_reduces holds wild items others)
      | var other =>
          exact differentKinds_reduce holds.different (first := .list) (second := .var)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | sym other =>
          exact differentKinds_reduce holds.different (first := .list) (second := .sym)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | expr others =>
          exact differentKinds_reduce holds.different (first := .list) (second := .expr)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | lit other =>
          obtain ⟨content, mark, shape⟩ := datum_reading (.lit other)
          have different : kindOf (.lit other) ≠ .list := by
            simp only [kindOf]
            split <;> decide
          have refused := differentKinds_reduce holds.different (first := .list) (by decide)
            different (modeTerm wild) (cells (data letterSpelling items)) (.con "canon") content mark
          have disagreed : agree wild (.list items) (.lit other) = false := by simp [agree]
          rw [disagreed, shape]
          exact refused

/-- The rules compute the agreement of the cells of two lists of data. -/
theorem sameItems_reduces {theory : Theory} (holds : HoldsComparison theory) (wild : Bool) :
    ∀ (items values : List EngineTerm),
      Reduces theory
        (sameItems (modeTerm wild) (cells (data letterSpelling items))
          (cells (data letterSpelling values)))
        (truth letterSpelling (agreeList wild items values))
  | [], [] =>
      fires (rule := Same.nilNil) (holds.sameKind _ (by simp [sameKindRules])) [modeTerm wild]
        (by side [Same.nilNil, data, cells]) (by side [Same.nilNil])
  | [], value :: others =>
      fires (rule := Same.nilCons) (holds.sameKind _ (by simp [sameKindRules]))
        [modeTerm wild, datum letterSpelling value, cells (data letterSpelling others)]
        (by side [Same.nilCons, data, cells]) (by side [Same.nilCons])
  | first :: rest, [] =>
      fires (rule := Same.consNil) (holds.sameKind _ (by simp [sameKindRules]))
        [modeTerm wild, datum letterSpelling first, cells (data letterSpelling rest)]
        (by side [Same.consNil, data, cells]) (by side [Same.consNil])
  | first :: rest, value :: others => by
      have step : Reduces theory
          (sameItems (modeTerm wild) (cells (data letterSpelling (first :: rest)))
            (cells (data letterSpelling (value :: others))))
          (bothTerm (same (modeTerm wild) (datum letterSpelling first) (datum letterSpelling value))
            (sameItems (modeTerm wild) (cells (data letterSpelling rest))
              (cells (data letterSpelling others)))) :=
        fires (rule := Same.consCons) (holds.sameKind _ (by simp [sameKindRules]))
          [modeTerm wild, datum letterSpelling first, cells (data letterSpelling rest),
            datum letterSpelling value, cells (data letterSpelling others)]
          (by side [Same.consCons, data, cells]) (by side [Same.consCons])
      have agreed : agreeList wild (first :: rest) (value :: others) =
          (agree wild first value && agreeList wild rest others) := by simp [agreeList]
      rw [agreed]
      exact step.trans (both_reduces holds.both (same_reduces holds wild first value)
        (sameItems_reduces holds wild rest others))

end

/-! ## The equality of data, as the larger host computes it -/

/-- A theory that holds the comparison rules and the rules for numbers. -/
theorem holdsComparison_of_holds {theory : Theory} (holds : Holds theory comparisonRules)
    (numbers : Holds theory (equalNumbersRules letterSpelling)) : HoldsComparison theory where
  sameKind := fun rule member =>
    holds rule (List.mem_cons_of_mem _ (List.mem_append_left _ member))
  different := fun rule member =>
    holds rule (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _ member)))
  exactVariable := fun rule member =>
    holds rule (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ member))))
  marks := fun rule member =>
    holds rule (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ member))))
  numbers := numbers

theorem dataEquality_unfold (arguments : List EngineTerm) :
    dataEqualityHost.primitive "nik:data-eq" arguments =
      (match arguments with
        | [left, right] => .value (boolean (decide (left = right)))
        | _ => .fault) := rfl

/-- **The rules agree with the larger host on the equality of data**, on all
data, with names in letters. -/
theorem dataEquality_realized {theory : Theory} (holds : Holds theory comparisonRules)
    (numbers : Holds theory (equalNumbersRules letterSpelling)) :
    RealizesPrimitives letterSpelling theory dataEqualityHost ["nik:data-eq"] := by
  intro head member arguments result returned
  obtain rfl : head = "nik:data-eq" := List.mem_singleton.mp member
  rw [dataEquality_unfold] at returned
  split at returned
  · next left right =>
    obtain rfl := PrimitiveResult.value.inj returned
    have agreed : decide (left = right) = agree false left right := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact (agree_exact_iff left right).symm
    rw [agreed, datum_boolean_eq_truth]
    exact (fires (rule := dataEqualityRule) (holds _ (List.mem_cons_self ..))
      [datum letterSpelling left, datum letterSpelling right]
      (by side [dataEqualityRule, data]) (by side [dataEqualityRule])).trans
      (same_reduces (holdsComparison_of_holds holds numbers) false left right)
  · cases returned

/-- The larger host handles the equality of data. -/
theorem dataEquality_handled (arguments : List EngineTerm) :
    dataEqualityHost.primitive "nik:data-eq" arguments ≠ .unhandled := by
  rw [dataEquality_unfold]
  split <;> simp

#print axioms both_reduces
#print axioms sameLetter_reduces
#print axioms sameName_reduces
#print axioms sameMark_reduces
#print axioms differentKinds_reduce
#print axioms agree_exact_iff
#print axioms agree_open
#print axioms sameLiteral_reduces
#print axioms same_reduces
#print axioms dataEquality_realized

end Mettapedia.Logic.HostingStyles.StoredPrograms
