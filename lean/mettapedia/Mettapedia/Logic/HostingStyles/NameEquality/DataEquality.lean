import Mettapedia.Logic.HostingStyles.NameEquality.Family
import Mettapedia.Logic.HostingStyles.StoredPrograms.Comparison

/-!
# The equality of data, for every spelling of names

The rules that compare two data constructor by constructor do not depend on
how a name is written, except where they compare two names.  This module
states them for an arbitrary spelling (`structuralRules`): **forty-eight
rules**, the sixty-one of the comparison with names in letters without the
thirteen that compare names letter by letter and letters digit by digit
(`structuralRules_length`, `comparisonRules_split`).

What they need from a theory is that it **compares written names**
(`ComparesNames`): the helper `same-name` on the writings of two names reduces
to the truth value of their equality.

* With names in letters the thirteen rules do it, in a number of steps that
  grows with the names (`letters_comparesNames`).
* With names as constants the family of the equality of names does it, in one
  step (`withNames_comparesNames`).

**In a theory that holds the forty-eight rules, compares numbers and compares
written names, the comparison of two data reduces to the truth value of their
agreement** (`same_reduces_over`), in both modes: equality, and the engine's
match of a pattern.  So the rule of `nik:data-eq` agrees with the host on all
data (`dataEquality_realized_over`).

Positive: at the spelling in letters the forty-eight rules are rules of the
existing table (`comparisonRules_split`).  Negative: the forty-eight alone
compare no names; with names as constants and no family the helper on two
names has no step (`dataEqualityTable_names_stuck`, in the module of names as
constants).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Host Env natural boolean dataEqualityHost matchTerm matchTerms PrimitiveResult)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces inst)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.Logic.HostingStyles.AtomsReduce (RunnableEquations programTheory)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-! ## The rules that answer, for a spelling -/

namespace Over

/-- The conjunction after `True` is its second term. -/
def whenYes (N : Spelling) : RewriteRule := ⟨bothTerm (truth N true) (.var 0), .var 0⟩

/-- The conjunction after `False` is `False`. -/
def whenNo (N : Spelling) : RewriteRule := ⟨bothTerm (truth N false) (.var 0), truth N false⟩

/-- Two numbers canonically written have one mark. -/
def canonCanon (N : Spelling) : RewriteRule :=
  ⟨sameMark (.con "canon") (.con "canon"), truth N true⟩

/-- A number canonically written and one that keeps its spelling differ. -/
def canonSpelled (N : Spelling) : RewriteRule :=
  ⟨sameMark (.con "canon") (tag "spelled" (.var 0)), truth N false⟩

/-- A number that keeps its spelling and one canonically written differ. -/
def spelledCanon (N : Spelling) : RewriteRule :=
  ⟨sameMark (tag "spelled" (.var 0)) (.con "canon"), truth N false⟩

/-- In the mode `open` a variable agrees with every datum. -/
def variableOpen (N : Spelling) : RewriteRule :=
  ⟨same (.con "open") (tag "var" (.var 0)) (.var 1), truth N true⟩

/-- Two lists without cell agree. -/
def nilNil (N : Spelling) : RewriteRule :=
  ⟨sameItems (.var 0) (.con "nil") (.con "nil"), truth N true⟩

/-- A list without cell and a list with one do not agree. -/
def nilCons (N : Spelling) : RewriteRule :=
  ⟨sameItems (.var 0) (.con "nil") (cell (.var 1) (.var 2)), truth N false⟩

/-- A list with a cell and a list without one do not agree. -/
def consNil (N : Spelling) : RewriteRule :=
  ⟨sameItems (.var 0) (cell (.var 1) (.var 2)) (.con "nil"), truth N false⟩

/-- The rule for a first datum of one kind and a second datum of another. -/
def differentKind (N : Spelling) (first second : StoredPrograms.Kind) : RewriteRule :=
  ⟨same (.var 0) (first.pattern 1) (second.pattern 3), truth N false⟩

/-- The rule for a variable and a datum of another kind, in the mode `exact`. -/
def exactVariable (N : Spelling) (second : StoredPrograms.Kind) : RewriteRule :=
  ⟨same (.con "exact") (tag "var" (.var 0)) (second.pattern 1), truth N false⟩

end Over

/-- The rules of the conjunction of two truth values. -/
def bothRulesOver (N : Spelling) : List RewriteRule := [Over.whenYes N, Over.whenNo N]

/-- The rules that compare the marks of two numbers.  Two spellings are
handed to the comparison of written names. -/
def sameMarkRulesOver (N : Spelling) : List RewriteRule :=
  [Over.canonCanon N, Over.canonSpelled N, Over.spelledCanon N, SameMark.spelledSpelled]

/-- The rules for two data of one kind, and for the cells of two lists.  Two
symbols, two literals and two variables are handed to the comparison of
written names. -/
def sameKindRulesOver (N : Spelling) : List RewriteRule :=
  [Same.symbols, Same.literals, Same.numbers, Same.expressions, Same.lists, Same.variablesExact,
    Over.variableOpen N, Over.nilNil N, Over.nilCons N, Over.consNil N, Same.consCons]

/-- The rules for two data of two kinds, the first no variable. -/
def differentKindRulesOver (N : Spelling) : List RewriteRule :=
  (allKinds.filter fun first => first ≠ .var).flatMap fun first =>
    (allKinds.filter fun second => second ≠ first).map fun second =>
      Over.differentKind N first second

/-- The rules for a variable and a datum of another kind, in the mode
`exact`. -/
def exactVariableRulesOver (N : Spelling) : List RewriteRule :=
  (allKinds.filter fun second => second ≠ .var).map (Over.exactVariable N)

/-- **The rules that compare data, without those that compare names**:
forty-eight rules, for every spelling. -/
def structuralRules (N : Spelling) : List RewriteRule :=
  dataEqualityRule :: (sameKindRulesOver N ++ (differentKindRulesOver N ++
    (exactVariableRulesOver N ++ (sameMarkRulesOver N ++ bothRulesOver N))))

/-- Forty-eight rules, whatever the spelling. -/
theorem structuralRules_length (N : Spelling) : (structuralRules N).length = 48 := by
  simp [structuralRules, sameKindRulesOver, differentKindRulesOver, exactVariableRulesOver,
    sameMarkRulesOver, bothRulesOver, allKinds]

/-- **The sixty-one rules with names in letters are the forty-eight and the
thirteen that compare names**: four for two names, letter by letter, and nine
for two letters, digit by digit. -/
theorem comparisonRules_split (rule : RewriteRule) :
    rule ∈ comparisonRules ↔
      rule ∈ structuralRules letterSpelling ∨ rule ∈ sameNameRules ∨ rule ∈ sameLetterRules := by
  simp only [comparisonRules, structuralRules, nameRules, List.mem_cons, List.mem_append]
  have kinds : sameKindRulesOver letterSpelling = sameKindRules := rfl
  have different : differentKindRulesOver letterSpelling = differentKindRules := rfl
  have exacts : exactVariableRulesOver letterSpelling = exactVariableRules := rfl
  have marks : sameMarkRulesOver letterSpelling = sameMarkRules := rfl
  have conjunction : bothRulesOver letterSpelling = bothRules := rfl
  rw [kinds, different, exacts, marks, conjunction]
  tauto

/-- The thirteen: four and nine. -/
theorem nameComparison_lengths : sameNameRules.length = 4 ∧ sameLetterRules.length = 9 := by
  decide

/-! ## Comparing written names -/

/-- **A theory compares written names**, for a spelling: the helper
`same-name` on the writings of two names reduces to the truth value of their
equality. -/
def ComparesNames (N : Spelling) (theory : Theory) : Prop :=
  ∀ first second : String,
    Reduces theory (sameName (N.write first) (N.write second)) (truth N (first == second))

/-- **With names in letters**, a theory that holds the rules of names, letters
and conjunction compares written names. -/
theorem letters_comparesNames {theory : Theory} (holds : Holds theory nameRules) :
    ComparesNames letterSpelling theory :=
  sameName_reduces holds

/-- **With names as constants**, the theory of a table with the family of the
equality of names compares written names, in one step. -/
theorem withNames_comparesNames (rules : List RewriteRule) :
    ComparesNames constantSpelling (withNames rules) := fun first second =>
  .single (nameTest_step rules first second)

/-! ## What the rules compute -/

/-- The parts of the rules that a theory holds, for a spelling. -/
structure HoldsStructural (N : Spelling) (theory : Theory) : Prop where
  sameKind : Holds theory (sameKindRulesOver N)
  different : Holds theory (differentKindRulesOver N)
  exactVariable : Holds theory (exactVariableRulesOver N)
  marks : Holds theory (sameMarkRulesOver N)
  both : Holds theory (bothRulesOver N)
  numbers : Holds theory (equalNumbersRules N)
  names : ComparesNames N theory

/-- A theory that holds the forty-eight rules and the rules for numbers, and
compares written names. -/
theorem holdsStructural_of_holds {N : Spelling} {theory : Theory}
    (holds : Holds theory (structuralRules N)) (numbers : Holds theory (equalNumbersRules N))
    (names : ComparesNames N theory) : HoldsStructural N theory where
  sameKind := fun rule member =>
    holds rule (List.mem_cons_of_mem _ (List.mem_append_left _ member))
  different := fun rule member =>
    holds rule (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _ member)))
  exactVariable := fun rule member =>
    holds rule (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ member))))
  marks := fun rule member =>
    holds rule (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member)))))
  both := fun rule member =>
    holds rule (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ member)))))
  numbers := numbers
  names := names

/-- The conjunction of two terms that reduce to truth values. -/
theorem both_reduces_over (N : Spelling) {theory : Theory} (holds : Holds theory (bothRulesOver N))
    {first second : LF.Term} {left right : Bool}
    (firstReduces : Reduces theory first (truth N left))
    (secondReduces : Reduces theory second (truth N right)) :
    Reduces theory (bothTerm first second) (truth N (left && right)) := by
  have start : Reduces theory (bothTerm first second) (bothTerm (truth N left) second) :=
    reduces_libTerm "both" (.cons firstReduces (.cons .refl .nil))
  cases left with
  | true =>
      exact (start.trans (fires (rule := Over.whenYes N) (holds _ (by simp [bothRulesOver]))
        [second] (by side [Over.whenYes]) (by side [Over.whenYes]))).trans secondReduces
  | false =>
      exact start.trans (fires (rule := Over.whenNo N) (holds _ (by simp [bothRulesOver]))
        [second] (by side [Over.whenNo]) (by side [Over.whenNo]))

/-- The mark of a literal that spells a number, for a spelling. -/
def markIn (N : Spelling) (spelling : String) (value : Nat) : LF.Term :=
  if value.repr = spelling then .con "canon" else tag "spelled" (N.write spelling)

/-- The reading of a literal that spells a number: the number in unary, with
its mark. -/
theorem literal_of_number_in (N : Spelling) {spelling : String} {value : Nat}
    (spelled : spelledNumber spelling = some value) :
    literal N spelling = numbered (unary value) (markIn N spelling value) := by
  simp only [literal, spelled, markIn]
  split <;> rfl

/-- The reading of a literal that spells no number: its spelling, written as
a name. -/
theorem literal_of_name_in (N : Spelling) {spelling : String}
    (spelled : spelledNumber spelling = none) :
    literal N spelling = tag "lit" (N.write spelling) := by
  simp only [literal, spelled]

/-- **Positive and negative**: the literal `12` is canonically written, and
`1_2` keeps its spelling. -/
theorem markIn_examples :
    markIn constantSpelling "12" 12 = .con "canon" ∧
      markIn constantSpelling "1_2" 12 = tag "spelled" (.con "1_2") := by
  decide +kernel

/-- The helper decides whether two literals of one number are one literal. -/
theorem sameMark_reduces_over (N : Spelling) {theory : Theory}
    (marks : Holds theory (sameMarkRulesOver N)) (names : ComparesNames N theory)
    (first second : String) (value : Nat) :
    Reduces theory (sameMark (markIn N first value) (markIn N second value))
      (truth N (first == second)) := by
  unfold markIn
  by_cases firstCanon : value.repr = first <;> by_cases secondCanon : value.repr = second
  · have equal : (first == second) = true := by simp [← firstCanon, ← secondCanon]
    rw [if_pos firstCanon, if_pos secondCanon, equal]
    exact fires (rule := Over.canonCanon N) (marks _ (by simp [sameMarkRulesOver])) []
      (by side [Over.canonCanon]) (by side [Over.canonCanon])
  · have different : (first == second) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun equal => secondCanon (equal ▸ firstCanon)
    rw [if_pos firstCanon, if_neg secondCanon, different]
    exact fires (rule := Over.canonSpelled N) (marks _ (by simp [sameMarkRulesOver]))
      [N.write second] (by side [Over.canonSpelled]) (by side [Over.canonSpelled])
  · have different : (first == second) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun equal => firstCanon (equal ▸ secondCanon)
    rw [if_neg firstCanon, if_pos secondCanon, different]
    exact fires (rule := Over.spelledCanon N) (marks _ (by simp [sameMarkRulesOver]))
      [N.write first] (by side [Over.spelledCanon]) (by side [Over.spelledCanon])
  · rw [if_neg firstCanon, if_neg secondCanon]
    exact (fires (rule := SameMark.spelledSpelled) (marks _ (by simp [sameMarkRulesOver]))
      [N.write first, N.write second] (by side [SameMark.spelledSpelled])
      (by side [SameMark.spelledSpelled])).trans (names first second)

/-- The reading of a datum is the reading of its kind, for every spelling. -/
theorem datum_reading_in (N : Spelling) (term : EngineTerm) :
    ∃ content mark, datum N term = (kindOf term).reading content mark := by
  cases term with
  | sym name => exact ⟨_, .con "canon", rfl⟩
  | var name => exact ⟨_, .con "canon", rfl⟩
  | expr items => exact ⟨_, .con "canon", rfl⟩
  | list items => exact ⟨_, .con "canon", rfl⟩
  | lit spelling =>
      cases spelled : spelledNumber spelling with
      | none =>
          refine ⟨N.write spelling, .con "canon", ?_⟩
          simp only [datum, literal_of_name_in N spelled, kindOf, spelled, Option.isSome_none,
            Bool.false_eq_true, if_false, StoredPrograms.Kind.reading]
      | some value =>
          refine ⟨unary value, markIn N spelling value, ?_⟩
          simp only [datum, literal_of_number_in N spelled, kindOf, spelled, Option.isSome_some,
            if_true, StoredPrograms.Kind.reading]

/-- Two data of two kinds, the first no variable, do not agree, in either
mode. -/
theorem differentKinds_reduce_over (N : Spelling) {theory : Theory}
    (holds : Holds theory (differentKindRulesOver N)) {first second : StoredPrograms.Kind}
    (notVariable : first ≠ .var) (different : second ≠ first)
    (mode content mark otherContent otherMark : LF.Term) :
    Reduces theory (same mode (first.reading content mark) (second.reading otherContent otherMark))
      (truth N false) := by
  have member : Over.differentKind N first second ∈ differentKindRulesOver N :=
    List.mem_flatMap.mpr ⟨first,
      List.mem_filter.mpr ⟨mem_allKinds first, by simpa using notVariable⟩,
      List.mem_map.mpr ⟨second,
        List.mem_filter.mpr ⟨mem_allKinds second, by simpa using different⟩, rfl⟩⟩
  exact fires (rule := Over.differentKind N first second) (holds _ member)
    [mode, content, mark, otherContent, otherMark]
    (by simp only [Over.differentKind, inst_libTerm, List.map_cons, List.map_nil,
      StoredPrograms.Kind.inst_pattern, Dedukti.inst_var, assign, List.getD_cons_zero,
      List.getD_cons_succ])
    (by side [Over.differentKind])

/-- In the mode `exact` a variable and a datum of another kind do not
agree. -/
theorem exactVariable_reduces_over (N : Spelling) {theory : Theory}
    (holds : Holds theory (exactVariableRulesOver N)) {second : StoredPrograms.Kind}
    (different : second ≠ .var) (name content mark : LF.Term) :
    Reduces theory (same (.con "exact") (tag "var" name) (second.reading content mark))
      (truth N false) := by
  have member : Over.exactVariable N second ∈ exactVariableRulesOver N :=
    List.mem_map.mpr ⟨second, List.mem_filter.mpr ⟨mem_allKinds second, by simpa using different⟩,
      rfl⟩
  exact fires (rule := Over.exactVariable N second) (holds _ member) [name, content, mark]
    (by simp only [Over.exactVariable, inst_libTerm, List.map_cons, List.map_nil,
      StoredPrograms.Kind.inst_pattern, inst_tag, Dedukti.inst_var, Dedukti.inst_con, assign,
      List.getD_cons_zero, List.getD_cons_succ])
    (by side [Over.exactVariable])

/-- Two literals, compared. -/
theorem sameLiteral_reduces_over (N : Spelling) {theory : Theory}
    (holds : HoldsStructural N theory) (mode : LF.Term) (first second : String) :
    Reduces theory (same mode (literal N first) (literal N second))
      (truth N (first == second)) := by
  cases firstSpelled : spelledNumber first with
  | none =>
      cases secondSpelled : spelledNumber second with
      | none =>
          rw [literal_of_name_in N firstSpelled, literal_of_name_in N secondSpelled]
          exact (fires (rule := Same.literals) (holds.sameKind _ (by simp [sameKindRulesOver]))
            [mode, N.write first, N.write second]
            (by side [Same.literals]) (by side [Same.literals])).trans
            (holds.names first second)
      | some value =>
          have different : (first == second) = false := by
            rw [beq_eq_false_iff_ne]
            intro equal
            rw [equal, secondSpelled] at firstSpelled
            cases firstSpelled
          rw [literal_of_name_in N firstSpelled, literal_of_number_in N secondSpelled, different]
          exact differentKinds_reduce_over N holds.different (first := .lit) (second := .num)
            (by decide) (by decide) mode _ (.con "canon") _ _
  | some value =>
      cases secondSpelled : spelledNumber second with
      | none =>
          have different : (first == second) = false := by
            rw [beq_eq_false_iff_ne]
            intro equal
            rw [equal, secondSpelled] at firstSpelled
            cases firstSpelled
          rw [literal_of_number_in N firstSpelled, literal_of_name_in N secondSpelled, different]
          exact differentKinds_reduce_over N holds.different (first := .num) (second := .lit)
            (by decide) (by decide) mode _ _ _ (.con "canon")
      | some other =>
          rw [literal_of_number_in N firstSpelled, literal_of_number_in N secondSpelled]
          have step : Reduces theory
              (same mode (numbered (unary value) (markIn N first value))
                (numbered (unary other) (markIn N second other)))
              (bothTerm (sameNumber (unary value) (unary other))
                (sameMark (markIn N first value) (markIn N second other))) :=
            fires (rule := Same.numbers) (holds.sameKind _ (by simp [sameKindRulesOver]))
              [mode, unary value, markIn N first value, unary other, markIn N second other]
              (by side [Same.numbers]) (by side [Same.numbers])
          have numbers := equalNumbers_reduces N holds.numbers value other
          by_cases sameValue : value = other
          · subst sameValue
            have conjunction := both_reduces_over N holds.both numbers
              (sameMark_reduces_over N holds.marks holds.names first second value)
            simpa using step.trans conjunction
          · have different : (first == second) = false := by
              rw [beq_eq_false_iff_ne]
              intro equal
              rw [equal, secondSpelled] at firstSpelled
              exact sameValue (Option.some.inj firstSpelled).symm
            have refused : Reduces theory
                (bothTerm (sameNumber (unary value) (unary other))
                  (sameMark (markIn N first value) (markIn N second other))) (truth N false) := by
              have start : Reduces theory
                  (bothTerm (sameNumber (unary value) (unary other))
                    (sameMark (markIn N first value) (markIn N second other)))
                  (bothTerm (truth N false)
                    (sameMark (markIn N first value) (markIn N second other))) := by
                have reduced := numbers
                simp only [sameValue, decide_false] at reduced
                exact reduces_libTerm "both" (.cons reduced (.cons .refl .nil))
              exact start.trans (fires (rule := Over.whenNo N)
                (holds.both _ (by simp [bothRulesOver]))
                [sameMark (markIn N first value) (markIn N second other)] (by side [Over.whenNo])
                (by side [Over.whenNo]))
            rw [different]
            exact step.trans refused

mutual

/-- **The rules compute the agreement of two data**, for every spelling, in
every theory that holds them, compares numbers and compares written names. -/
theorem same_reduces_over (N : Spelling) {theory : Theory} (holds : HoldsStructural N theory)
    (wild : Bool) :
    ∀ (first second : EngineTerm),
      Reduces theory (same (modeTerm wild) (datum N first) (datum N second))
        (truth N (agree wild first second))
  | .var name, second => by
      cases wild with
      | true =>
          have agreed : agree true (.var name) second = true := by simp [agree]
          rw [agreed]
          exact fires (rule := Over.variableOpen N)
            (holds.sameKind _ (by simp [sameKindRulesOver]))
            [N.write name, datum N second]
            (by side [Over.variableOpen, modeTerm, datum]) (by side [Over.variableOpen])
      | false =>
          cases second with
          | var other =>
              have agreed : agree false (.var name) (.var other) = (name == other) := by
                simp [agree]
              rw [agreed]
              exact (fires (rule := Same.variablesExact)
                (holds.sameKind _ (by simp [sameKindRulesOver]))
                [N.write name, N.write other]
                (by side [Same.variablesExact, modeTerm, datum])
                (by side [Same.variablesExact])).trans (holds.names name other)
          | sym other =>
              exact exactVariable_reduces_over N holds.exactVariable (second := .sym) (by decide)
                _ _ (.con "canon")
          | expr others =>
              exact exactVariable_reduces_over N holds.exactVariable (second := .expr) (by decide)
                _ _ (.con "canon")
          | list others =>
              exact exactVariable_reduces_over N holds.exactVariable (second := .list) (by decide)
                _ _ (.con "canon")
          | lit other =>
              obtain ⟨content, mark, shape⟩ := datum_reading_in N (.lit other)
              have different : kindOf (.lit other) ≠ .var := by
                simp only [kindOf]
                split <;> decide
              have refused := exactVariable_reduces_over N holds.exactVariable different
                (N.write name) content mark
              have disagreed : agree false (.var name) (.lit other) = false := by simp [agree]
              rw [disagreed, shape]
              exact refused
  | .sym name, second => by
      cases second with
      | sym other =>
          have agreed : agree wild (.sym name) (.sym other) = (name == other) := by simp [agree]
          rw [agreed]
          exact (fires (rule := Same.symbols) (holds.sameKind _ (by simp [sameKindRulesOver]))
            [modeTerm wild, N.write name, N.write other]
            (by side [Same.symbols, datum]) (by side [Same.symbols])).trans
            (holds.names name other)
      | var other =>
          exact differentKinds_reduce_over N holds.different (first := .sym) (second := .var)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | expr others =>
          exact differentKinds_reduce_over N holds.different (first := .sym) (second := .expr)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | list others =>
          exact differentKinds_reduce_over N holds.different (first := .sym) (second := .list)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | lit other =>
          obtain ⟨content, mark, shape⟩ := datum_reading_in N (.lit other)
          have different : kindOf (.lit other) ≠ .sym := by
            simp only [kindOf]
            split <;> decide
          have refused := differentKinds_reduce_over N holds.different (first := .sym) (by decide)
            different (modeTerm wild) (N.write name) (.con "canon") content mark
          have disagreed : agree wild (.sym name) (.lit other) = false := by simp [agree]
          rw [disagreed, shape]
          exact refused
  | .lit spelling, second => by
      cases second with
      | lit other =>
          have agreed : agree wild (.lit spelling) (.lit other) = (spelling == other) := by
            simp [agree]
          rw [agreed]
          exact sameLiteral_reduces_over N holds (modeTerm wild) spelling other
      | var other =>
          obtain ⟨content, mark, shape⟩ := datum_reading_in N (.lit spelling)
          have notVariable : kindOf (.lit spelling) ≠ .var := by
            simp only [kindOf]
            split <;> decide
          have refused := differentKinds_reduce_over N holds.different (second := .var)
            notVariable notVariable.symm (modeTerm wild) content mark (N.write other)
            (.con "canon")
          have disagreed : agree wild (.lit spelling) (.var other) = false := by simp [agree]
          rw [disagreed, shape]
          exact refused
      | sym other =>
          obtain ⟨content, mark, shape⟩ := datum_reading_in N (.lit spelling)
          have notVariable : kindOf (.lit spelling) ≠ .var := by
            simp only [kindOf]
            split <;> decide
          have notSymbol : StoredPrograms.Kind.sym ≠ kindOf (.lit spelling) := by
            simp only [kindOf]
            split <;> decide
          have refused := differentKinds_reduce_over N holds.different (second := .sym)
            notVariable notSymbol (modeTerm wild) content mark (N.write other) (.con "canon")
          have disagreed : agree wild (.lit spelling) (.sym other) = false := by simp [agree]
          rw [disagreed, shape]
          exact refused
      | expr others =>
          obtain ⟨content, mark, shape⟩ := datum_reading_in N (.lit spelling)
          have notVariable : kindOf (.lit spelling) ≠ .var := by
            simp only [kindOf]
            split <;> decide
          have notExpression : StoredPrograms.Kind.expr ≠ kindOf (.lit spelling) := by
            simp only [kindOf]
            split <;> decide
          have refused := differentKinds_reduce_over N holds.different (second := .expr)
            notVariable notExpression (modeTerm wild) content mark (cells (data N others))
            (.con "canon")
          have disagreed : agree wild (.lit spelling) (.expr others) = false := by simp [agree]
          rw [disagreed, shape]
          exact refused
      | list others =>
          obtain ⟨content, mark, shape⟩ := datum_reading_in N (.lit spelling)
          have notVariable : kindOf (.lit spelling) ≠ .var := by
            simp only [kindOf]
            split <;> decide
          have notList : StoredPrograms.Kind.list ≠ kindOf (.lit spelling) := by
            simp only [kindOf]
            split <;> decide
          have refused := differentKinds_reduce_over N holds.different (second := .list)
            notVariable notList (modeTerm wild) content mark (cells (data N others)) (.con "canon")
          have disagreed : agree wild (.lit spelling) (.list others) = false := by simp [agree]
          rw [disagreed, shape]
          exact refused
  | .expr items, second => by
      cases second with
      | expr others =>
          have agreed : agree wild (.expr items) (.expr others) = agreeList wild items others := by
            simp [agree]
          rw [agreed]
          exact (fires (rule := Same.expressions) (holds.sameKind _ (by simp [sameKindRulesOver]))
            [modeTerm wild, cells (data N items), cells (data N others)]
            (by side [Same.expressions, datum]) (by side [Same.expressions])).trans
            (sameItems_reduces_over N holds wild items others)
      | var other =>
          exact differentKinds_reduce_over N holds.different (first := .expr) (second := .var)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | sym other =>
          exact differentKinds_reduce_over N holds.different (first := .expr) (second := .sym)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | list others =>
          exact differentKinds_reduce_over N holds.different (first := .expr) (second := .list)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | lit other =>
          obtain ⟨content, mark, shape⟩ := datum_reading_in N (.lit other)
          have different : kindOf (.lit other) ≠ .expr := by
            simp only [kindOf]
            split <;> decide
          have refused := differentKinds_reduce_over N holds.different (first := .expr) (by decide)
            different (modeTerm wild) (cells (data N items)) (.con "canon") content mark
          have disagreed : agree wild (.expr items) (.lit other) = false := by simp [agree]
          rw [disagreed, shape]
          exact refused
  | .list items, second => by
      cases second with
      | list others =>
          have agreed : agree wild (.list items) (.list others) = agreeList wild items others := by
            simp [agree]
          rw [agreed]
          exact (fires (rule := Same.lists) (holds.sameKind _ (by simp [sameKindRulesOver]))
            [modeTerm wild, cells (data N items), cells (data N others)]
            (by side [Same.lists, datum]) (by side [Same.lists])).trans
            (sameItems_reduces_over N holds wild items others)
      | var other =>
          exact differentKinds_reduce_over N holds.different (first := .list) (second := .var)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | sym other =>
          exact differentKinds_reduce_over N holds.different (first := .list) (second := .sym)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | expr others =>
          exact differentKinds_reduce_over N holds.different (first := .list) (second := .expr)
            (by decide) (by decide) _ _ (.con "canon") _ (.con "canon")
      | lit other =>
          obtain ⟨content, mark, shape⟩ := datum_reading_in N (.lit other)
          have different : kindOf (.lit other) ≠ .list := by
            simp only [kindOf]
            split <;> decide
          have refused := differentKinds_reduce_over N holds.different (first := .list) (by decide)
            different (modeTerm wild) (cells (data N items)) (.con "canon") content mark
          have disagreed : agree wild (.list items) (.lit other) = false := by simp [agree]
          rw [disagreed, shape]
          exact refused

/-- The rules compute the agreement of the cells of two lists of data. -/
theorem sameItems_reduces_over (N : Spelling) {theory : Theory} (holds : HoldsStructural N theory)
    (wild : Bool) :
    ∀ (items values : List EngineTerm),
      Reduces theory
        (sameItems (modeTerm wild) (cells (data N items)) (cells (data N values)))
        (truth N (agreeList wild items values))
  | [], [] =>
      fires (rule := Over.nilNil N) (holds.sameKind _ (by simp [sameKindRulesOver]))
        [modeTerm wild] (by side [Over.nilNil, data, cells]) (by side [Over.nilNil])
  | [], value :: others =>
      fires (rule := Over.nilCons N) (holds.sameKind _ (by simp [sameKindRulesOver]))
        [modeTerm wild, datum N value, cells (data N others)]
        (by side [Over.nilCons, data, cells]) (by side [Over.nilCons])
  | first :: rest, [] =>
      fires (rule := Over.consNil N) (holds.sameKind _ (by simp [sameKindRulesOver]))
        [modeTerm wild, datum N first, cells (data N rest)]
        (by side [Over.consNil, data, cells]) (by side [Over.consNil])
  | first :: rest, value :: others => by
      have step : Reduces theory
          (sameItems (modeTerm wild) (cells (data N (first :: rest)))
            (cells (data N (value :: others))))
          (bothTerm (same (modeTerm wild) (datum N first) (datum N value))
            (sameItems (modeTerm wild) (cells (data N rest)) (cells (data N others)))) :=
        fires (rule := Same.consCons) (holds.sameKind _ (by simp [sameKindRulesOver]))
          [modeTerm wild, datum N first, cells (data N rest), datum N value, cells (data N others)]
          (by side [Same.consCons, data, cells]) (by side [Same.consCons])
      have agreed : agreeList wild (first :: rest) (value :: others) =
          (agree wild first value && agreeList wild rest others) := by simp [agreeList]
      rw [agreed]
      exact step.trans (both_reduces_over N holds.both (same_reduces_over N holds wild first value)
        (sameItems_reduces_over N holds wild rest others))

end

/-- **The rules agree with the host on the equality of data**, on all data,
for every spelling: in a theory that holds the forty-eight rules and the rules
for numbers and compares written names, the call of `nik:data-eq` on two data
reduces to the datum of what the host returns. -/
theorem dataEquality_realized_over (N : Spelling) {theory : Theory}
    (holds : Holds theory (structuralRules N)) (numbers : Holds theory (equalNumbersRules N))
    (names : ComparesNames N theory) :
    RealizesPrimitives N theory dataEqualityHost ["nik:data-eq"] := by
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
      [datum N left, datum N right]
      (by side [dataEqualityRule, data]) (by side [dataEqualityRule])).trans
      (same_reduces_over N (holdsStructural_of_holds holds numbers names) false left right)
  · cases returned

#print axioms structuralRules_length
#print axioms comparisonRules_split
#print axioms letters_comparesNames
#print axioms withNames_comparesNames
#print axioms sameMark_reduces_over
#print axioms sameLiteral_reduces_over
#print axioms same_reduces_over
#print axioms dataEquality_realized_over

end Mettapedia.Logic.HostingStyles.NameEquality
