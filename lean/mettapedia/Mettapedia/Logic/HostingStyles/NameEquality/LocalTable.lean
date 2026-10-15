import Mettapedia.Logic.HostingStyles.NameEquality.Family
import Mettapedia.Logic.HostingStyles.StoredPrograms.Obstruction
import Mettapedia.GSLT.Dedukti.LeanMinusPaperNormalForm
import Mathlib.Data.List.Dedup

/-!
# Locally a finite table

The family of the equality of names has a rule for every two names, so the
theory of a table with the family is the theory of no list of rules.  Seen
from one term it is: **a step creates no name**, so only the rules of the
family for the names of the term can ever fire.

* The names that the theory of a table with the family mentions, beside the
  two names that a rule of the family tests, are those of the rules of the
  table and those of the test and of its answers (`fixedNames`).
* `nameRulesOn names` are the rules of the family for the pairs of names of a
  list, and `localTable rules names` adds them to a table: a finite table.
* **For a term whose names lie in a list that holds the fixed names, a step
  of the theory with the family is a step of the local table, to a term whose
  names lie in the list again** (`step_local`).  The table is asked that its
  right sides mention only variables of their left sides; otherwise a step
  creates any name (`freeRule_creates_name`).
* So from such a term the steps, the reductions and the normal forms of the
  theory with the family are those of the local table
  (`step_withNames_iff_local`, `reduces_withNames_iff_local`,
  `normal_withNames_iff_local`), and every name of a reduct is a name of the
  term or a fixed name (`names_of_reduct`).

Every term has such a list, its own names with the fixed ones (`namesFor`).
So a statement proved for the theories of finite tables holds of the theory
with the family, term by term.  No one list serves all terms: the family for
the names of a list answers no test of a name outside it
(`localTable_test_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dedukti
  (Theory RewriteRule RootStep Step Reduces inst patternVars usesOnly
    instantiate_congr_of_usesOnly)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (step_of_rule freeRule)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.Logic.HostingStyles.AtomsReduce (programTheory rootStep_program_inv)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-! ## The names of a term -/

/-- The two functions that list the constants of a term are one function. -/
theorem constantsOf_eq_dedukti : (constantsOf : LF.Term → List String) = Dedukti.constantsOf := by
  funext term
  induction term with
  | con name => rfl
  | var index => rfl
  | srt sort => rfl
  | pi domain body ihDomain ihBody => simp [constantsOf, Dedukti.constantsOf, ihDomain, ihBody]
  | lam domain body ihDomain ihBody => simp [constantsOf, Dedukti.constantsOf, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      simp [constantsOf, Dedukti.constantsOf, ihFunction, ihArgument]

/-- **The names of a term lie in a list.** -/
def NamesWithin (names : List String) (term : LF.Term) : Prop :=
  ∀ name ∈ constantsOf term, name ∈ names

instance (names : List String) (term : LF.Term) : Decidable (NamesWithin names term) :=
  inferInstanceAs (Decidable (∀ name ∈ constantsOf term, name ∈ names))

/-- **The names of the test and of its answers**: the constants that every
rule of the family mentions beside the two names that it tests. -/
def testNames : List String := ["lib", "same-name", "cons", "nil", "sym", "True", "False"]

/-- **The fixed names of the theory of a table with the family**: the names
of the rules of the table, and those of the test and of its answers. -/
def fixedNames (rules : List RewriteRule) : List String := constantsOfRules rules ++ testNames

/-- **Positive and negative**: over the table without rule the fixed names are
the seven of the test and of its answers; `sym` is one of them, and the name
`a` is none. -/
theorem fixedNames_examples :
    fixedNames [] = testNames ∧ "sym" ∈ fixedNames [] ∧ "a" ∉ fixedNames [] := by
  decide

/-- The names of a test of two names: the two, and four of the test. -/
theorem constantsOf_nameTest (first second : String) :
    constantsOf (nameTest first second) =
      ["lib", "same-name", "cons", first, "cons", second, "nil"] :=
  rfl

/-- The names of an answer are names of the test and of its answers. -/
theorem constantsOf_truth (value : Bool) :
    ∀ name ∈ constantsOf (truth constantSpelling value), name ∈ testNames := by
  cases value <;> decide

/-- **Positive**: the names of the test of `a` and `b` lie in the list of the
two with the names of the test.  **Negative**: they do not lie in the list
without `b`. -/
theorem namesWithin_examples :
    NamesWithin ("a" :: "b" :: testNames) (nameTest "a" "b") ∧
      ¬ NamesWithin ("a" :: testNames) (nameTest "a" "b") := by
  decide

/-! ## The family for the names of a list -/

/-- **The rules of the family for the pairs of names of a list.** -/
def nameRulesOn (names : List String) : List RewriteRule :=
  names.flatMap fun first => names.map fun second => nameRule first second

/-- A rule of the family for a list is the rule of two names of the list. -/
theorem mem_nameRulesOn {names : List String} {rule : RewriteRule} :
    rule ∈ nameRulesOn names ↔
      ∃ first ∈ names, ∃ second ∈ names, rule = nameRule first second := by
  simp only [nameRulesOn, List.mem_flatMap, List.mem_map]
  exact ⟨fun ⟨first, inFirst, second, inSecond, same⟩ =>
      ⟨first, inFirst, second, inSecond, same.symm⟩,
    fun ⟨first, inFirst, second, inSecond, same⟩ =>
      ⟨first, inFirst, second, inSecond, same.symm⟩⟩

/-- A list of `n` names has `n * n` rules of the family. -/
theorem nameRulesOn_length (names : List String) :
    (nameRulesOn names).length = names.length * names.length := by
  simp [nameRulesOn, List.length_flatMap]

/-- **The local table**: a table with the rules of the family for the names
of a list. -/
def localTable (rules : List RewriteRule) (names : List String) : List RewriteRule :=
  rules ++ nameRulesOn names

/-- **Positive and negative**: the family for `a` and `b` holds the rule of
the two, and no rule of `a` and `c`. -/
theorem nameRulesOn_examples :
    nameRule "a" "b" ∈ nameRulesOn ["a", "b"] ∧ nameRule "a" "c" ∉ nameRulesOn ["a", "b"] := by
  decide

/-- **Positive and negative**: the local table of the names `a` and `b`, over
the table without rule, has four rules, the rule of `a` and `b` among them and
no rule of `a` and `c`. -/
theorem localTable_examples :
    (localTable [] ["a", "b"]).length = 4 ∧ nameRule "a" "b" ∈ localTable [] ["a", "b"] ∧
      nameRule "a" "c" ∉ localTable [] ["a", "b"] := by
  decide

/-- The theory of a local table is contained in the theory of the table with
the whole family. -/
theorem localTable_extends (rules : List RewriteRule) (names : List String) :
    (programTheory (localTable rules names)).Extends (withNames rules) := by
  refine ⟨fun _ _ same => same, fun _ _ same => same, fun rule member => ?_⟩
  rcases List.mem_append.mp member with inTable | inFamily
  · exact .inl inTable
  · obtain ⟨first, -, second, -, rfl⟩ := mem_nameRulesOn.mp inFamily
    exact .inr ⟨first, second, rfl⟩

/-! ## A step creates no name -/

/-- **A step of the theory with the family, from a term whose names lie in a
list that holds the fixed names, is a step of the local table of the list, and
the names of its target lie in the list.**  The right sides of the table
mention only variables of their left sides. -/
theorem step_local {rules : List RewriteRule} {names : List String}
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (covers : ∀ name ∈ fixedNames rules, name ∈ names) {source target : LF.Term}
    (within : NamesWithin names source) (step : Step (withNames rules) source target) :
    Step (programTheory (localTable rules names)) source target ∧ NamesWithin names target := by
  have moved := Dedukti.Step.transfer (first := withNames rules)
    (second := programTheory (localTable rules names)) (fun name => name ∉ names)
    (fun name body defined _ => by cases defined)
    (by
      rintro rule (inTable | ⟨first, second, rfl⟩) leftClean
      · refine ⟨List.mem_append_left _ inTable, fun other inRight => not_not.mpr ?_⟩
        rw [← constantsOf_eq_dedukti] at inRight
        exact covers other (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨rule, inTable, List.mem_append_right _ inRight⟩))
      · rw [← constantsOf_eq_dedukti] at leftClean
        have firstIn : first ∈ names :=
          not_not.mp (leftClean first (by rw [nameRule, constantsOf_nameTest]; simp))
        have secondIn : second ∈ names :=
          not_not.mp (leftClean second (by rw [nameRule, constantsOf_nameTest]; simp))
        refine ⟨List.mem_append_right _
            (mem_nameRulesOn.mpr ⟨first, firstIn, second, secondIn, rfl⟩),
          fun other inRight => not_not.mpr ?_⟩
        rw [← constantsOf_eq_dedukti] at inRight
        exact covers other (List.mem_append_right _ (constantsOf_truth _ other inRight)))
    (by
      rintro rule (inTable | ⟨first, second, rfl⟩) left right agree
      · exact instantiate_congr_of_usesOnly agree rule.rhs 0 (bound rule inTable)
      · exact (inst_truth constantSpelling left _).trans (inst_truth constantSpelling right _).symm)
    (source := source) (target := target)
    (fun other member => not_not.mpr (within other (by rwa [constantsOf_eq_dedukti])))
    step
  refine ⟨moved.1, fun name member => not_not.mp (moved.2 name ?_)⟩
  rwa [← constantsOf_eq_dedukti]

/-- **From a term whose names lie in the list, the steps of the theory with
the family are those of the local table.** -/
theorem step_withNames_iff_local {rules : List RewriteRule} {names : List String}
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (covers : ∀ name ∈ fixedNames rules, name ∈ names) {source target : LF.Term}
    (within : NamesWithin names source) :
    Step (withNames rules) source target ↔
      Step (programTheory (localTable rules names)) source target :=
  ⟨fun step => (step_local bound covers within step).1,
    fun step => step.mono (localTable_extends rules names)⟩

/-- A reduction of the theory with the family, from a term whose names lie in
the list, is a reduction of the local table, to a term whose names lie in the
list. -/
theorem reduces_local {rules : List RewriteRule} {names : List String}
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (covers : ∀ name ∈ fixedNames rules, name ∈ names) {source target : LF.Term}
    (within : NamesWithin names source) (reduces : Reduces (withNames rules) source target) :
    Reduces (programTheory (localTable rules names)) source target ∧ NamesWithin names target := by
  induction reduces with
  | refl => exact ⟨.refl, within⟩
  | tail _ step ih =>
      obtain ⟨moved, targetWithin⟩ := step_local bound covers ih.2 step
      exact ⟨ih.1.tail moved, targetWithin⟩

/-- **From a term whose names lie in the list, the reductions of the theory
with the family are those of the local table.** -/
theorem reduces_withNames_iff_local {rules : List RewriteRule} {names : List String}
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (covers : ∀ name ∈ fixedNames rules, name ∈ names) {source target : LF.Term}
    (within : NamesWithin names source) :
    Reduces (withNames rules) source target ↔
      Reduces (programTheory (localTable rules names)) source target :=
  ⟨fun reduces => (reduces_local bound covers within reduces).1,
    fun reduces => reduces.mono (localTable_extends rules names)⟩

/-- **And so are the normal forms**: a term whose names lie in the list has a
step in the theory with the family exactly when it has one in the local
table. -/
theorem normal_withNames_iff_local {rules : List RewriteRule} {names : List String}
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (covers : ∀ name ∈ fixedNames rules, name ∈ names) {source : LF.Term}
    (within : NamesWithin names source) :
    IsNormal (Step (withNames rules)) source ↔
      IsNormal (Step (programTheory (localTable rules names))) source :=
  ⟨fun normal target step =>
      normal target ((step_withNames_iff_local bound covers within).mpr step),
    fun normal target step =>
      normal target ((step_withNames_iff_local bound covers within).mp step)⟩

/-- **The names of a term over a table**: its own, with the fixed names of
the theory of the table with the family, each listed once. -/
def namesFor (rules : List RewriteRule) (term : LF.Term) : List String :=
  (fixedNames rules ++ constantsOf term).dedup

/-- The names of a term over a table hold the fixed names. -/
theorem namesFor_covers (rules : List RewriteRule) (term : LF.Term) :
    ∀ name ∈ fixedNames rules, name ∈ namesFor rules term :=
  fun _ member => List.mem_dedup.mpr (List.mem_append_left _ member)

/-- The names of a term lie in its names over a table. -/
theorem namesFor_within (rules : List RewriteRule) (term : LF.Term) :
    NamesWithin (namesFor rules term) term :=
  fun _ member => List.mem_dedup.mpr (List.mem_append_right _ member)

/-- **Positive and negative**: over the table without rule, the names of the
test of `a` and `b` are the seven of the test and the two, nine names, each
once; `c` is not among them. -/
theorem namesFor_examples :
    (namesFor [] (nameTest "a" "b")).length = 9 ∧ "c" ∉ namesFor [] (nameTest "a" "b") := by
  decide

/-- **A step creates no name**: a name of a reduct is a name of the term or a
fixed name of the theory. -/
theorem names_of_reduct {rules : List RewriteRule}
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {source target : LF.Term} (reduces : Reduces (withNames rules) source target) :
    ∀ name ∈ constantsOf target, name ∈ constantsOf source ∨ name ∈ fixedNames rules := by
  intro name member
  have within := (reduces_local bound (namesFor_covers rules source)
    (namesFor_within rules source) reduces).2 name member
  exact (List.mem_append.mp (List.mem_dedup.mp within)).symm

/-- **Every term has its finite table**: the reductions of the theory with
the family from a term are those of the local table of the names of the
term. -/
theorem reduces_withNames_iff_namesFor {rules : List RewriteRule}
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {source target : LF.Term} :
    Reduces (withNames rules) source target ↔
      Reduces (programTheory (localTable rules (namesFor rules source))) source target :=
  reduces_withNames_iff_local bound (namesFor_covers rules source) (namesFor_within rules source)

/-- **Negative**: with a right side that mentions a variable that its left
side does not bind, a step creates a name.  The rule `c ⟶ x` rewrites `c` to
the constant `new`. -/
theorem freeRule_creates_name :
    Step (withNames [freeRule]) (.con "c") (.con "new") ∧
      "new" ∉ constantsOf (.con "c") ∧ "new" ∉ fixedNames [freeRule] := by
  refine ⟨step_of_rule (theory := withNames [freeRule]) (rule := freeRule)
    (Or.inl (List.mem_singleton.mpr rfl)) (fun _ => .con "new") rfl rfl, by decide, by decide⟩

/-! ## No one list serves all terms -/

/-- **The local table of a list answers no test of a name outside the list**:
over a table that leaves the test to the family, the test of two names of
which one is not in the list has no step. -/
theorem localTable_test_stuck {rules : List RewriteRule} (leaves : LeavesNames rules)
    {names : List String} {first second : String} (outside : first ∉ names ∨ second ∉ names) :
    IsNormal (Step (programTheory (localTable rules names))) (nameTest first second) := by
  intro target step
  have applied : Step (programTheory (localTable rules names))
      (.app (.app (.con "lib") (.con "same-name")) (cells [.con first, .con second])) target := step
  have rooted : ∀ rule, (programTheory (localTable rules names)).rule rule →
      rewritesCall rule = true := fun rule member =>
    withNames_rooted leaves.rooted rule ((localTable_extends rules names).rule rule member)
  rcases applied.app_inv with root | ⟨_, inner, -⟩ | ⟨_, inner, -⟩
  · rcases rootStep_program_inv root with ⟨domain, body, argument, shape, -⟩ |
      ⟨rule, member, assignment, shape, -⟩
    · simp at shape
    · rcases List.mem_append.mp member with inTable | inFamily
      · exact leaves.unanswered rule inTable assignment first second shape.symm
      · obtain ⟨other, otherIn, last, lastIn, rfl⟩ := mem_nameRulesOn.mp inFamily
        obtain ⟨rfl, rfl⟩ := nameTest_injective (first := first) (second := second) shape
        rcases outside with absent | absent
        · exact absent otherIn
        · exact absent lastIn
  · exact passive_normal (fun _ => rfl) rooted _ rfl _ inner
  · exact passive_normal (fun _ => rfl) rooted _ (passive_cells (by simp [passive])) _ inner

#print axioms constantsOf_eq_dedukti
#print axioms step_local
#print axioms step_withNames_iff_local
#print axioms reduces_local
#print axioms reduces_withNames_iff_local
#print axioms normal_withNames_iff_local
#print axioms names_of_reduct
#print axioms reduces_withNames_iff_namesFor
#print axioms freeRule_creates_name
#print axioms localTable_test_stuck

end Mettapedia.Logic.HostingStyles.NameEquality
