import Mettapedia.Logic.HostingStyles.NameEquality.CheckRunNames
import Mettapedia.Logic.HostingStyles.NameEquality.AdmissionRunNames
import Mettapedia.Logic.HostingStyles.NameEquality.VerificationRunNames
import Mettapedia.Logic.HostingStyles.NameEquality.VerificationRefusalNames
import Mettapedia.Logic.HostingStyles.NameEquality.NamesAsConstants
import Mettapedia.Logic.HostingStyles.NameEquality.RepeatedVariable
import Mettapedia.Logic.HostingStyles.NameEquality.OrderOfEquations
import Mettapedia.Logic.HostingStyles.NameEquality.FreshnessPremise
import Mettapedia.Logic.HostingStyles.NameEquality.Numbers

/-!
# Names in the candidate, same and different: the table

The candidate in which atoms reduce has "same" in one step: a rule whose left
side repeats a variable compares.  What no finite table has is "different".
This directory adds the test of the equality of names to the candidate as
theory, in three ways, and states what each costs.

## Four ways to write names and to test them

| | names in letters | names as constants, no test | names as constants, the test as steps | the test as a premise |
|---|---|---|---|---|
| same in one step | no, for two names that both have a letter (`letters_no_answer_in_one_step`); eleven steps for `a` with itself and one hundred and sixty for `Certificate:Node`, leftmost innermost (`letters_eleven_steps`, `letters_tag_steps`) | by a rule with a repeated variable (`candidate_same_step`, `sameTable_reduces_iff`) | `nameTest_step`, and no other step (`nameTest_step_iff`); in the candidate `nameTest_localRun_step` | by the repeated variable of the matcher (`matchPattern_repeated`) |
| different in one step | no, for two names that both have a letter (`letters_no_answer_in_one_step`); four steps for `a` and `b`, leftmost innermost (`letters_four_steps`) | **by no finite table** (`table_decides_no_difference`, `StoredPrograms.no_table_decides_constants`, `candidate_different_stuck`) | `nameTest_step`; `False` exactly for two names (`nameTest_reduces_truth_iff`) | one rewrite with the premise, which the engine applies exactly when the names differ (`freshness_iff_differ`, `differRewrite_fires`) |
| renamings of names that steps survive | none acts: a renaming that fixes the table fixes every written name (`letterSpelling_renamed`) | every renaming that fixes the names of the table, injective or not (`programTheory_closedUnder`) | **exactly the injective ones** (`steps_renamed_iff_injective`, `merge_breaks_step`) | the premise is kept by the injective ones (`freshness_injective_iff`) and not by a merging (`freshness_examples`) |
| relations on two names that it answers | equal and different (`StoredPrograms.sameName_reduces`) | none, equal, all, and no other (`Question.one_of_three`); equal by one rule (`sameTable_reduces_iff`) | none, equal, different, all, and no other (`Question.one_of_four`, `withNames_four_relations`) | equal and different (`matchPattern_repeated`, `freshness_iff_differ`) |
| rules for the equality of data | 61 (`StoredPrograms.comparisonRules_length`) | none: no finite table decides the equality of two symbols (`StoredPrograms.no_table_decides_constants`), and a table that computes the primitive is not orthogonal (`stores_dataEquality_not_orthogonal`) | 48 and the family (`structuralRules_length`, `dataEquality_withNames_iff`); in a space of `n` names the family is `n * n` closed rules (`nameRulesOn_length`) | open |
| steps of the certificate check | 7353, measured, not replayed | no orthogonal table stores the check (`checkPart_no_orthogonal_table`) | **1062, replayed** (`checkNames_instance_replays`, `checkNames_instance_run_steps`) | open |
| orthogonal | yes (`StoredPrograms.check_stored`) | yes, for what a table computes (`StoredPrograms.lookup_orthogonal`) | **yes** (`withNames_orthogonal`, `checkNames_stored`) | open |

The three cells that are open are in the last column.  With the test as a
premise no table of the equality of data is built in the engine of language
definitions and no check of a certificate is run there.  Orthogonality is
stated for theories of rules without premise, and no statement of confluence
is made for a rewrite with a premise; in the theory of steps, "same" by a
repeated variable loses orthogonality, and confluence over an orthogonal
table (`withDifference_not_orthogonal`, `repeatedVariable_loses_confluence`).

## MM0's kernel, run over the test

The three programs of the kernel, each with names in letters and with names as
constants over the test of names.  A count that is replayed is a theorem of
Lean's kernel; a count that is measured is an evaluation.

| | rules, letters | rules, over the test | steps, letters | steps, over the test | of them tests of two names |
|---|---|---|---|---|---|
| check of a certificate, accepted | 390 | 377 (`checkNames_size`) | 7353, measured | **1062, replayed** (`checkNames_instance_replays`) | 62 (`checkTraceNames_parts`) |
| the same, refused | | | 2128, measured | 320, replayed (`checkNames_refusal_replays`) | 17 (`refusalTraceNames_parts`) |
| admission of a development | 453 | 440 (`admissionNames_size`) | 343, replayed (`StoredPrograms.admission_instance_replays`) | 225, replayed (`admissionNames_instance_replays`) | 2 (`admissionTraceNames_parts`) |
| the same, refused | | | 26, replayed | 26, replayed (`admissionNames_refusal_replays`) | 0 (`admissionRefusalTraceNames_parts`) |
| verification against a specification | 497 | 484 (`verificationNames_size`) | 4360, measured | **788, replayed** (`verificationNames_instance_replays`) | 36 (`verificationTraceNames_parts`) |
| the same, refused | | | 2569, measured | 451, replayed (`verificationNames_refusal_replays`) | 22 (`verificationRefusalTraceNames_parts`) |

Each run is by the candidate, in the space that stores the table and the rules
of the family for the names of the call.  The run of the check of some
certificate reaches the accepting run exactly when the kernel derives the
judgment (`checkNames_run_iff_derives`); the runs of the admission and of the
verification reach the run of an encoded result exactly when the kernel's
function returns that result (`admissionNames_run_iff`,
`verificationNames_run_iff`).  The replayed runs are that many transitions of
the candidate (`checkNames_instance_run_steps`,
`admissionNames_instance_run_steps`, `verificationNames_instance_run_steps`).

## The three ways to have the test

* **As steps**: the family of the equality of names (`withNames`).  The theory
  of an orthogonal table with the family is orthogonal and confluent.  The
  family is no list, and from one term it is one: a step creates no name
  (`step_local`, `names_of_reduct`).  The price is in the renamings: steps
  survive the injective renamings and no other.
* **A repeated variable for "same", a family for "different"**
  (`withDifference`): "same" in one step on every term, one rule; the theory
  is never orthogonal, and confluence is lost over an orthogonal table.
* **A premise**: the freshness premise of the engine of language definitions,
  on names read as free variables.  An evaluator that answers it stays weak;
  it respects the static equivalence only if it reads the names through the
  contraction (`contractingEvaluator_respectsStatics`,
  `freshnessEvaluator_not_respectsStatics`); answered at the root step of a
  run instead, the test costs the weak evaluator (`answersWithTest_not_weak`).

The order of equations is no fourth way: the first match is not stable under
substitution (`firstMatch_not_stable`), and in the theory both rules answer
(`orderedPair_both_answers`).

## The four separations between the engine and the candidate

* **Primitives of a host: changed.**  The equality of data with names as
  constants, which no finite table computes, is computed by forty-eight rules
  and the family, in agreement with the host on all data
  (`dataEquality_withNames_iff`, `withNames_decides_constants`).
* **First match: unchanged in kind.**  The questions of the ordered heads are
  answered over the family (`dispatches_of_tables_in`).  By evaluation they
  are 370 comparisons of the 1062 steps of the check, beside 213 for the
  equality of data and 231 conjunctions of the answers.
* **Arguments first: unchanged.**  The theory with the family is orthogonal,
  so every normal form that a call reaches is the engine's value
  (`StoresWithNames.normalForm_unique`).
* **A repeated variable: unchanged.**  The class still asks that no variable
  occur twice in a left side: the engine does not compare, and a rule does.

## Numbers

A numeral written as one constant is a name: no finite table computes the
successor, with or without the family (`no_table_computes_successor`,
`withNames_no_successor`); a theory closed under the injective renamings
computes only functions whose values are the argument or a listed numeral
(`computed_value_argument_or_listed`).  As data, three rules compute the
successor of a number in binary and nine compare two numbers
(`binarySuccessor_number`, `binaryComparison_reduces`, `binaryRules_stored`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (Program boolean dataEqualityHost)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces normal_form_unique_of_orthogonal)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.Languages.MM0.Presentation.ComputationalCalculus (calculusProgram)
open Mettapedia.Logic.HostingStyles.AtomsReduce (programTheory)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-! ## Names in letters are not renamed -/

/-- **The five constants of the alphabet** in which a name is written in
letters. -/
def alphabet : List String := ["cons", "nil", "one", "nought", "end"]

/-- The constants of the digits of a letter are constants of the alphabet. -/
theorem constantsOf_digitsTerm : ∀ letter : List Bool,
    ∀ name ∈ constantsOf (digitsTerm letter), name ∈ alphabet
  | [] => by simp [digitsTerm, constantsOf, alphabet]
  | true :: rest => by
      intro name member
      simp only [digitsTerm, constantsOf, List.mem_append, List.mem_singleton] at member
      rcases member with rfl | later
      · simp [alphabet]
      · exact constantsOf_digitsTerm rest name later
  | false :: rest => by
      intro name member
      simp only [digitsTerm, constantsOf, List.mem_append, List.mem_singleton] at member
      rcases member with rfl | later
      · simp [alphabet]
      · exact constantsOf_digitsTerm rest name later

/-- The constants of the letters of a name are constants of the alphabet. -/
theorem constantsOf_lettersTerm : ∀ letters : List (List Bool),
    ∀ name ∈ constantsOf (lettersTerm letters), name ∈ alphabet
  | [] => by simp [lettersTerm, cells, constantsOf, alphabet]
  | letter :: rest => by
      intro name member
      simp only [lettersTerm, List.map_cons, cells, constantsOf, List.mem_append,
        List.mem_singleton] at member
      rcases member with (rfl | inLetter) | inRest
      · simp [alphabet]
      · exact constantsOf_digitsTerm letter name inLetter
      · exact constantsOf_lettersTerm rest name inRest

/-- **A name in letters is not renamed**: a renaming that fixes the five
constants of the alphabet fixes every written name.  The renamings of names do
not act on a table with names in letters. -/
theorem letterSpelling_renamed {naming : String → String}
    (fixes : ∀ name ∈ alphabet, naming name = name) (name : String) :
    renameConstants naming (letterSpelling.write name) = letterSpelling.write name :=
  renameConstants_of_fixed naming _ fun constant member =>
    fixes constant (constantsOf_lettersTerm (lettersOf name) constant member)

/-- **Negative**: a name written as one constant is renamed with its name. -/
theorem constantSpelling_renamed (naming : String → String) (name : String) :
    renameConstants naming (constantSpelling.write name) = constantSpelling.write (naming name) :=
  rfl

/-! ## Names as constants without the test -/

/-- **With names as constants and no test, no orthogonal finite table computes
the equality of data**: a table that stores a program and computes
`nik:data-eq` as the host does has a theory that is not orthogonal. -/
theorem stores_dataEquality_not_orthogonal {table : List RewriteRule} {program : Program}
    {primitives : List String}
    (stores : Stores constantSpelling table program dataEqualityHost primitives)
    (uses : "nik:data-eq" ∈ primitives) : ¬ (programTheory table).Orthogonal := by
  intro orthogonal
  refine no_table_decides_constants table fun first second => ?_
  have computed : Reduces (programTheory table) (symbolsCall first second)
      (truth constantSpelling (decide (first = second))) := by
    have returned := stores.realizes "nik:data-eq" uses [.sym first, .sym second]
      (boolean (decide (first = second))) (by
        rw [dataEquality_unfold]
        simp)
    rwa [datum_boolean_eq_truth] at returned
  have normal : ∀ value : Bool,
      IsNormal (Step (programTheory table)) (truth constantSpelling value) := fun value =>
    passive_normal (fun _ => rfl) stores.rooted _ (passive_truth constantSpelling value)
  constructor
  · rintro reduces rfl
    have equal := truth_injective constantSpelling_injective
      (normal_form_unique_of_orthogonal orthogonal reduces (normal false) computed (normal _))
    simp at equal
  · intro different
    simpa [different] using computed

/-- **So no orthogonal finite table stores the check of a certificate with
names as constants.** -/
theorem checkPart_no_orthogonal_table (table : List RewriteRule)
    (stores : Stores constantSpelling table (partAt calculusProgram certificateHeads)
      dataEqualityHost largerPrimitives) : ¬ (programTheory table).Orthogonal :=
  stores_dataEquality_not_orthogonal stores (by decide)

#print axioms letterSpelling_renamed
#print axioms stores_dataEquality_not_orthogonal
#print axioms checkPart_no_orthogonal_table

end Mettapedia.Logic.HostingStyles.NameEquality
