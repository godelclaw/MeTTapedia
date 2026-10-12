import Mettapedia.Logic.HostingStyles.NameEquality.DataEquality
import Mettapedia.Logic.HostingStyles.NameEquality.Renaming
import Mettapedia.Logic.HostingStyles.StoredPrograms.Running

/-!
# The equality of data over the test, with names as constants

With a name written as one constant no finite table decides the equality of
two symbols (`StoredPrograms.no_table_decides_constants`).  With the family of
the equality of names a table does.

`dataEqualityTable` is the table: the forty-eight rules that compare data
without comparing names, and the four that compare two numbers in unary.
**Fifty-two rules, beside the sixty-five that do the same with names in
letters** (sixty-one and the same four; `dataEqualityTable_length`).  It is a
stored table and leaves the test to the family, so its theory with the family
is orthogonal (`dataEqualityTable_orthogonal`).

* **It agrees with the host on all data**: the call of `nik:data-eq` on two
  data reduces to the datum of what the host returns
  (`dataEquality_realized_withNames`), and reaches a truth value exactly when
  that is the value of the equality of the two data
  (`dataEquality_withNames_iff`).
* **So it decides the equality of two symbols**, which no finite table does:
  the call on two symbols reduces to `False` exactly when the two names differ
  (`withNames_decides_constants`).
* Negative: without the family the table answers no test of two names, and
  its theory does not compare written names (`dataEqualityTable_names_stuck`,
  `dataEqualityTable_not_comparesNames`).

## The length of a comparison

The comparison of two symbols takes three steps, whatever the names: the rule
of the primitive, the rule of two symbols, and the rule of the family
(`symbols_three_steps`, by running the table).  With names in letters the
comparison of two names runs through their letters and digits.  **No one step
answers the test of two names that both have a letter**
(`letters_no_answer_in_one_step`): the step at the root is to the conjunction
of the test of the first letters and the test of the rest.  The names `a` and
`a` take eleven steps of the rules of names, and the name `Certificate:Node`
with itself one hundred and sixty (`letters_eleven_steps`,
`letters_tag_steps`); two names that differ in their first digit take four
(`letters_four_steps`).  The counts are those of the leftmost innermost
strategy.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (boolean dataEqualityHost)
open Mettapedia.GSLT.Dedukti
  (Theory RewriteRule Step Reduces inst normal_form_unique_of_orthogonal)
open Mettapedia.Logic.Relation (IsNormal Confluent)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory rootStep_program_inv)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-- **The table that computes the equality of data from the test of names**:
the forty-eight rules that compare data without comparing names, and the four
rules that compare two numbers in unary. -/
def dataEqualityTable : List RewriteRule :=
  structuralRules constantSpelling ++ equalNumbersRules constantSpelling

/-- Fifty-two rules. -/
theorem dataEqualityTable_length : dataEqualityTable.length = 52 := by
  simp [dataEqualityTable, structuralRules_length, equalNumbersRules]

/-- With names in letters the same takes sixty-five rules. -/
theorem lettersTable_length :
    (comparisonRules ++ equalNumbersRules letterSpelling).length = 65 := by
  simp [comparisonRules_length, equalNumbersRules]

/-- **It is a stored table**, hence orthogonal. -/
theorem dataEqualityTable_stored : StoredTable dataEqualityTable :=
  storedTable_of_check (by decide)

/-- **It leaves the test to the family**: none of its rules has the root of
the test. -/
theorem dataEqualityTable_leavesNames : LeavesNames dataEqualityTable :=
  leavesNames_of_storedTable dataEqualityTable_stored (by decide)

/-- **Its theory with the family is orthogonal.** -/
theorem dataEqualityTable_orthogonal : (withNames dataEqualityTable).Orthogonal :=
  withNames_orthogonal dataEqualityTable_stored.orthogonal dataEqualityTable_leavesNames

/-- **With the family the table agrees with the host on the equality of
data**, on all data, with names written as constants. -/
theorem dataEquality_realized_withNames :
    RealizesPrimitives constantSpelling (withNames dataEqualityTable) dataEqualityHost
      ["nik:data-eq"] :=
  dataEquality_realized_over constantSpelling
    (fun _ member => Or.inl (List.mem_append_left _ member))
    (fun _ member => Or.inl (List.mem_append_right _ member))
    (withNames_comparesNames dataEqualityTable)

/-- **The call of the equality of data on two data reaches a truth value
exactly when that is the value of their equality.** -/
theorem dataEquality_withNames_iff (left right : EngineTerm) (value : Bool) :
    Reduces (withNames dataEqualityTable)
        (callTerm "nik:data-eq" (data constantSpelling [left, right]))
        (truth constantSpelling value) ↔
      value = decide (left = right) := by
  have computed : Reduces (withNames dataEqualityTable)
      (callTerm "nik:data-eq" (data constantSpelling [left, right]))
      (truth constantSpelling (decide (left = right))) := by
    have returned := dataEquality_realized_withNames "nik:data-eq" (List.mem_singleton.mpr rfl)
      [left, right] (boolean (decide (left = right))) rfl
    rwa [datum_boolean_eq_truth] at returned
  have normal : ∀ answer : Bool,
      IsNormal (Step (withNames dataEqualityTable)) (truth constantSpelling answer) := fun answer =>
    withNames_normal_of_passive dataEqualityTable_leavesNames.rooted
      (passive_truth constantSpelling answer)
  constructor
  · intro reduces
    exact truth_injective constantSpelling_injective
      (normal_form_unique_of_orthogonal dataEqualityTable_orthogonal reduces (normal value)
        computed (normal _))
  · rintro rfl
    exact computed

/-- **With the family the table decides the equality of two symbols**: the
call on two symbols reduces to `False` exactly when the two names differ.  No
finite table does this. -/
theorem withNames_decides_constants (first second : String) :
    Reduces (withNames dataEqualityTable) (symbolsCall first second)
        (truth constantSpelling false) ↔
      first ≠ second := by
  have decided := dataEquality_withNames_iff (.sym first) (.sym second) false
  rw [show symbolsCall first second =
    callTerm "nik:data-eq" (data constantSpelling [.sym first, .sym second]) from rfl, decided]
  simp

/-- **Negative**: without the family the table answers no test of two
names. -/
theorem dataEqualityTable_names_stuck (first second : String) :
    IsNormal (Step (programTheory dataEqualityTable)) (nameTest first second) := by
  have stuck := localTable_test_stuck dataEqualityTable_leavesNames (names := [])
    (first := first) (second := second) (.inl (List.not_mem_nil))
  simpa [localTable, nameRulesOn] using stuck

/-- **Negative**: so the theory of the table without the family does not
compare written names. -/
theorem dataEqualityTable_not_comparesNames :
    ¬ ComparesNames constantSpelling (programTheory dataEqualityTable) := by
  intro compares
  have stuck := (dataEqualityTable_names_stuck "a" "b").reflTransGen_eq (compares "a" "b")
  revert stuck
  decide

/-! ## The length of a comparison -/

/-- **Positive**: the comparison of the symbols `a` and `b` takes three
steps, in the table with the rules of the family for the two names. -/
theorem symbols_three_steps :
    run (localTable dataEqualityTable ["a", "b"]) 3 (symbolsCall "a" "b") =
      truth constantSpelling false := by
  decide +kernel

/-- **Negative**: two steps do not suffice. -/
theorem symbols_two_steps :
    run (localTable dataEqualityTable ["a", "b"]) 2 (symbolsCall "a" "b") ≠
      truth constantSpelling false := by
  decide +kernel

/-- **With names in letters no one step answers the test of two names that
both have a letter**: no step takes the test to a truth value.  The step at
its root is to the conjunction of the test of the first letters and the test
of the rest. -/
theorem letters_no_answer_in_one_step (letter other : List Bool) (rest others : List (List Bool))
    (value : Bool) :
    ¬ Step (programTheory nameRules)
      (sameName (lettersTerm (letter :: rest)) (lettersTerm (other :: others)))
      (truth letterSpelling value) := by
  intro step
  have rooted : ∀ rule, (programTheory nameRules).rule rule → rewritesCall rule = true := by
    intro rule member
    have listed : ∀ candidate ∈ nameRules, rewritesCall candidate = true := by decide
    exact listed rule member
  have quiet : ∀ letters : List (List Bool), passive (lettersTerm letters) = true := fun letters =>
    passive_cells fun item member => by
      obtain ⟨digits, -, rfl⟩ := List.mem_map.mp member
      exact passive_digitsTerm digits
  have applied : Step (programTheory nameRules)
      (.app (.app (.con "lib") (.con "same-name"))
        (cells [lettersTerm (letter :: rest), lettersTerm (other :: others)]))
      (truth letterSpelling value) := step
  rcases applied.app_inv with root | ⟨_, inner, -⟩ | ⟨_, inner, -⟩
  · rcases rootStep_program_inv root with ⟨domain, body, argument, shape, -⟩ |
      ⟨rule, member, assignment, source, target⟩
    · simp at shape
    · simp only [nameRules, sameNameRules, sameLetterRules, bothRules, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with (rfl | rfl | rfl | rfl) |
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
      all_goals first
        | (simp [SameName.nilNil, SameName.nilCons, SameName.consNil, SameName.consCons,
            SameLetter.endEnd, SameLetter.endNought, SameLetter.endOne, SameLetter.noughtEnd,
            SameLetter.oneEnd, SameLetter.noughtNought, SameLetter.oneOne, SameLetter.noughtOne,
            SameLetter.oneNought, Both.whenYes, Both.whenNo, libTerm, cells, lettersTerm]
            at source; done)
        | simp [SameName.consCons, libTerm, cells, truth, tag] at target
  · exact passive_normal (fun _ => rfl) rooted _ rfl _ inner
  · exact passive_normal (fun _ => rfl) rooted _
      (passive_cells (by simp [quiet])) _ inner

/-- With names in letters, the comparison of the name `a` with itself by the
rules of names takes eleven steps. -/
theorem letters_eleven_steps :
    run nameRules 11 (sameName (letterSpelling.write "a") (letterSpelling.write "a")) =
        truth letterSpelling true ∧
      run nameRules 10 (sameName (letterSpelling.write "a") (letterSpelling.write "a")) ≠
        truth letterSpelling true := by
  decide +kernel

/-- Two names that differ in the first digit of their first letter take
four. -/
theorem letters_four_steps :
    run nameRules 4 (sameName (letterSpelling.write "a") (letterSpelling.write "b")) =
        truth letterSpelling false ∧
      run nameRules 3 (sameName (letterSpelling.write "a") (letterSpelling.write "b")) ≠
        truth letterSpelling false := by
  decide +kernel

/-- The name `Certificate:Node`, which the checker of certificates compares at
every node, takes one hundred and sixty with itself. -/
theorem letters_tag_steps :
    run nameRules 160 (sameName (letterSpelling.write "Certificate:Node")
        (letterSpelling.write "Certificate:Node")) = truth letterSpelling true ∧
      run nameRules 159 (sameName (letterSpelling.write "Certificate:Node")
        (letterSpelling.write "Certificate:Node")) ≠ truth letterSpelling true := by
  decide +kernel

#print axioms dataEqualityTable_stored
#print axioms dataEqualityTable_orthogonal
#print axioms dataEquality_realized_withNames
#print axioms dataEquality_withNames_iff
#print axioms withNames_decides_constants
#print axioms dataEqualityTable_names_stuck
#print axioms symbols_three_steps
#print axioms letters_no_answer_in_one_step
#print axioms letters_eleven_steps
#print axioms letters_tag_steps

end Mettapedia.Logic.HostingStyles.NameEquality
