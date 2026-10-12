import Mettapedia.Logic.HostingStyles.NameEquality.LocalTable
import Mettapedia.Logic.HostingStyles.NameEquality.NameSymmetry

/-!
# The price of the test: the renamings of names that steps survive

A renaming of names acts on terms (`renameConstants`) and on rules
(`renameRule`).  A theory is **closed under a renaming** when the renaming
carries its definitions to definitions and its rules to rules
(`ClosedUnder`); then it carries steps to steps, reductions to reductions and
conversions to conversions (`step_renamed`, `reduces_renamed`,
`conv_renamed`).  The rules of the theory may be any set.

## What each theory is closed under

* The theory of a finite table is closed under **every** renaming that fixes
  the names of its rules, injective or not (`programTheory_closedUnder`).
* The theory of a table with the family of the equality of names is closed
  under every **injective** renaming that fixes its fixed names
  (`withNames_closedUnder`), and under no other: over a table that leaves the
  test to the family, a renaming that fixes those names carries steps to
  steps exactly when it is injective (`steps_renamed_iff_injective`).  The
  instance: making `b` into `a` carries the step of the test of `a` and `b`
  to no step (`merge_breaks_step`).

## What a theory can then say about two names

A **question about two names** is a term for each pair of names, natural in
the two names, with an answer that mentions no name outside a list
(`Question`).  A theory answers it for the pairs whose term reduces to the
answer (`Question.Holds`).

* **Closed under every renaming that fixes the list**, whatever the size of
  the set of rules: on names outside the list the question is answered for no
  pair, for the equal pairs, or for all pairs (`Question.one_of_three`).  It
  is never answered for the different pairs exactly
  (`Question.not_difference`): the theory **decides no difference** of names
  outside the list.  The theories of finite tables are of this kind
  (`table_decides_no_difference`).
* **Closed under the injective renamings that fix the list**: no pair, the
  equal pairs, the different pairs, or all pairs (`Question.one_of_four`).
  The theory with the family answers each of the four
  (`withNames_four_relations`); equality and difference are the two answers
  of its one test (`nameQuestion_holds_iff`).

For more than two names: under the injective renamings a question is answered
alike for two lists of names with one equality pattern
(`reduces_iff_of_same_pattern`), and under all renamings an answer is kept
when names are made one (`reduces_of_coarser_pattern`).

So no finite table has the reductions of the theory with the family
(`no_table_has_reductions_of_withNames`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFTyping (subst0)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule RootStep Step Reduces Conv inst)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.Logic.HostingStyles.AtomsReduce (programTheory)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-! ## Theories closed under a renaming -/

/-- **A rule with its names renamed.** -/
def renameRule (naming : String → String) (rule : RewriteRule) : RewriteRule :=
  ⟨renameConstants naming rule.lhs, renameConstants naming rule.rhs⟩

/-- **Positive**: the rule of `a` and `b`, with `a` and `b` exchanged, is the
rule of `b` and `a`.  **Negative**: with `b` made into `a` it is no rule of
the family: it answers the test of `a` with itself by `False`. -/
theorem renameRule_examples :
    renameRule (Equiv.swap "a" "b") (nameRule "a" "b") = nameRule "b" "a" ∧
      renameRule (mergeInto "b" "a") (nameRule "a" "b") =
        ⟨nameTest "a" "a", truth constantSpelling false⟩ ∧
      ¬ NameRule (renameRule (mergeInto "b" "a") (nameRule "a" "b")) := by
  have merged : renameRule (mergeInto "b" "a") (nameRule "a" "b") =
      ⟨nameTest "a" "a", truth constantSpelling false⟩ := by decide
  refine ⟨by decide, merged, ?_⟩
  rw [merged]
  exact nameRule_membership.2

/-- **A theory is closed under a renaming of names**: the renaming carries
definitions to definitions and rules to rules. -/
structure ClosedUnder (theory : Theory) (naming : String → String) : Prop where
  /-- The renamed body of a definition is the body of the renamed name. -/
  body : ∀ name term, theory.body name = some term →
    theory.body (naming name) = some (renameConstants naming term)
  /-- A renamed rule is a rule. -/
  rule : ∀ rule, theory.rule rule → theory.rule (renameRule naming rule)

/-- **A renaming under which a theory is closed carries a step to a step.** -/
theorem step_renamed {theory : Theory} {naming : String → String}
    (closed : ClosedUnder theory naming) {source target : LF.Term}
    (step : Step theory source target) :
    Step theory (renameConstants naming source) (renameConstants naming target) := by
  cases step with
  | inContext context root =>
      rw [renameConstants_plug, renameConstants_plug]
      refine Step.inContext _ ?_
      cases root with
      | beta domain body argument =>
          have contracted := RootStep.beta (theory := theory) (renameConstants naming domain)
            (renameConstants naming body) (renameConstants naming argument)
          simpa [renameConstants, subst0, renameConstants_subst] using contracted
      | delta defined => exact .delta (closed.body _ _ defined)
      | @rule rule assignment member =>
          have fired := RootStep.rule (theory := theory)
            (fun index => renameConstants naming (assignment index)) (closed.rule rule member)
          simpa [inst, renameConstants_instantiate, renameRule] using fired

/-- It carries a reduction to a reduction. -/
theorem reduces_renamed {theory : Theory} {naming : String → String}
    (closed : ClosedUnder theory naming) {source target : LF.Term}
    (reduces : Reduces theory source target) :
    Reduces theory (renameConstants naming source) (renameConstants naming target) := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step_renamed closed step)

/-- It carries a conversion to a conversion. -/
theorem conv_renamed {theory : Theory} {naming : String → String}
    (closed : ClosedUnder theory naming) {source target : LF.Term}
    (convertible : Conv theory source target) :
    Conv theory (renameConstants naming source) (renameConstants naming target) := by
  induction convertible with
  | rel _ _ step => exact .rel _ _ (step_renamed closed step)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-- **The theory of a finite table is closed under every renaming that fixes
the names of its rules**, injective or not. -/
theorem programTheory_closedUnder {rules : List RewriteRule} {naming : String → String}
    (fixes : ∀ name ∈ constantsOfRules rules, naming name = name) :
    ClosedUnder (programTheory rules) naming where
  body := fun _ _ defined => by cases defined
  rule := by
    intro rule member
    have left : renameConstants naming rule.lhs = rule.lhs :=
      renameConstants_of_fixed naming _ fun name found =>
        fixes name (List.mem_flatMap.mpr ⟨rule, member, List.mem_append_left _ found⟩)
    have right : renameConstants naming rule.rhs = rule.rhs :=
      renameConstants_of_fixed naming _ fun name found =>
        fixes name (List.mem_flatMap.mpr ⟨rule, member, List.mem_append_right _ found⟩)
    show renameRule naming rule ∈ rules
    rw [renameRule, left, right]
    exact member

/-- A renaming that fixes the names of the test carries the test of two names
to the test of their images. -/
theorem renameConstants_nameTest {naming : String → String}
    (fixes : ∀ name ∈ testNames, naming name = name) (first second : String) :
    renameConstants naming (nameTest first second) = nameTest (naming first) (naming second) := by
  simp [nameTest, libTerm, cells, renameConstants, fixes "lib" (by decide),
    fixes "same-name" (by decide), fixes "cons" (by decide), fixes "nil" (by decide)]

/-- A renaming that fixes the names of the answers fixes the answers. -/
theorem renameConstants_truth {naming : String → String}
    (fixes : ∀ name ∈ testNames, naming name = name) (value : Bool) :
    renameConstants naming (truth constantSpelling value) = truth constantSpelling value :=
  renameConstants_of_fixed naming _ fun name member =>
    fixes name (constantsOf_truth value name member)

/-- **The theory of a table with the family is closed under every injective
renaming that fixes its fixed names.** -/
theorem withNames_closedUnder {rules : List RewriteRule} {naming : String → String}
    (injective : Function.Injective naming)
    (fixes : ∀ name ∈ fixedNames rules, naming name = name) :
    ClosedUnder (withNames rules) naming where
  body := fun _ _ defined => by cases defined
  rule := by
    have testFixed : ∀ name ∈ testNames, naming name = name := fun name member =>
      fixes name (List.mem_append_right _ member)
    rintro rule (inTable | ⟨first, second, rfl⟩)
    · exact .inl ((programTheory_closedUnder fun name member =>
        fixes name (List.mem_append_left _ member)).rule rule inTable)
    · refine .inr ⟨naming first, naming second, ?_⟩
      have same : decide (first = second) = decide (naming first = naming second) :=
        decide_eq_decide.mpr ⟨congrArg naming, fun images => injective images⟩
      simp only [renameRule, nameRule, renameConstants_nameTest testFixed,
        renameConstants_truth testFixed, same]

/-- **Negative**: the theory of the family alone is not closed under the
renaming that makes `b` into `a`. -/
theorem withNames_not_closedUnder_merge : ¬ ClosedUnder (withNames []) (mergeInto "b" "a") := by
  intro closed
  rcases closed.rule (nameRule "a" "b") (Or.inr ⟨"a", "b", rfl⟩) with inTable | inFamily
  · cases inTable
  · exact renameRule_examples.2.2 inFamily

/-- **Steps of the theory with the family survive exactly the injective
renamings**: over a table that leaves the test to the family, a renaming that
fixes the fixed names carries every step to a step exactly when it is
injective. -/
theorem steps_renamed_iff_injective {rules : List RewriteRule} (leaves : LeavesNames rules)
    {naming : String → String} (fixes : ∀ name ∈ fixedNames rules, naming name = name) :
    (∀ source target : LF.Term, Step (withNames rules) source target →
        Step (withNames rules) (renameConstants naming source) (renameConstants naming target)) ↔
      Function.Injective naming := by
  have testFixed : ∀ name ∈ testNames, naming name = name := fun name member =>
    fixes name (List.mem_append_right _ member)
  constructor
  · intro survive first second images
    by_contra different
    have step := survive _ _ (nameTest_step rules first second)
    rw [renameConstants_nameTest testFixed, renameConstants_truth testFixed, images] at step
    have values := truth_injective constantSpelling_injective ((nameTest_step_iff leaves).mp step)
    simp [different] at values
  · intro injective source target step
    exact step_renamed (withNames_closedUnder injective fixes) step

/-- **The instance.**  The test of `a` and `b` steps to `False`.  The renaming
that makes `b` into `a` and leaves every other name as it is carries that step
to no step: the test of `a` with itself does not step to `False`. -/
theorem merge_breaks_step :
    Step (withNames []) (nameTest "a" "b") (truth constantSpelling false) ∧
      ¬ Step (withNames []) (renameConstants (mergeInto "b" "a") (nameTest "a" "b"))
        (renameConstants (mergeInto "b" "a") (truth constantSpelling false)) := by
  refine ⟨nameTest_step [] "a" "b", fun step => ?_⟩
  have renamedTest : renameConstants (mergeInto "b" "a") (nameTest "a" "b") = nameTest "a" "a" := by
    decide
  have renamedAnswer : renameConstants (mergeInto "b" "a") (truth constantSpelling false) =
      truth constantSpelling false := by decide
  rw [renamedTest, renamedAnswer] at step
  have answer := (nameTest_step_iff leavesNames_nil).mp step
  revert answer
  decide

/-! ## Questions about two names -/

/-- **A question about two names that mentions no other name outside a
list**: a term for each pair of names, natural in the two names under the
renamings that fix the list, and an answer whose names are in the list. -/
structure Question (fixed : List String) where
  /-- The term that is asked, for each pair of names. -/
  probe : String → String → LF.Term
  /-- The term that is the answer. -/
  answer : LF.Term
  /-- A renaming that fixes the list carries the term of a pair to the term
  of the renamed pair. -/
  natural : ∀ naming : String → String, (∀ name ∈ fixed, naming name = name) →
    ∀ first second : String,
      renameConstants naming (probe first second) = probe (naming first) (naming second)
  /-- The names of the answer are in the list. -/
  answerFixed : ∀ name ∈ constantsOf answer, name ∈ fixed

/-- **A theory answers a question for a pair of names**: the term of the pair
reduces to the answer. -/
def Question.Holds {fixed : List String} (question : Question fixed) (theory : Theory)
    (first second : String) : Prop :=
  Reduces theory (question.probe first second) question.answer

/-- An answer is kept by every renaming that fixes the list and under which
the theory is closed. -/
theorem Question.holds_renamed {fixed : List String} (question : Question fixed)
    {theory : Theory} {naming : String → String} (fixes : ∀ name ∈ fixed, naming name = name)
    (closed : ClosedUnder theory naming) {first second : String}
    (held : question.Holds theory first second) :
    question.Holds theory (naming first) (naming second) := by
  have moved := reduces_renamed closed held
  rwa [question.natural naming fixes, renameConstants_of_fixed naming _ fun name member =>
    fixes name (question.answerFixed name member)] at moved

/-- **The question of the test**: the test of the two names, with one of the
two truth values as the answer. -/
def nameQuestion (fixed : List String) (covers : ∀ name ∈ testNames, name ∈ fixed)
    (value : Bool) : Question fixed where
  probe := nameTest
  answer := truth constantSpelling value
  natural := fun _ fixes first second =>
    renameConstants_nameTest (fun name member => fixes name (covers name member)) first second
  answerFixed := fun name member => covers name (constantsOf_truth value name member)

/-- **A question that asks nothing of the names**: one term for all pairs. -/
def constantQuestion (fixed : List String) (asked answer : LF.Term)
    (askedFixed : ∀ name ∈ constantsOf asked, name ∈ fixed)
    (answerFixed : ∀ name ∈ constantsOf answer, name ∈ fixed) : Question fixed where
  probe := fun _ _ => asked
  answer := answer
  natural := fun naming fixes _ _ =>
    renameConstants_of_fixed naming _ fun name member => fixes name (askedFixed name member)
  answerFixed := answerFixed

/-- **Negative**: the test of a name against `c` is no question over a list
that does not hold `c`: it is not natural in its two names. -/
theorem testAgainstC_not_natural :
    ¬ ∀ naming : String → String, (∀ name ∈ testNames, naming name = name) →
      ∀ first : String,
        renameConstants naming (nameTest first "c") = nameTest (naming first) "c" := by
  intro natural
  have moved := natural (mergeInto "c" "d") (mergeInto_fixes (fixed := {name | name ∈ testNames})
    (by decide) "d") "a"
  revert moved
  decide

/-- **The theory with the family answers the question of the test for the
pairs for which the answer is right.** -/
theorem nameQuestion_holds_iff {rules : List RewriteRule} (leaves : LeavesNames rules)
    {fixed : List String} (covers : ∀ name ∈ testNames, name ∈ fixed) (value : Bool)
    (first second : String) :
    (nameQuestion fixed covers value).Holds (withNames rules) first second ↔
      value = decide (first = second) :=
  nameTest_reduces_truth_iff leaves first second value

/-! ## Three relations, and four -/

/-- There are two different names outside every list. -/
theorem exists_two_names_outside (fixed : List String) :
    ∃ first second : String, first ∉ fixed ∧ second ∉ fixed ∧ first ≠ second := by
  have names := infinite_names
  obtain ⟨first, firstFresh⟩ := Infinite.exists_notMem_finset fixed.toFinset
  obtain ⟨second, secondFresh⟩ := Infinite.exists_notMem_finset (insert first fixed.toFinset)
  refine ⟨first, second, fun member => firstFresh (List.mem_toFinset.mpr member),
    fun member => secondFresh (Finset.mem_insert_of_mem (List.mem_toFinset.mpr member)),
    fun same => secondFresh (same ▸ Finset.mem_insert_self first _)⟩

/-- **A theory closed under every renaming that fixes a list answers a
question, on the names outside the list, for no pair, for the equal pairs, or
for all pairs.**  The set of its rules may be of any size. -/
theorem Question.one_of_three {theory : Theory} {fixed : List String}
    (closed : ∀ naming : String → String, (∀ name ∈ fixed, naming name = name) →
      ClosedUnder theory naming) (question : Question fixed) :
    (∀ first second, first ∉ fixed → second ∉ fixed → ¬ question.Holds theory first second) ∨
      (∀ first second, first ∉ fixed → second ∉ fixed →
        (question.Holds theory first second ↔ first = second)) ∨
      ∀ first second, first ∉ fixed → second ∉ fixed → question.Holds theory first second :=
  pair_relation_one_of_three (fixed := {name | name ∈ fixed}) (holds := question.Holds theory)
    fun naming fixes _ _ held => question.holds_renamed fixes (closed naming fixes) held

/-- **Such a theory decides no difference of names outside the list**: it
answers no question for the different pairs exactly. -/
theorem Question.not_difference {theory : Theory} {fixed : List String}
    (closed : ∀ naming : String → String, (∀ name ∈ fixed, naming name = name) →
      ClosedUnder theory naming) (question : Question fixed) :
    ¬ ∀ first second, first ∉ fixed → second ∉ fixed →
      (question.Holds theory first second ↔ first ≠ second) := by
  intro decides
  obtain ⟨first, second, outFirst, outSecond, different⟩ := exists_two_names_outside fixed
  have held := (decides first second outFirst outSecond).mpr different
  rcases question.one_of_three closed with empty | equality | full
  · exact empty first second outFirst outSecond held
  · exact different ((equality first second outFirst outSecond).mp held)
  · exact (decides first first outFirst outFirst).mp (full first first outFirst outFirst) rfl

/-- **A theory closed under every injective renaming that fixes a list
answers a question, on the names outside the list, for no pair, for the equal
pairs, for the different pairs, or for all pairs.** -/
theorem Question.one_of_four {theory : Theory} {fixed : List String}
    (closed : ∀ naming : String → String, Function.Injective naming →
      (∀ name ∈ fixed, naming name = name) → ClosedUnder theory naming)
    (question : Question fixed) :
    (∀ first second, first ∉ fixed → second ∉ fixed → ¬ question.Holds theory first second) ∨
      (∀ first second, first ∉ fixed → second ∉ fixed →
        (question.Holds theory first second ↔ first = second)) ∨
      (∀ first second, first ∉ fixed → second ∉ fixed →
        (question.Holds theory first second ↔ first ≠ second)) ∨
      ∀ first second, first ∉ fixed → second ∉ fixed → question.Holds theory first second :=
  pair_relation_one_of_four (fixed := {name | name ∈ fixed}) (holds := question.Holds theory)
    fun naming fixes _ _ held =>
      question.holds_renamed fixes (closed naming naming.injective fixes) held

/-- **No finite table decides a difference of names**: the theory of a list
of rules answers no question, over the names of its rules, for the different
pairs exactly. -/
theorem table_decides_no_difference (table : List RewriteRule)
    (question : Question (constantsOfRules table)) :
    ¬ ∀ first second, first ∉ constantsOfRules table → second ∉ constantsOfRules table →
      (question.Holds (programTheory table) first second ↔ first ≠ second) :=
  question.not_difference fun _ fixes => programTheory_closedUnder fixes

/-- **The theory with the family answers each of the four**: no pair, the
equal pairs, the different pairs, all pairs. -/
theorem withNames_four_relations {rules : List RewriteRule} (leaves : LeavesNames rules) :
    (∃ question : Question (fixedNames rules),
        ∀ first second, ¬ question.Holds (withNames rules) first second) ∧
      (∃ question : Question (fixedNames rules),
        ∀ first second, question.Holds (withNames rules) first second ↔ first = second) ∧
      (∃ question : Question (fixedNames rules),
        ∀ first second, question.Holds (withNames rules) first second ↔ first ≠ second) ∧
      ∃ question : Question (fixedNames rules),
        ∀ first second, question.Holds (withNames rules) first second := by
  have covers : ∀ name ∈ testNames, name ∈ fixedNames rules := fun _ member =>
    List.mem_append_right _ member
  have answersFixed : ∀ value : Bool, ∀ name ∈ constantsOf (truth constantSpelling value),
      name ∈ fixedNames rules := fun value name member =>
    covers name (constantsOf_truth value name member)
  refine ⟨⟨constantQuestion _ (truth constantSpelling false) (truth constantSpelling true)
      (answersFixed false) (answersFixed true), fun first second held => ?_⟩,
    ⟨nameQuestion _ covers true, fun first second => ?_⟩,
    ⟨nameQuestion _ covers false, fun first second => ?_⟩,
    ⟨constantQuestion _ (truth constantSpelling true) (truth constantSpelling true)
      (answersFixed true) (answersFixed true), fun _ _ => .refl⟩⟩
  · have stuck := (withNames_normal_of_passive leaves.rooted
      (passive_truth constantSpelling false)).reflTransGen_eq held
    exact absurd (truth_injective constantSpelling_injective stuck) (by decide)
  · rw [nameQuestion_holds_iff leaves covers]
    simp
  · rw [nameQuestion_holds_iff leaves covers]
    simp

/-- **So the theory with the family is closed under some renamings only**:
over a table that leaves the test to the family, it is not closed under every
renaming that fixes its fixed names. -/
theorem withNames_not_closedUnder_all {rules : List RewriteRule} (leaves : LeavesNames rules) :
    ¬ ∀ naming : String → String, (∀ name ∈ fixedNames rules, naming name = name) →
      ClosedUnder (withNames rules) naming := by
  intro closed
  have covers : ∀ name ∈ testNames, name ∈ fixedNames rules := fun _ member =>
    List.mem_append_right _ member
  refine (nameQuestion (fixedNames rules) covers false).not_difference closed
    fun first second _ _ => ?_
  rw [nameQuestion_holds_iff leaves covers]
  simp

/-- **No finite table has the reductions of the theory with the family**,
over a table that leaves the test to the family. -/
theorem no_table_has_reductions_of_withNames {rules : List RewriteRule}
    (leaves : LeavesNames rules) (table : List RewriteRule) :
    ¬ ∀ source target : LF.Term,
      Reduces (withNames rules) source target ↔ Reduces (programTheory table) source target := by
  intro same
  have covers : ∀ name ∈ testNames, name ∈ constantsOfRules table ++ testNames := fun _ member =>
    List.mem_append_right _ member
  refine (nameQuestion (constantsOfRules table ++ testNames) covers false).not_difference
    (theory := programTheory table)
    (fun naming fixes => programTheory_closedUnder fun name member =>
      fixes name (List.mem_append_left _ member))
    fun first second _ _ => ?_
  have local_ := nameQuestion_holds_iff leaves covers false first second
  rw [Question.Holds, same] at local_
  rw [Question.Holds, local_]
  simp

/-! ## More than two names -/

/-- **Under the injective renamings a question about some names is answered
alike for two lists with one equality pattern.** -/
theorem reduces_iff_of_same_pattern {theory : Theory} {fixed : List String}
    (closed : ∀ naming : String → String, Function.Injective naming →
      (∀ name ∈ fixed, naming name = name) → ClosedUnder theory naming)
    {count : Nat} {probe : (Fin count → String) → LF.Term} {answer : LF.Term}
    (natural : ∀ naming : String → String, (∀ name ∈ fixed, naming name = name) →
      ∀ names, renameConstants naming (probe names) = probe (naming ∘ names))
    (answerFixed : ∀ name ∈ constantsOf answer, name ∈ fixed)
    {first second : Fin count → String} (outsideFirst : ∀ index, first index ∉ fixed)
    (outsideSecond : ∀ index, second index ∉ fixed)
    (pattern : ∀ index other, first index = first other ↔ second index = second other) :
    Reduces theory (probe first) answer ↔ Reduces theory (probe second) answer :=
  holds_iff_of_same_pattern (fixed := {name | name ∈ fixed})
    (holds := fun names => Reduces theory (probe names) answer)
    (fun naming fixes names held => by
      have moved := reduces_renamed (closed naming naming.injective fixes) held
      rwa [natural naming fixes, renameConstants_of_fixed naming _ fun name member =>
        fixes name (answerFixed name member)] at moved)
    outsideFirst outsideSecond pattern

/-- **Under all renamings an answer is kept when names are made one.** -/
theorem reduces_of_coarser_pattern {theory : Theory} {fixed : List String}
    (closed : ∀ naming : String → String, (∀ name ∈ fixed, naming name = name) →
      ClosedUnder theory naming)
    {count : Nat} {probe : (Fin count → String) → LF.Term} {answer : LF.Term}
    (natural : ∀ naming : String → String, (∀ name ∈ fixed, naming name = name) →
      ∀ names, renameConstants naming (probe names) = probe (naming ∘ names))
    (answerFixed : ∀ name ∈ constantsOf answer, name ∈ fixed)
    {first second : Fin count → String} (outsideFirst : ∀ index, first index ∉ fixed)
    (coarser : ∀ index other, first index = first other → second index = second other)
    (reduces : Reduces theory (probe first) answer) : Reduces theory (probe second) answer :=
  holds_of_coarser_pattern (fixed := {name | name ∈ fixed})
    (holds := fun names => Reduces theory (probe names) answer)
    (fun naming fixes names held => by
      have moved := reduces_renamed (closed naming fixes) held
      rwa [natural naming fixes, renameConstants_of_fixed naming _ fun name member =>
        fixes name (answerFixed name member)] at moved)
    outsideFirst coarser reduces

#print axioms step_renamed
#print axioms reduces_renamed
#print axioms conv_renamed
#print axioms programTheory_closedUnder
#print axioms withNames_closedUnder
#print axioms withNames_not_closedUnder_merge
#print axioms steps_renamed_iff_injective
#print axioms merge_breaks_step
#print axioms nameQuestion_holds_iff
#print axioms Question.one_of_three
#print axioms Question.not_difference
#print axioms Question.one_of_four
#print axioms table_decides_no_difference
#print axioms withNames_four_relations
#print axioms withNames_not_closedUnder_all
#print axioms no_table_has_reductions_of_withNames
#print axioms reduces_iff_of_same_pattern
#print axioms reduces_of_coarser_pattern

end Mettapedia.Logic.HostingStyles.NameEquality
