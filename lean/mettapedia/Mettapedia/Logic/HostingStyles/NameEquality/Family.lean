import Mettapedia.Logic.HostingStyles.StoredPrograms.TableCheck

/-!
# The equality of names as steps

A name is written as one constant.  The **test** of two names is the helper
`same-name` on the two constants (`nameTest`).  The **family of the equality
of names** has one closed rule for each pair of names (`nameRule`,
`NameRule`): the test of a name with itself rewrites to `True`, the test of
two names to `False`.  The family is not a list: there is a rule for every two
strings.  The **theory of a table with the family** is `withNames`.

A table **leaves the test to the family** (`LeavesNames`) when its rules
rewrite calls and no left side, and no headed part of a left side, has a test
of two names as an instance.  A stored table none of whose rules has the root
of the test does (`leavesNames_of_storedTable`).  For such a table:

* the test of two names has one step, to the right answer, and no other
  (`nameTest_step`, `nameTest_step_iff`);
* the answer has no step (`withNames_normal_of_passive`), so it is the only
  normal form that the test reaches, and the test reaches the answer `True`
  exactly when the names are one name, and `False` exactly when they are two
  (`nameTest_normalForm_unique`, `nameTest_reduces_truth_iff`);
* no rule of the family overlaps another, or a rule of the table: **the
  theory of an orthogonal table with the family is orthogonal**
  (`withNames_orthogonal`), hence confluent (`withNames_confluent`).

Negative: a table that answers the test of `a` and `b` itself does not leave
the test to the family, and with the family the test has two normal forms
(`answeringTable_not_leavesNames`, `answeringTable_not_confluent`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFTyping (subst0)
open Mettapedia.GSLT.Dedukti
  (Theory RewriteRule RootStep Step Reduces inst algebraic patternVars subpatterns Inert
    confluent_of_orthogonal)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (step_of_rule not_confluent_of_fork)
open Mettapedia.Logic.Relation (IsNormal Confluent)
open Mettapedia.Logic.HostingStyles.AtomsReduce (programTheory)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-! ## The test and the family -/

/-- **The test of the equality of two names**: the helper `same-name` on the
two names, each written as one constant. -/
def nameTest (first second : String) : LF.Term := libTerm "same-name" [.con first, .con second]

/-- **The rule of a pair of names**: their test rewrites to `True` when they
are one name, and to `False` when they are two. -/
def nameRule (first second : String) : RewriteRule :=
  ⟨nameTest first second, truth constantSpelling (decide (first = second))⟩

/-- **The family of the equality of names**: the rules of all pairs of names. -/
def NameRule (rule : RewriteRule) : Prop := ∃ first second : String, rule = nameRule first second

/-- **The theory of a table with the family of the equality of names.** -/
def withNames (rules : List RewriteRule) : Theory :=
  { programTheory rules with rule := fun rule => rule ∈ rules ∨ NameRule rule }

/-- Two tests of names are one term only when they test the same names in the
same order. -/
theorem nameTest_injective {first second other last : String}
    (same : nameTest first second = nameTest other last) : first = other ∧ second = last := by
  simpa [nameTest, libTerm, cells] using same

/-- A test of names has no variable. -/
theorem inst_nameTest (assignment : Nat → LF.Term) (first second : String) :
    inst assignment (nameTest first second) = nameTest first second := rfl

/-- **Positive**: the test of `a` and `b` is the call of the helper on the two
constants.  **Negative**: it is not the test of `b` and `a`, and it is no
passive term. -/
theorem nameTest_examples :
    nameTest "a" "b" = libTerm "same-name" [.con "a", .con "b"] ∧
      nameTest "a" "b" ≠ nameTest "b" "a" ∧ passive (nameTest "a" "b") = false := by
  decide

/-- **Positive**: the rule of `a` with itself answers `True`; the rule of `a`
and `b` answers `False`. -/
theorem nameRule_examples :
    (nameRule "a" "a").rhs = truth constantSpelling true ∧
      (nameRule "a" "b").rhs = truth constantSpelling false := by
  decide

/-- **Positive**: the rule of `a` and `b` is in the family.  **Negative**: the
rule that answers the test of `a` with itself by `False` is not. -/
theorem nameRule_membership :
    NameRule (nameRule "a" "b") ∧ ¬ NameRule ⟨nameTest "a" "a", truth constantSpelling false⟩ := by
  refine ⟨⟨"a", "b", rfl⟩, ?_⟩
  rintro ⟨first, second, same⟩
  have sides := RewriteRule.mk.inj same
  obtain ⟨rfl, rfl⟩ := nameTest_injective sides.1
  have answers := sides.2
  revert answers
  decide

/-- The rule of a pair of names rewrites a call of a helper. -/
theorem rewritesCall_nameRule (first second : String) :
    rewritesCall (nameRule first second) = true := rfl

/-- The theory of a table is contained in its theory with the family. -/
theorem withNames_extends (rules : List RewriteRule) :
    (programTheory rules).Extends (withNames rules) :=
  ⟨fun _ _ same => same, fun _ _ same => same, fun _ member => Or.inl member⟩

/-- The theory with the family has no definition. -/
theorem withNames_undefined (rules : List RewriteRule) (name : String) :
    (withNames rules).body name = none := rfl

/-- If the rules of a table rewrite calls, so do those of its theory with the
family. -/
theorem withNames_rooted {rules : List RewriteRule}
    (rooted : ∀ rule ∈ rules, rewritesCall rule = true) :
    ∀ rule, (withNames rules).rule rule → rewritesCall rule = true := by
  rintro rule (inTable | ⟨first, second, rfl⟩)
  · exact rooted rule inTable
  · exact rewritesCall_nameRule first second

/-- **A passive term has no step** in the theory of a table with the family,
when the rules of the table rewrite calls. -/
theorem withNames_normal_of_passive {rules : List RewriteRule}
    (rooted : ∀ rule ∈ rules, rewritesCall rule = true) {term : LF.Term}
    (quietTerm : passive term = true) : IsNormal (Step (withNames rules)) term :=
  passive_normal (withNames_undefined rules) (withNames_rooted rooted) term quietTerm

/-- What a contraction at the root is in the theory of a table with the
family: beta, an instance of a rule of the table, or the rule of a pair of
names. -/
theorem rootStep_withNames_inv {rules : List RewriteRule} {source target : LF.Term}
    (root : RootStep (withNames rules) source target) :
    (∃ domain body argument, source = .app (.lam domain body) argument ∧
        target = subst0 argument body) ∨
      (∃ rule ∈ rules, ∃ assignment : Nat → LF.Term,
        source = inst assignment rule.lhs ∧ target = inst assignment rule.rhs) ∨
      ∃ first second : String, source = nameTest first second ∧
        target = truth constantSpelling (decide (first = second)) := by
  cases root with
  | beta domain body argument => exact .inl ⟨domain, body, argument, rfl, rfl⟩
  | delta defined => cases defined
  | @rule rule assignment member =>
      rcases member with inTable | ⟨first, second, rfl⟩
      · exact .inr (.inl ⟨rule, inTable, assignment, rfl, rfl⟩)
      · exact .inr (.inr ⟨first, second, rfl, inst_truth constantSpelling assignment _⟩)

/-! ## Tables that leave the test to the family -/

/-- **A table leaves the test of names to the family**: its rules rewrite
calls, no left side has a test of two names as an instance, and no headed
proper part of a left side has one. -/
structure LeavesNames (rules : List RewriteRule) : Prop where
  /-- Every rule rewrites a call. -/
  rooted : ∀ rule ∈ rules, rewritesCall rule = true
  /-- No rule answers a test: no left side has a test of two names as an
  instance. -/
  unanswered : ∀ rule ∈ rules, ∀ (assignment : Nat → LF.Term) (first second : String),
    inst assignment rule.lhs ≠ nameTest first second
  /-- No test is inside a left side: no headed proper part of a left side has
  a test of two names as an instance. -/
  unnested : ∀ rule ∈ rules, ∀ part ∈ subpatterns rule.lhs, algebraic true part = true →
    ∀ (assignment : Nat → LF.Term) (first second : String),
      inst assignment part ≠ nameTest first second

/-- **Positive**: the table without rule. -/
theorem leavesNames_nil : LeavesNames [] :=
  ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
    fun _ member => absurd member List.not_mem_nil⟩

/-- A rule that rewrites a call of another root than that of the test answers
no test. -/
theorem ne_nameTest_of_rootOf_ne {rule : RewriteRule} (rooted : rewritesCall rule = true)
    (other : rootOf rule ≠ ("lib", "same-name")) (assignment : Nat → LF.Term)
    (first second : String) : inst assignment rule.lhs ≠ nameTest first second := by
  intro same
  obtain ⟨kind, head, argument, shape, -⟩ := rewritesCall_shape rooted
  have root : rootOf rule = (kind, head) := by simp [rootOf, shape]
  rw [shape] at same
  simp only [nameTest, libTerm, Dedukti.inst_app, Dedukti.inst_con, LF.Term.app.injEq,
    LF.Term.con.injEq] at same
  exact other (by rw [root, same.1.1, same.1.2])

/-- **A stored table none of whose rules has the root of the test leaves the
test to the family.** -/
theorem leavesNames_of_storedTable {rules : List RewriteRule} (stored : StoredTable rules)
    (other : ∀ rule ∈ rules, rootOf rule ≠ ("lib", "same-name")) : LeavesNames rules where
  rooted := stored.rewriteCalls
  unanswered := fun rule member =>
    ne_nameTest_of_rootOf_ne (stored.rewriteCalls rule member) (other rule member)
  unnested := by
    intro rule member part partMember partAlgebraic assignment first second same
    obtain ⟨rooted, -, -, -, -, argumentQuiet⟩ := storedRuleCheck_spec (stored.each rule member)
    obtain ⟨kind, head, argument, shape, -⟩ := rewritesCall_shape rooted
    rw [shape] at partMember argumentQuiet
    simp only [callArgument] at argumentQuiet
    simp only [subpatterns, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
      at partMember
    rcases partMember with rfl | rfl | (rfl | rfl) | inArgument
    · simp [nameTest, libTerm] at same
    · exact quiet_ne_call argumentQuiet partAlgebraic assignment (kind := "lib") rfl _ _ same
    · simp [nameTest, libTerm] at same
    · simp [nameTest, libTerm] at same
    · exact quiet_ne_call (quiet_of_mem_subpatterns inArgument argumentQuiet) partAlgebraic
        assignment (kind := "lib") rfl _ _ same

/-- **Positive**: the table of unary addition leaves the test to the family. -/
theorem additionRules_leavesNames :
    LeavesNames (programRules constantSpelling additionProgram []) :=
  leavesNames_of_storedTable (storedTable_of_check storedTableCheck_examples.1) (by decide)

/-- **A table that answers the test of `a` and `b` itself**, with `True`. -/
def answeringTable : List RewriteRule := [⟨nameTest "a" "b", truth constantSpelling true⟩]

/-- **Negative**: it does not leave the test to the family. -/
theorem answeringTable_not_leavesNames : ¬ LeavesNames answeringTable := fun leaves =>
  leaves.unanswered _ (List.mem_singleton.mpr rfl) (fun _ => .con "unbound") "a" "b" rfl

/-! ## One step, to the right answer -/

/-- **The test of two names has a step to the right answer**: `True` when they
are one name, `False` when they are two. -/
theorem nameTest_step (rules : List RewriteRule) (first second : String) :
    Step (withNames rules) (nameTest first second)
      (truth constantSpelling (decide (first = second))) :=
  step_of_rule (theory := withNames rules) (rule := nameRule first second)
    (Or.inr ⟨first, second, rfl⟩) (fun _ => .con "unbound") rfl
    (inst_truth constantSpelling _ _)

/-- **And it has no other step**, over a table that leaves the test to the
family. -/
theorem nameTest_step_iff {rules : List RewriteRule} (leaves : LeavesNames rules)
    {first second : String} {target : LF.Term} :
    Step (withNames rules) (nameTest first second) target ↔
      target = truth constantSpelling (decide (first = second)) := by
  refine ⟨fun step => ?_, fun same => same ▸ nameTest_step rules first second⟩
  have applied : Step (withNames rules)
      (.app (.app (.con "lib") (.con "same-name")) (cells [.con first, .con second])) target := step
  rcases applied.app_inv with root | ⟨_, inner, -⟩ | ⟨_, inner, -⟩
  · rcases rootStep_withNames_inv root with ⟨domain, body, argument, shape, -⟩ |
      ⟨rule, member, assignment, shape, -⟩ | ⟨other, last, shape, result⟩
    · simp at shape
    · exact absurd shape.symm (leaves.unanswered rule member assignment first second)
    · obtain ⟨rfl, rfl⟩ := nameTest_injective (first := first) (second := second) shape
      exact result
  · exact absurd inner (withNames_normal_of_passive leaves.rooted rfl _)
  · exact absurd inner (withNames_normal_of_passive leaves.rooted
      (passive_cells (by simp [passive])) _)

/-- **The reducts of the test of two names are the test and its answer.** -/
theorem nameTest_reduces_iff {rules : List RewriteRule} (leaves : LeavesNames rules)
    {first second : String} {target : LF.Term} :
    Reduces (withNames rules) (nameTest first second) target ↔
      target = nameTest first second ∨
        target = truth constantSpelling (decide (first = second)) := by
  constructor
  · intro reduces
    rcases Relation.ReflTransGen.cases_head reduces with same | ⟨middle, step, rest⟩
    · exact .inl same.symm
    · rw [(nameTest_step_iff leaves).mp step] at rest
      exact .inr ((withNames_normal_of_passive leaves.rooted
        (passive_truth constantSpelling _)).reflTransGen_eq rest)
  · rintro (rfl | rfl)
    · exact .refl
    · exact .single (nameTest_step rules first second)

/-- **The answer is the only normal form that the test reaches.** -/
theorem nameTest_normalForm_unique {rules : List RewriteRule} (leaves : LeavesNames rules)
    {first second : String} {target : LF.Term}
    (reduces : Reduces (withNames rules) (nameTest first second) target)
    (normal : IsNormal (Step (withNames rules)) target) :
    target = truth constantSpelling (decide (first = second)) := by
  rcases (nameTest_reduces_iff leaves).mp reduces with rfl | same
  · exact absurd (nameTest_step rules first second) (normal _)
  · exact same

/-- **The test of two names reaches a truth value exactly when it is the right
one**: `True` when they are one name and `False` when they are two. -/
theorem nameTest_reduces_truth_iff {rules : List RewriteRule} (leaves : LeavesNames rules)
    (first second : String) (value : Bool) :
    Reduces (withNames rules) (nameTest first second) (truth constantSpelling value) ↔
      value = decide (first = second) := by
  constructor
  · intro reduces
    exact truth_injective constantSpelling_injective
      (nameTest_normalForm_unique leaves reduces
        (withNames_normal_of_passive leaves.rooted (passive_truth constantSpelling value)))
  · rintro rfl
    exact .single (nameTest_step rules first second)

/-! ## No overlap: the theory of an orthogonal table with the family -/

/-- The parts of a passive term are passive. -/
theorem passive_of_mem_subpatterns : ∀ {whole part : LF.Term}, part ∈ subpatterns whole →
    passive whole = true → passive part = true := by
  intro whole
  induction whole with
  | app function argument ihFunction ihArgument =>
      intro part member quietWhole
      obtain ⟨-, functionQuiet, argumentQuiet⟩ := passive_app.mp quietWhole
      simp only [subpatterns, List.mem_cons, List.mem_append] at member
      rcases member with rfl | rfl | inFunction | inArgument
      · exact functionQuiet
      · exact argumentQuiet
      · exact ihFunction inFunction functionQuiet
      · exact ihArgument inArgument argumentQuiet
  | var index => intro part member; simp [subpatterns] at member
  | con name => intro part member; simp [subpatterns] at member
  | srt sort => intro part member; simp [subpatterns] at member
  | pi domain body _ _ => intro part member; simp [subpatterns] at member
  | lam domain body _ _ => intro part member; simp [subpatterns] at member

/-- The proper parts of a test of two names are passive. -/
theorem passive_of_mem_subpatterns_nameTest {first second : String} {part : LF.Term}
    (member : part ∈ subpatterns (nameTest first second)) : passive part = true := by
  have function : passive (.app (.con "lib") (.con "same-name")) = true := rfl
  have argument : passive (cells [.con first, .con second]) = true :=
    passive_cells (by simp [passive])
  have listed : part ∈ LF.Term.app (.con "lib") (.con "same-name") ::
      cells [.con first, .con second] ::
        (subpatterns (.app (.con "lib") (.con "same-name")) ++
          subpatterns (cells [.con first, .con second])) := member
  simp only [List.mem_cons, List.mem_append] at listed
  rcases listed with rfl | rfl | inFunction | inArgument
  · exact function
  · exact argument
  · exact passive_of_mem_subpatterns inFunction function
  · exact passive_of_mem_subpatterns inArgument argument

/-- **No instance of a passive term is a redex at its root**, in a theory
without definition whose rules rewrite calls. -/
theorem inert_of_passive {theory : Theory} (undefined : ∀ name, theory.body name = none)
    (rooted : ∀ rule, theory.rule rule → rewritesCall rule = true) {part : LF.Term}
    (quietPart : passive part = true) : Inert theory part where
  undefined := fun name _ => undefined name
  unmatched := by
    intro rule first second member same
    obtain ⟨kind, head, argument, shape, isKind⟩ := rewritesCall_shape (rooted rule member)
    rw [inst_passive first quietPart, shape, Dedukti.inst_app, Dedukti.inst_app,
      Dedukti.inst_con] at same
    rw [same] at quietPart
    simp only [passive, opensRedex, Bool.and_eq_true, Bool.not_eq_true'] at quietPart
    rw [isKind] at quietPart
    exact absurd quietPart.1.1 (by decide)

/-- **The theory of an orthogonal table that leaves the test to the family is
orthogonal with the family.**  The rules of the family are closed, two of them
have one left side only when they are one rule, their proper parts are
passive, and the table neither answers a test nor has one inside a left side. -/
theorem withNames_orthogonal {rules : List RewriteRule}
    (orthogonal : (programTheory rules).Orthogonal) (leaves : LeavesNames rules) :
    (withNames rules).Orthogonal where
  closedBodies := fun name term defined => orthogonal.closedBodies name term defined
  leftAlgebraic := by
    rintro rule (inTable | ⟨first, second, rfl⟩)
    · exact orthogonal.leftAlgebraic rule inTable
    · rfl
  leftLinear := by
    rintro rule (inTable | ⟨first, second, rfl⟩)
    · exact orthogonal.leftLinear rule inTable
    · exact List.nodup_nil
  rightDetermined := by
    rintro rule (inTable | ⟨first, second, rfl⟩) left right agree
    · exact orthogonal.rightDetermined rule inTable left right agree
    · exact (inst_truth constantSpelling left _).trans (inst_truth constantSpelling right _).symm
  leftUndefined := fun _ _ _ _ => rfl
  rootUnique := by
    rintro first second (firstIn | ⟨name, other, rfl⟩) (secondIn | ⟨third, last, rfl⟩) left right
      same
    · exact orthogonal.rootUnique first second firstIn secondIn left right same
    · exact absurd same (leaves.unanswered first firstIn left third last)
    · exact absurd same.symm (leaves.unanswered second secondIn right name other)
    · obtain ⟨rfl, rfl⟩ := nameTest_injective (first := name) (second := other) same
      rfl
  nonOverlapping := by
    rintro rule (inTable | ⟨name, other, rfl⟩) part partMember partAlgebraic
    · refine ⟨fun _ _ => rfl, ?_⟩
      rintro candidate first second (candidateIn | ⟨third, last, rfl⟩)
      · exact (orthogonal.nonOverlapping rule inTable part partMember partAlgebraic).unmatched
          candidate first second candidateIn
      · exact leaves.unnested rule inTable part partMember partAlgebraic first third last
    · exact inert_of_passive (withNames_undefined rules) (withNames_rooted leaves.rooted)
        (passive_of_mem_subpatterns_nameTest partMember)

/-- **Reduction is confluent in the theory of an orthogonal table with the
family**, when the table leaves the test to the family. -/
theorem withNames_confluent {rules : List RewriteRule}
    (orthogonal : (programTheory rules).Orthogonal) (leaves : LeavesNames rules) :
    Confluent (Step (withNames rules)) :=
  confluent_of_orthogonal (withNames_orthogonal orthogonal leaves)

/-- **With the family alone**: the theory of the table without rule and the
family is orthogonal. -/
theorem withNames_nil_orthogonal : (withNames []).Orthogonal :=
  withNames_orthogonal
    (Dedukti.orthogonal_of_check [] (fun _ member => member) (fun _ => rfl) rfl) leavesNames_nil

/-- **Negative**: with a table that answers the test of `a` and `b` itself,
the test has two normal forms, and reduction is not confluent. -/
theorem answeringTable_not_confluent : ¬ Confluent (Step (withNames answeringTable)) := by
  have rooted : ∀ rule ∈ answeringTable, rewritesCall rule = true := by decide
  refine not_confluent_of_fork (source := nameTest "a" "b")
    (left := truth constantSpelling true) (right := truth constantSpelling false) ?_ ?_
    (withNames_normal_of_passive rooted (passive_truth constantSpelling true))
    (withNames_normal_of_passive rooted (passive_truth constantSpelling false)) (by decide)
  · exact .single (step_of_rule (theory := withNames answeringTable)
      (rule := ⟨nameTest "a" "b", truth constantSpelling true⟩)
      (Or.inl (List.mem_singleton.mpr rfl)) (fun _ => .con "unbound") rfl rfl)
  · exact .single (nameTest_step answeringTable "a" "b")

#print axioms nameTest_step
#print axioms nameTest_step_iff
#print axioms nameTest_reduces_iff
#print axioms nameTest_normalForm_unique
#print axioms nameTest_reduces_truth_iff
#print axioms leavesNames_of_storedTable
#print axioms additionRules_leavesNames
#print axioms inert_of_passive
#print axioms withNames_orthogonal
#print axioms withNames_confluent
#print axioms withNames_nil_orthogonal
#print axioms answeringTable_not_leavesNames
#print axioms answeringTable_not_confluent

end Mettapedia.Logic.HostingStyles.NameEquality
