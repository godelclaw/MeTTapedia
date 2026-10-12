import Mettapedia.Logic.HostingStyles.NameEquality.Renaming

/-!
# "Same" by a repeated variable, "different" by a family

A second way to have the test.  A rule whose left side repeats a variable
compares the two terms that the variable stands for: `sameRule` rewrites the
helper `same-name` on one term twice to `True`.  It is one rule, and it needs
no family.  What it cannot say is `False`: that is left to a family, one rule
for each pair of two names (`differRule`).  The theory of a table with both is
`withDifference`.

## What it gives

* **"Same" in one step, for every term**, not only for names (`same_step`):
  the comparison of two terms that are one term is one step, whatever their
  size.
* On two names it answers as the family of the equality of names does
  (`nameTest_step_withDifference`), and every step of the theory with that
  family is a step of this theory (`step_withDifference_of_withNames`).
* **The one rule alone is a finite table that answers equality**
  (`sameTable_reduces_iff`): of the three relations that the theory of a
  finite table can answer, equality is one.  Difference is the one that needs
  the family.  The candidate runs that table: the run of the test of a name
  with itself has a transition to the run of `True`, and the run of the test
  of two names has none (`candidate_same_step`, `candidate_different_stuck`).

## What it costs

* **The theory is not orthogonal**, over any table: the left side of
  `sameRule` is not linear (`withDifference_not_orthogonal`).
* **Confluence is lost**, over a table that is orthogonal and leaves the
  test to the family (`repeatedVariable_loses_confluence`).  The table
  `loopTable` has two rules, `(c x) ⟶ (same x (c x))` and `(a) ⟶ (c (a))`.
  Over it the theory with the family of the equality of names is confluent.
  With the repeated variable `(c (a))` reduces to `True`, since
  `(same (c (a)) (c (a)))` is a step away, and to `(c True)`, which never
  reaches `True`: its reducts are `(c True)`, `(same True (c True))`,
  `(same True (same True (c True)))`, and so on (`Tower`).

The reason is that a repeated variable compares terms that still reduce.  The
family compares names, which do not.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFTyping (subst0)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule RootStep Step Reduces inst patternVars)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (step_of_rule)
open Mettapedia.Logic.Relation (IsNormal Confluent)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory rootStep_program_inv atomsReduce atomsReduceTheory closedAtom
    runTermIn program_rewrites program_normal)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-! ## Steps of cells, in a theory whose rules rewrite calls -/

section Rooted

variable {theory : Theory} (undefined : ∀ name, theory.body name = none)
  (rooted : ∀ rule, theory.rule rule → rewritesCall rule = true)

include undefined rooted

/-- A term that is contracted at its root is a beta redex or a call. -/
theorem rootStep_shape {source target : LF.Term} (root : RootStep theory source target) :
    (∃ domain body argument, source = .app (.lam domain body) argument) ∨
      ∃ kind head argument, source = .app (.app (.con kind) (.con head)) argument ∧
        redexKinds.contains kind = true := by
  cases root with
  | beta domain body argument => exact .inl ⟨domain, body, argument, rfl⟩
  | @delta name _ defined =>
      rw [undefined name] at defined
      cases defined
  | @rule rule assignment member =>
      obtain ⟨kind, head, argument, shape, isKind⟩ := rewritesCall_shape (rooted rule member)
      exact .inr ⟨kind, head, inst assignment argument, by rw [shape]; rfl, isKind⟩

/-- **A step of the cells of a list is a step of its first term or of the
cells of the rest.** -/
theorem step_cells_cons_inv {first : LF.Term} {rest : List LF.Term} {target : LF.Term}
    (step : Step theory (cells (first :: rest)) target) :
    (∃ next, Step theory first next ∧ target = cells (next :: rest)) ∨
      ∃ next, Step theory (cells rest) next ∧ target = .app (.app (.con "cons") first) next := by
  have applied : Step theory (.app (.app (.con "cons") first) (cells rest)) target := step
  rcases applied.app_inv with root | ⟨function, inner, rfl⟩ | ⟨argument, inner, rfl⟩
  · rcases rootStep_shape undefined rooted root with ⟨_, _, _, shape⟩ | ⟨kind, _, _, shape, isKind⟩
    · simp at shape
    · simp only [LF.Term.app.injEq, LF.Term.con.injEq] at shape
      obtain ⟨⟨rfl, -⟩, -⟩ := shape
      exact absurd isKind (by decide)
  · rcases inner.app_inv with root | ⟨_, deeper, -⟩ | ⟨next, deeper, rfl⟩
    · rcases rootStep_shape undefined rooted root with ⟨_, _, _, shape⟩ | ⟨_, _, _, shape, -⟩
      · simp at shape
      · simp at shape
    · exact absurd deeper (passive_normal undefined rooted _ rfl _)
    · exact .inl ⟨next, deeper, rfl⟩
  · exact .inr ⟨argument, inner, rfl⟩

/-- **A step of the call of a helper is at its root or in its cells.** -/
theorem step_libTerm_inv {head : String} {arguments : List LF.Term} {target : LF.Term}
    (step : Step theory (libTerm head arguments) target) :
    RootStep theory (libTerm head arguments) target ∨
      ∃ next, Step theory (cells arguments) next ∧
        target = .app (.app (.con "lib") (.con head)) next := by
  have applied : Step theory (.app (.app (.con "lib") (.con head)) (cells arguments)) target := step
  rcases applied.app_inv with root | ⟨_, inner, -⟩ | ⟨next, inner, rfl⟩
  · exact .inl root
  · exact absurd inner (passive_normal undefined rooted _ rfl _)
  · exact .inr ⟨next, inner, rfl⟩

end Rooted

/-! ## The rule with a repeated variable, and the family for two names -/

/-- **The rule of "same" with a repeated variable**: the helper `same-name` on
one term twice rewrites to `True`. -/
def sameRule : RewriteRule :=
  ⟨libTerm "same-name" [.var 0, .var 0], truth constantSpelling true⟩

/-- **The rule of two different names**: their test rewrites to `False`. -/
def differRule (first second : String) : RewriteRule :=
  ⟨nameTest first second, truth constantSpelling false⟩

/-- **The theory of a table with a repeated variable for "same" and a family
for "different"**: the rule `sameRule`, and the rule of each pair of two
names. -/
def withDifference (rules : List RewriteRule) : Theory :=
  { programTheory rules with
    rule := fun rule => rule ∈ rules ∨ rule = sameRule ∨
      ∃ first second : String, first ≠ second ∧ rule = differRule first second }

/-- The left side of `sameRule` under an assignment. -/
theorem inst_sameRule_lhs (assignment : Nat → LF.Term) :
    inst assignment sameRule.lhs = libTerm "same-name" [assignment 0, assignment 0] := by
  simp [sameRule, inst_libTerm]

/-- **"Same" in one step, for every term**: the helper on one term twice
steps to `True`. -/
theorem same_step (rules : List RewriteRule) (term : LF.Term) :
    Step (withDifference rules) (libTerm "same-name" [term, term])
      (truth constantSpelling true) :=
  step_of_rule (theory := withDifference rules) (rule := sameRule) (Or.inr (Or.inl rfl))
    (fun _ => term) (inst_sameRule_lhs _) (inst_truth constantSpelling _ _)

/-- **Positive and negative**: the family for "different" holds the rule of
`a` and `b`, and no rule of `a` with itself. -/
theorem differRule_examples :
    (withDifference []).rule (differRule "a" "b") ∧
      ¬ (withDifference []).rule (differRule "a" "a") := by
  refine ⟨Or.inr (Or.inr ⟨"a", "b", by decide, rfl⟩), ?_⟩
  rintro (inTable | isSame | ⟨first, second, different, same⟩)
  · cases inTable
  · revert isSame
    decide
  · obtain ⟨rfl, rfl⟩ := nameTest_injective (RewriteRule.mk.inj same).1
    exact different rfl

/-- The test of two names is contracted to its answer. -/
theorem rootStep_nameTest_withDifference (rules : List RewriteRule) (first second : String) :
    RootStep (withDifference rules) (nameTest first second)
      (truth constantSpelling (decide (first = second))) := by
  by_cases same : first = second
  · subst same
    have fired := RootStep.rule (theory := withDifference rules) (rule := sameRule)
      (fun _ => .con first) (Or.inr (Or.inl rfl))
    rw [inst_sameRule_lhs, show inst (fun _ => LF.Term.con first) sameRule.rhs =
      truth constantSpelling true from inst_truth constantSpelling _ true] at fired
    rw [decide_eq_true rfl]
    exact fired
  · have fired := RootStep.rule (theory := withDifference rules) (rule := differRule first second)
      (fun _ => .con "unbound") (Or.inr (Or.inr ⟨first, second, same, rfl⟩))
    simpa [differRule, inst_nameTest, inst_truth, same] using fired

/-- **On two names it answers as the family of the equality of names does.** -/
theorem nameTest_step_withDifference (rules : List RewriteRule) (first second : String) :
    Step (withDifference rules) (nameTest first second)
      (truth constantSpelling (decide (first = second))) :=
  Step.root (rootStep_nameTest_withDifference rules first second)

/-- **Every step of the theory with the family of the equality of names is a
step of the theory with the repeated variable.** -/
theorem step_withDifference_of_withNames {rules : List RewriteRule} {source target : LF.Term}
    (step : Step (withNames rules) source target) : Step (withDifference rules) source target := by
  cases step with
  | inContext context root =>
      refine Step.inContext context ?_
      cases root with
      | beta domain body argument => exact .beta domain body argument
      | delta defined => cases defined
      | @rule rule assignment member =>
          rcases member with inTable | ⟨first, second, rfl⟩
          · exact .rule assignment (Or.inl inTable)
          · have contracted := rootStep_nameTest_withDifference rules first second
            rwa [← inst_truth constantSpelling assignment (decide (first = second))] at contracted

/-- **The theory with the repeated variable is not orthogonal**, over any
table: the left side of `sameRule` repeats a variable. -/
theorem withDifference_not_orthogonal (rules : List RewriteRule) :
    ¬ (withDifference rules).Orthogonal := fun orthogonal =>
  absurd (orthogonal.leftLinear sameRule (Or.inr (Or.inl rfl))) (by decide)

/-! ## The one rule alone answers equality -/

/-- The one rule steps the test of a name with itself to `True`. -/
theorem sameTable_step (name : String) :
    Step (programTheory [sameRule]) (nameTest name name) (truth constantSpelling true) :=
  step_of_rule (theory := programTheory [sameRule]) (rule := sameRule)
    (List.mem_singleton.mpr rfl) (fun _ => .con name) (inst_sameRule_lhs _)
    (inst_truth constantSpelling _ _)

/-- **The one rule has no step on the test of two names.** -/
theorem sameTable_normal {first second : String} (different : first ≠ second) :
    IsNormal (Step (programTheory [sameRule])) (nameTest first second) := by
  have rooted : ∀ rule, (programTheory [sameRule]).rule rule → rewritesCall rule = true := by
    intro rule member
    obtain rfl := List.mem_singleton.mp member
    rfl
  intro target step
  rcases step_libTerm_inv (fun _ => rfl) rooted step with root | ⟨_, inner, -⟩
  · rcases rootStep_program_inv root with ⟨domain, body, argument, shape, -⟩ |
      ⟨rule, member, assignment, shape, -⟩
    · simp [libTerm] at shape
    · obtain rfl := List.mem_singleton.mp member
      rw [inst_sameRule_lhs] at shape
      simp only [libTerm, cells, LF.Term.app.injEq, true_and, and_true] at shape
      exact different (LF.Term.con.inj (shape.1.trans shape.2.symm))
  · exact passive_normal (fun _ => rfl) rooted _ (passive_cells (by simp [passive])) _ inner

/-- **The table of the one rule answers `True` exactly for a name with
itself**: a finite table has "same". -/
theorem sameTable_reduces_iff (first second : String) :
    Reduces (programTheory [sameRule]) (nameTest first second) (truth constantSpelling true) ↔
      first = second := by
  constructor
  · intro reduces
    by_contra different
    have stuck := (sameTable_normal different).reflTransGen_eq reduces
    simp [nameTest, truth, tag, libTerm, constantSpelling] at stuck
  · rintro rfl
    exact .single (sameTable_step first)

/-! ## The candidate has "same" in one step, and no "different" -/

/-- The one rule is a rule that a space of the candidate runs: a space does
not ask that a variable occur once in a left side. -/
theorem sameRule_runnable : RunnableEquations [sameRule] := by
  constructor <;> decide

/-- **The candidate has "same" in one step**: in the space that stores the
one rule, the run of the test of a name with itself has a transition to the
run of `True`. -/
theorem candidate_same_step (name : String) :
    atomsReduceTheory.rewrites (runTermIn [sameRule] (nameTest name name))
      (runTermIn [sameRule] (truth constantSpelling true)) :=
  program_rewrites sameRule_runnable (sameTable_step name)

/-- **And it has no "different"**: in that space the run of the test of two
names has no transition. -/
theorem candidate_different_stuck {first second : String} (different : first ≠ second)
    (target : Contexts.Term atomsReduce closedAtom) :
    ¬ atomsReduceTheory.rewrites (runTermIn [sameRule] (nameTest first second)) target :=
  program_normal sameRule_runnable (sameTable_normal different) target

/-! ## Confluence is lost -/

/-- **A table of two rules**: `(c x) ⟶ (same x (c x))` and `(a) ⟶ (c (a))`. -/
def loopTable : List RewriteRule :=
  [⟨callTerm "c" [.var 0], libTerm "same-name" [.var 0, callTerm "c" [.var 0]]⟩,
    ⟨callTerm "a" [], callTerm "c" [callTerm "a" []]⟩]

/-- It is a stored table, hence orthogonal. -/
theorem loopTable_stored : StoredTable loopTable := storedTable_of_check (by decide)

/-- It leaves the test to the family. -/
theorem loopTable_leavesNames : LeavesNames loopTable :=
  leavesNames_of_storedTable loopTable_stored (by decide)

/-- The rules of the theory with the repeated variable rewrite calls, when
those of the table do. -/
theorem withDifference_rooted {rules : List RewriteRule}
    (rooted : ∀ rule ∈ rules, rewritesCall rule = true) :
    ∀ rule, (withDifference rules).rule rule → rewritesCall rule = true := by
  rintro rule (inTable | rfl | ⟨first, second, -, rfl⟩)
  · exact rooted rule inTable
  · rfl
  · rfl

/-- What a contraction at the root is in the theory with the repeated
variable. -/
theorem rootStep_withDifference_inv {rules : List RewriteRule} {source target : LF.Term}
    (root : RootStep (withDifference rules) source target) :
    (∃ domain body argument, source = .app (.lam domain body) argument ∧
        target = subst0 argument body) ∨
      (∃ rule ∈ rules, ∃ assignment : Nat → LF.Term,
        source = inst assignment rule.lhs ∧ target = inst assignment rule.rhs) ∨
      (∃ term, source = libTerm "same-name" [term, term] ∧
        target = truth constantSpelling true) ∨
      ∃ first second : String, first ≠ second ∧ source = nameTest first second ∧
        target = truth constantSpelling false := by
  cases root with
  | beta domain body argument => exact .inl ⟨domain, body, argument, rfl, rfl⟩
  | delta defined => cases defined
  | @rule rule assignment member =>
      rcases member with inTable | rfl | ⟨first, second, different, rfl⟩
      · exact .inr (.inl ⟨rule, inTable, assignment, rfl, rfl⟩)
      · exact .inr (.inr (.inl ⟨assignment 0, inst_sameRule_lhs assignment,
          inst_truth constantSpelling assignment true⟩))
      · exact .inr (.inr (.inr ⟨first, second, different, rfl,
          inst_truth constantSpelling assignment false⟩))

/-- The term `(a)`. -/
def loopStart : LF.Term := callTerm "a" []

/-- The term `(c t)`. -/
def loopCall (term : LF.Term) : LF.Term := callTerm "c" [term]

/-- **The reducts of `(c True)`**: `(c True)`, and `(same True t)` for a
reduct `t`. -/
inductive Tower : LF.Term → Prop
  | base : Tower (loopCall (truth constantSpelling true))
  | above {term : LF.Term} :
      Tower term → Tower (libTerm "same-name" [truth constantSpelling true, term])

/-- **Negative**: `True` is not among them. -/
theorem Tower.ne_truth {term : LF.Term} (tower : Tower term) :
    term ≠ truth constantSpelling true := by
  cases tower <;> simp [loopCall, callTerm, libTerm, truth, tag]

/-- **Positive**: `(same True (c True))` is among them. -/
theorem tower_example :
    Tower (libTerm "same-name"
      [truth constantSpelling true, loopCall (truth constantSpelling true)]) :=
  .above .base

/-- A step from one of them goes to one of them. -/
theorem Tower.step {source : LF.Term} (tower : Tower source) :
    ∀ {target : LF.Term}, Step (withDifference loopTable) source target → Tower target := by
  have rooted := withDifference_rooted (rules := loopTable) (by decide)
  have undefined : ∀ name, (withDifference loopTable).body name = none := fun _ => rfl
  have truthNormal : IsNormal (Step (withDifference loopTable)) (truth constantSpelling true) :=
    passive_normal undefined rooted _ (passive_truth constantSpelling true)
  induction tower with
  | base =>
      intro target step
      have applied : Step (withDifference loopTable)
          (.app (.app (.con "call") (.con "c")) (cells [truth constantSpelling true])) target :=
        step
      rcases applied.app_inv with root | ⟨_, inner, -⟩ | ⟨_, inner, -⟩
      · rcases rootStep_withDifference_inv root with ⟨_, _, _, shape, -⟩ |
          ⟨rule, member, assignment, shape, rfl⟩ | ⟨_, shape, -⟩ | ⟨_, _, -, shape, -⟩
        · simp at shape
        · simp only [loopTable, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · dsimp only at shape ⊢
            rw [inst_callTerm] at shape
            simp only [List.map_cons, List.map_nil, Dedukti.inst_var, callTerm, cells,
              LF.Term.app.injEq, true_and, and_true] at shape
            rw [inst_libTerm]
            simp only [List.map_cons, List.map_nil, Dedukti.inst_var, inst_callTerm, ← shape]
            exact .above .base
          · simp [callTerm, cells] at shape
        · simp [libTerm] at shape
        · simp [nameTest, libTerm] at shape
      · exact absurd inner (passive_normal undefined rooted _ rfl _)
      · exact absurd inner (passive_normal undefined rooted _
          (passive_cells (by simp [passive_truth])) _)
  | @above term inner ih =>
      intro target step
      rcases step_libTerm_inv undefined rooted step with root | ⟨next, inCells, rfl⟩
      · rcases rootStep_withDifference_inv root with ⟨_, _, _, shape, -⟩ |
          ⟨rule, member, assignment, shape, -⟩ | ⟨other, shape, -⟩ | ⟨_, _, -, shape, -⟩
        · simp [libTerm] at shape
        · simp only [loopTable, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> simp [callTerm, libTerm] at shape
        · simp only [libTerm, cells, LF.Term.app.injEq, true_and, and_true] at shape
          exact absurd (shape.2.trans shape.1.symm) inner.ne_truth
        · simp [nameTest, libTerm, cells, truth, tag] at shape
      · rcases step_cells_cons_inv undefined rooted inCells with ⟨_, moved, -⟩ |
          ⟨rest, inRest, rfl⟩
        · exact absurd moved (truthNormal _)
        · rcases step_cells_cons_inv undefined rooted inRest with ⟨reduct, moved, rfl⟩ |
            ⟨_, inNil, -⟩
          · exact .above (ih moved)
          · exact absurd inNil (passive_normal undefined rooted _ rfl _)

/-- Every reduct of one of them is one of them. -/
theorem Tower.reduces {source target : LF.Term} (tower : Tower source)
    (reduces : Reduces (withDifference loopTable) source target) : Tower target := by
  induction reduces with
  | refl => exact tower
  | tail _ step ih => exact ih.step step

/-- `(c (a))` reduces to `True`: by the first rule to `(same (a) (c (a)))`,
by the second rule in the first argument to `(same (c (a)) (c (a)))`, and by
the repeated variable to `True`. -/
theorem loopCall_reduces_truth :
    Reduces (withDifference loopTable) (loopCall loopStart) (truth constantSpelling true) := by
  have unfolds : Step (withDifference loopTable) (loopCall loopStart)
      (libTerm "same-name" [loopStart, loopCall loopStart]) :=
    step_of_rule (theory := withDifference loopTable)
      (rule := ⟨callTerm "c" [.var 0], libTerm "same-name" [.var 0, callTerm "c" [.var 0]]⟩)
      (Or.inl (by decide)) (fun _ => loopStart) (by simp [inst_callTerm, loopCall])
      (by simp [inst_libTerm, inst_callTerm, loopCall])
  have grows : Step (withDifference loopTable) loopStart (loopCall loopStart) :=
    step_of_rule (theory := withDifference loopTable)
      (rule := ⟨callTerm "a" [], callTerm "c" [callTerm "a" []]⟩)
      (Or.inl (by decide)) (fun _ => .con "unbound") rfl rfl
  exact ((Relation.ReflTransGen.single unfolds).trans
    (reduces_libTerm "same-name" (.cons (.single grows) (.cons .refl .nil)))).tail
    (same_step loopTable (loopCall loopStart))

/-- `(c (a))` also reduces to `(c True)`: the second rule in the argument,
and then the reduction of that argument to `True`. -/
theorem loopCall_reduces_call :
    Reduces (withDifference loopTable) (loopCall loopStart)
      (loopCall (truth constantSpelling true)) := by
  have grows : Step (withDifference loopTable) loopStart (loopCall loopStart) :=
    step_of_rule (theory := withDifference loopTable)
      (rule := ⟨callTerm "a" [], callTerm "c" [callTerm "a" []]⟩)
      (Or.inl (by decide)) (fun _ => .con "unbound") rfl rfl
  exact (reduces_callTerm "c" (.cons (.single grows) .nil)).trans
    (reduces_callTerm "c" (.cons loopCall_reduces_truth .nil))

/-- **With the repeated variable, reduction over the table is not
confluent**: `(c (a))` reduces to `True` and to `(c True)`, and these have no
common reduct. -/
theorem withDifference_loopTable_not_confluent :
    ¬ Confluent (Step (withDifference loopTable)) := by
  intro confluent
  obtain ⟨common, fromTruth, fromCall⟩ := confluent (loopCall loopStart)
    (truth constantSpelling true) (loopCall (truth constantSpelling true))
    loopCall_reduces_truth loopCall_reduces_call
  have rooted := withDifference_rooted (rules := loopTable) (by decide)
  have isTruth := (passive_normal (theory := withDifference loopTable) (fun _ => rfl) rooted _
    (passive_truth constantSpelling true)).reflTransGen_eq fromTruth
  exact (Tower.base.reduces fromCall).ne_truth isTruth

/-- **What confluence becomes.**  Over one orthogonal table that leaves the
test to the family: with the family of the equality of names reduction is
confluent; with a repeated variable for "same" it is not. -/
theorem repeatedVariable_loses_confluence :
    (programTheory loopTable).Orthogonal ∧ LeavesNames loopTable ∧
      Confluent (Step (withNames loopTable)) ∧ ¬ Confluent (Step (withDifference loopTable)) :=
  ⟨loopTable_stored.orthogonal, loopTable_leavesNames,
    withNames_confluent loopTable_stored.orthogonal loopTable_leavesNames,
    withDifference_loopTable_not_confluent⟩

#print axioms step_cells_cons_inv
#print axioms same_step
#print axioms nameTest_step_withDifference
#print axioms step_withDifference_of_withNames
#print axioms withDifference_not_orthogonal
#print axioms sameTable_reduces_iff
#print axioms candidate_same_step
#print axioms candidate_different_stuck
#print axioms Tower.step
#print axioms loopCall_reduces_truth
#print axioms loopCall_reduces_call
#print axioms withDifference_loopTable_not_confluent
#print axioms repeatedVariable_loses_confluence

end Mettapedia.Logic.HostingStyles.NameEquality
