import Mettapedia.Logic.HostingStyles.NameEquality.StoredNames
import Mettapedia.Logic.HostingStyles.StoredPrograms.Replay

/-!
# Running a table with the family of the equality of names

The family is no list, so the functions that run a list of rules do not run
it.  Two things are added.

* `contractName` is the family at the root of a term: the answer of the test
  of two names, when the term is one (`contractName_nameTest`), and nothing
  otherwise.  What it gives is a step of the theory of any table with the
  family (`contractName_sound`).
* `replayNames rules trace term` replays a trace in which a step is, at a
  position, either the rule of the table at an index or the family.  A term
  reduces to what the replay gives, in as many steps as the trace has entries
  (`replayNames_stepsIn`), in a stored table; the trace is found by any means
  and is not trusted.

`StepsIn theory count source target` is a reduction of exactly `count` steps.
From a term whose names lie in a list that holds the fixed names of the
theory, such a reduction is a reduction of as many steps of the local table of
the list (`stepsIn_local`), and so of as many transitions of the candidate
between the runs of the terms in the space of that table (`localRun_steps`).

Positive: the test of `a` and `b` replays in one step to `False`
(`replayNames_test`).  Negative: the family rewrites no term that is not a test
of two names (`contractName_call`).

## Where the steps of a trace go

The table of a program that calls the larger host is four lists, in order:
the rules of the equations of the unordered heads, the ordered rules, the
nineteen rules of the shared host and the forty-eight rules that compare data
without comparing names (`partRules`).  The number of an entry of a trace
names one of them, or the family (`partOf`), and the rule at that number is a
rule of the part named (`rule_mem_partRules`).  So the entries of a trace are
counted by part.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (Program)
open Mettapedia.GSLT.Dedukti
  (Theory RewriteRule Step Reduces inst algebraic patternVars usesOnly)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory atomsReduce atomsReduceTheory closedAtom runTermIn
    program_rewrites)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-! ## Reductions of a number of steps -/

/-- **A reduction of exactly `count` steps**, in a theory. -/
inductive StepsIn (theory : Theory) : Nat → LF.Term → LF.Term → Prop
  | zero (term : LF.Term) : StepsIn theory 0 term term
  | succ {count : Nat} {term next final : LF.Term} :
      Step theory term next → StepsIn theory count next final →
        StepsIn theory (count + 1) term final

/-- A reduction of some steps is a reduction. -/
theorem StepsIn.reduces {theory : Theory} {count : Nat} {source target : LF.Term}
    (steps : StepsIn theory count source target) : Reduces theory source target := by
  induction steps with
  | zero term => exact .refl
  | succ step _ ih => exact Relation.ReflTransGen.head step ih

/-- **Positive**: the test of `a` and `b` reduces to `False` in one step.
**Negative**: not in none. -/
theorem stepsIn_examples :
    StepsIn (withNames []) 1 (nameTest "a" "b") (truth constantSpelling false) ∧
      ¬ StepsIn (withNames []) 0 (nameTest "a" "b") (truth constantSpelling false) := by
  refine ⟨.succ (nameTest_step [] "a" "b") (.zero _), fun steps => ?_⟩
  cases steps

/-- **From a term whose names lie in the list, a reduction of some steps of
the theory with the family is a reduction of as many steps of the local
table.** -/
theorem stepsIn_local {rules : List RewriteRule} {names : List String}
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (covers : ∀ name ∈ fixedNames rules, name ∈ names) {count : Nat} {source target : LF.Term}
    (within : NamesWithin names source) (steps : StepsIn (withNames rules) count source target) :
    StepsIn (programTheory (localTable rules names)) count source target := by
  induction steps with
  | zero term => exact .zero term
  | succ step _ ih =>
      obtain ⟨moved, nextWithin⟩ := step_local bound covers within step
      exact .succ moved (ih nextWithin)

/-- A reduction of some steps of the theory of a table that a space runs is a
reduction of as many transitions of the candidate, between the runs. -/
theorem program_steps {rules : List RewriteRule} (runnable : RunnableEquations rules)
    {count : Nat} {source target : LF.Term}
    (steps : StepsIn (programTheory rules) count source target) :
    atomsReduceTheory.Steps count (runTermIn rules source) (runTermIn rules target) := by
  induction steps with
  | zero term => exact .zero _
  | succ step _ ih => exact .succ (program_rewrites runnable step) ih

/-- **A reduction of some steps of the theory with the family, from a term
whose names lie in the list, is a reduction of as many transitions of the
candidate**, between the runs of the terms in the space of the local table. -/
theorem localRun_steps {rules : List RewriteRule} (runnable : RunnableEquations rules)
    {names : List String} (covers : ∀ name ∈ fixedNames rules, name ∈ names) {count : Nat}
    {source target : LF.Term} (within : NamesWithin names source)
    (steps : StepsIn (withNames rules) count source target) :
    atomsReduceTheory.Steps count (localRun rules names source) (localRun rules names target) :=
  program_steps (localTable_runnable runnable names) (stepsIn_local runnable.2 covers within steps)

/-! ## The family at the root -/

/-- **The family at the root of a term**: the answer of the test of two names,
when the term is one. -/
def contractName (term : LF.Term) : Option LF.Term :=
  match term with
  | .app (.app (.con kind) (.con head))
      (.app (.app (.con left) (.con first)) (.app (.app (.con right) (.con second)) (.con last))) =>
      if kind = "lib" ∧ head = "same-name" ∧ left = "cons" ∧ right = "cons" ∧ last = "nil" then
        some (truth constantSpelling (decide (first = second)))
      else none
  | _ => none

/-- **Positive**: on the test of two names it gives their answer. -/
theorem contractName_nameTest (first second : String) :
    contractName (nameTest first second) =
      some (truth constantSpelling (decide (first = second))) := by
  simp [contractName, nameTest, libTerm, cells]

/-- **Negative**: it rewrites no call of a head of a program. -/
theorem contractName_call (head : String) (arguments : List LF.Term) :
    contractName (callTerm head arguments) = none := by
  unfold contractName callTerm
  split
  · next kind _ _ _ _ _ _ shape =>
    simp only [LF.Term.app.injEq, LF.Term.con.injEq] at shape
    obtain ⟨⟨rfl, -⟩, -⟩ := shape
    simp
  · rfl

/-- **What it gives is a step of the theory of a table with the family.** -/
theorem contractName_sound (rules : List RewriteRule) {term next : LF.Term}
    (contracted : contractName term = some next) : Step (withNames rules) term next := by
  unfold contractName at contracted
  split at contracted
  · next kind head left first right second last =>
    split at contracted
    · next shape =>
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := shape
      obtain rfl := Option.some.inj contracted
      exact nameTest_step rules first second
    · cases contracted
  · cases contracted

/-- **The family at a position.**  The path names the position from the root:
`false` the function of an application, `true` its argument. -/
def contractNameAt : List Bool → LF.Term → Option LF.Term
  | [], term => contractName term
  | false :: path, .app function argument =>
      (contractNameAt path function).map fun next => .app next argument
  | true :: path, .app function argument =>
      (contractNameAt path argument).map fun next => .app function next
  | _ :: _, _ => none

/-- What the family gives at a position is a step of the theory of a table
with the family. -/
theorem contractNameAt_sound (rules : List RewriteRule) (path : List Bool) :
    ∀ {term next : LF.Term}, contractNameAt path term = some next →
      Step (withNames rules) term next := by
  induction path with
  | nil =>
      intro term next contracted
      exact contractName_sound rules contracted
  | cons side path ih =>
      intro term next contracted
      cases term with
      | app function argument =>
          cases side with
          | false =>
              simp only [contractNameAt, Option.map_eq_some_iff] at contracted
              obtain ⟨inner, found, rfl⟩ := contracted
              exact (ih found).plug (.appFunction .hole argument)
          | true =>
              simp only [contractNameAt, Option.map_eq_some_iff] at contracted
              obtain ⟨inner, found, rfl⟩ := contracted
              exact (ih found).plug (.appArgument function .hole)
      | _ => cases side <;> simp [contractNameAt] at contracted

/-! ## Replaying a trace -/

/-- **The replay of a trace in a table with the family.**  An entry names a
position and a number: nought for the family, and the number after the index
of a rule of the table for that rule. -/
def replayNames (rules : List RewriteRule) : List (List Bool × Nat) → LF.Term → Option LF.Term
  | [], term => some term
  | (path, 0) :: trace, term =>
      match contractNameAt path term with
      | some next => replayNames rules trace next
      | none => none
  | (path, index + 1) :: trace, term =>
      match rules[index]? with
      | some rule =>
          match contractLinearAt rule path term with
          | some next => replayNames rules trace next
          | none => none
      | none => none

/-- **A term reduces to what a replay gives, in as many steps as the trace has
entries**, when the left side of every rule of the table is an algebraic
pattern without a repeated variable. -/
theorem replayNames_stepsIn {rules : List RewriteRule}
    (linear : ∀ rule ∈ rules, algebraic true rule.lhs = true ∧ (patternVars rule.lhs).Nodup) :
    ∀ (trace : List (List Bool × Nat)) {term result : LF.Term},
      replayNames rules trace term = some result →
        StepsIn (withNames rules) trace.length term result
  | [], _, _, replayed => by
      obtain rfl := Option.some.inj replayed
      exact .zero _
  | (path, 0) :: trace, term, result, replayed => by
      simp only [replayNames] at replayed
      split at replayed
      · next inner contracted =>
        exact .succ (contractNameAt_sound rules path contracted)
          (replayNames_stepsIn linear trace replayed)
      · cases replayed
  | (path, index + 1) :: trace, term, result, replayed => by
      simp only [replayNames] at replayed
      split at replayed
      · next rule found =>
        split at replayed
        · next inner contracted =>
          have member := List.mem_of_getElem? found
          exact .succ
            (contractLinearAt_sound (theory := withNames rules) (Or.inl member)
              (linear rule member).1 (linear rule member).2 path contracted)
            (replayNames_stepsIn linear trace replayed)
        · cases replayed
      · cases replayed

/-- **The replay of a trace whose paths are numbers.** -/
def replayNamesCoded (rules : List RewriteRule) (trace : List (Nat × Nat)) (term : LF.Term) :
    Option LF.Term :=
  replayNames rules (trace.map fun step => (decodePath step.1, step.2)) term

/-- **In a stored table with the family a term reduces to what the replay
gives, in as many steps as the trace has entries.** -/
theorem replayNamesCoded_stepsIn {rules : List RewriteRule} (stored : StoredTable rules)
    {trace : List (Nat × Nat)} {term result : LF.Term}
    (replayed : replayNamesCoded rules trace term = some result) :
    StepsIn (withNames rules) trace.length term result := by
  have steps := replayNames_stepsIn stored.linear _ replayed
  rwa [List.length_map] at steps

/-- **Positive**: the test of `a` and `b` replays in one step of the family,
at the root, to `False`.  **Negative**: the same entry on the test as a part
of a call does not replay: the family is asked at the root, where the call
is. -/
theorem replayNames_test :
    replayNamesCoded [] [(1, 0)] (nameTest "a" "b") = some (truth constantSpelling false) ∧
      replayNamesCoded [] [(1, 0)] (callTerm "f" [nameTest "a" "b"]) = none := by
  decide

/-! ## The parts of the table of a program, in a trace -/

/-- **What an entry of a trace names**: the family, or one of the four parts
of the table of a program that calls the larger host. -/
inductive TablePart where
  | family | equations | ordered | sharedHost | comparison
  deriving DecidableEq, Repr

/-- **The rules of a part of the table of a program**: the rules of the
equations of the unordered heads, the ordered rules, the rules of the shared
host, and the rules that compare data without comparing names.  The table is
these four lists, in this order; the family is no part of it. -/
def partRules (N : Spelling) (program : Program) (heads ordered : List String) :
    TablePart → List RewriteRule
  | .family => []
  | .equations =>
      ((partAt program heads).filter fun equation => !ordered.contains equation.head).map
        (ruleOf N (isCalled program largerPrimitives))
  | .ordered => orderedPartIn N program ordered
  | .sharedHost => sharedRules N
  | .comparison => structuralRules N

/-- **The part that a number names**, in a table that begins with `equations`
rules of equations and `ordered` ordered rules: nought is the family, and a
rule of the table has the number after its index. -/
def partOf (equations ordered number : Nat) : TablePart :=
  if number = 0 then .family
  else if number ≤ equations then .equations
  else if number ≤ equations + ordered then .ordered
  else if number ≤ equations + ordered + 19 then .sharedHost
  else .comparison

/-- **Positive and negative**: in a table of two rules of equations and one
ordered rule, nought names the family, three the ordered rule and not a rule
of an equation, and twenty-three a rule that compares data. -/
theorem partOf_examples :
    partOf 2 1 0 = .family ∧ partOf 2 1 3 = .ordered ∧ partOf 2 1 3 ≠ .equations ∧
      partOf 2 1 23 = .comparison := by
  decide

/-- **Positive**: the rules that compare data are a part of every table, the
same forty-eight.  **Negative**: the family is none: no rule of a table is a
rule of that part. -/
theorem partRules_examples (program : Program) (heads ordered : List String) :
    (partRules constantSpelling program heads ordered .comparison).length = 48 ∧
      partRules constantSpelling program heads ordered .family = [] :=
  ⟨structuralRules_length constantSpelling, rfl⟩

/-- **The number of a rule names its part**: in a table whose rules of
equations and whose ordered rules have the two given numbers, the rule at an
index is a rule of the part that the number after the index names. -/
theorem rule_mem_partRules {N : Spelling} {program : Program} {heads ordered : List String}
    {equations orderedRules : Nat}
    (equationsLength : (partRules N program heads ordered .equations).length = equations)
    (orderedLength : (partRules N program heads ordered .ordered).length = orderedRules)
    {index : Nat} {rule : RewriteRule}
    (found : (partTableIn N program heads ordered)[index]? = some rule) :
    rule ∈ partRules N program heads ordered (partOf equations orderedRules (index + 1)) := by
  have shape : partTableIn N program heads ordered =
      partRules N program heads ordered .equations ++
        (partRules N program heads ordered .ordered ++
          (partRules N program heads ordered .sharedHost ++
            partRules N program heads ordered .comparison)) := rfl
  have sharedLength : (partRules N program heads ordered .sharedHost).length = 19 :=
    sharedRules_length N
  rw [shape] at found
  unfold partOf
  rw [if_neg (show ¬ index + 1 = 0 by omega)]
  by_cases inEquations : index + 1 ≤ equations
  · rw [if_pos inEquations]
    rw [List.getElem?_append_left (by omega)] at found
    exact List.mem_of_getElem? found
  · rw [if_neg inEquations]
    rw [List.getElem?_append_right (by omega)] at found
    by_cases inOrdered : index + 1 ≤ equations + orderedRules
    · rw [if_pos inOrdered]
      rw [List.getElem?_append_left (by omega)] at found
      exact List.mem_of_getElem? found
    · rw [if_neg inOrdered]
      rw [List.getElem?_append_right (by omega)] at found
      by_cases inShared : index + 1 ≤ equations + orderedRules + 19
      · rw [if_pos inShared]
        rw [List.getElem?_append_left (by omega)] at found
        exact List.mem_of_getElem? found
      · rw [if_neg inShared]
        rw [List.getElem?_append_right (by omega)] at found
        exact List.mem_of_getElem? found

#print axioms stepsIn_local
#print axioms localRun_steps
#print axioms contractName_sound
#print axioms contractNameAt_sound
#print axioms replayNames_stepsIn
#print axioms replayNamesCoded_stepsIn
#print axioms replayNames_test
#print axioms rule_mem_partRules

end Mettapedia.Logic.HostingStyles.NameEquality
