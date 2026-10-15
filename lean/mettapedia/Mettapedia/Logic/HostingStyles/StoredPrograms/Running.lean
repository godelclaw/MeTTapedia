import Mettapedia.Logic.HostingStyles.StoredPrograms.Firing

/-!
# Running a table

A function that rewrites a term by the rules of a list, to check single
instances by computation.

* `contract rules term` rewrites a term at its root by the first rule of the
  list whose left side it is an instance of.  It matches the left side
  against the term (`bindVariables`) and then **compares the instance of the
  left side with the term**, so the result is an instance of the rule also
  when a variable occurs twice in the left side.
* `stepInside rules term` rewrites at the leftmost innermost position, and
  `run rules fuel term` repeats it at most `fuel` times.

Every step that the function takes is a step of the theory of the list
(`stepInside_sound`), so a term reduces to what the function returns
(`run_reduces`).  The function is no decision of normal forms: that it stops
with fuel left says only that it found no rule.

Positive: by the table of unary addition, the call of `add` on two and one
runs to three in three steps (`addition_runs`).  Negative: two steps do not
suffice (`addition_two_steps`).

## Replaying a trace

`run` looks for the next step in the whole term and among all the rules, which
costs too much on a large table.  A trace says where each step is: the path to
the position, and the index of the rule in the list.

* `contractAt rule path term` rewrites by the rule at the position of the
  path: `false` is the function of an application, `true` its argument.
* `replay rules trace term` does the steps of the trace in turn, and gives
  nothing when a step of the trace is no step.

A term reduces to what a replay gives (`replay_reduces`), whatever the trace:
the trace is found by any means and is not trusted.

Positive: the three steps of the addition, replayed (`addition_replays`).
Negative: the first rule does not rewrite the call of `add` on two and one, so
the trace that names it replays to nothing (`addition_wrong_rule`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces inst)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (step_of_rule)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
open Mettapedia.Logic.HostingStyles.AtomsReduce (programTheory)

/-- **The bindings of a match** of a pattern without binder against a term,
one for each occurrence of a variable. -/
def bindVariables : LF.Term → LF.Term → Option (List (Nat × LF.Term))
  | .var index, term => some [(index, term)]
  | .con name, .con other => if name = other then some [] else none
  | .app function argument, .app otherFunction otherArgument =>
      match bindVariables function otherFunction, bindVariables argument otherArgument with
      | some left, some right => some (left ++ right)
      | _, _ => none
  | _, _ => none

/-- The assignment of a list of bindings: the first binding of a variable. -/
def boundTo (bindings : List (Nat × LF.Term)) : Nat → LF.Term :=
  fun index =>
    match bindings.lookup index with
    | some term => term
    | none => .con "unbound"

/-- **One rule at the root**: the instance of the right side, when the term
is the instance of the left side under the bindings of the match. -/
def contractWith (rule : RewriteRule) (term : LF.Term) : Option LF.Term :=
  match bindVariables rule.lhs term with
  | some bindings =>
      if inst (boundTo bindings) rule.lhs = term then some (inst (boundTo bindings) rule.rhs)
      else none
  | none => none

/-- **The first rule of a list that rewrites the term at its root.** -/
def contract (rules : List RewriteRule) (term : LF.Term) : Option LF.Term :=
  rules.findSome? fun rule => contractWith rule term

/-- **One step at the leftmost innermost position.** -/
def stepInside (rules : List RewriteRule) : LF.Term → Option LF.Term
  | .app function argument =>
      match stepInside rules function with
      | some next => some (.app next argument)
      | none =>
          match stepInside rules argument with
          | some next => some (.app function next)
          | none => contract rules (.app function argument)
  | .con name => contract rules (.con name)
  | _ => none

/-- **At most `fuel` steps.** -/
def run (rules : List RewriteRule) : Nat → LF.Term → LF.Term
  | 0, term => term
  | fuel + 1, term =>
      match stepInside rules term with
      | some next => run rules fuel next
      | none => term

theorem contractWith_sound {theory : Theory} {rule : RewriteRule} (member : theory.rule rule)
    {term next : LF.Term} (contracted : contractWith rule term = some next) :
    Step theory term next := by
  unfold contractWith at contracted
  split at contracted
  · next bindings _ =>
    split at contracted
    · next isInstance =>
      exact step_of_rule member (boundTo bindings) isInstance (Option.some.inj contracted)
    · cases contracted
  · cases contracted

theorem contract_sound {rules : List RewriteRule} {term next : LF.Term}
    (contracted : contract rules term = some next) : Step (programTheory rules) term next := by
  obtain ⟨rule, member, found⟩ := List.exists_of_findSome?_eq_some contracted
  exact contractWith_sound (theory := programTheory rules) member found

/-- **Every step of the function is a step of the theory of the list.** -/
theorem stepInside_sound (rules : List RewriteRule) :
    ∀ {term next : LF.Term}, stepInside rules term = some next →
      Step (programTheory rules) term next := by
  intro term
  induction term with
  | app function argument ihFunction ihArgument =>
      intro next stepped
      simp only [stepInside] at stepped
      split at stepped
      · next inner found =>
        obtain rfl := Option.some.inj stepped
        exact (ihFunction found).plug (.appFunction .hole argument)
      · split at stepped
        · next inner found =>
          obtain rfl := Option.some.inj stepped
          exact (ihArgument found).plug (.appArgument function .hole)
        · exact contract_sound stepped
  | con name =>
      intro next stepped
      exact contract_sound stepped
  | var index => intro next stepped; cases stepped
  | srt sort => intro next stepped; cases stepped
  | pi domain body _ _ => intro next stepped; cases stepped
  | lam domain body _ _ => intro next stepped; cases stepped

/-- **A term reduces to what the function returns.** -/
theorem run_reduces (rules : List RewriteRule) :
    ∀ (fuel : Nat) (term : LF.Term), Reduces (programTheory rules) term (run rules fuel term)
  | 0, _ => .refl
  | fuel + 1, term => by
      simp only [run]
      split
      · next inner found =>
        exact Relation.ReflTransGen.head (stepInside_sound rules found) (run_reduces rules fuel inner)
      · exact .refl

/-- A term reduces to a given term when the function returns it. -/
theorem reduces_of_run {rules : List RewriteRule} {fuel : Nat} {term result : LF.Term}
    (computed : run rules fuel term = result) : Reduces (programTheory rules) term result :=
  computed ▸ run_reduces rules fuel term

/-! ## Replaying a trace -/

/-- **A rule at a position.**  The path names the position from the root:
`false` the function of an application, `true` its argument. -/
def contractAt (rule : RewriteRule) : List Bool → LF.Term → Option LF.Term
  | [], term => contractWith rule term
  | false :: path, .app function argument =>
      (contractAt rule path function).map fun next => .app next argument
  | true :: path, .app function argument =>
      (contractAt rule path argument).map fun next => .app function next
  | _ :: _, _ => none

/-- **The replay of a trace**: each entry names a position and the index of a
rule in the list. -/
def replay (rules : List RewriteRule) : List (List Bool × Nat) → LF.Term → Option LF.Term
  | [], term => some term
  | (path, index) :: trace, term =>
      match rules[index]? with
      | some rule =>
          match contractAt rule path term with
          | some next => replay rules trace next
          | none => none
      | none => none

theorem contractAt_sound {theory : Theory} {rule : RewriteRule} (member : theory.rule rule)
    (path : List Bool) : ∀ {term next : LF.Term}, contractAt rule path term = some next →
      Step theory term next := by
  induction path with
  | nil =>
      intro term next contracted
      exact contractWith_sound member contracted
  | cons side path ih =>
      intro term next contracted
      cases term with
      | app function argument =>
          cases side with
          | false =>
              simp only [contractAt, Option.map_eq_some_iff] at contracted
              obtain ⟨inner, found, rfl⟩ := contracted
              exact (ih found).plug (.appFunction .hole argument)
          | true =>
              simp only [contractAt, Option.map_eq_some_iff] at contracted
              obtain ⟨inner, found, rfl⟩ := contracted
              exact (ih found).plug (.appArgument function .hole)
      | _ => cases side <;> simp [contractAt] at contracted

/-- **A term reduces to what a replay gives**, whatever the trace. -/
theorem replay_reduces {rules : List RewriteRule} :
    ∀ (trace : List (List Bool × Nat)) {term result : LF.Term},
      replay rules trace term = some result → Reduces (programTheory rules) term result
  | [], _, _, replayed => by
      obtain rfl := Option.some.inj replayed
      exact .refl
  | (path, index) :: trace, term, result, replayed => by
      simp only [replay] at replayed
      split at replayed
      · next rule found =>
        split at replayed
        · next inner contracted =>
          exact Relation.ReflTransGen.head
            (contractAt_sound (theory := programTheory rules) (List.mem_of_getElem? found) path
              contracted)
            (replay_reduces trace replayed)
        · cases replayed
      · cases replayed

/-- **Positive**: by the table of unary addition, the call of `add` on two
and one runs to three, in three steps. -/
theorem addition_runs :
    run (programRules constantSpelling additionProgram []) 3
        (callTerm "add" (data constantSpelling
          [.expr [.sym "S", .expr [.sym "S", .sym "Z"]], .expr [.sym "S", .sym "Z"]])) =
      datum constantSpelling (.expr [.sym "S", .expr [.sym "S", .expr [.sym "S", .sym "Z"]]]) := by
  decide +kernel

/-- **Negative**: two steps do not suffice. -/
theorem addition_two_steps :
    run (programRules constantSpelling additionProgram []) 2
        (callTerm "add" (data constantSpelling
          [.expr [.sym "S", .expr [.sym "S", .sym "Z"]], .expr [.sym "S", .sym "Z"]])) ≠
      datum constantSpelling (.expr [.sym "S", .expr [.sym "S", .expr [.sym "S", .sym "Z"]]]) := by
  decide +kernel

/-- **Positive**: the three steps, replayed: the second rule at the root, the
second rule at the call under the first `S`, the first rule at the call under
the second. -/
theorem addition_replays :
    replay (programRules constantSpelling additionProgram [])
        [([], 1), ([true, true, false, true], 1),
          ([true, true, false, true, true, true, false, true], 0)]
        (callTerm "add" (data constantSpelling
          [.expr [.sym "S", .expr [.sym "S", .sym "Z"]], .expr [.sym "S", .sym "Z"]])) =
      some (datum constantSpelling
        (.expr [.sym "S", .expr [.sym "S", .expr [.sym "S", .sym "Z"]]])) := by
  decide +kernel

/-- **Negative**: the first rule does not rewrite that call. -/
theorem addition_wrong_rule :
    replay (programRules constantSpelling additionProgram []) [([], 0)]
        (callTerm "add" (data constantSpelling
          [.expr [.sym "S", .expr [.sym "S", .sym "Z"]], .expr [.sym "S", .sym "Z"]])) =
      none := by
  decide +kernel

#print axioms contractWith_sound
#print axioms stepInside_sound
#print axioms run_reduces
#print axioms addition_runs
#print axioms addition_two_steps
#print axioms contractAt_sound
#print axioms replay_reduces
#print axioms addition_replays
#print axioms addition_wrong_rule

end Mettapedia.Logic.HostingStyles.StoredPrograms
