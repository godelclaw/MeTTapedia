import Mettapedia.Logic.HostingStyles.NameEquality.Family
import Mettapedia.Logic.HostingStyles.StoredPrograms.Running

/-!
# The order of equations is no test

Two rules for one head, the first with a repeated variable (`orderedPair`):

    (eq2 x x) ⟶ True
    (eq2 x y) ⟶ False

If the first rule that rewrites a call were the only one to fire, the two
would be the test of two names: on two names the first match answers `True`
when they are one name and `False` when they are two
(`firstMatch_tests_names`).  `contract` is that first match: it takes the
first rule of the list whose left side has the term as an instance, and it
compares the two terms of a repeated variable.

## Why the theory does not have it

**The first match is not stable under substitution**
(`firstMatch_not_stable`).  On the open term `(eq2 u v)` the first rule does
not match, since `u` and `v` are two variables, and the first match answers
`False`.  Put the name `a` for both variables: on `(eq2 a a)` the first match
answers `True`.  So a step taken by the first match on a term with variables
is no step of its instances.

A step of a theory of rules is stable under substitution (`Dedukti.Step.subst`).
Hence the step of `(eq2 u v)` to `False`, which the second rule takes, is a
step of `(eq2 a a)` to `False` as well: **on a name with itself both rules
answer** (`orderedPair_both_answers`), `True` and `False` are two normal forms
of one term, and reduction by the two rules is not confluent
(`orderedPair_not_confluent`).  The order in which the rules are written
decides nothing.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFTyping (subst)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule RootStep Step Reduces inst)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (step_of_rule not_confluent_of_fork)
open Mettapedia.Logic.Relation (IsNormal Confluent)
open Mettapedia.Logic.HostingStyles.AtomsReduce (programTheory)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-- **Two rules for one head, the first with a repeated variable**:
`(eq2 x x) ⟶ True` and `(eq2 x y) ⟶ False`. -/
def orderedPair : List RewriteRule :=
  [⟨callTerm "eq2" [.var 0, .var 0], truth constantSpelling true⟩,
    ⟨callTerm "eq2" [.var 0, .var 1], truth constantSpelling false⟩]

/-- The call of `eq2` on two terms. -/
def pairCall (first second : LF.Term) : LF.Term := callTerm "eq2" [first, second]

/-- **Taken in order, the two rules would be the test of two names**: the
first rule that rewrites the call of `eq2` on two names answers `True` when
they are one name, and `False` when they are two. -/
theorem firstMatch_tests_names (first second : String) :
    contract orderedPair (pairCall (.con first) (.con second)) =
      some (truth constantSpelling (decide (first = second))) := by
  by_cases same : first = second
  · subst same
    simp [contract, contractWith, bindVariables, boundTo, orderedPair, pairCall, callTerm, cells,
      inst_truth]
  · simp [contract, contractWith, bindVariables, boundTo, orderedPair, pairCall, callTerm, cells,
      inst_truth, same, List.lookup]

/-- On the open term `(eq2 u v)` the first match answers `False`: the first
rule does not match two variables. -/
theorem firstMatch_open :
    contract orderedPair (pairCall (.var 0) (.var 1)) = some (truth constantSpelling false) := by
  decide

/-- **The first match is not stable under substitution.**  On the open term
`(eq2 u v)` it answers `False`, and `False` with `a` put for the two variables
is `False`.  On the term with `a` put for the two variables it answers
`True`. -/
theorem firstMatch_not_stable :
    (contract orderedPair (pairCall (.var 0) (.var 1))).map
        (fun reduct => subst 0 (.con "a") (subst 0 (.con "a") reduct)) =
      some (truth constantSpelling false) ∧
    contract orderedPair (subst 0 (.con "a") (subst 0 (.con "a") (pairCall (.var 0) (.var 1)))) =
      some (truth constantSpelling true) := by
  decide

/-- The second rule rewrites the open term `(eq2 u v)` to `False`. -/
theorem orderedPair_open_step :
    Step (programTheory orderedPair) (pairCall (.var 0) (.var 1)) (truth constantSpelling false) :=
  step_of_rule (theory := programTheory orderedPair)
    (rule := ⟨callTerm "eq2" [.var 0, .var 1], truth constantSpelling false⟩)
    (show _ ∈ orderedPair by decide) (fun index => .var index) (by decide) (by decide)

/-- **On a name with itself both rules answer**: the first by its repeated
variable, and the second because its step on the open term is a step of every
instance. -/
theorem orderedPair_both_answers (name : String) :
    Step (programTheory orderedPair) (pairCall (.con name) (.con name))
        (truth constantSpelling true) ∧
      Step (programTheory orderedPair) (pairCall (.con name) (.con name))
        (truth constantSpelling false) := by
  refine ⟨step_of_rule (theory := programTheory orderedPair)
    (rule := ⟨callTerm "eq2" [.var 0, .var 0], truth constantSpelling true⟩)
    (show _ ∈ orderedPair by decide) (fun _ => .con name) (by simp [inst_callTerm, pairCall])
    (inst_truth constantSpelling _ _), ?_⟩
  have closed : (programTheory orderedPair).ClosedBodies := fun _ _ defined => by cases defined
  have moved := (orderedPair_open_step.subst closed 0 (.con name)).subst closed 0 (.con name)
  exact moved

/-- **Negative**: reduction by the two rules is not confluent: `True` and
`False` are two normal forms of `(eq2 a a)`. -/
theorem orderedPair_not_confluent : ¬ Confluent (Step (programTheory orderedPair)) := by
  have listed : ∀ rule ∈ orderedPair, rewritesCall rule = true := by decide
  have rooted : ∀ rule, (programTheory orderedPair).rule rule → rewritesCall rule = true :=
    fun rule member => listed rule member
  exact not_confluent_of_fork (.single (orderedPair_both_answers "a").1)
    (.single (orderedPair_both_answers "a").2)
    (passive_normal (fun _ => rfl) rooted _ (passive_truth constantSpelling true))
    (passive_normal (fun _ => rfl) rooted _ (passive_truth constantSpelling false)) (by decide)

/-- **Positive**: on two different names the first match and the theory
agree: the one step of `(eq2 a b)` is to `False`. -/
theorem orderedPair_different_names :
    contract orderedPair (pairCall (.con "a") (.con "b")) = some (truth constantSpelling false) ∧
      Step (programTheory orderedPair) (pairCall (.con "a") (.con "b"))
        (truth constantSpelling false) :=
  ⟨by decide, contract_sound (by decide)⟩

#print axioms firstMatch_tests_names
#print axioms firstMatch_not_stable
#print axioms orderedPair_both_answers
#print axioms orderedPair_not_confluent
#print axioms orderedPair_different_names

end Mettapedia.Logic.HostingStyles.NameEquality
