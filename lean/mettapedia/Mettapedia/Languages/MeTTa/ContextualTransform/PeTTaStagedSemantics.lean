import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaResumptionSemantics

/-!
# Staged PeTTa evaluation

SWI-PeTTa translates a `!` query when it is reached. A function call enters
already compiled clauses. Named edits can refresh stored clauses when they
change recorded decisions. Running code keeps its translation after its own
edits and on backtracking. Each newly reached call selects its alternatives
from the clauses available at that call's entry.

`stagedAt` models a fresh translation at an entry and retention inside the
running unit. The fresh entry also describes a stored clause whose
translation reads still agree with the current world. A run-time `eval`
provides an explicit fresh translation. The Lean results concern the
abstract policy and its read-agreement condition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStagedSemantics

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Search Trace)
open Mettapedia.Machines.ReadOnlyQuery (Program run Agrees)
open PeTTaWorldSemantics
open PeTTaResumptionSemantics (Policy Boundary evalAt evalAt_live)

variable {World Key Fact Plan A : Type}

/-- Translate at an entry. After an edit and on resumption, keep what the
entry translated. Execution always uses the actual world. -/
def stagedAt (boundary : Boundary) (observe : World → Key → Fact)
    (preparedIn : World) (prepare : Program Key Fact Plan)
    (execute : Plan → Search World A) : Search World A :=
  match boundary with
  | .entry => DecisionStaging.enterLive observe prepare execute
  | .afterEdit => execute (run (observe preparedIn) prepare).answer
  | .resume => execute (run (observe preparedIn) prepare).answer

/-- At an entry with a fresh translation, the staged and live readings
coincide. -/
theorem staged_entry_eq_live (observe : World → Key → Fact) (preparedIn : World)
    (prepare : Program Key Fact Plan) (execute : Plan → Search World A) :
    stagedAt .entry observe preparedIn prepare execute =
      evalAt .live .entry observe preparedIn prepare execute := rfl

/-- On resumption, staging keeps the prepared decisions, as edits-only does. -/
theorem staged_resume_eq_editsOnly (observe : World → Key → Fact) (preparedIn : World)
    (prepare : Program Key Fact Plan) (execute : Plan → Search World A) :
    stagedAt .resume observe preparedIn prepare execute =
      evalAt .editsOnly .resume observe preparedIn prepare execute := rfl

/-- The staged and the live readings differ only where an edit changed
something the translation read. -/
theorem staged_eq_live_of_agrees (boundary : Boundary) (observe : World → Key → Fact)
    {preparedIn current : World} (prepare : Program Key Fact Plan)
    (execute : Plan → Search World A)
    (agrees : Agrees (observe current) (run (observe preparedIn) prepare).reads) :
    stagedAt boundary observe preparedIn prepare execute current =
      evalAt .live boundary observe preparedIn prepare execute current := by
  cases boundary
  · rfl
  all_goals
    rw [evalAt_live]
    change execute (run (observe preparedIn) prepare).answer current =
      execute (run (observe current) prepare).answer current
    rw [Mettapedia.Machines.ReadOnlyQuery.run_eq_of_agrees _ _ _ agrees]

namespace Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Store)
open PeTTaWorldSemantics (Expr Model eval invokeAtEntry)
open PeTTaWorldSemantics.Search (pure append)

private def helper : Atom := .expression [.symbol "helper"]
private def value : Atom := .grounded (.int 42)
private def truth : Atom := .symbol "true"

private def equation (name : String) (body : Atom) : Atom :=
  .expression [.symbol "=", .expression [.symbol name], body]

private def installed : Atom := equation "helper" value

private def equations (world : Store) (head : String) : List Atom :=
  world.filterMap fun row => match row with
  | .expression [.symbol "=", .expression [.symbol name], body] =>
      if name = head then some body else none
  | _ => none

private def nullaryModel : Model Store String Atom Atom Atom where
  update row world := world ++ [row]
  editValue _ := truth
  argumentModes _ _ := []
  holdArgument _ := .symbol "held"
  data head args := .expression (.symbol head :: args)
  candidates := equations
  runCandidate candidate _ := pure candidate

private def install : Search Store Atom := eval nullaryModel (.edit installed)

private def observe (world : Store) (head : String) : Bool := !(equations world head).isEmpty

private def named (boundary : Boundary) (preparedIn : Store) (head : String) :
    Search Store Atom :=
  stagedAt boundary observe preparedIn (.read head .pure) fun callable =>
    if callable then invokeAtEntry nullaryModel head [] else pure (nullaryModel.data head [])

/-- `!(let $u (add-atom &self (= (helper) 42)) (helper))`: the code after the
edit keeps the decision it was translated with, so `(helper)` stays data.
A fresh translation, as in `(eval (helper))`, sees the new equation. -/
theorem edit_then_plain_or_entry :
    ((install.bind fun _ => named .afterEdit [] "helper") []).drain.1 = [helper] ∧
    ((install.bind fun _ => named .entry [] "helper") []).drain.1 = [value] := by
  decide +kernel

/-- A later `superpose` branch keeps its translation. Written with `eval`, it
is an entry and sees the equation an earlier branch added. -/
theorem later_branch_plain_or_entry :
    (append install (named .resume [] "helper") []).drain.1 = [truth, helper] ∧
    (append install (named .entry [] "helper") []).drain.1 = [truth, value] := by
  decide +kernel

/-- A function that already had an equation is a call in the translation, and
the call finds the equation added since. -/
theorem kept_call_reads_new_equations :
    let before := [equation "helper" (.symbol "old")]
    (append install (named .resume before "helper") before).drain.1 =
      [truth, .symbol "old", value] := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStagedSemantics
