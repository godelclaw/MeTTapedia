import Mettapedia.OSLF.MeTTaIL.Complete.Explore
import Mettapedia.OSLF.MeTTaIL.Complete.Termination
import Mettapedia.OSLF.MeTTaIL.Complete.Controls
import Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderFrontierControls

/-!
# Controls: steps modulo equations, and fair exploration

**Equations.** The guarded-binder profile has a conditional scope-extrusion equation,
`new x.(P | Q) = (new x.P) | Q` when the provider allows `Q`, and two rules with identical bodies
that fire only on `(new x.P) | Q`. On `new x.(cell x | guard permit)` no rule matches directly; the
step goes through the equation. With `permit` allowed, both members of the class are found, both
rule declarations fire, and the search certifies. With nothing allowed, the class is the source
alone and the search certifies that there is no step.

**Termination.** The guarded-binder plan's rules and equation premises descend, so its search
certifies at every well-sorted source, with or without `permit` (`guarded_eventually_complete`).

**Exploration.** In a two-rule language with `A → A` declared before `A → B`, the runner commits
the first published receipt and stays at `A`; the explorer reaches `B`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.ClassesControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open Mettapedia.Machines

/-! ## Equations -/

open EquationFrontierBinderProfile GeneralGuardedBinderFrontierControls in
/-- Represented members, published targets and completeness after some rounds. -/
def guarded (allowed : List Token) (work : Nat) : List Pattern × List Pattern × Bool :=
  let plan := GeneralGuardedBinderExecution.plan allowed
  let state := Classes.rounds plan [] .proc work (Classes.begin plan [] .proc source)
  (state.reps.map (·.pattern), state.log.map (·.firing.target), Classes.complete plan state)

open EquationFrontierBinderProfile GeneralGuardedBinderFrontierControls in
#guard guarded [.permit] 400 == ([source, exposed], [target, target], true)

open EquationFrontierBinderProfile GeneralGuardedBinderFrontierControls in
#guard guarded [] 400 == ([source], [], true)

/-! ## A loop declared before a halt -/

private def term : TypeExpr := .base "T"

def constant (label : String) : GrammarRule where
  label := label
  category := "T"
  params := []
  syntaxPattern := [.terminal label]

def rewrite (name : String) (target : String) : RewriteRule where
  name := name
  typeContext := []
  premises := []
  left := .apply "A" []
  right := .apply target []

def branching : LanguageDef where
  name := "Branching"
  types := ["T"]
  terms := [constant "A", constant "B"]
  equations := []
  rewrites := [rewrite "loop" "A", rewrite "halt" "B"]

def branchingPlan : Plan := Controls.rootPlan branching

/-- The runner's states after some ticks. -/
def runnerStates (ticks : Nat) : List Pattern :=
  (ResumableSearchRunner.Machine.advance (Classes.search branchingPlan [] term) ticks 20
    (ResumableSearchRunner.Machine.begin (Classes.search branchingPlan [] term) (.apply "A" []))).states.reverse

/-- The explorer's states after some rounds. -/
def explored (work : Nat) : List Pattern :=
  ((Explore.explore (Classes.search branchingPlan [] term) (.apply "A" []) work).nodes.map (·.state))

#guard runnerStates 4 == List.replicate 5 (.apply "A" [])
#guard (explored 30).contains (.apply "B" [])
#guard !(runnerStates 4).contains (.apply "B" [])

/-! ## The guarded-binder search always certifies -/

theorem guarded_descends (allowed : List EquationFrontierBinderProfile.Token) (chosen : allowed = [.permit] ∨ allowed = []) :
    Classes.Descends (GeneralGuardedBinderExecution.plan allowed) := by
  have premises : ((GeneralGuardedBinderExecution.plan allowed).equations.all fun equation =>
      StructuralDescent.checkPremises equation.rule equation.binding.spec 0 equation.rule.premises) = true := by
    rcases chosen with rfl | rfl <;> cbv
  refine ⟨by rcases chosen with rfl | rfl <;> cbv, fun equation member => ?_⟩
  simpa using List.all_eq_true.mp premises equation member

/-- **With or without `permit`, the guarded binder's search certifies at every well-sorted source.** -/
theorem guarded_eventually_complete (allowed : List EquationFrontierBinderProfile.Token)
    (chosen : allowed = [.permit] ∨ allowed = []) (source : Pattern)
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralGuardedBinderAdmission.snapshot allowed).language (GeneralGuardedBinderAdmission.snapshot allowed).free
      [] .proc source) :
    ∃ work, Classes.complete (GeneralGuardedBinderExecution.plan allowed)
      (Classes.runAt (GeneralGuardedBinderExecution.plan allowed) [] .proc source work) = true :=
  Classes.compiled_eventually_complete [] .proc source (GeneralGuardedBinderAdmission.admission_complete allowed)
    (guarded_descends allowed chosen) sorted

end Mettapedia.OSLF.MeTTaIL.Complete.ClassesControls
