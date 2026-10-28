import Mettapedia.Logic.Prolog.Syntax
import Mettapedia.Logic.LP.RuntimeQuery

/-!
# Pure Prolog sessions on the canonical LP runtime

This is the control-free specialization of the canonical Prolog syntax.  It
does not implement resolution: accepted goals and programs project exactly to
`Logic.LP`, and execution delegates to `LP.RuntimeQuery`.

Control-bearing syntax is rejected explicitly.  In particular, `cut` is not
encoded as a distinguished predicate symbol, so an ordinary source predicate
can never be mislabeled as control by this boundary.
-/

namespace Mettapedia.Logic.Prolog.PureRuntime

open Mettapedia.Logic

/-- Failure to enter the pure runtime specialization. -/
inductive OpenError where
  | controlInProgram
  | controlInGoal
  | query (error : LP.RuntimeQuery.QueryError)
deriving Repr

/-- The control-free builtin profile.  The canonical syntax projection has
already rejected every control constructor before this profile is used. -/
def noControl (sigma : LP.LPSignature) : LP.RuntimeQuery.Builtins sigma where
  isCut := fun _ => false
  cut_arity_zero := by simp

@[simp]
theorem noControl_isCut {sigma : LP.LPSignature}
    (symbol : sigma.relationSymbols) :
    (noControl sigma).isCut symbol = false := rfl

/-- A resumable pure session stores the projected LP program and the one LP
runtime state.  There is no second resolver state. -/
structure Session (sigma : LP.LPSignature) where
  program : LP.Program sigma
  state : LP.RuntimeQuery.State sigma

/-- Open a canonical Prolog goal only when both it and its program are in the
pure definite-clause fragment. -/
def openSession {sigma : LP.LPSignature} [DecidableEq sigma.vars]
    (memory : LP.RuntimeTerm.Memory sigma.scoped)
    (queryScope nextScope : Nat) (program : Program sigma)
    (goal : Goal sigma) : Except OpenError (Session sigma) :=
  match program.toLP? with
  | none => .error .controlInProgram
  | some pureProgram =>
      match goal.toAtoms? with
      | none => .error .controlInGoal
      | some goals =>
          match LP.RuntimeQuery.openQuery memory queryScope nextScope goals with
          | .error error => .error (.query error)
          | .ok state => .ok { program := pureProgram, state }

/-- Open an isolated source query at the conventional query/activation scopes
used by the grounded LP theorem. -/
def openEmpty {sigma : LP.LPSignature} [DecidableEq sigma.vars]
    (program : Program sigma) (goal : Goal sigma) :
    Except OpenError (Session sigma) :=
  openSession (LP.RuntimeTerm.Memory.empty sigma.scoped) 0 1 program goal

/-- Demand-driven results retain the canonical LP answer and a resumable
session. Fuel exhaustion remains open. -/
inductive PullResult (sigma : LP.LPSignature) where
  | open (session : Session sigma)
  | answer (value : LP.RuntimeQuery.Answer sigma) (session : Session sigma)
  | terminal (result : LP.RuntimeQuery.Terminal sigma)

/-- Pull from the one LP runtime and repackage only the resumed session. -/
def pull {sigma : LP.LPSignature} [DecidableEq sigma.vars]
    [DecidableEq sigma.constants] [DecidableEq sigma.functionSymbols]
    [DecidableEq sigma.relationSymbols]
    (fuel : Nat) (session : Session sigma) : PullResult sigma :=
  match LP.RuntimeQuery.pull (noControl sigma) session.program fuel session.state with
  | .open state => .open { session with state }
  | .answer answer state => .answer answer { session with state }
  | .terminal result => .terminal result

/-- Pure LP programs and ordered goal lists enter this specialization without
any translation loss. -/
theorem openSession_ofLP {sigma : LP.LPSignature} [DecidableEq sigma.vars]
    (memory : LP.RuntimeTerm.Memory sigma.scoped)
    (queryScope nextScope : Nat) (program : LP.Program sigma)
    (goals : List (LP.Atom sigma)) :
    openSession memory queryScope nextScope (Program.ofLP program)
        (Goal.calls goals) =
      match LP.RuntimeQuery.openQuery memory queryScope nextScope goals with
      | .error error => .error (.query error)
      | .ok state => .ok { program, state } := by
  simp [openSession]

end Mettapedia.Logic.Prolog.PureRuntime
