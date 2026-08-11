import Mettapedia.Logic.Prolog.PureRuntimeSoundness
import Mettapedia.Logic.LP.RuntimeQueryRegression

/-!
# Canonical pure-Prolog runtime regressions

These gates exercise the `Logic.Prolog` entrypoint itself.  The positive case
runs a source-ordered Prolog program through the one `Logic.LP.RuntimeQuery`
state.  The negative cases ensure that Prolog control is rejected by the pure
specialization instead of being erased or encoded as an ordinary predicate.
-/

namespace Mettapedia.Logic.Prolog.PureRuntimeRegression

open Mettapedia.Logic
open LP.RuntimeQueryRegression
open PureRuntime

/-- The two-clause program used here contains no control and projects exactly
to the canonical LP clauses. -/
def pureProgram : Program qSig := Program.ofLP [
  fact .p (.const .a),
  fact .p (.const .b)
]

def pureQuery : Goal qSig := Goal.calls queryP

/-- Pull all answers from a bounded regression run.  An open fuel boundary or
runtime error is a failed gate, never reported as completion. -/
def collect (answerBudget : Nat) (session : Session qSig) :
    Option (List QConst × Nat × Nat) :=
  match answerBudget with
  | 0 => none
  | answerBudget + 1 =>
      match pull 64 session with
      | .open _ => none
      | .terminal (.runtimeError _ _) => none
      | .terminal (.completed memory) =>
          some ([], memory.heap.size, memory.trail.size)
      | .answer answer next =>
          match answerConstant? answer, collect answerBudget next with
          | some symbol, some (symbols, heapSize, trailSize) =>
              some (symbol :: symbols, heapSize, trailSize)
          | _, _ => none

def runPure : Option (List QConst × Nat × Nat) :=
  match openEmpty pureProgram pureQuery with
  | .error _ => none
  | .ok session => collect 4 session

/-- A source-level cut is not accepted by the control-free query boundary. -/
def rejectsCutGoal : Bool :=
  match openEmpty (Program.ofLP ([] : LP.Program qSig)) (.cut : Goal qSig) with
  | .error .controlInGoal => true
  | _ => false

/-- A source-level cut in a clause body is not accepted by the control-free
program boundary. -/
def rejectsCutClause : Bool :=
  let sourceProgram : Program qSig := [{
    head := unary .choose (.var .x)
    body := .cut
  }]
  match openEmpty sourceProgram (.succeed : Goal qSig) with
  | .error .controlInProgram => true
  | _ => false

-- Source order, multiplicity, and final memory restoration remain observable
-- through the canonical Prolog entrypoint.
#guard runPure == some ([.a, .b], 0, 0)

-- Neither query control nor clause-body control can be silently laundered
-- into the pure LP runtime.
#guard rejectsCutGoal
#guard rejectsCutClause

end Mettapedia.Logic.Prolog.PureRuntimeRegression
