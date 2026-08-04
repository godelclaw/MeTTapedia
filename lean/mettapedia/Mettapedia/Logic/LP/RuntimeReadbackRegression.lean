import Mettapedia.Logic.LP.RuntimeReadback
import Mettapedia.Logic.LP.RuntimeQueryRegression

/-!
# Readback regressions on live query runs

These gates re-run the demand-driven query fixtures and read every answer back
through the general `RuntimeReadback.Heap.readTerm` — exercising real variable
link chains produced by unification, not hand-placed cells.  They discriminate
the reader against truncation (`notFinite` on legal answers), wrong-cell
readback, and arity confusion.
-/

namespace Mettapedia.Logic.LP.RuntimeReadbackRegression

open RuntimeTerm RuntimeQuery RuntimeReadback RuntimeQueryRegression

/-- Project one answer through the general reader.  The query has exactly one
source variable; its readback must be a constant for these ground programs. -/
def readbackConstant? (answer : Answer qSig) : Option QConst :=
  match readAnswer answer with
  | .ok [(_, .const symbol)] => some symbol
  | _ => none

/-- Collect answers through the general readback instead of the ad-hoc
projection used by the query regression. -/
def collectRead (answerBudget : Nat) (state : State qSig) :
    Option (List QConst) :=
  match answerBudget with
  | 0 => none
  | answerBudget + 1 =>
      match pull builtins program 64 state with
      | .open _ => none
      | .terminal (.runtimeError _ _) => none
      | .terminal (.completed _) => some []
      | .answer answer next =>
          match readbackConstant? answer, collectRead answerBudget next with
          | some symbol, some symbols => some (symbol :: symbols)
          | _, _ => none

def runRead (goals : List (Atom qSig)) : Option (List QConst) :=
  match openQuery (Memory.empty qSig.scoped) 0 1 goals with
  | .error _ => none
  | .ok state => collectRead 4 state

-- The general reader traverses the live binding chain of each answer: both
-- `p` facts read back in source order, and the committed `choose` answer reads
-- back through its unification link.
#guard runRead queryP == some [.a, .b]
#guard runRead queryChoose == some [.a]

end Mettapedia.Logic.LP.RuntimeReadbackRegression
