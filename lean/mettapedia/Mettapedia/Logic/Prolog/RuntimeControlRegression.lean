import Mettapedia.Logic.Prolog.RuntimeControl
import Mettapedia.Logic.LP.RuntimeQueryRegression

/-!
# Runtime-control materialization regressions

The fixture below checks two load-bearing properties at once: canonical source
variables retain sharing in the LP heap, and source-level cut remains a typed
control instruction rather than becoming an ordinary runtime atom.
-/

namespace Mettapedia.Logic.Prolog.RuntimeControlRegression

open Mettapedia.Logic
open LP.RuntimeTerm
open LP.RuntimeQueryRegression
open RuntimeControl

def sharedUnifyThenCut : Goal qSig :=
  .conj (.unify (.var .x) (.var .x)) .cut

def sharedUnifyThenCutMaterializes : Bool :=
  match materializeGoal (Memory.empty qSig) sharedUnifyThenCut with
  | .error _ => false
  | .ok result =>
      match result.goals with
      | [.unify left right, .cut] =>
          left == right && result.memory.heap.size == 1 &&
            result.memory.trail.size == 0
      | _ => false

#guard sharedUnifyThenCutMaterializes

end Mettapedia.Logic.Prolog.RuntimeControlRegression
