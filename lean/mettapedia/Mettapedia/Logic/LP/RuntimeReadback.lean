import Mettapedia.Logic.LP.RuntimeFiniteReadback
import Mettapedia.Logic.LP.RuntimeQuery

/-!
# Reading runtime heap terms back into finite LP terms

`RuntimeQuery` yields answers as live heap roots.  Grounding those answers in
the declarative `Logic.LP` semantics requires reading a heap address back into
an inductive `Term` — the direction the runtime never otherwise needs.

The heap-to-term mechanism lives in `RuntimeFiniteReadback`, below query
execution.  This module adds only the answer-level projection.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeReadback

open RuntimeTerm

/-- Read every recorded source query variable of an answer.  The result maps
each source variable to the finite term its heap root denotes now. -/
def readAnswer {σ : LPSignature} (answer : RuntimeQuery.Answer σ) :
    Except ReadbackError (List (ScopedVar σ.vars × Term σ.scoped)) :=
  answer.queryVarMap.foldrM (init := []) fun (variable_, address) acc => do
    let term ← Heap.readTerm answer.memory.heap address
    .ok ((variable_, term) :: acc)

end RuntimeReadback
end Mettapedia.Logic.LP
