import Mettapedia.Logic.Prolog.RuntimeControlSoundness
import Mettapedia.Logic.LP.RuntimeCompoundQueryRegression
import Mettapedia.Logic.Prolog.RuntimeControlRegression

/-!
# Executable canary for typed-runtime grounding

The concrete two-clause query below runs through `RuntimeControl`, not through
the pure-session wrapper.  It witnesses that the conserved fragment has real
ordered answers while the theorem in `RuntimeControlSoundness` grounds every
such pulled answer in scoped SLD and the least Herbrand model.
-/

namespace Mettapedia.Logic.Prolog.RuntimeControlSoundnessRegression

open Mettapedia.Logic
open LP.RuntimeQueryRegression
open RuntimeControl
open RuntimeControlRegression

instance : IsEmpty qSig.functionSymbols := ⟨fun symbol => nomatch symbol⟩

def groundedProgram : LP.Program qSig := [
  fact .p (.const .a),
  fact .p (.const .b)
]

def groundedKnowledgeBase : LP.KnowledgeBase qSig where
  prog := groundedProgram
  db := ∅

def groundedTypedRun : Option (List QConst × Nat × Nat) :=
  runTyped (Program.ofLP groundedProgram) (Goal.calls queryP)

-- The executable witness fixes source order, multiplicity, and final
-- checkpoint restoration on the same typed entrypoint named by the theorem.
#guard groundedTypedRun == some ([.a, .b], 0, 0)

/-- Concrete specialization of the grounding theorem.  The hypotheses are
the actual `openQuery` and `pull` equations used by the executable witness,
not an alternate evaluator. -/
theorem groundedTypedAnswer_leastModel
    (state : State qSig) (fuel : Nat) (answer : LP.RuntimeQuery.Answer qSig)
    (resumed : State qSig)
    (hOpen : openQuery (LP.RuntimeTerm.Memory.empty qSig.scoped) 0 1
      (Goal.calls queryP) = .ok state)
    (hPull : pull (Program.ofLP groundedProgram) fuel state =
      .answer answer resumed) :
    ∃ theta : LP.Subst qSig.scoped,
      LP.SLDScopedTree groundedProgram 1 (LP.queryAtScope 0 queryP) theta ∧
      (∀ pair ∈ answer.queryVarMap, ∀ term,
        LP.RuntimeReadback.Heap.readTerm answer.memory.heap pair.2 = .ok term →
        theta pair.1 = term) ∧
      ∀ grounding : LP.Grounding qSig.scoped,
        ∀ atom ∈ LP.queryAtScope 0 queryP,
          ((grounding.compSubst theta).groundAtom atom).unscope ∈
            LP.leastHerbrandModel groundedKnowledgeBase := by
  exact pureCallAnswer_leastModel groundedKnowledgeBase queryP state fuel
    answer resumed hOpen hPull

end Mettapedia.Logic.Prolog.RuntimeControlSoundnessRegression
