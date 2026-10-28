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

abbrev compoundSig := LP.RuntimeCompoundQueryRegression.cSig
def compoundProgram : LP.Program compoundSig :=
  LP.RuntimeCompoundQueryRegression.program
def compoundQuery : List (LP.Atom compoundSig) :=
  LP.RuntimeCompoundQueryRegression.query

def compoundKnowledgeBase : LP.KnowledgeBase compoundSig where
  prog := compoundProgram
  db := ∅

/-- Execute the compound fixture through the typed Prolog representation of
the same shared runtime. -/
def groundedTypedCompoundRun : Bool :=
  match openQuery (LP.RuntimeTerm.Memory.empty compoundSig.scoped) 0 1
      (Goal.calls compoundQuery) with
  | .error _ => false
  | .ok state =>
      match pull (Program.ofLP compoundProgram) 32 state with
      | .answer answer _ =>
          match answer.queryVarMap with
          | [(_, address)] =>
              match LP.RuntimeReadback.Heap.readTerm answer.memory.heap
                  address with
              | .ok (.app .pair args) =>
                  match args ⟨0, by
                      simp [compoundSig,
                        LP.RuntimeCompoundQueryRegression.cSig]⟩,
                      args ⟨1, by
                        simp [compoundSig,
                          LP.RuntimeCompoundQueryRegression.cSig]⟩ with
                  | .const .a, .const .b => true
                  | _, _ => false
              | _ => false
          | _ => false
      | _ => false

#guard groundedTypedCompoundRun

/-- Concrete typed-Prolog specialization of finite compound grounding. -/
theorem groundedTypedCompoundAnswer_leastModel
    (state : State compoundSig)
    (answer : LP.RuntimeQuery.Answer compoundSig)
    (resumed : State compoundSig)
    (hOpen : openQuery (LP.RuntimeTerm.Memory.empty compoundSig.scoped) 0 1
      (Goal.calls compoundQuery) = .ok state)
    (hPull : pull (Program.ofLP compoundProgram) 32 state =
      .answer answer resumed)
    (hfinite : LP.RuntimeUnificationSoundness.FiniteReadback
      answer.memory.heap) :
    ∃ theta : LP.Subst compoundSig.scoped,
      LP.SLDScopedTree compoundProgram 1
        (LP.queryAtScope 0 compoundQuery) theta ∧
      (∀ pair ∈ answer.queryVarMap, ∀ term,
        LP.RuntimeReadback.Heap.readTerm answer.memory.heap pair.2 = .ok term →
        theta pair.1 = term) ∧
      ∀ grounding : LP.Grounding compoundSig.scoped,
        ∀ atom ∈ LP.queryAtScope 0 compoundQuery,
          ((grounding.compSubst theta).groundAtom atom).unscope ∈
            LP.leastHerbrandModel compoundKnowledgeBase := by
  exact pureCallAnswer_finiteReadback_leastModel compoundKnowledgeBase
    compoundQuery state 32 answer resumed hOpen hPull hfinite

end Mettapedia.Logic.Prolog.RuntimeControlSoundnessRegression
