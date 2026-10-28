import Mettapedia.Logic.LP.RuntimeBranchInvariant
import Mettapedia.Logic.Prolog.RuntimeControlMaterializeSoundness

/-!
# Structured branch checkpoints across typed Prolog clause materialization

This is a narrow composition theorem over the one shared engine.  Typed
Prolog's clause adapter materializes into the LP heap; the branch checkpoint
therefore follows that allocation history before the canonical graph unifier
enters the clause head.
-/

namespace Mettapedia.Logic.Prolog.RuntimeControl

open Mettapedia.Logic
open LP.RuntimeTerm
open LP.RuntimeBranchInvariant

/-- A live structured-branch checkpoint survives materialization of a selected
typed Prolog clause.  The result is a certificate over the adapter's actual
returned memory, not a parallel source-level store. -/
theorem BranchCheckpoint.advance_clause_materialization
    {sigma : LP.LPSignature} [DecidableEq sigma.scoped.vars]
    {anchor : Memory sigma.scoped}
    {state : LP.RuntimeQuery.StateCore sigma (RuntimeGoal sigma.scoped)
      (Clause sigma)}
    {alternative : LP.RuntimeQuery.BranchChoiceCore sigma (RuntimeGoal sigma.scoped)}
    (certificate : BranchCheckpoint anchor state alternative)
    {scope : Nat} {clause : Clause sigma}
    {result : LP.RuntimeQuery.MaterializedBody sigma (RuntimeGoal sigma.scoped)}
    (run : (clauseMaterializer (sigma := sigma)).materialize state.memory scope
      clause = .ok result) :
    BranchCheckpoint anchor { state with memory := result.memory } alternative :=
  certificate.advance (clauseMaterializer_extends run)

/-- The ordinary nested-call path composes without a private heap: typed
clause materialization advances the branch certificate, then the canonical
graph unifier advances the same certificate again on head success. -/
theorem typedBranchClauseThenUnify
    {sigma : LP.LPSignature}
    [DecidableEq sigma.scoped.vars] [DecidableEq sigma.scoped.constants]
    [DecidableEq sigma.scoped.functionSymbols]
    {anchor : Memory sigma.scoped}
    {state : LP.RuntimeQuery.StateCore sigma (RuntimeGoal sigma.scoped)
      (Clause sigma)}
    {alternative : LP.RuntimeQuery.BranchChoiceCore sigma (RuntimeGoal sigma.scoped)}
    (certificate : BranchCheckpoint anchor state alternative)
    {scope : Nat} {clause : Clause sigma}
    {copied : LP.RuntimeQuery.MaterializedBody sigma (RuntimeGoal sigma.scoped)}
    (materialized : (clauseMaterializer (sigma := sigma)).materialize
      state.memory scope clause = .ok copied)
    (fuel : Nat) (agenda : List (Addr × Addr)) (memory : Memory sigma.scoped)
    (unified : LP.RuntimeUnification.runSteps fuel
      (LP.RuntimeUnification.startMany copied.memory agenda) =
        .terminal (.success memory)) :
    BranchCheckpoint anchor { state with memory } alternative := by
  exact LP.RuntimeBranchInvariant.BranchCheckpoint.advance_unifier_success
    (certificate.advance (clauseMaterializer_extends materialized))
    fuel agenda memory unified

end Mettapedia.Logic.Prolog.RuntimeControl
