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

end Mettapedia.Logic.Prolog.RuntimeControl
