import Mettapedia.Logic.Prolog.SourceRuntime

/-!
# Source loader goals on the canonical persistent runtime

Prolog directives and `initialization/1` goals use ordinary Prolog execution.
This module supplies only the loader's *first-solution policy*: it opens a
fresh query against the current persistent database and stops at the first
answer.  Clause selection, control, meta-call, dynamic updates, exceptions,
and restoration remain transitions of `SourceRuntime`, hence of the single
shared `Logic.LP.RuntimeQuery` engine.

The result keeps failure, fuel exhaustion, exceptions, and runtime errors
distinct.  A successful goal returns the complete persistent world from the
answered session; it never restores the database, non-backtrackable globals,
or allocator state captured before the goal.  Remaining answers are
deliberately abandoned, matching the once-like execution policy of a source
directive.  Ordering policy across multiple source units remains a separate
loader responsibility.
-/

namespace Mettapedia.Logic.Prolog.ReaderLoadRuntime

open Mettapedia.Logic
open RuntimeControl SourceSignature

abbrev Database :=
  LP.RuntimeDatabase.Database SourceSignature.Clause

abbrev World := RuntimeControl.World SourceRuntime.Sigma

/-- Lift a database-only caller into the complete persistent source world. -/
def worldOfDatabase (database : Database) : World := {
  database
  memory := LP.RuntimeTerm.Memory.empty SourceRuntime.Sigma.scoped
  nextScope := 1
}

/-- One bounded attempt to execute a source loader goal to its first answer. -/
inductive FirstResult where
  | succeeded (world : World)
  | failed (memory : LP.RuntimeTerm.Memory SourceRuntime.Sigma.scoped)
      (world : World)
  | open (session : SourceRuntime.Session)
  | raised (packet : LP.RuntimeException.Packet SourceRuntime.Sigma)
      (memory : LP.RuntimeTerm.Memory SourceRuntime.Sigma.scoped)
      (world : World)
  | runtimeError (error : LP.RuntimeQuery.QueryError)
      (memory : LP.RuntimeTerm.Memory SourceRuntime.Sigma.scoped)
      (world : World)

/-- Resume an already-open loader goal.  An answer transfers the session's
complete persistent world and discards only the backtrackable continuation. -/
def resumeFirst (fuel : Nat) (session : SourceRuntime.Session) : FirstResult :=
  match SourceRuntime.pullSession fuel session with
  | .answer _ resumed => .succeeded resumed.commitWorld
  | .open resumed => .open resumed
  | .terminal (.completed memory) world => .failed memory world
  | .terminal (.raised packet memory) world =>
      .raised packet memory world
  | .terminal (.runtimeError error memory) world =>
      .runtimeError error memory world

/-- Execute against a complete persistent source world. -/
def runFirstWorld (fuel : Nat) (world : World)
    (goal : SourceSignature.Goal) :
    Except LP.RuntimeQuery.QueryError FirstResult := do
  let session ← SourceRuntime.openWorld world goal
  pure (resumeFirst fuel session)

/-- Compatibility entry point for database-only callers.  It creates a new
world, so callers that execute more than one top-level goal and need persistent
globals must thread the `World` returned by `runFirstWorld` instead.  Opening
errors remain explicit in `Except`; execution outcomes remain explicit in
`FirstResult`. -/
def runFirst (fuel : Nat) (database : Database)
    (goal : SourceSignature.Goal) :
    Except LP.RuntimeQuery.QueryError FirstResult := do
  runFirstWorld fuel (worldOfDatabase database) goal

@[simp]
theorem resumeFirst_answer (fuel : Nat) (session resumed : SourceRuntime.Session)
    (answer : LP.RuntimeQuery.Answer SourceRuntime.Sigma)
    (hPull : SourceRuntime.pullSession fuel session = .answer answer resumed) :
    resumeFirst fuel session = .succeeded resumed.commitWorld := by
  simp [resumeFirst, hPull]

@[simp]
theorem resumeFirst_completed (fuel : Nat) (session : SourceRuntime.Session)
    (memory : LP.RuntimeTerm.Memory SourceRuntime.Sigma.scoped)
    (world : World)
    (hPull : SourceRuntime.pullSession fuel session =
      .terminal (.completed memory) world) :
    resumeFirst fuel session = .failed memory world := by
  simp [resumeFirst, hPull]

end Mettapedia.Logic.Prolog.ReaderLoadRuntime
