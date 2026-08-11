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
distinct.  A successful goal returns the database from the answered session;
it never restores the database captured before the goal.  Remaining answers
are deliberately abandoned, matching the once-like execution policy of a
source directive.  Ordering policy across multiple source units remains a
separate loader responsibility.
-/

namespace Mettapedia.Logic.Prolog.ReaderLoadRuntime

open Mettapedia.Logic
open RuntimeControl SourceSignature

abbrev Database :=
  LP.RuntimeDatabase.Database SourceSignature.Clause

/-- One bounded attempt to execute a source loader goal to its first answer. -/
inductive FirstResult where
  | succeeded (database : Database)
  | failed (memory : LP.RuntimeTerm.Memory SourceRuntime.Sigma.scoped)
      (database : Database)
  | open (session : SourceRuntime.Session)
  | raised (packet : LP.RuntimeException.Packet SourceRuntime.Sigma)
      (memory : LP.RuntimeTerm.Memory SourceRuntime.Sigma.scoped)
      (database : Database)
  | runtimeError (error : LP.RuntimeQuery.QueryError)
      (memory : LP.RuntimeTerm.Memory SourceRuntime.Sigma.scoped)
      (database : Database)

/-- Resume an already-open loader goal.  An answer transfers the session's
current persistent database and discards only the backtrackable continuation.
-/
def resumeFirst (fuel : Nat) (session : SourceRuntime.Session) : FirstResult :=
  match SourceRuntime.pullSession fuel session with
  | .answer _ resumed => .succeeded resumed.database
  | .open resumed => .open resumed
  | .terminal (.completed memory) database => .failed memory database
  | .terminal (.raised packet memory) database =>
      .raised packet memory database
  | .terminal (.runtimeError error memory) database =>
      .runtimeError error memory database

/-- Open and execute one canonical source goal against an existing database.
Opening errors remain explicit in `Except`; execution outcomes remain explicit
in `FirstResult`. -/
def runFirst (fuel : Nat) (database : Database)
    (goal : SourceSignature.Goal) :
    Except LP.RuntimeQuery.QueryError FirstResult := do
  let session ← SourceRuntime.openDatabase database goal
  pure (resumeFirst fuel session)

@[simp]
theorem resumeFirst_answer (fuel : Nat) (session resumed : SourceRuntime.Session)
    (answer : LP.RuntimeQuery.Answer SourceRuntime.Sigma)
    (hPull : SourceRuntime.pullSession fuel session = .answer answer resumed) :
    resumeFirst fuel session = .succeeded resumed.database := by
  simp [resumeFirst, hPull]

@[simp]
theorem resumeFirst_completed (fuel : Nat) (session : SourceRuntime.Session)
    (memory : LP.RuntimeTerm.Memory SourceRuntime.Sigma.scoped)
    (database : Database)
    (hPull : SourceRuntime.pullSession fuel session =
      .terminal (.completed memory) database) :
    resumeFirst fuel session = .failed memory database := by
  simp [resumeFirst, hPull]

end Mettapedia.Logic.Prolog.ReaderLoadRuntime
