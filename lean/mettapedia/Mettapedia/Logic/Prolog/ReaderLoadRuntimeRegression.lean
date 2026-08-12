import Mettapedia.Logic.Prolog.ReaderLoadRuntime

namespace Mettapedia.Logic.Prolog.ReaderLoadRuntimeRegression

open Mettapedia.Logic
open SourceSignature ReaderLoadRuntime

private def emptyDatabase : ReaderLoadRuntime.Database :=
  LP.RuntimeDatabase.Database.ofProgram []

private def asserted (name value : String) : SourceSignature.Term :=
  SourceSignature.compound name [SourceSignature.atom value]

private def assertz (clause : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "assertz" [clause]

private def hasFirstAnswer (database : ReaderLoadRuntime.Database)
    (goal : SourceSignature.Goal) : Bool :=
  match SourceRuntime.openDatabase database goal with
  | .error _ => false
  | .ok session =>
      match SourceRuntime.pullSession 128 session with
      | .answer _ _ => true
      | _ => false

/-- The loader returns the database *after* the source goal's persistent
mutation, and a later fresh query observes that exact insertion. -/
def successfulDirectiveCarriesDatabase : Bool :=
  match ReaderLoadRuntime.runFirst 128 emptyDatabase
      (assertz (asserted "loaded" "a")) with
  | .ok (.succeeded world) =>
      world.database.generation == 1 &&
        hasFirstAnswer world.database (SourceSignature.call "loaded"
          [SourceSignature.atom "a"])
  | _ => false

#guard successfulDirectiveCarriesDatabase

/-- Stopping at the first solution is observable: the abandoned right branch
cannot perform its assertion.  A zero-step or exhaust-to-completion policy
would fail this discriminator. -/
def remainingSolutionsAreNotExecuted : Bool :=
  let goal : SourceSignature.Goal := .disj .succeed
    (assertz (asserted "late" "value"))
  match ReaderLoadRuntime.runFirst 128 emptyDatabase goal with
  | .ok (.succeeded world) =>
      world.database.generation == 0 &&
        !hasFirstAnswer world.database (SourceSignature.call "late"
          [SourceSignature.atom "value"])
  | _ => false

#guard remainingSolutionsAreNotExecuted

/-- Exhaustion without an answer is source-goal failure, not successful load
completion and not a fabricated answer. -/
def failureIsDistinct : Bool :=
  match ReaderLoadRuntime.runFirst 128 emptyDatabase .fail with
  | .ok (.failed memory world) =>
      memory.heap.isEmpty && memory.trail.isEmpty &&
        world.database.generation == 0
  | _ => false

#guard failureIsDistinct

/-- A zero fuel budget exposes the resumable canonical session; it never
turns an unfinished loader goal into success or failure. -/
def zeroFuelIsOpen : Bool :=
  match ReaderLoadRuntime.runFirst 0 emptyDatabase .succeed with
  | .ok (.open _) => true
  | _ => false

#guard zeroFuelIsOpen

end Mettapedia.Logic.Prolog.ReaderLoadRuntimeRegression
