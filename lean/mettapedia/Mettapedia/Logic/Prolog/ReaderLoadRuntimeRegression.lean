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

private def sourceVar (name : String) (occurrence : Nat) :
    SourceSignature.Term := .var { spelling := name, occurrence }

private def setGlobal (name : String) (value : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "nb_setval" [SourceSignature.atom name, value]

private def getGlobal (name : String) (value : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "nb_getval" [SourceSignature.atom name, value]

/-- The first top-level goal stores a copied residual variable; the second
fresh query sees and binds that exact persistent graph.  A batch runner that
threads only the database cannot satisfy this witness. -/
def goalsThreadCompleteWorld : Bool :=
  let x := sourceVar "X" 0
  let y := sourceVar "Y" 0
  let goals := [
    setGlobal "loader_world" (SourceSignature.compound "f" [x]),
    .conj (getGlobal "loader_world" y)
      (.unify y (SourceSignature.compound "f" [SourceSignature.atom "later"]))
  ]
  match ReaderLoadRuntime.runGoalsWorld 1024
      (ReaderLoadRuntime.worldOfDatabase emptyDatabase) goals with
  | .succeeded world =>
      world.globals.lookup (.atom "loader_world") |>.isSome
  | _ => false

#guard goalsThreadCompleteWorld

/-- Failure consumes the current goal but does not execute or discard the
source-order tail. -/
def failureRetainsUnexecutedTail : Bool :=
  let late := setGlobal "must_not_run" (SourceSignature.atom "value")
  match ReaderLoadRuntime.runGoalsWorld 128
      (ReaderLoadRuntime.worldOfDatabase emptyDatabase) [.fail, late] with
  | .failed _ world [.call remaining] =>
      remaining.symbol.name == "nb_setval" &&
        remaining.symbol.arity == 2 &&
        (world.globals.lookup (.atom "must_not_run")).isNone
  | _ => false

#guard failureRetainsUnexecutedTail

end Mettapedia.Logic.Prolog.ReaderLoadRuntimeRegression
