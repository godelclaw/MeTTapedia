import Mettapedia.Logic.Prolog.SourceRuntime
import Mettapedia.Logic.LP.RuntimeReadback

/-!
# Concrete meta-call regressions

These fixtures start from canonical source terms, materialize them into the
shared LP heap, and execute through `SourceRuntime`.  They discriminate
dynamic heap decoding, `call/N` argument extension, DFS order, and the local
cut boundary installed by the shared engine.
-/

namespace Mettapedia.Logic.Prolog.SourceRuntimeRegression

open Mettapedia.Logic
open SourceSignature SourceRuntime

def x : SourceSignature.Term := var "X" 0
def g : SourceSignature.Term := var "G" 0
def y : SourceSignature.Term := var "Y" 0
def z : SourceSignature.Term := var "Z" 0
def leftVar : SourceSignature.Term := var "Left" 0
def rightVar : SourceSignature.Term := var "Right" 0

def equality (left right : SourceSignature.Term) : SourceSignature.Term :=
  compound "=" [left, right]

def conjunction (left right : SourceSignature.Term) : SourceSignature.Term :=
  compound "," [left, right]

def disjunction (left right : SourceSignature.Term) : SourceSignature.Term :=
  compound ";" [left, right]

def pair (left right : SourceSignature.Term) : SourceSignature.Term :=
  compound "pair" [left, right]

def metaGoal (callable : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "call" [callable]

def fact (name : String) (arguments : List SourceSignature.Term) :
    SourceSignature.Clause := {
  head := predicate name arguments
  body := .succeed
}

private def answerAtom? (answer : LP.RuntimeQuery.Answer Sigma) :
    Option String :=
  match answer.queryVarMap with
  | [(_, address)] =>
      match LP.RuntimeReadback.Heap.readTerm answer.memory.heap address with
      | .ok (.const (.atom name)) => some name
      | _ => none
  | _ => none

def collectAtoms : Nat → Session → Option (List String × Nat × Nat)
  | 0, _ => none
  | budget + 1, session =>
      match SourceRuntime.pullSession 128 session with
      | .open _ => none
      | .terminal (.completed memory) =>
          some ([], memory.heap.size, memory.trail.size)
      | .terminal (.runtimeError _ _) => none
      | .terminal (.raised _ _) => none
      | .answer answer resumed =>
          match answerAtom? answer, collectAtoms budget resumed with
          | some value, some (rest, heapSize, trailSize) =>
              some (value :: rest, heapSize, trailSize)
          | _, _ => none

def collectCount : Nat → Nat → Session → Option (Nat × Nat × Nat)
  | 0, _, _ => none
  | answerBudget + 1, count, session =>
      match SourceRuntime.pullSession 128 session with
      | .open _ => none
      | .terminal (.completed memory) =>
          some (count, memory.heap.size, memory.trail.size)
      | .terminal (.runtimeError _ _) => none
      | .terminal (.raised _ _) => none
      | .answer _ resumed => collectCount answerBudget (count + 1) resumed

def runAtoms (program : SourceSignature.Program) (goal : SourceSignature.Goal) :
    Option (List String × Nat × Nat) :=
  match SourceRuntime.openEmpty program goal with
  | .error _ => none
  | .ok session => collectAtoms 8 session

def runCount (program : SourceSignature.Program) (goal : SourceSignature.Goal) :
    Option (Nat × Nat × Nat) :=
  match SourceRuntime.openEmpty program goal with
  | .error _ => none
  | .ok session => collectCount 8 0 session

/-- Run to an uncaught finite atomic exception.  The packet is detached from
the rolled-back heap, whose exact cleanup remains separately observable. -/
def runRaisedAtom (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) : Option (String × Nat × Nat) :=
  match SourceRuntime.openEmpty program goal with
  | .error _ => none
  | .ok session =>
      match SourceRuntime.pullSession 256 session with
      | .terminal (.raised packet memory) =>
          match packet.term with
          | .const (.atom name) =>
              some (name, memory.heap.size, memory.trail.size)
          | _ => none
      | _ => none

/-- A disjunction that exists only as a heap term is decoded at call time and
retains SWI's left-to-right answer order. -/
def dynamicDisjunction : SourceSignature.Goal :=
  metaGoal (disjunction (equality x (atom "a")) (equality x (atom "b")))

/-- Cut inside meta-call prunes the meta-call's own right branch but not the
older alternative of its caller.  The only answer is therefore `c`. -/
def metaCutRetainsCaller : SourceSignature.Goal :=
  let guarded := disjunction
    (conjunction (equality x (atom "a"))
      (conjunction (atom "!") (atom "fail")))
    (equality x (atom "b"))
  .disj (metaGoal guarded) (.unify x (atom "c"))

/-- `call/3` appends two arguments to an atomic predicate name. -/
def callThree : SourceSignature.Goal :=
  SourceSignature.call "call" [atom "p", atom "a", atom "b"]

/-- The callable itself may be constructed by unification before `call/1`;
the decoder observes the current heap graph rather than source syntax. -/
def heapBuiltCallable : SourceSignature.Goal :=
  .conj (.unify g (compound "p" [atom "a", atom "b"])) (metaGoal g)

def binaryFactProgram : SourceSignature.Program :=
  [fact "p" [atom "a", atom "b"]]

/-! ## Exception control through the shared frame stack -/

/-- A fresh catcher is selected at throw time and reconstructed after rollback
before recovery executes. -/
def caughtGround : SourceSignature.Goal :=
  .catch (.throw (atom "ball")) x (.unify x (atom "ball"))

/-- Catcher selection must observe bindings made by the protected goal.  The
entry-time `X` is free, but the throw-time `X = body` rejects `ball`. -/
def throwTimeBoundCatcherRejects : SourceSignature.Goal :=
  .catch
    (.conj (.unify x (atom "body")) (.throw (atom "ball")))
    x .succeed

/-- Recovery executes outside the consumed handler, so its exception cannot
be swallowed by the same `catch/3`. -/
def recoveryRethrowEscapes : SourceSignature.Goal :=
  .catch (.throw (atom "a")) x (.throw (atom "b"))

/-- The protected goal is cut-opaque: its cut cannot remove the caller's older
right disjunct. -/
def guardedCutRetainsCaller : SourceSignature.Goal :=
  .disj
    (.catch
      (.conj (.unify x (atom "a")) (.conj .cut .fail))
      (atom "never") .succeed)
    (.unify x (atom "c"))

/-- Recovery is also cut-opaque and returns to the caller's cut scope only
after its own frame completes. -/
def recoveryCutRetainsCaller : SourceSignature.Goal :=
  .disj
    (.catch (.throw (atom "a")) (atom "a") (.conj .cut .fail))
    (.unify x (atom "c"))

/-- Ordinary answers retain the catch frame on the saved right branch, so
backtracking re-enters the protected goal rather than skipping the delimiter. -/
def catchRetainsGuardedAnswers : SourceSignature.Goal :=
  .catch
    (.disj (.unify x (atom "a")) (.unify x (atom "b")))
    (atom "never") .fail

/-- An inner mismatch must not erase throw-time bindings before an outer
catcher is tested.  SWI tests every candidate against the original throw-time
state before performing the selected unwind. -/
def nestedMismatchRetainsThrowTimeBinding : SourceSignature.Goal :=
  .catch
    (.catch
      (.conj (.unify x (atom "body")) (.throw (atom "ball")))
      (atom "nope") .fail)
    x .succeed

/-- The copied packet variable is fresh relative to the caller's original
`Y`; binding the catcher in recovery cannot bind that original variable. -/
def packetCopySeparatesCaller : SourceSignature.Goal :=
  .catch (.throw (compound "box" [y])) (compound "box" [x])
    (.conj (.unify x (atom "a")) (.isVar y))

/-- Known conformance boundary: SWI raises `instantiation_error` for a bare
variable ball, while the current finite-packet transition accepts it.  This
canary is intentionally paired with the expected-divergence gate. -/
def throwVariableCurrentlyAccepted : SourceSignature.Goal :=
  .catch (.throw y) x
    (.conj (.unify x (atom "a")) (.isVar y))

/-- One repeated packet variable remains shared after capture, freshening, and
reinstallation, so incompatible recovery bindings fail. -/
def packetCopyPreservesSharing : SourceSignature.Goal :=
  .catch (.throw (pair y y)) (pair leftVar rightVar)
    (.conj (.unify leftVar (atom "a"))
      (.unify rightVar (atom "b")))

/-- Distinct packet variables do not collapse during copying. -/
def packetCopyPreservesSeparation : SourceSignature.Goal :=
  .catch (.throw (pair y z)) (pair leftVar rightVar)
    (.conj (.unify leftVar (atom "a"))
      (.unify rightVar (atom "b")))

#guard runAtoms [] dynamicDisjunction == some (["a", "b"], 0, 0)
#guard runAtoms [] metaCutRetainsCaller == some (["c"], 0, 0)
#guard runCount binaryFactProgram callThree == some (1, 0, 0)
#guard runCount binaryFactProgram heapBuiltCallable == some (1, 0, 0)
#guard runAtoms [] caughtGround == some (["ball"], 0, 0)
#guard runRaisedAtom [] throwTimeBoundCatcherRejects == some ("ball", 0, 0)
#guard runRaisedAtom [] recoveryRethrowEscapes == some ("b", 0, 0)
#guard runAtoms [] guardedCutRetainsCaller == some (["c"], 0, 0)
#guard runAtoms [] recoveryCutRetainsCaller == some (["c"], 0, 0)
#guard runAtoms [] catchRetainsGuardedAnswers == some (["a", "b"], 0, 0)
#guard runRaisedAtom [] nestedMismatchRetainsThrowTimeBinding ==
  some ("ball", 0, 0)
#guard runCount [] packetCopySeparatesCaller == some (1, 0, 0)
#guard runCount [] packetCopyPreservesSharing == some (0, 0, 0)
#guard runCount [] packetCopyPreservesSeparation == some (1, 0, 0)
#guard runCount [] throwVariableCurrentlyAccepted == some (1, 0, 0)

end Mettapedia.Logic.Prolog.SourceRuntimeRegression
