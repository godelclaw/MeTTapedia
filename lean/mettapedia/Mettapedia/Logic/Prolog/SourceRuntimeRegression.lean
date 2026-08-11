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

def equality (left right : SourceSignature.Term) : SourceSignature.Term :=
  compound "=" [left, right]

def conjunction (left right : SourceSignature.Term) : SourceSignature.Term :=
  compound "," [left, right]

def disjunction (left right : SourceSignature.Term) : SourceSignature.Term :=
  compound ";" [left, right]

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

#guard runAtoms [] dynamicDisjunction == some (["a", "b"], 0, 0)
#guard runAtoms [] metaCutRetainsCaller == some (["c"], 0, 0)
#guard runCount binaryFactProgram callThree == some (1, 0, 0)
#guard runCount binaryFactProgram heapBuiltCallable == some (1, 0, 0)

end Mettapedia.Logic.Prolog.SourceRuntimeRegression
