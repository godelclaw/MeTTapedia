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
def bagVar : SourceSignature.Term := var "Bag" 0
def innerVar : SourceSignature.Term := var "Inner" 0
def outerVar : SourceSignature.Term := var "Outer" 0

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

private def answerTermFor? (identity : SourceSignature.Variable)
    (answer : LP.RuntimeQuery.Answer Sigma) : Option (LP.Term Sigma.scoped) :=
  match answer.queryVarMap.find? fun entry =>
      decide (entry.1 = LP.ScopedVar.at 0 identity) with
  | none => none
  | some (_, address) =>
      match LP.RuntimeReadback.Heap.readTerm answer.memory.heap address with
      | .ok term => some term
      | .error _ => none

def collectTermsFor : Nat → SourceSignature.Variable → Session →
    Option (List (LP.Term Sigma.scoped) × Nat × Nat)
  | 0, _, _ => none
  | budget + 1, identity, session =>
      match SourceRuntime.pullSession 512 session with
      | .open _ => none
      | .terminal (.completed memory) =>
          some ([], memory.heap.size, memory.trail.size)
      | .terminal (.runtimeError _ _) => none
      | .terminal (.raised _ _) => none
      | .answer answer resumed =>
          match answerTermFor? identity answer,
              collectTermsFor budget identity resumed with
          | some value, some (rest, heapSize, trailSize) =>
              some (value :: rest, heapSize, trailSize)
          | _, _ => none

def runTermsFor (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) (identity : SourceSignature.Variable) :
    Option (List (LP.Term Sigma.scoped) × Nat × Nat) :=
  match SourceRuntime.openEmpty program goal with
  | .error _ => none
  | .ok session => collectTermsFor 8 identity session

/-- Finite, executable observation of the dependent runtime term used only by
these source-runtime regressions. -/
inductive RuntimeTermShape where
  | variable (scope : Nat) (spelling : String) (occurrence : Nat)
  | atom (name : String)
  | integer (value : Int)
  | floatBits (bits : UInt64)
  | string (value : String)
  | compound (name : String) (arguments : List RuntimeTermShape)
deriving BEq, Repr

def runtimeTermShape : LP.Term Sigma.scoped → RuntimeTermShape
  | .var identity =>
      .variable identity.scope identity.name.spelling identity.name.occurrence
  | .const (.atom name) => .atom name
  | .const (.integer value) => .integer value
  | .const (.floatBits bits) => .floatBits bits
  | .const (.string value) => .string value
  | .app indicator arguments =>
      .compound indicator.name
        (List.ofFn fun index => runtimeTermShape (arguments index))

def RuntimeTermShape.listElements? : RuntimeTermShape →
    Option (List RuntimeTermShape)
  | .atom "[]" => some []
  | .compound "[|]" [head, tail] => do
      let rest ← tail.listElements?
      pure (head :: rest)
  | _ => none

def RuntimeTermShape.atomList? (shape : RuntimeTermShape) :
    Option (List String) := do
  let elements ← shape.listElements?
  elements.mapM fun element =>
    match element with
    | .atom name => some name
    | _ => none

def runAtomBagsFor (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) (identity : SourceSignature.Variable) :
    Option (List (List String) × Nat × Nat) := do
  let (terms, heapSize, trailSize) ← runTermsFor program goal identity
  let bags ← terms.mapM fun term => (runtimeTermShape term).atomList?
  pure (bags, heapSize, trailSize)

def runShapesFor (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) (identity : SourceSignature.Variable) :
    Option (List RuntimeTermShape × Nat × Nat) := do
  let (terms, heapSize, trailSize) ← runTermsFor program goal identity
  pure (terms.map runtimeTermShape, heapSize, trailSize)

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

/-! ## Private answer collection on the shared choice stack -/

def bagIdentity : SourceSignature.Variable := { spelling := "Bag", occurrence := 0 }
def outerIdentity : SourceSignature.Variable := { spelling := "Outer", occurrence := 0 }

def expectedScoped (term : SourceSignature.Term) : LP.Term Sigma.scoped :=
  LP.Term.atScope 0 term

/-- The collector reverses its private accumulator exactly once, preserving
DFS order and multiplicity. -/
def findallOrderMultiplicity : SourceSignature.Goal :=
  .findall x
    (.disj (.unify x (atom "a"))
      (.disj (.unify x (atom "b")) (.unify x (atom "a"))))
    bagVar

/-- Generator bindings are backtrack-local: only the copied bag crosses the
delimiter, while the original template variable remains unbound. -/
def findallIsolatesGeneratorBindings : SourceSignature.Goal :=
  .conj (.findall x (.unify x (atom "a")) bagVar) (.isVar x)

/-- Exhausting a failing generator succeeds once with the empty list. -/
def findallEmpty : SourceSignature.Goal :=
  .findall x .fail bagVar

/-- A generator cut prunes only generator-local alternatives.  It cannot
remove the caller's right disjunct. -/
def findallCutRetainsCaller : SourceSignature.Goal :=
  .disj
    (.findall x
      (.disj (.conj (.unify x (atom "a")) .cut)
        (.unify x (atom "b")))
      bagVar)
    (.unify bagVar (SourceSignature.list [atom "c"]))

/-- An exception escapes the collector and discards the partial bag; recovery
sees the caller's entry binding state. -/
def findallExceptionDiscardsPartialBag : SourceSignature.Goal :=
  .catch
    (.findall x
      (.disj (.unify x (atom "a")) (.throw (atom "ball")))
      bagVar)
    (atom "ball")
    (.unify bagVar (SourceSignature.list [atom "caught"]))

/-- Nested collectors use distinct sentinels and preserve the inner bag as one
ordinary outer solution. -/
def nestedFindall : SourceSignature.Goal :=
  .findall innerVar
    (.findall x
      (.disj (.unify x (atom "a")) (.unify x (atom "b")))
      innerVar)
    outerVar

private def repeatedPairVariables? (term : LP.Term Sigma.scoped) :
    Option (LP.ScopedVar SourceSignature.Variable ×
      LP.ScopedVar SourceSignature.Variable) :=
  match term with
  | .app symbol arguments =>
      match symbol.name, List.ofFn arguments with
      | "[|]", [first, tail] =>
          match first, tail with
          | .app firstSymbol firstArguments, .app consSymbol consArguments =>
              match firstSymbol.name, List.ofFn firstArguments,
                  consSymbol.name, List.ofFn consArguments with
              | "pair", [.var firstLeft, .var firstRight], "[|]", [second, nil] =>
                  match second, nil with
                  | .app secondSymbol secondArguments, .const (.atom "[]") =>
                      match secondSymbol.name, List.ofFn secondArguments with
                      | "pair", [.var secondLeft, .var secondRight] =>
                          if firstLeft = firstRight && secondLeft = secondRight &&
                              firstLeft != secondLeft then
                            some (firstLeft, secondLeft)
                          else none
                      | _, _ => none
                  | _, _ => none
              | _, _, _, _ => none
          | _, _ => none
      | _, _ => none
  | _ => none

private def oneSeparatedPair? (term : LP.Term Sigma.scoped) : Bool :=
  match term with
  | .app consSymbol consArguments =>
      match consSymbol.name, List.ofFn consArguments with
      | "[|]", [pairTerm, .const (.atom "[]")] =>
          match pairTerm with
          | .app pairSymbol pairArguments =>
              match pairSymbol.name, List.ofFn pairArguments with
              | "pair", [.var left, .var right] => left != right
              | _, _ => false
          | _ => false
      | _, _ => false
  | _ => false

/-- Every solution copies its template at the current persistent high-water:
sharing is preserved within a solution and separated between solutions. -/
def findallCopiesPerSolution : SourceSignature.Goal :=
  .findall (pair y y) (.disj .succeed .succeed) bagVar

def copiedSolutionsAreFreshAndShared : Bool :=
  match runTermsFor [] findallCopiesPerSolution bagIdentity with
  | some ([term], 0, 0) => (repeatedPairVariables? term).isSome
  | _ => false

/-- Distinct residual variables in one template remain distinct in its copy. -/
def findallCopyPreservesSeparation : SourceSignature.Goal :=
  .findall (pair y z) .succeed bagVar

def copiedSolutionPreservesSeparation : Bool :=
  match runTermsFor [] findallCopyPreservesSeparation bagIdentity with
  | some ([term], 0, 0) => oneSeparatedPair? term
  | _ => false

def answerThenLoopProgram : SourceSignature.Program := [
  fact "answer_then_loop" [atom "a"],
  {
    head := predicate "answer_then_loop" [x]
    body := SourceSignature.call "answer_then_loop" [x]
  }
]

def findallAnswerThenLoop : SourceSignature.Goal :=
  .findall x (SourceSignature.call "answer_then_loop" [x]) bagVar

private def collectionAnswerCount :
    List (LP.RuntimeQuery.ChoicePointCore Sigma
      (RuntimeControl.RuntimeGoal Sigma.scoped) SourceSignature.Clause) → Nat
  | [] => 0
  | .collection boundary :: _ => boundary.reversed.length
  | _ :: older => collectionAnswerCount older

/-- Suppressed generator answers remain real machine progress steps.  A
left-recursive generator therefore yields an open finite prefix with a growing
private bag, never a fabricated public answer or completion. -/
def findallAnswerThenLoopHasOpenPrivatePrefix : Bool :=
  match SourceRuntime.openEmpty answerThenLoopProgram findallAnswerThenLoop with
  | .error _ => false
  | .ok session =>
      match SourceRuntime.pullSession 512 session with
      | .open resumed => collectionAnswerCount resumed.state.choices > 0
      | _ => false

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

/-- A bare variable ball raises SWI's exact `throw/1` instantiation-error
shape.  Recovery also verifies that unwinding did not bind the caller's
original variable. -/
def throwVariableRaisesInstantiationError : SourceSignature.Goal :=
  let catcher := compound "error" [
    atom "instantiation_error",
    compound "context" [
      compound ":" [atom "system", compound "/" [atom "throw", integer 1]],
      z
    ]
  ]
  .catch (.throw y) catcher (.isVar y)

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
#guard runCount [] throwVariableRaisesInstantiationError == some (1, 0, 0)
#guard runShapesFor [] findallOrderMultiplicity bagIdentity ==
  some ([runtimeTermShape
    (expectedScoped (SourceSignature.list [atom "a", atom "b", atom "a"]))],
    0, 0)
#guard runShapesFor [] findallIsolatesGeneratorBindings bagIdentity ==
  some ([runtimeTermShape
    (expectedScoped (SourceSignature.list [atom "a"]))], 0, 0)
#guard runShapesFor [] findallEmpty bagIdentity ==
  some ([runtimeTermShape (expectedScoped SourceSignature.nil)], 0, 0)
#guard runShapesFor [] findallCutRetainsCaller bagIdentity ==
  some ([runtimeTermShape (expectedScoped (SourceSignature.list [atom "a"])),
    runtimeTermShape (expectedScoped (SourceSignature.list [atom "c"]))], 0, 0)
#guard runShapesFor [] findallExceptionDiscardsPartialBag bagIdentity ==
  some ([runtimeTermShape
    (expectedScoped (SourceSignature.list [atom "caught"]))], 0, 0)
#guard runShapesFor [] nestedFindall outerIdentity ==
  some ([runtimeTermShape (expectedScoped
    (SourceSignature.list [SourceSignature.list [atom "a", atom "b"]]))], 0, 0)
#guard copiedSolutionsAreFreshAndShared
#guard copiedSolutionPreservesSeparation
#guard findallAnswerThenLoopHasOpenPrivatePrefix

end Mettapedia.Logic.Prolog.SourceRuntimeRegression
