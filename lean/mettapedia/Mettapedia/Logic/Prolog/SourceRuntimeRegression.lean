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
def referenceVar : SourceSignature.Term := var "Reference" 0
def otherReferenceVar : SourceSignature.Term := var "OtherReference" 0

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
      | .terminal (.completed memory) _ =>
          some ([], memory.heap.size, memory.trail.size)
      | .terminal (.runtimeError _ _) _ => none
      | .terminal (.raised _ _) _ => none
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
      | .terminal (.completed memory) _ =>
          some (count, memory.heap.size, memory.trail.size)
      | .terminal (.runtimeError _ _) _ => none
      | .terminal (.raised _ _) _ => none
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
      | .terminal (.completed memory) _ =>
          some ([], memory.heap.size, memory.trail.size)
      | .terminal (.runtimeError _ _) _ => none
      | .terminal (.raised _ _) _ => none
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
  | clauseReference (reference : Nat)
  | compound (name : String) (arguments : List RuntimeTermShape)
deriving BEq, Repr

def runtimeTermShape : LP.Term Sigma.scoped → RuntimeTermShape
  | .var identity =>
      .variable identity.scope identity.name.spelling identity.name.occurrence
  | .const (.atom name) => .atom name
  | .const (.integer value) => .integer value
  | .const (.floatBits bits) => .floatBits bits
  | .const (.string value) => .string value
  | .const (.clauseReference reference) => .clauseReference reference
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

def runAtomsFor (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) (identity : SourceSignature.Variable) :
    Option (List String × Nat × Nat) := do
  let (terms, heapSize, trailSize) ← runTermsFor program goal identity
  let atoms ← terms.mapM fun term =>
    match term with
    | .const (.atom name) => some name
    | _ => none
  pure (atoms, heapSize, trailSize)

def runIntegersFor (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) (identity : SourceSignature.Variable) :
    Option (List Int × Nat × Nat) := do
  let (terms, heapSize, trailSize) ← runTermsFor program goal identity
  let integers ← terms.mapM fun term =>
    match term with
    | .const (.integer value) => some value
    | _ => none
  pure (integers, heapSize, trailSize)

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
      | .terminal (.raised packet memory) _ =>
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

/-! ## Derived negation and non-unifiability on shared hard-if checkpoints -/

def negationRejectsSuccess : SourceSignature.Goal := .neg .succeed

def negationAcceptsFailure : SourceSignature.Goal := .neg .fail

/-- Bindings made by a failing negated goal are restored before its success
continuation runs. -/
def negationRestoresTrialBindings : SourceSignature.Goal :=
  .conj (.neg (.conj (.unify x (atom "a")) .fail))
    (.conj (.isVar x) (.unify x (atom "b")))

/-- A cut inside the protected negated goal cannot prune the caller's older
disjunction alternative. -/
def negationCutRetainsCaller : SourceSignature.Goal :=
  .disj (.neg (.conj .cut .succeed)) (.unify x (atom "c"))

def distinctAtomsAreNotUnifiable : SourceSignature.Goal :=
  .notUnify (atom "a") (atom "b")

def variableAndAtomAreUnifiable : SourceSignature.Goal :=
  .notUnify x (atom "a")

/-- A failed `\=/2` trial restores its temporary binding before the caller's
right alternative is entered. -/
def notUnifyRestoresTrialBindings : SourceSignature.Goal :=
  .disj (.notUnify x (atom "a"))
    (.conj (.isVar x) (.unify x (atom "b")))

/-- These use heap-built callables, pinning the same derived expansion in the
read-only dynamic meta-call decoder rather than only in source classification. -/
def metaNonvarBound : SourceSignature.Goal :=
  metaGoal (compound "nonvar" [atom "a"])

def metaNonvarVariable : SourceSignature.Goal :=
  metaGoal (compound "nonvar" [x])

def metaForallSucceeds : SourceSignature.Goal :=
  metaGoal (compound "forall" [
    disjunction (equality x (atom "a")) (equality x (atom "b")),
    compound "\\=" [x, atom "c"]
  ])

def metaForallFails : SourceSignature.Goal :=
  metaGoal (compound "forall" [
    disjunction (equality x (atom "a")) (equality x (atom "b")),
    equality x (atom "a")
  ])

def metaForallRestoresBindings : SourceSignature.Goal :=
  .conj
    (metaGoal (compound "forall" [equality x (atom "a"), atom "true"]))
    (.conj (.isVar x) (.unify x (atom "c")))

/-! ## Shallow source-term tests through engine-owned dereference -/

def atomAcceptsAtom : SourceSignature.Goal :=
  SourceSignature.call "atom" [atom "a"]

def atomRejectsInteger : SourceSignature.Goal :=
  SourceSignature.call "atom" [integer 1]

def atomRejectsListNil : SourceSignature.Goal :=
  SourceSignature.call "atom" [SourceSignature.nil]

def atomicAcceptsString : SourceSignature.Goal :=
  SourceSignature.call "atomic" [string "a"]

def atomicRejectsCompound : SourceSignature.Goal :=
  SourceSignature.call "atomic" [pair (atom "a") (atom "b")]

def compoundAcceptsPair : SourceSignature.Goal :=
  SourceSignature.call "compound" [pair (atom "a") (atom "b")]

def compoundRejectsAtom : SourceSignature.Goal :=
  SourceSignature.call "compound" [atom "a"]

def numberAcceptsInteger : SourceSignature.Goal :=
  SourceSignature.call "number" [integer 1]

def numberAcceptsFloat : SourceSignature.Goal :=
  SourceSignature.call "number" [floatBits 0]

def numberRejectsAtom : SourceSignature.Goal :=
  SourceSignature.call "number" [atom "a"]

def stringAcceptsString : SourceSignature.Goal :=
  SourceSignature.call "string" [string "a"]

def stringRejectsAtom : SourceSignature.Goal :=
  SourceSignature.call "string" [atom "a"]

/-! ## Cycle-safe graph groundness -/

def groundTest (term : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "ground" [term]

def groundAcceptsCompound : SourceSignature.Goal :=
  groundTest (pair (atom "a") (SourceSignature.list [integer 1, atom "b"]))

def groundRejectsVariable : SourceSignature.Goal := groundTest x

def groundRejectsNestedVariable : SourceSignature.Goal :=
  groundTest (pair (atom "a") x)

def groundAcceptsRationalCompound : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x])) (groundTest x)

def groundRejectsRationalCompoundWithFreeLeaf : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x, y])) (groundTest x)

/-- A heap-built meta-call returns to the same source service rather than
using a second dynamic classification path. -/
def metaAtomAcceptsAtom : SourceSignature.Goal :=
  metaGoal (compound "atom" [atom "a"])

/-- Stable clause references are atomic runtime values but not source atoms,
matching SWI's opaque reference classification without making them forgeable. -/
def referenceIsAtomicButNotAtom : SourceSignature.Goal :=
  .conj
    (SourceSignature.call "assertz"
      [compound "p" [atom "a"], referenceVar])
    (.conj
      (SourceSignature.call "atomic" [referenceVar])
      (.neg (SourceSignature.call "atom" [referenceVar])))

/-! ## Read-only strict graph identity -/

def strictIdentity (left right : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "==" [left, right]

def strictNonIdentity (left right : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "\\==" [left, right]

def identitySameVariable : SourceSignature.Goal := strictIdentity x x

def identityDistinctVariables : SourceSignature.Goal := strictIdentity x y

def nonIdentityDistinctVariables : SourceSignature.Goal :=
  strictNonIdentity x y

def identitySeparateCompounds : SourceSignature.Goal :=
  strictIdentity (pair (atom "a") (atom "b"))
    (pair (atom "a") (atom "b"))

def identityDifferentCompounds : SourceSignature.Goal :=
  strictIdentity (pair (atom "a") (atom "b"))
    (pair (atom "a") (atom "c"))

def identityDistinguishesVariableSharing : SourceSignature.Goal :=
  strictIdentity (pair x x) (pair y z)

def identityEqualRationalCycles : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x]))
    (.conj (.unify y (compound "f" [y])) (strictIdentity x y))

def identityDifferentRationalCycles : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x]))
    (.conj (.unify y (compound "g" [y])) (strictIdentity x y))

/-- A failed identity test performs no trial binding before the caller's right
alternative; the old variable remains visibly unbound. -/
def identityFailureDoesNotBind : SourceSignature.Goal :=
  .disj (strictIdentity x (atom "a"))
    (.conj (.isVar x) (.unify x (atom "b")))

def metaIdentitySameVariable : SourceSignature.Goal :=
  metaGoal (compound "==" [x, x])

def identityDistinguishesNumericTypes : SourceSignature.Goal :=
  strictIdentity (integer 1) (floatBits 0)

def identityEqualStrings : SourceSignature.Goal :=
  strictIdentity (string "a") (string "a")

def identityAtomNotZeroArityCompound : SourceSignature.Goal :=
  strictIdentity (atom "f") (compound "f" [])

def nonIdentityDifferentCompounds : SourceSignature.Goal :=
  strictNonIdentity (pair (atom "a") (atom "b"))
    (pair (atom "a") (atom "c"))

/-! ## `=../2` on the shared heap -/

def univ (term list : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "=.." [term, list]

def univDecomposesCompound : SourceSignature.Goal :=
  univ (pair (atom "a") (atom "b")) x

def univConstructsCompound : SourceSignature.Goal :=
  univ x (SourceSignature.list [atom "pair", atom "a", atom "b"])

def univDecomposesAtom : SourceSignature.Goal :=
  univ (atom "a") x

def univConstructsAtom : SourceSignature.Goal :=
  univ x (SourceSignature.list [atom "a"])

def univDecomposesInteger : SourceSignature.Goal :=
  univ (integer 1) x

/-- Construction reuses list-element roots: repeated variables remain the
same variable inside the newly allocated application. -/
def univConstructionPreservesSharing : SourceSignature.Goal :=
  .conj
    (univ x (SourceSignature.list [atom "pair", y, y]))
    (.conj (.unify x (pair leftVar rightVar))
      (strictIdentity leftVar rightVar))

/-- Decomposition reuses application-argument roots: one repeated argument
is not copied into two fresh variables in the result list. -/
def univDecompositionPreservesSharing : SourceSignature.Goal :=
  .conj
    (univ (pair y y)
      (SourceSignature.list [atom "pair", leftVar, rightVar]))
    (strictIdentity leftVar rightVar)

/-- A heap-built meta-call reaches the same source service and shared engine
operation as a statically present `=../2` call. -/
def metaUnivConstructsCompound : SourceSignature.Goal :=
  metaGoal (compound "=.."
    [x, SourceSignature.list [atom "pair", atom "a", atom "b"]])

def univUnboundList : SourceSignature.Goal := univ x y

def univEmptyList : SourceSignature.Goal :=
  univ x SourceSignature.nil

def univUnboundFunctor : SourceSignature.Goal :=
  univ x (SourceSignature.list [y, atom "a"])

def univNonAtomFunctor : SourceSignature.Goal :=
  univ x (SourceSignature.list [integer 1, atom "a"])

def univExplicitZeroArityCompound : SourceSignature.Goal :=
  univ (compound "f" []) x

/-- Observe a typed runtime error without identifying ordinary Prolog
failure with an engine-side malformed-operation result. -/
def runQueryError? (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) : Option LP.RuntimeQuery.QueryError :=
  match SourceRuntime.openEmpty program goal with
  | .error error => some error
  | .ok session =>
      match SourceRuntime.pullSession 512 session with
      | .terminal (.runtimeError error _) _ => some error
      | _ => none

def univRejectsUnboundList : Bool :=
  match runQueryError? [] univUnboundList with
  | some .univListUnbound => true
  | _ => false

def univRejectsEmptyList : Bool :=
  match runQueryError? [] univEmptyList with
  | some .invalidUnivList => true
  | _ => false

def univRejectsUnboundFunctor : Bool :=
  match runQueryError? [] univUnboundFunctor with
  | some .univFunctorUnbound => true
  | _ => false

def univRejectsNonAtomFunctor : Bool :=
  match runQueryError? [] univNonAtomFunctor with
  | some .invalidUnivFunctor => true
  | _ => false

def univRejectsExplicitZeroArityCompound : Bool :=
  match runQueryError? [] univExplicitZeroArityCompound with
  | some .invalidUnivFunctor => true
  | _ => false

/-! ## Unbounded integer arithmetic on the shared heap -/

def arithmetic (name : String) (arguments : List SourceSignature.Term) :
    SourceSignature.Term := compound name arguments

def integerIs (result expression : SourceSignature.Term) :
    SourceSignature.Goal := SourceSignature.call "is" [result, expression]

def integerComparison (name : String) (left right : SourceSignature.Term) :
    SourceSignature.Goal := SourceSignature.call name [left, right]

def integerAddition : SourceSignature.Goal :=
  integerIs x (arithmetic "+" [integer 2, integer 3])

def integerNestedArithmetic : SourceSignature.Goal :=
  integerIs x (arithmetic "*"
    [arithmetic "+" [integer 2, integer 3], integer 4])

def integerSubtraction : SourceSignature.Goal :=
  integerIs x (arithmetic "-" [integer 3, integer 5])

def integerModuloNegativeDividend : SourceSignature.Goal :=
  integerIs x (arithmetic "mod" [integer (-5), integer 3])

def integerModuloNegativeDivisor : SourceSignature.Goal :=
  integerIs x (arithmetic "mod" [integer 5, integer (-3)])

def integerIsMismatchFails : SourceSignature.Goal :=
  integerIs (integer 4) (arithmetic "+" [integer 2, integer 3])

def integerComparisonsSucceed : SourceSignature.Goal :=
  .conj (integerComparison "<" (integer 1) (integer 2))
    (.conj (integerComparison "=<" (integer 2) (integer 2))
      (.conj (integerComparison ">" (integer 3) (integer 2))
        (.conj (integerComparison ">=" (integer 3) (integer 3))
          (.conj (integerComparison "=:="
            (arithmetic "+" [integer 2, integer 3]) (integer 5))
            (integerComparison "=\\=" (integer 5) (integer 6))))))

def integerComparisonFailureRetainsCaller : SourceSignature.Goal :=
  .disj (integerComparison "<" (integer 2) (integer 1))
    (.unify x (atom "b"))

def metaIntegerAddition : SourceSignature.Goal :=
  metaGoal (compound "is"
    [x, arithmetic "+" [integer 2, integer 3]])

def integerArithmeticUnbound : SourceSignature.Goal := integerIs x y

def integerArithmeticFloatOperand : SourceSignature.Goal :=
  integerIs x (floatBits 0)

def integerArithmeticUnsupportedExpression : SourceSignature.Goal :=
  integerIs x (arithmetic "/" [integer 4, integer 2])

def integerArithmeticZeroDivisorExpression : SourceSignature.Goal :=
  integerIs x (arithmetic "mod" [integer 4, integer 0])

def integerArithmeticRejectsUnbound : Bool :=
  match runQueryError? [] integerArithmeticUnbound with
  | some .arithmeticOperandUnbound => true
  | _ => false

def integerArithmeticRejectsFloat : Bool :=
  match runQueryError? [] integerArithmeticFloatOperand with
  | some .invalidArithmeticOperand => true
  | _ => false

def integerArithmeticRejectsUnsupported : Bool :=
  match runQueryError? [] integerArithmeticUnsupportedExpression with
  | some .unsupportedArithmeticFunction => true
  | _ => false

def integerArithmeticRejectsZeroDivisor : Bool :=
  match runQueryError? [] integerArithmeticZeroDivisorExpression with
  | some .arithmeticZeroDivisor => true
  | _ => false

def binaryFactProgram : SourceSignature.Program :=
  [fact "p" [atom "a", atom "b"]]

/-! ## Private answer collection on the shared choice stack -/

def bagIdentity : SourceSignature.Variable := { spelling := "Bag", occurrence := 0 }
def outerIdentity : SourceSignature.Variable := { spelling := "Outer", occurrence := 0 }
def xIdentity : SourceSignature.Variable := { spelling := "X", occurrence := 0 }
def yIdentity : SourceSignature.Variable := { spelling := "Y", occurrence := 0 }

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

/-! ## Persistent dynamic database through the shared session handler -/

def assertedP (value : String) : SourceSignature.Term :=
  compound "p" [atom value]

def assertedRuleP (value : String) : SourceSignature.Term :=
  compound ":-" [assertedP value, compound "q" [atom value]]

def assertzGoal (clause : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "assertz" [clause]

def assertaGoal (clause : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "asserta" [clause]

def assertzWithReferenceGoal (clause reference : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "assertz" [clause, reference]

def assertaWithReferenceGoal (clause reference : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "asserta" [clause, reference]

def retractGoal (clause : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "retract" [clause]

def clauseGoal (head body reference : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "clause" [head, body, reference]

def assertzThenCall : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (SourceSignature.call "p" [x])

/-- The assertion occurs in a branch that fails and is backtracked over.  The
right branch and later call can observe it only if the database is persistent
rather than stored in a choice checkpoint. -/
def failedBranchAssertionPersists : SourceSignature.Goal :=
  .conj
    (.disj (.conj (assertzGoal (assertedP "a")) .fail) .succeed)
    (SourceSignature.call "p" [x])

def assertaAndAssertzOrder : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "b"))
    (.conj (assertaGoal (assertedP "a"))
      (SourceSignature.call "p" [x]))

/-- `assertz/2` binds its fresh output through the canonical graph unifier to
an opaque stable occurrence identity. -/
def assertzReferenceIsBound : SourceSignature.Goal :=
  .conj (assertzWithReferenceGoal (assertedP "a") referenceVar)
    (.ifThenElse (.isVar referenceVar) .fail .succeed)

/-- The front-insertion form exposes the same kind of opaque identity. -/
def assertaReferenceIsBound : SourceSignature.Goal :=
  .conj (assertaWithReferenceGoal (assertedP "a") referenceVar)
    (.ifThenElse (.isVar referenceVar) .fail .succeed)

/-- Stable occurrence identities are never reused for two insertions. -/
def assertedReferencesAreDistinct : SourceSignature.Goal :=
  .conj (assertzWithReferenceGoal (assertedP "a") referenceVar)
    (.conj
      (assertzWithReferenceGoal (assertedP "b") otherReferenceVar)
      (.ifThenElse (.unify referenceVar otherReferenceVar) .fail .succeed))

/-- The opaque identity remains ordinary Prolog data: a later asserted fact
can store it and canonical clause execution reads back the same value. -/
def assertedReferenceRoundTrip : SourceSignature.Goal :=
  .conj (assertzWithReferenceGoal (assertedP "a") referenceVar)
    (.conj (assertzGoal (compound "saved" [referenceVar]))
      (SourceSignature.call "saved" [otherReferenceVar]))

/-- The second argument is output-only.  A bound value is rejected by the
shared engine before the session can advance the persistent database. -/
def preboundAssertReferenceRejectedBeforeInsert : Bool :=
  match SourceRuntime.openEmpty []
      (assertzWithReferenceGoal (assertedP "a") (atom "forged")) with
  | .error _ => false
  | .ok session =>
      match SourceRuntime.pullSession 256 session with
      | .terminal
          (.runtimeError (.databaseReferenceOutputNotVariable) memory)
          database =>
          memory.heap.size == 0 && memory.trail.size == 0 &&
            database.generation == 0 && database.visibleClauses.isEmpty
      | _ => false

/-- `retract/1` is nondeterministic over the call-time clause snapshot and
uses the shared leftmost choice stack, so matching occurrences are erased and
reported in source order. -/
def retractFactsInOrder : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (retractGoal (compound "p" [x])))

/-- The retained retract cursor is an ordinary shared-engine choice point.
A cut after the first match therefore prunes the second candidate. -/
def retractCutPrunesLater : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (.conj (retractGoal (compound "p" [x])) .cut))

/-- A head-only retract pattern denotes `Head :- true`: it skips a
same-headed non-fact rule and continues to the later matching fact. -/
def retractFactSkipsRule : SourceSignature.Goal :=
  .conj (assertzGoal (assertedRuleP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (retractGoal (compound "p" [x])))

/-- Clause erasure is persistent session state rather than part of a
backtrackable checkpoint: failing after deletion cannot resurrect `p(a)`. -/
def failedBranchRetractionPersists : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj
      (.disj
        (.conj (retractGoal (assertedP "a")) .fail)
        .succeed)
      (SourceSignature.call "p" [x]))

/-- The retract cursor is frozen before its first candidate is tried.  The
first candidate inserts `p(c)` and then fails; retry must advance to the
already-snapshotted `p(b)`, never drift onto the new occurrence. -/
def retractSnapshotGoal : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (.conj (retractGoal (compound "p" [x]))
        (.ifThenElse (.unify x (atom "a"))
          (.conj (assertzGoal (assertedP "c")) .fail)
          .succeed)))

/-- A later occurrence erased by a nested operation remains in the outer
call's frozen logical-update snapshot.  Its stable erase request becomes a
successful no-op, so the outer call still reports that one snapshotted match. -/
def retractSnapshotRetainsErasedCandidate : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (.conj (retractGoal (compound "p" [x]))
        (.ifThenElse (.unify x (atom "a"))
          (.conj (retractGoal (assertedP "b")) .fail)
          .succeed)))

/-- `clause/3` enumerates one immutable visible-clause snapshot in source
order. Facts expose `true` as their body and their opaque reference does not
alter the observed head binding. -/
def clauseFactsInOrder : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (clauseGoal (compound "p" [x]) (atom "true") referenceVar))

/-- A reference obtained from `assertz/2` can filter `clause/3`; source text
still has no constructor capable of forging that identity. -/
def clauseBoundReferenceSelectsOccurrence : SourceSignature.Goal :=
  .conj (assertzWithReferenceGoal (assertedP "a") referenceVar)
    (.conj (assertzWithReferenceGoal (assertedP "b") otherReferenceVar)
      (clauseGoal (compound "p" [x]) (atom "true") otherReferenceVar))

/-- Rule bodies are reflected separately from their heads, with the selected
clause standardized apart before the canonical graph unifier sees it. -/
def clauseRuleBody : SourceSignature.Goal :=
  .conj (assertzGoal (assertedRuleP "a"))
    (clauseGoal (assertedP "a") (compound "q" [y]) referenceVar)

/-- The retained read-only cursor is the same ordinary choice resource as a
retract cursor, so a following cut prunes later visible clauses. -/
def clauseCutPrunesLater : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (.conj
        (clauseGoal (compound "p" [x]) (atom "true") referenceVar)
        .cut))

/-- Clause inspection reports the exact stable identity allocated by
`assertz/2`, rather than an independently generated or position-derived one. -/
def clauseReferenceRoundTrip : SourceSignature.Goal :=
  .conj (assertzWithReferenceGoal (assertedP "a") referenceVar)
    (.conj
      (clauseGoal (assertedP "a") (atom "true") otherReferenceVar)
      (.unify referenceVar otherReferenceVar))

/-- A wholly variable head cannot be used as an unrestricted database
enumerator. It fails closed before a candidate cursor or binding is created. -/
def clauseVariableHeadRejected : Bool :=
  match SourceRuntime.openEmpty [] (clauseGoal x y referenceVar) with
  | .error _ => false
  | .ok session =>
      match SourceRuntime.pullSession 128 session with
      | .terminal (.runtimeError (.invalidDynamicClause) memory) database =>
          memory.heap.size == 0 && memory.trail.size == 0 &&
            database.generation == 0 && database.visibleClauses.isEmpty
      | _ => false

/-- The visible-clause list is frozen when `clause/3` opens. A clause asserted
after its first solution persists in the database but is not appended to this
already-live cursor. -/
def clauseSnapshotDoesNotDrift : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (.conj
        (clauseGoal (compound "p" [x]) (atom "true") referenceVar)
        (.ifThenElse (.unify x (atom "a"))
          (.conj (assertzGoal (assertedP "c")) .fail)
          .succeed)))

/-- A snapshotted occurrence remains inspectable once even if a nested
operation erases it before the outer cursor reaches it. -/
def clauseSnapshotRetainsErasedCandidate : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (.conj
        (clauseGoal (compound "p" [x]) (atom "true") referenceVar)
        (.ifThenElse (.unify x (atom "a"))
          (.conj (retractGoal (assertedP "b")) .fail)
          .succeed)))

def snapshotProgram : SourceSignature.Program := [
  fact "p" [atom "old"],
  {
    head := predicate "driver" []
    body := .conj (SourceSignature.call "p" [x])
      (.conj (assertzGoal (assertedP "new")) .fail)
  }
]

def collectCountDatabase : Nat → Nat → Session →
    Option (Nat × LP.RuntimeDatabase.Database SourceSignature.Clause)
  | 0, _, _ => none
  | budget + 1, count, session =>
      match SourceRuntime.pullSession 256 session with
      | .open _ => none
      | .answer _ next => collectCountDatabase budget (count + 1) next
      | .terminal (.runtimeError _ _) _ => none
      | .terminal (.raised _ _) _ => none
      | .terminal (.completed _) database => some (count, database)

def collectAtomsDatabase : Nat → Session →
    Option (List String × Nat × Nat ×
      LP.RuntimeDatabase.Database SourceSignature.Clause)
  | 0, _ => none
  | budget + 1, session =>
      match SourceRuntime.pullSession 256 session with
      | .open _ => none
      | .terminal (.runtimeError _ _) _ => none
      | .terminal (.raised _ _) _ => none
      | .terminal (.completed memory) database =>
          some ([], memory.heap.size, memory.trail.size, database)
      | .answer answer resumed =>
          match answerAtom? answer, collectAtomsDatabase budget resumed with
          | some value, some (rest, heapSize, trailSize, database) =>
              some (value :: rest, heapSize, trailSize, database)
          | _, _ => none

def retractSnapshotRun :
    Option (List String × Nat × Nat ×
      LP.RuntimeDatabase.Database SourceSignature.Clause) :=
  match SourceRuntime.openEmpty [] retractSnapshotGoal with
  | .error _ => none
  | .ok session => collectAtomsDatabase 8 session

/-- Snapshot isolation is observed both in the answer stream (`c` was not a
candidate) and in the final persistent database (`a` and `b` were erased;
the later assertion remains visible). -/
def retractSnapshotDoesNotDrift : Bool :=
  match retractSnapshotRun with
  | some (["b"], 0, 0, database) =>
      database.generation == 5 &&
      database.visibleClauses.filterMap
        (fun entry => ClauseReflection.reflect? entry.2 |>.map
          ClauseReflection.termCode) ==
          [ClauseReflection.termCode
            (ReaderSource.normalizedClauseTerm (assertedP "c") (atom "true"))]
  | _ => false

/-- An open `p/1` cursor was frozen before `p(new)` was asserted.  It reaches
no new answer, but the completed session still carries the advanced database.
-/
def snapshotRun :
    Option (Nat × LP.RuntimeDatabase.Database SourceSignature.Clause) :=
  match SourceRuntime.openEmpty snapshotProgram
      (SourceSignature.call "driver" []) with
  | .error _ => none
  | .ok session => collectCountDatabase 8 0 session

def snapshotDoesNotDrift : Bool :=
  match snapshotRun with
  | some (0, database) =>
      database.generation == 1 &&
      database.visibleClauses.map (fun entry => entry.2.head.symbol.name) ==
        ["p", "driver", "p"]
  | _ => false

def laterCallSeesAssertion :
    Option (List String × Nat × Nat) := do
  let (_, database) ← snapshotRun
  let session ← (SourceRuntime.openDatabase database
    (SourceSignature.call "p" [x])).toOption
  collectAtoms 8 session

#guard runAtoms [] dynamicDisjunction == some (["a", "b"], 0, 0)
#guard runAtoms [] metaCutRetainsCaller == some (["c"], 0, 0)
#guard runCount binaryFactProgram callThree == some (1, 0, 0)
#guard runCount binaryFactProgram heapBuiltCallable == some (1, 0, 0)
#guard runCount [] negationRejectsSuccess == some (0, 0, 0)
#guard runCount [] negationAcceptsFailure == some (1, 0, 0)
#guard runAtoms [] negationRestoresTrialBindings == some (["b"], 0, 0)
#guard runAtoms [] negationCutRetainsCaller == some (["c"], 0, 0)
#guard runCount [] distinctAtomsAreNotUnifiable == some (1, 0, 0)
#guard runCount [] variableAndAtomAreUnifiable == some (0, 0, 0)
#guard runAtoms [] notUnifyRestoresTrialBindings == some (["b"], 0, 0)
#guard runCount [] metaNonvarBound == some (1, 0, 0)
#guard runCount [] metaNonvarVariable == some (0, 0, 0)
#guard runCount [] metaForallSucceeds == some (1, 0, 0)
#guard runCount [] metaForallFails == some (0, 0, 0)
#guard runAtoms [] metaForallRestoresBindings == some (["c"], 0, 0)
#guard runCount [] atomAcceptsAtom == some (1, 0, 0)
#guard runCount [] atomRejectsInteger == some (0, 0, 0)
#guard runCount [] atomRejectsListNil == some (0, 0, 0)
#guard runCount [] atomicAcceptsString == some (1, 0, 0)
#guard runCount [] atomicRejectsCompound == some (0, 0, 0)
#guard runCount [] compoundAcceptsPair == some (1, 0, 0)
#guard runCount [] compoundRejectsAtom == some (0, 0, 0)
#guard runCount [] numberAcceptsInteger == some (1, 0, 0)
#guard runCount [] numberAcceptsFloat == some (1, 0, 0)
#guard runCount [] numberRejectsAtom == some (0, 0, 0)
#guard runCount [] stringAcceptsString == some (1, 0, 0)
#guard runCount [] stringRejectsAtom == some (0, 0, 0)
#guard runCount [] groundAcceptsCompound == some (1, 0, 0)
#guard runCount [] groundRejectsVariable == some (0, 0, 0)
#guard runCount [] groundRejectsNestedVariable == some (0, 0, 0)
#guard runCount [] groundAcceptsRationalCompound == some (1, 0, 0)
#guard runCount [] groundRejectsRationalCompoundWithFreeLeaf == some (0, 0, 0)
#guard runCount [] metaAtomAcceptsAtom == some (1, 0, 0)
#guard runCount [] referenceIsAtomicButNotAtom == some (1, 0, 0)
#guard runCount [] identitySameVariable == some (1, 0, 0)
#guard runCount [] identityDistinctVariables == some (0, 0, 0)
#guard runCount [] nonIdentityDistinctVariables == some (1, 0, 0)
#guard runCount [] identitySeparateCompounds == some (1, 0, 0)
#guard runCount [] identityDifferentCompounds == some (0, 0, 0)
#guard runCount [] identityDistinguishesVariableSharing == some (0, 0, 0)
#guard runCount [] identityEqualRationalCycles == some (1, 0, 0)
#guard runCount [] identityDifferentRationalCycles == some (0, 0, 0)
#guard runAtoms [] identityFailureDoesNotBind == some (["b"], 0, 0)
#guard runCount [] metaIdentitySameVariable == some (1, 0, 0)
#guard runCount [] identityDistinguishesNumericTypes == some (0, 0, 0)
#guard runCount [] identityEqualStrings == some (1, 0, 0)
#guard runCount [] identityAtomNotZeroArityCompound == some (0, 0, 0)
#guard runCount [] nonIdentityDifferentCompounds == some (1, 0, 0)
#guard runShapesFor [] univDecomposesCompound xIdentity ==
  some ([runtimeTermShape (expectedScoped
    (SourceSignature.list [atom "pair", atom "a", atom "b"]))], 0, 0)
#guard runShapesFor [] univConstructsCompound xIdentity ==
  some ([runtimeTermShape (expectedScoped
    (pair (atom "a") (atom "b")))], 0, 0)
#guard runShapesFor [] univDecomposesAtom xIdentity ==
  some ([runtimeTermShape (expectedScoped
    (SourceSignature.list [atom "a"]))], 0, 0)
#guard runShapesFor [] univConstructsAtom xIdentity ==
  some ([runtimeTermShape (expectedScoped (atom "a"))], 0, 0)
#guard runShapesFor [] univDecomposesInteger xIdentity ==
  some ([runtimeTermShape (expectedScoped
    (SourceSignature.list [integer 1]))], 0, 0)
#guard runCount [] univConstructionPreservesSharing == some (1, 0, 0)
#guard runCount [] univDecompositionPreservesSharing == some (1, 0, 0)
#guard runShapesFor [] metaUnivConstructsCompound xIdentity ==
  some ([runtimeTermShape (expectedScoped
    (pair (atom "a") (atom "b")))], 0, 0)
#guard univRejectsUnboundList
#guard univRejectsEmptyList
#guard univRejectsUnboundFunctor
#guard univRejectsNonAtomFunctor
#guard univRejectsExplicitZeroArityCompound
#guard runShapesFor [] integerAddition xIdentity ==
  some ([.integer 5], 0, 0)
#guard runShapesFor [] integerNestedArithmetic xIdentity ==
  some ([.integer 20], 0, 0)
#guard runShapesFor [] integerSubtraction xIdentity ==
  some ([.integer (-2)], 0, 0)
#guard runShapesFor [] integerModuloNegativeDividend xIdentity ==
  some ([.integer 1], 0, 0)
#guard runShapesFor [] integerModuloNegativeDivisor xIdentity ==
  some ([.integer (-1)], 0, 0)
#guard runCount [] integerIsMismatchFails == some (0, 0, 0)
#guard runCount [] integerComparisonsSucceed == some (1, 0, 0)
#guard runAtoms [] integerComparisonFailureRetainsCaller ==
  some (["b"], 0, 0)
#guard runShapesFor [] metaIntegerAddition xIdentity ==
  some ([.integer 5], 0, 0)
#guard integerArithmeticRejectsUnbound
#guard integerArithmeticRejectsFloat
#guard integerArithmeticRejectsUnsupported
#guard integerArithmeticRejectsZeroDivisor
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
#guard runAtoms [] assertzThenCall == some (["a"], 0, 0)
#guard runAtoms [] failedBranchAssertionPersists == some (["a"], 0, 0)
#guard runAtoms [] assertaAndAssertzOrder == some (["a", "b"], 0, 0)
#guard runCount [] assertzReferenceIsBound == some (1, 0, 0)
#guard runCount [] assertaReferenceIsBound == some (1, 0, 0)
#guard runCount [] assertedReferencesAreDistinct == some (1, 0, 0)
#guard runCount [] assertedReferenceRoundTrip == some (1, 0, 0)
#guard preboundAssertReferenceRejectedBeforeInsert
#guard runAtoms [] retractFactsInOrder == some (["a", "b"], 0, 0)
#guard runAtoms [] retractCutPrunesLater == some (["a"], 0, 0)
#guard runAtoms [] retractFactSkipsRule == some (["b"], 0, 0)
#guard runAtoms [] failedBranchRetractionPersists == some ([], 0, 0)
#guard runAtoms [] retractSnapshotRetainsErasedCandidate ==
  some (["b"], 0, 0)
#guard retractSnapshotDoesNotDrift
#guard runAtomsFor [] clauseFactsInOrder xIdentity ==
  some (["a", "b"], 0, 0)
#guard runAtomsFor [] clauseBoundReferenceSelectsOccurrence xIdentity ==
  some (["b"], 0, 0)
#guard runAtomsFor [] clauseRuleBody yIdentity == some (["a"], 0, 0)
#guard runAtomsFor [] clauseCutPrunesLater xIdentity == some (["a"], 0, 0)
#guard runCount [] clauseReferenceRoundTrip == some (1, 0, 0)
#guard clauseVariableHeadRejected
#guard runAtomsFor [] clauseSnapshotDoesNotDrift xIdentity ==
  some (["b"], 0, 0)
#guard runAtomsFor [] clauseSnapshotRetainsErasedCandidate xIdentity ==
  some (["b"], 0, 0)
#guard snapshotDoesNotDrift
#guard laterCallSeesAssertion == some (["old", "new"], 0, 0)

end Mettapedia.Logic.Prolog.SourceRuntimeRegression
