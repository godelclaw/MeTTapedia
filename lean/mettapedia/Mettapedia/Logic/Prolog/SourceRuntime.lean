import Mettapedia.Logic.Prolog.SourceSignature
import Mettapedia.Logic.Prolog.RuntimeControl
import Mettapedia.Logic.Prolog.RuntimeClauseDecode
import Mettapedia.Logic.Prolog.ClauseReflection

/-!
# Concrete callable decoding for Prolog source terms

This module gives the concrete source signature a read-only realization of
`call/N`.  It is not a resolver or a second dispatch loop: `RuntimeQuery`
invokes this decoder from its single phase transition and installs the
predicate-like cut boundary.  The decoder only interprets an existing heap
graph as typed `RuntimeGoal` instructions.

The callable spine follows SWI-Prolog V10.1.9 `i_metacall_common` in
`src/pl-vmi.c`: an atom supplies a predicate name, a compound supplies its
functor and existing arguments, and `call/N` appends the extra arguments.
With no extra arguments, the standard control functors are decoded back into
the same typed control constructors produced by the source reader.
-/

namespace Mettapedia.Logic.Prolog.SourceRuntime

open Mettapedia.Logic
open LP.RuntimeTerm LP.RuntimeMaterialize
open SourceSignature RuntimeControl

abbrev Sigma := SourceSignature.signature
abbrev State := RuntimeControl.State Sigma
abbrev Session := RuntimeControl.Session Sigma

/-- SWI-Prolog's ISO instantiation-error term for `throw/1`, including the
predicate context reported by version 10.1.9. -/
def throwInstantiationErrorTerm : SourceSignature.Term :=
  compound "error" [
    atom "instantiation_error",
    compound "context" [
      compound ":" [atom "system", compound "/" [atom "throw", integer 1]],
      var "_" 0
    ]
  ]

/-- Language-owned packet content for an unbound throw root.  `RuntimeQuery`
detects that root and owns every raise, match, unwind, and recovery
transition. -/
def throwInstantiationError : LP.RuntimeException.Packet Sigma := {
  term := LP.Term.atScope 0 throwInstantiationErrorTerm
}

@[simp]
theorem throwInstantiationError_term :
    throwInstantiationError.term =
      LP.Term.atScope 0 throwInstantiationErrorTerm := rfl

/-- Concrete Prolog list symbols used by the shared collector. -/
def collectionEncoding : LP.RuntimeQuery.CollectionEncoding Sigma where
  nil := .atom "[]"
  cons := { name := "[|]", arity := 2 }
  cons_arity_two := rfl

/-- Source atoms name compound functors for `=../2`.  The arity is supplied
by the list length on construction and remains explicit in the canonical
`CompoundIndicator`; non-atom constants cannot name applications. -/
def univEncoding : LP.RuntimeQuery.UnivEncoding Sigma where
  list := collectionEncoding
  functorConstant symbol := .atom symbol.name
  functionOf constant arity :=
    match constant with
    | .atom name => some ⟨{ name, arity }, rfl⟩
    | _ => none

private def integerOperation (symbol : CompoundIndicator) :
    Option LP.RuntimeQuery.IntegerOperation :=
  if symbol.arity = 2 then
    match symbol.name with
    | "+" => some .add
    | "-" => some .subtract
    | "*" => some .multiply
    | "mod" => some .modulo
    | _ => none
  else none

/-- The exact unbounded-integer fragment currently realized from source
constants.  Float and transcendental arithmetic are separate obligations. -/
def integerArithmeticEncoding :
    LP.RuntimeQuery.IntegerArithmeticEncoding Sigma where
  decodeInteger
    | .integer value => some value
    | _ => none
  encodeInteger := .integer
  decode_encode _ := rfl
  operation := integerOperation

/-- Canonical source symbols used by the shared engine to normalize and
inspect dynamic facts/rules and to expose opaque stable references. -/
def clauseEncoding : LP.RuntimeQuery.ClauseEncoding Sigma where
  trueConstant := .atom "true"
  rule := { name := ":-", arity := 2 }
  rule_arity_two := rfl
  referenceConstant := SourceSignature.Constant.clauseReference

/-- The exact function-symbol to relation-symbol bridge used by ordinary
callable compounds.  Extra `call/N` arguments extend, rather than replace,
the compound's existing arity. -/
def predicateOfCompound (symbol : CompoundIndicator) (extraArity : Nat) :
    PredicateIndicator := {
  name := symbol.name
  arity := symbol.arity + extraArity
}

@[simp]
theorem predicateOfCompound_arity (symbol : CompoundIndicator)
    (extraArity : Nat) :
    (predicateOfCompound symbol extraArity).arity =
      symbol.arity + extraArity := rfl

private def ordinaryCall (name : String) (arguments : List Addr) :
    RuntimeGoal Sigma.scoped :=
  .call {
    symbol := { name, arity := arguments.length }
    args := arguments.toArray
  }

private def compoundCall (symbol : CompoundIndicator)
    (arguments extraArgs : List Addr) : RuntimeGoal Sigma.scoped :=
  .call {
    symbol := predicateOfCompound symbol extraArgs.length
    args := (arguments ++ extraArgs).toArray
  }

/-- Dereference one callable root without exposing trail/checkpoint authority
to the decoder. -/
private def dereferencedCell (heap : Heap Sigma.scoped) (address : Addr) :
    Except LP.RuntimeQuery.QueryError (Cell Sigma.scoped) :=
  match heap.deref address with
  | .error error => .error (.memory error)
  | .ok (.variableCycle cycle) =>
      .error (.memory (.variableReferenceCycle cycle))
  | .ok (.root root) =>
      match heap[root]? with
      | none => .error (.memory (.invalidAddress root))
      | some cell => .ok cell

/-- Bounded decoding of one finite callable graph.  Rational cycles are not
silently unfolded; exhausting the heap-sized bound fails closed until the
runtime exception channel can expose the corresponding ISO error term. -/
def decodeCallableAux : Nat → Heap Sigma.scoped → Addr → List Addr →
    Except LP.RuntimeQuery.QueryError (List (RuntimeGoal Sigma.scoped))
  | 0, _, _, _ => .error .unsupportedInstruction
  | fuel + 1, heap, address, extraArgs => do
      let cell ← dereferencedCell heap address
      match cell with
      | .var _ none => .error .unsupportedInstruction
      | .var _ (some _) => .error .unsupportedInstruction
      | .const (.atom name) =>
          if extraArgs.isEmpty then
            match name with
            | "true" => pure []
            | "fail" => pure [.fail]
            | "!" => pure [.cut]
            | _ => pure [ordinaryCall name []]
          else
            pure [ordinaryCall name extraArgs]
      | .const _ => .error .unsupportedInstruction
      | .app symbol arguments =>
          let arguments := arguments.toList
          if arguments.length != symbol.arity then
            .error (.memory .illFormedHeap)
          else if !extraArgs.isEmpty then
            pure [compoundCall symbol arguments extraArgs]
          else
            match symbol.name, arguments with
            | ",", [left, right] => do
                let decodedLeft ← decodeCallableAux fuel heap left []
                let decodedRight ← decodeCallableAux fuel heap right []
                pure (decodedLeft ++ decodedRight)
            | ";", [choice, elseBranch] => do
                let choiceCell ← dereferencedCell heap choice
                match choiceCell with
                | .app choiceSymbol choiceArguments =>
                    match choiceSymbol.name, choiceArguments.toList with
                    | "->", [condition, thenBranch] => do
                        let decodedCondition ←
                          decodeCallableAux fuel heap condition []
                        let decodedThen ←
                          decodeCallableAux fuel heap thenBranch []
                        let decodedElse ←
                          decodeCallableAux fuel heap elseBranch []
                        pure [.ifThenElse decodedCondition decodedThen decodedElse]
                    | "*->", [condition, thenBranch] => do
                        let decodedCondition ←
                          decodeCallableAux fuel heap condition []
                        let decodedThen ←
                          decodeCallableAux fuel heap thenBranch []
                        let decodedElse ←
                          decodeCallableAux fuel heap elseBranch []
                        pure [.softIfThenElse decodedCondition decodedThen
                          decodedElse]
                    | _, _ => do
                        let decodedLeft ← decodeCallableAux fuel heap choice []
                        let decodedRight ←
                          decodeCallableAux fuel heap elseBranch []
                        pure [.disj decodedLeft decodedRight]
                | _ => do
                    let decodedLeft ← decodeCallableAux fuel heap choice []
                    let decodedRight ← decodeCallableAux fuel heap elseBranch []
                    pure [.disj decodedLeft decodedRight]
            | "->", [condition, thenBranch] => do
                let decodedCondition ← decodeCallableAux fuel heap condition []
                let decodedThen ← decodeCallableAux fuel heap thenBranch []
                pure [.ifThenElse decodedCondition decodedThen [.fail]]
            | "*->", [condition, thenBranch] => do
                let decodedCondition ← decodeCallableAux fuel heap condition []
                let decodedThen ← decodeCallableAux fuel heap thenBranch []
                pure [.softIfThenElse decodedCondition decodedThen [.fail]]
            | "once", [goal] => do
                let decoded ← decodeCallableAux fuel heap goal []
                pure [.once decoded]
            | "\\+", [goal] => do
                let decoded ← decodeCallableAux fuel heap goal []
                pure [.neg decoded]
            | "=", [left, right] => pure [.unify left right]
            | "\\=", [left, right] => pure [.notUnify left right]
            | "var", [term] => pure [.isVar term]
            | "nonvar", [term] => pure [.neg [.isVar term]]
            | "forall", [condition, action] => do
                let decodedCondition ← decodeCallableAux fuel heap condition []
                let decodedAction ← decodeCallableAux fuel heap action []
                pure [.neg (decodedCondition ++ [.neg decodedAction])]
            | "findall", [template, generator, bag] => do
                let decodedGenerator ← decodeCallableAux fuel heap generator []
                pure [.findall template decodedGenerator bag]
            | "catch", [guarded, catcher, recovery] => do
                let decodedGuarded ← decodeCallableAux fuel heap guarded []
                let decodedRecovery ← decodeCallableAux fuel heap recovery []
                pure [.catch decodedGuarded catcher decodedRecovery]
            | "throw", [ball] => pure [.throw ball]
            | _, _ => pure [compoundCall symbol arguments []]

/-- Decode one callable at the current heap high-water. -/
def decodeCallable (heap : Heap Sigma.scoped) (address : Addr)
    (extraArgs : List Addr) :
    Except LP.RuntimeQuery.QueryError (List (RuntimeGoal Sigma.scoped)) :=
  decodeCallableAux (heap.size + 1) heap address extraArgs

/-- Recognize `call/N` without inspecting the heap.  The classifier exposes
only the first argument and ordered extra arguments; the shared engine invokes
`decodeCallable` afterwards. -/
def metaCall? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × List Addr) :=
  if goal.symbol.name = "call" then
    match goal.args.toList with
    | callable :: extraArgs =>
        if goal.symbol.arity = extraArgs.length + 1 then
          some (callable, extraArgs)
        else none
    | [] => none
  else none

/-- Recognize the ISO `phrase/3` entry without inspecting its arguments.
`phrase/2` is elaborated to this form by the source goal classifier. -/
def dcgCall? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × Addr) :=
  match goal.symbol.name, goal.args.toList with
  | "phrase", [body, input, rest] =>
      if goal.symbol.arity = 3 then some (body, input, rest) else none
  | _, _ => none

/-- SWI's `phrase_input/1` accepts an unbound variable, `[]`, or any outer
list cell.  It deliberately does not traverse the tail at this boundary. -/
private def checkPhraseState (heap : Heap Sigma.scoped) (address : Addr) :
    Except LP.RuntimeQuery.QueryError Unit := do
  let cell ← dereferencedCell heap address
  match cell with
  | .var _ none => pure ()
  | .const value =>
      if value = collectionEncoding.nil then pure ()
      else .error .invalidDcgState
  | .app symbol arguments =>
      if symbol = collectionEncoding.cons && arguments.size = 2 then pure ()
      else .error .invalidDcgState
  | .var _ (some _) => .error (.memory .illFormedHeap)

private def stringCodeConstants (value : String) :
    List SourceSignature.Constant :=
  value.toList.map fun character =>
    .integer (Int.ofNat character.toNat)

/-- Read one dynamic grammar body in the finite fragment needed by the pinned
PeTTa parser.  Ordinary nonterminals reuse the callable decoder with the two
state arguments appended.  Proper lists and strings become terminal plans;
cut and braced goals become ordinary typed instructions under the engine's
meta-call boundary.  Compound DCG control remains fail-closed until its fresh
intermediate-state allocation is represented by an engine plan. -/
def decodeDcgAux : Nat → Heap Sigma.scoped → Addr → Addr → Addr →
    Except LP.RuntimeQuery.QueryError
      (LP.RuntimeQuery.DcgPlan Sigma (RuntimeGoal Sigma.scoped))
  | 0, _, _, _, _ => .error .unsupportedInstruction
  | fuel + 1, heap, body, input, rest => do
      let cell ← dereferencedCell heap body
      match cell with
      | .var _ none => .error .dcgBodyUnbound
      | .var _ (some _) => .error (.memory .illFormedHeap)
      | .const (.atom "[]") =>
          pure (.addressTerminals collectionEncoding [])
      | .const (.string value) =>
          pure (.constantTerminals collectionEncoding
            (stringCodeConstants value))
      | .const (.atom "!") =>
          pure (.goals [.cut, .unify rest input])
      | .const (.atom "{}") =>
          pure (.goals [.unify input rest])
      | .const (.atom name) =>
          pure (.goals [ordinaryCall name [input, rest]])
      | .const _ => .error .invalidDcgBody
      | .app symbol arguments =>
          let arguments := arguments.toList
          if arguments.length != symbol.arity then
            .error (.memory .illFormedHeap)
          else if symbol = collectionEncoding.cons then
            match LP.RuntimeQuery.decodeAddressList collectionEncoding heap body with
            | .ok heads =>
                pure (.addressTerminals collectionEncoding heads)
            | .error (.memory error) => .error (.memory error)
            | .error _ => .error .invalidDcgBody
          else
            match symbol.name, arguments with
            | "{}", [goal] => do
                let goals ← decodeCallableAux fuel heap goal []
                pure (.goals (goals ++ [.unify rest input]))
            | ",", _ | ";", _ | "|", _ | "->", _ | "*->", _
            | "\\+", _ => .error .unsupportedInstruction
            | _, _ =>
                pure (.goals [compoundCall symbol arguments [input, rest]])

/-- Decode `phrase/3` after enforcing its shallow ISO list contract. -/
def decodeDcg (heap : Heap Sigma.scoped) (body input rest : Addr) :
    Except LP.RuntimeQuery.QueryError
      (LP.RuntimeQuery.DcgPlan Sigma (RuntimeGoal Sigma.scoped)) := do
  checkPhraseState heap input
  checkPhraseState heap rest
  decodeDcgAux (heap.size + 1) heap body input rest

private def isAtomConstant : SourceSignature.Constant → Bool
  | .atom _ => true
  | _ => false

private def isNumberConstant : SourceSignature.Constant → Bool
  | .integer _ | .floatBits _ => true
  | _ => false

private def isStringConstant : SourceSignature.Constant → Bool
  | .string _ => true
  | _ => false

/-- Recognize SWI's read-only term-test family without heap authority.  The
classifier supplies only a root and a test descriptor; the shared runtime
performs shallow dereference or recursive graph traversal and owns the
resulting transition. -/
def termTest? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × LP.RuntimeQuery.TermTest Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "atom", [root] =>
      if goal.symbol.arity = 1 then
        some (root, .constantWhere isAtomConstant)
      else none
  | "atomic", [root] =>
      if goal.symbol.arity = 1 then some (root, .isAtomic) else none
  | "compound", [root] =>
      if goal.symbol.arity = 1 then some (root, .isCompound) else none
  | "number", [root] =>
      if goal.symbol.arity = 1 then
        some (root, .constantWhere isNumberConstant)
      else none
  | "string", [root] =>
      if goal.symbol.arity = 1 then
        some (root, .constantWhere isStringConstant)
      else none
  | "ground", [root] =>
      if goal.symbol.arity = 1 then some (root, .isGround) else none
  | _, _ => none

/-- Recognize strict identity and its negation.  The source layer exposes only
two roots and the expected Bool; rational-graph comparison remains in the
shared LP runtime. -/
def termIdentity? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × Bool) :=
  match goal.symbol.name, goal.args.toList with
  | "==", [left, right] =>
      if goal.symbol.arity = 2 then some (left, right, true) else none
  | "\\==", [left, right] =>
      if goal.symbol.arity = 2 then some (left, right, false) else none
  | _, _ => none

/-- Recognize `=../2` without inspecting the heap.  Direction selection and
all graph work occur later inside the shared runtime. -/
def univ? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × LP.RuntimeQuery.UnivEncoding Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "=..", [termRoot, listRoot] =>
      if goal.symbol.arity = 2 then
        some (termRoot, listRoot, univEncoding)
      else none
  | _, _ => none

def integerIs? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × LP.RuntimeQuery.IntegerArithmeticEncoding Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "is", [resultRoot, expressionRoot] =>
      if goal.symbol.arity = 2 then
        some (resultRoot, expressionRoot, integerArithmeticEncoding)
      else none
  | _, _ => none

private def integerComparisonOfName : String →
    Option LP.RuntimeQuery.IntegerComparison
  | "<" => some .less
  | "=<" => some .lessEqual
  | ">" => some .greater
  | ">=" => some .greaterEqual
  | "=:=" => some .equal
  | "=\\=" => some .notEqual
  | _ => none

def integerComparison? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × LP.RuntimeQuery.IntegerComparison ×
      LP.RuntimeQuery.IntegerArithmeticEncoding Sigma) :=
  match goal.args.toList with
  | [leftRoot, rightRoot] =>
      if goal.symbol.arity = 2 then
        match integerComparisonOfName goal.symbol.name with
        | some comparison =>
            some (leftRoot, rightRoot, comparison, integerArithmeticEncoding)
        | none => none
      else none
  | _ => none

/-- Recognize the first persistent mutation fragment without heap authority.
Clause decoding and database replacement remain separate engine/session
operations. -/
def databaseRequest? (goal : RuntimeAtom Sigma.scoped) :
    Option LP.RuntimeQuery.DatabaseRequest :=
  match goal.symbol.name, goal.args.toList with
  | "asserta", [clauseRoot] =>
      if goal.symbol.arity = 1 then some (.asserta clauseRoot) else none
  | "asserta", [clauseRoot, referenceRoot] =>
      if goal.symbol.arity = 2 then
        some (.assertaWithReference clauseRoot referenceRoot)
      else none
  | "assertz", [clauseRoot] =>
      if goal.symbol.arity = 1 then some (.assertz clauseRoot) else none
  | "assertz", [clauseRoot, referenceRoot] =>
      if goal.symbol.arity = 2 then
        some (.assertzWithReference clauseRoot referenceRoot)
      else none
  | "retract", [patternRoot] =>
      if goal.symbol.arity = 1 then some (.retract patternRoot) else none
  | "clause", [headRoot, bodyRoot, referenceRoot] =>
      if goal.symbol.arity = 3 then
        some (.clause headRoot bodyRoot referenceRoot)
      else none
  | _, _ => none

/-- Map the precise local decoder boundary into runtime errors.  ISO packet
construction for these errors remains an explicit later conformance step. -/
def decodeClause (heap : Heap Sigma.scoped) (root : Addr) :
    Except LP.RuntimeQuery.QueryError SourceSignature.Clause :=
  match RuntimeClauseDecode.decodeClause heap root with
  | .ok clause => .ok clause
  | .error (.readback error) => .error (.dynamicClauseReadback error)
  | .error (.source _) => .error .invalidDynamicClause
  | .error .notClause => .error .invalidDynamicClause

def services : RuntimeControl.Services Sigma where
  metaCall? := metaCall?
  decoder := { decode := decodeCallable, decodeDcg := decodeDcg }
  dcgCall? := dcgCall?
  termTest? := termTest?
  termIdentity? := termIdentity?
  univ? := univ?
  integerIs? := integerIs?
  integerComparison? := integerComparison?
  databaseRequest? := databaseRequest?
  decodeClause := decodeClause
  reflectClause := ClauseReflection.reflect?
  unboundThrowError := some throwInstantiationError
  collectionEncoding := some collectionEncoding
  clauseEncoding := some clauseEncoding

@[simp]
theorem services_unboundThrowError :
    services.unboundThrowError = some throwInstantiationError := rfl

@[simp]
theorem services_clauseEncoding :
    services.clauseEncoding = some clauseEncoding := rfl

@[simp]
theorem services_collectionEncoding :
    services.collectionEncoding = some collectionEncoding := rfl

@[simp]
theorem services_dcgCall : services.dcgCall? = dcgCall? := rfl

@[simp]
theorem services_decodeDcg : services.decoder.decodeDcg = decodeDcg := rfl

@[simp]
theorem services_termTest :
    services.termTest? = termTest? := rfl

@[simp]
theorem services_termIdentity :
    services.termIdentity? = termIdentity? := rfl

@[simp]
theorem services_univ :
    services.univ? = univ? := rfl

@[simp]
theorem services_integerIs :
    services.integerIs? = integerIs? := rfl

@[simp]
theorem services_integerComparison :
    services.integerComparison? = integerComparison? := rfl

/-- Execute concrete source terms through the one shared runtime with
callable decoding enabled. -/
def step (program : SourceSignature.Program) (state : State) :
    RuntimeControl.StepResult Sigma :=
  RuntimeControl.stepWith services program state

def pull (program : SourceSignature.Program) : Nat → State →
    RuntimeControl.PullResult Sigma :=
  RuntimeControl.pullWith services program

def openSession (memory : Memory Sigma.scoped) (queryScope nextScope : Nat)
    (program : SourceSignature.Program) (goal : SourceSignature.Goal) :
    Except LP.RuntimeQuery.QueryError Session :=
  RuntimeControl.openSessionWith services memory queryScope nextScope program goal

def openEmpty (program : SourceSignature.Program) (goal : SourceSignature.Goal) :
    Except LP.RuntimeQuery.QueryError Session :=
  openSession (Memory.empty Sigma.scoped) 0 1 program goal

/-- Open a later query against a database carried out of a completed source
session. -/
def openDatabase
    (database : LP.RuntimeDatabase.Database SourceSignature.Clause)
    (goal : SourceSignature.Goal) :
    Except LP.RuntimeQuery.QueryError Session :=
  RuntimeControl.openSessionDatabaseWith services
    (Memory.empty Sigma.scoped) 0 1 database goal

/-- Session resumption delegates to `RuntimeControl.pullSession`; the stored
service selects `pullCoreWithMeta` inside the same canonical phase loop. -/
def pullSession (fuel : Nat) (session : Session) :
    RuntimeControl.SessionPullResult Sigma :=
  RuntimeControl.pullSession fuel session

end Mettapedia.Logic.Prolog.SourceRuntime
