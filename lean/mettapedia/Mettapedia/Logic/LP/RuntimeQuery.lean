import Mettapedia.Logic.LP.RuntimeMaterialize
import Mettapedia.Logic.LP.RuntimeClauseEntry
import Mettapedia.Logic.LP.RuntimeException

/-!
# Demand-driven execution of typed LP clauses

This is the single executable query layer over the `Logic.LP` term graph.  It
does not compile PeTTa or define a second clause semantics: it selects ordinary
`Program` clauses, standardizes each live activation apart, materializes it in
the shared heap, and delegates head unification to `RuntimeUnification`.

The control layout follows the semantic spine of SWI-Prolog V10.1.9:

* `src/pl-incl.h`: `localFrame`, `choice`, `CHP_CLAUSE`, and `CHP_JUMP`;
* `src/pl-vmi.c`: `shallow_backtrack`, `deep_backtrack`, and `I_CUT`;
* `src/pl-wam.c`: `discardChoicesAfter`; and
* `src/pl-wam.c`: `PL_next_solution` resumption.

The Lean representation is intentionally smaller than SWI's VM.  A return
frame stores a caller continuation and its cut depth.  One tagged choice stack
stores either a clause retry or a control continuation.  Both own the exact
heap/trail checkpoint restored before resumption; cut retains only choices
older than the current predicate frame.  The fresh activation scope is
persistent query state and is therefore never rewound by backtracking.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeQuery

open RuntimeTerm RuntimeMaterialize

/-- Runtime hooks whose control behavior must be handled by the query engine.
Only cut is needed for the pure-clause kernel; further built-ins extend this
record rather than becoming synthetic clauses. -/
structure Builtins (σ : LPSignature) where
  isCut : σ.relationSymbols → Bool
  cut_arity_zero : ∀ symbol, isCut symbol = true → σ.relationArity symbol = 0

/-- Structured query failures.  Unsupported/corrupt states do not become
ordinary Prolog failure. -/
inductive QueryError where
  | memory (error : MemoryError)
  | staleScopeSupply (queryScope nextScope : Nat)
  | malformedCut
  | invalidCutDepth (mark depth : Nat)
  | invalidCommitDepth (mark depth : Nat)
  | predicateMismatch
  | stalledUnifier
  | unsupportedInstruction
  | exceptionReadback (error : RuntimeReadback.ReadbackError)
  | collectionReadback (error : RuntimeReadback.ReadbackError)
  | dynamicClauseReadback (error : RuntimeReadback.ReadbackError)
  | invalidDynamicClause
  | databaseReferenceOutputNotVariable
  | termIdentityBudgetExhausted
  | univListUnbound
  | invalidUnivList
  | univFunctorUnbound
  | invalidUnivFunctor
  | arithmeticEvaluationBudgetExhausted
  | arithmeticOperandUnbound
  | invalidArithmeticOperand
  | unsupportedArithmeticFunction
  | arithmeticZeroDivisor
  | unhandledDatabaseRequest
  | missingCollectionBoundary
  | exceptionCleanupFailed (cleanup : MemoryError)
  | cleanupFailed (primary : QueryError) (cleanup : MemoryError)
deriving Repr

/-- Read-only interpretation of a callable heap root.  The shared engine owns
when the decoder is invoked and the cut boundary installed around its result;
the decoder can return only an ordered instruction list or an explicit error.
It receives the heap rather than `Memory`, so it cannot mutate the trail or
restore checkpoints. -/
structure MetaCallDecoder (σ : LPSignature) (Instruction : Type*) where
  decode : Heap σ.scoped → Addr → List Addr →
    Except QueryError (List Instruction)

/-- Pure LP and typed runtimes without meta-call support fail closed. -/
def rejectingMetaCallDecoder (σ : LPSignature) (Instruction : Type*) :
    MetaCallDecoder σ Instruction where
  decode _ _ _ := .error .unsupportedInstruction

/-- Language-owned encoding of ordinary Prolog-style lists.  The engine owns
the fold, materialization, and bag unification; a realization supplies only
the nil constant and a binary constructor symbol. -/
structure CollectionEncoding (σ : LPSignature) where
  nil : σ.constants
  cons : σ.functionSymbols
  cons_arity_two : σ.functionArity cons = 2

namespace CollectionEncoding

/-- One encoded list cell. -/
def consTerm (encoding : CollectionEncoding σ)
    (head tail : Term σ.scoped) : Term σ.scoped :=
  let arguments : Fin 2 → Term σ.scoped :=
    Fin.cases head (Fin.cases tail Fin.elim0)
  .app encoding.cons fun index =>
    arguments (Fin.cast encoding.cons_arity_two index)

/-- Encode answers in their supplied order. -/
def listTerm (encoding : CollectionEncoding σ)
    (answers : List (Term σ.scoped)) : Term σ.scoped :=
  answers.foldr encoding.consTerm (.const encoding.nil)

end CollectionEncoding

/-- Language-owned symbols for `=../2`.  The engine owns heap traversal,
allocation, and unification.  A realization supplies only the existing list
encoding and the lossless atom/functor name bridge for its signature. -/
structure UnivEncoding (σ : LPSignature) where
  list : CollectionEncoding σ
  functorConstant : σ.functionSymbols → σ.constants
  functionOf : (constant : σ.constants) → (arity : Nat) →
    Option { symbol : σ.functionSymbols // σ.functionArity symbol = arity }

/-- A prepared `=../2` result contains only a new memory and one canonical
unification pair.  It carries no continuation, choice point, or answer. -/
structure UnivPrepared (σ : LPSignature) where
  memory : Memory σ.scoped
  left : Addr
  right : Addr

/-- Allocate a proper list whose heads are existing graph roots.  The roots
are reused, not read back and rematerialized, preserving variable identity
and sharing exactly. -/
def allocateAddressList {σ : LPSignature} (encoding : CollectionEncoding σ) :
    Memory σ.scoped → List Addr → Except MemoryError (Addr × Memory σ.scoped)
  | memory, [] => memory.allocate (.const encoding.nil)
  | memory, head :: tail => do
      let (tailRoot, memory) ← allocateAddressList encoding memory tail
      memory.allocate (.app encoding.cons #[head, tailRoot])

/-- Decode only the proper-list spine, retaining each element's existing heap
root.  Rational or malformed spines fail visibly; element graphs themselves
are not copied or traversed. -/
def decodeAddressListAux {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (encoding : CollectionEncoding σ)
    (heap : Heap σ.scoped) : Nat → Addr → Except QueryError (List Addr)
  | 0, _ => .error .invalidUnivList
  | fuel + 1, address =>
      match heap.deref address with
      | .error error => .error (.memory error)
      | .ok (.variableCycle cycle) =>
          .error (.memory (.variableReferenceCycle cycle))
      | .ok (.root root) =>
          match heap[root]? with
          | none => .error (.memory (.invalidAddress root))
          | some (.var _ none) => .error .univListUnbound
          | some (.var _ (some _)) => .error (.memory .illFormedHeap)
          | some (.const value) =>
              if value = encoding.nil then .ok [] else .error .invalidUnivList
          | some (.app symbol arguments) =>
              if symbol = encoding.cons ∧ arguments.size = 2 then
                match arguments[0]?, arguments[1]? with
                | some head, some tail => do
                    let rest ← decodeAddressListAux encoding heap fuel tail
                    pure (head :: rest)
                | _, _ => .error (.memory .illFormedHeap)
              else .error .invalidUnivList

def decodeAddressList {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (encoding : CollectionEncoding σ)
    (heap : Heap σ.scoped) (address : Addr) :
    Except QueryError (List Addr) :=
  decodeAddressListAux encoding heap (heap.size + 1) address

/-- Prepare `Term =.. List` in the direction selected by the dereferenced term
root.  A nonvariable term is decomposed into a newly allocated list that
reuses its argument roots.  An unbound term consumes a proper list, allocates
at most one application root, and returns a canonical unification pair. -/
def prepareUniv {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (encoding : UnivEncoding σ)
    (memory : Memory σ.scoped) (termRoot listRoot : Addr) :
    Except QueryError (UnivPrepared σ) := do
  let dereferenced ←
    match memory.heap.deref termRoot with
    | .error error => .error (.memory error)
    | .ok (.variableCycle cycle) =>
        .error (.memory (.variableReferenceCycle cycle))
    | .ok (.root root) => .ok root
  let cell ←
    match memory.heap[dereferenced]? with
    | none => .error (.memory (.invalidAddress dereferenced))
    | some cell => .ok cell
  match cell with
  | .var _ none =>
      let elements ← decodeAddressList encoding.list memory.heap listRoot
      match elements with
      | [] => .error .invalidUnivList
      | [functorRoot] =>
          let functorCell ←
            match memory.heap.deref functorRoot with
            | .error error => .error (.memory error)
            | .ok (.variableCycle cycle) =>
                .error (.memory (.variableReferenceCycle cycle))
            | .ok (.root root) =>
                match memory.heap[root]? with
                | none => .error (.memory (.invalidAddress root))
                | some cell => .ok cell
          match functorCell with
          | .var _ none => .error .univFunctorUnbound
          | .var _ (some _) => .error (.memory .illFormedHeap)
          | .const _ => .ok { memory, left := termRoot, right := functorRoot }
          | .app _ _ => .error .invalidUnivFunctor
      | functorRoot :: arguments =>
          let functorCell ←
            match memory.heap.deref functorRoot with
            | .error error => .error (.memory error)
            | .ok (.variableCycle cycle) =>
                .error (.memory (.variableReferenceCycle cycle))
            | .ok (.root root) =>
                match memory.heap[root]? with
                | none => .error (.memory (.invalidAddress root))
                | some cell => .ok cell
          match functorCell with
          | .var _ none => .error .univFunctorUnbound
          | .var _ (some _) => .error (.memory .illFormedHeap)
          | .const value =>
              match encoding.functionOf value arguments.length with
              | none => .error .invalidUnivFunctor
              | some symbol =>
                  match memory.allocate (.app symbol.1 arguments.toArray) with
                  | .error error => .error (.memory error)
                  | .ok (constructed, memory) =>
                      .ok { memory, left := termRoot, right := constructed }
          | .app _ _ => .error .invalidUnivFunctor
  | .var _ (some _) => .error (.memory .illFormedHeap)
  | .const _ =>
      match allocateAddressList encoding.list memory [dereferenced] with
      | .error error => .error (.memory error)
      | .ok (list, memory) => .ok { memory, left := listRoot, right := list }
  | .app symbol arguments =>
      if arguments.size = 0 then
        .error .invalidUnivFunctor
      else if arguments.size = σ.functionArity symbol then
        match memory.allocate (.const (encoding.functorConstant symbol)) with
        | .error error => .error (.memory error)
        | .ok (functorRoot, memory) =>
            match allocateAddressList encoding.list memory
                (functorRoot :: arguments.toList) with
            | .error error => .error (.memory error)
            | .ok (list, memory) =>
                .ok { memory, left := listRoot, right := list }
      else .error (.memory .illFormedHeap)

/-! ## Integer arithmetic on the shared graph -/

/-- The integer operations needed by the pinned PeTTa parser and translator.
This is intentionally not a claim to implement SWI's full numeric tower. -/
inductive IntegerOperation where
  | add
  | subtract
  | multiply
  | modulo
deriving DecidableEq, Repr

inductive IntegerComparison where
  | less
  | lessEqual
  | greater
  | greaterEqual
  | equal
  | notEqual
deriving DecidableEq, Repr

/-- Language-owned recognition of integer constants and arithmetic functors.
The engine owns dereference, recursive evaluation, result allocation,
unification, and comparison control. -/
structure IntegerArithmeticEncoding (σ : LPSignature) where
  decodeInteger : σ.constants → Option Int
  encodeInteger : Int → σ.constants
  decode_encode : ∀ value, decodeInteger (encodeInteger value) = some value
  operation : σ.functionSymbols → Option IntegerOperation

def IntegerOperation.apply : IntegerOperation → Int → Int →
    Except QueryError Int
  | .add, left, right => .ok (left + right)
  | .subtract, left, right => .ok (left - right)
  | .multiply, left, right => .ok (left * right)
  | .modulo, _, 0 => .error .arithmeticZeroDivisor
  | .modulo, left, right =>
      let remainder := left % right
      /- Lean's integer remainder is nonnegative.  SWI's `mod/2` gives a
      nonzero remainder the divisor's sign. -/
      .ok (if remainder = 0 ∨ 0 < right then remainder else remainder + right)

def IntegerComparison.holds : IntegerComparison → Int → Int → Bool
  | .less, left, right => decide (left < right)
  | .lessEqual, left, right => decide (left ≤ right)
  | .greater, left, right => decide (left > right)
  | .greaterEqual, left, right => decide (left ≥ right)
  | .equal, left, right => decide (left = right)
  | .notEqual, left, right => decide (left ≠ right)

/-- Evaluate an integer expression directly over the canonical heap.  Fuel is
structural cycle protection; ordinary acyclic expressions visit fewer
application nodes than the heap contains. -/
def evalIntegerAux {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (encoding : IntegerArithmeticEncoding σ)
    (heap : Heap σ.scoped) : Nat → Addr → Except QueryError Int
  | 0, _ => .error .arithmeticEvaluationBudgetExhausted
  | fuel + 1, address => do
      let root ←
        match heap.deref address with
        | .error error => .error (.memory error)
        | .ok (.variableCycle cycle) =>
            .error (.memory (.variableReferenceCycle cycle))
        | .ok (.root root) => .ok root
      let cell ←
        match heap[root]? with
        | none => .error (.memory (.invalidAddress root))
        | some cell => .ok cell
      match cell with
      | .var _ none => .error .arithmeticOperandUnbound
      | .var _ (some _) => .error (.memory .illFormedHeap)
      | .const value =>
          match encoding.decodeInteger value with
          | some integer => .ok integer
          | none => .error .invalidArithmeticOperand
      | .app symbol arguments =>
          if arguments.size = 2 ∧ σ.functionArity symbol = 2 then
            match encoding.operation symbol, arguments[0]?, arguments[1]? with
            | some operation, some leftRoot, some rightRoot => do
                let left ← evalIntegerAux encoding heap fuel leftRoot
                let right ← evalIntegerAux encoding heap fuel rightRoot
                operation.apply left right
            | none, _, _ => .error .unsupportedArithmeticFunction
            | _, _, _ => .error (.memory .illFormedHeap)
          else .error .unsupportedArithmeticFunction

def evalInteger {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (encoding : IntegerArithmeticEncoding σ)
    (heap : Heap σ.scoped) (address : Addr) : Except QueryError Int :=
  evalIntegerAux encoding heap (heap.size + 1) address

/-- Language-owned symbols for the ordinary `Head :- Body` representation and
opaque database references shared by `retract/1`, `clause/3`, and assertion.
The engine owns heap inspection and allocation; a realization supplies only
canonical symbols. -/
structure ClauseEncoding (σ : LPSignature) where
  trueConstant : σ.constants
  rule : σ.functionSymbols
  rule_arity_two : σ.functionArity rule = 2
  /-- Runtime-only stable occurrence identity; the source reader must not
  expose a constructor for values in this image. -/
  referenceConstant : Nat → σ.constants

/-- A read-only predicate on the three canonical shallow heap shapes.  A
language realization may classify its own constant payloads, but it receives
no memory, continuation, or answer authority. -/
structure TermTest (σ : LPSignature) where
  acceptsVariable : Bool
  acceptsConstant : σ.constants → Bool
  acceptsApplication : Bool

namespace TermTest

def accepts (test : TermTest σ) : Cell σ.scoped → Bool
  | .var _ none => test.acceptsVariable
  | .var _ (some _) => false
  | .const value => test.acceptsConstant value
  | .app _ _ => test.acceptsApplication

def isVariable : TermTest σ where
  acceptsVariable := true
  acceptsConstant _ := false
  acceptsApplication := false

def isAtomic : TermTest σ where
  acceptsVariable := false
  acceptsConstant _ := true
  acceptsApplication := false

def isCompound : TermTest σ where
  acceptsVariable := false
  acceptsConstant _ := false
  acceptsApplication := true

def constantWhere (predicate : σ.constants → Bool) : TermTest σ where
  acceptsVariable := false
  acceptsConstant := predicate
  acceptsApplication := false

end TermTest

/-! ## Read-only strict term identity -/

/-- Count graph edges once to size the read-only pair traversal below.  The
bound follows the counting argument that an application root can be paired
with at most `heap.size` other roots.  Until the general no-exhaustion theorem
is established, exhaustion remains an explicit error rather than inequality. -/
def termIdentityFuel (heap : Heap σ) : Nat :=
  let edges := heap.foldl (fun total cell =>
    total + cell.references.length) 0
  (heap.size + 1) * (edges + 1) + 1

/-- Equality-only counterpart of SWI-Prolog V10.1.9's
`compareStandard(..., eq=true)` (`src/pl-prims.c`).  It dereferences both
roots, distinguishes unbound variables by address, compares constants
exactly, and traverses matching compounds through a visited pair set so
rational graphs terminate.  It never binds or trails. -/
def termIdenticalAux {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (heap : Heap σ.scoped) :
    Nat → List (Addr × Addr) → List (Addr × Addr) → Except QueryError Bool
  | 0, _, _ => .error .termIdentityBudgetExhausted
  | _ + 1, [], _ => .ok true
  | fuel + 1, (left, right) :: rest, visited =>
      match heap.deref left with
      | .error error => .error (.memory error)
      | .ok (.variableCycle cycle) =>
          .error (.memory (.variableReferenceCycle cycle))
      | .ok (.root leftRoot) =>
          match heap.deref right with
          | .error error => .error (.memory error)
          | .ok (.variableCycle cycle) =>
              .error (.memory (.variableReferenceCycle cycle))
          | .ok (.root rightRoot) =>
              if leftRoot = rightRoot then
                termIdenticalAux heap fuel rest visited
              else
                match heap[leftRoot]?, heap[rightRoot]? with
                | some (.var _ none), some (.var _ none) => .ok false
                | some (.var _ none), some _ => .ok false
                | some _, some (.var _ none) => .ok false
                | some (.const leftValue), some (.const rightValue) =>
                    if leftValue = rightValue then
                      termIdenticalAux heap fuel rest visited
                    else .ok false
                | some (.app leftSymbol leftArgs),
                    some (.app rightSymbol rightArgs) =>
                    if leftSymbol = rightSymbol ∧
                        leftArgs.size = rightArgs.size then
                      if RuntimeUnification.seen visited leftRoot rightRoot then
                        termIdenticalAux heap fuel rest visited
                      else
                        termIdenticalAux heap fuel
                          (leftArgs.toList.zip rightArgs.toList ++ rest)
                          (RuntimeUnification.orderedPair leftRoot rightRoot ::
                            visited)
                    else .ok false
                | some (.var _ (some _)), _ =>
                    .error (.memory .illFormedHeap)
                | _, some (.var _ (some _)) =>
                    .error (.memory .illFormedHeap)
                | some _, some _ => .ok false
                | none, _ => .error (.memory (.invalidAddress leftRoot))
                | _, none => .error (.memory (.invalidAddress rightRoot))

/-- Decide strict identity of two roots in one finite heap.  Budget exhaustion
is a typed runtime error, never ordinary inequality or fabricated completion. -/
def termIdentical {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (heap : Heap σ.scoped)
    (left right : Addr) : Except QueryError Bool :=
  termIdenticalAux heap (termIdentityFuel heap) [(left, right)] []

/-- Reflexivity is reached through real dereference and the nonempty computed
budget; invalid or variable-cycle roots are deliberately outside the premise. -/
theorem termIdentical_same_of_deref {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (heap : Heap σ.scoped) (address root : Addr)
    (hDeref : heap.deref address = .ok (.root root)) :
    termIdentical heap address address = .ok true := by
  simp [termIdentical, termIdentityFuel, termIdenticalAux, hDeref]
  generalize hFuel :
    (heap.size + 1) *
      (heap.foldl (fun total cell =>
        total + cell.references.length) 0 + 1) = fuel
  cases fuel with
  | zero =>
      have hPositive :
          0 < (heap.size + 1) *
            (heap.foldl (fun total cell =>
              total + cell.references.length) 0 + 1) :=
        Nat.mul_pos (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      omega
  | succ fuel => rfl

/-- One immutable candidate in a call-time database-clause snapshot. Stable
identity is separate from the normalized clause term so matching cannot forge
the database occurrence inspected or erased. -/
structure DatabaseClauseCandidate (σ : LPSignature) where
  reference : Nat
  clause : Term σ

/-- What success on one reflected database clause is allowed to do.  Both
operations share the same snapshot cursor and canonical unifier: `retract`
requests erasure of the selected occurrence, while `inspect` only unifies the
caller's opaque reference argument. -/
inductive DatabaseClauseAction (σ : LPSignature) where
  | retract
  | inspect (referenceRoot : Addr) (referenceConstant : Nat → σ.constants)

/-- Saved exception delimiter.  It records only backtrackable entry data;
the persistent fresh-scope supply remains in `StateCore` and is never restored
from this frame. -/
structure CatchHandlerCore (σ : LPSignature) (Instruction : Type*) where
  checkpoint : Memory.Checkpoint
  choiceDepth : Nat
  catcher : Addr
  recovery : List Instruction

/-- Success delimiter for one active answer collector.  `choiceDepth` names
the collection sentinel by the number of older choices beneath it. -/
structure CollectionHandlerCore (σ : LPSignature) where
  choiceDepth : Nat
  template : Addr

/-- Success behavior attached to one return frame.  `hard` discards the
conditional marker together with condition-local alternatives.  `soft`
discards only its distinguished else marker, leaving condition alternatives
available for later answers. -/
inductive ReturnCommit where
  | ordinary
  | hard (mark : Nat)
  | soft (mark : Nat)
deriving DecidableEq, Repr

/-- Caller state saved while one predicate body is active.  The instruction
type is abstract so pure LP atoms and typed Prolog control share this exact
frame representation. -/
structure ReturnFrameCore (σ : LPSignature) (Instruction : Type*) where
  continuation : List Instruction
  callerCutDepth : Nat
  commit : ReturnCommit := .ordinary
  handler : Option (CatchHandlerCore σ Instruction) := none
  collection : Option (CollectionHandlerCore σ) := none

/-- The nearest exception delimiter together with the outer frames that
survive if it handles the packet.  Frames above it are exactly the unwound
protected computation. -/
structure CatchTargetCore (σ : LPSignature) (Instruction : Type*) where
  frame : ReturnFrameCore σ Instruction
  handler : CatchHandlerCore σ Instruction
  outerFrames : List (ReturnFrameCore σ Instruction)

/-- State retained while the canonical graph unifier tests a catcher against
the throw-time packet. -/
structure CatchSelectionCore (σ : LPSignature) (Instruction : Type*) where
  packet : RuntimeException.Packet σ
  target : CatchTargetCore σ Instruction
  /-- The original throw-time heap plus the one installed packet copy.  Every
  candidate catcher is tested against this same immutable value; no rejected
  inner delimiter may erase bindings before an outer catcher is considered. -/
  throwMemory : Memory σ.scoped
  packetRoot : Addr

/-- The established pure-LP return frame. -/
abbrev ReturnFrame (σ : LPSignature) :=
  ReturnFrameCore σ (RuntimeAtom σ.scoped)

/-- Backtrackable execution control, generic only in the instruction payload.
`cutDepth` counts the choice points that predate the current predicate
activation. -/
structure ControlCore (σ : LPSignature) (Instruction : Type*) where
  current : List Instruction
  cutDepth : Nat
  frames : List (ReturnFrameCore σ Instruction)

/-- The established pure-LP control state. -/
abbrev Control (σ : LPSignature) :=
  ControlCore σ (RuntimeAtom σ.scoped)

/-- A frozen, ordered clause cursor.  `checkpoint` is the state immediately
before entering this predicate call.  Retained clauses use the source-clause
type of the one instantiated language. -/
structure ClauseCursorCore (σ : LPSignature) (Instruction SourceClause : Type*) where
  checkpoint : Memory.Checkpoint
  goal : RuntimeAtom σ.scoped
  clauses : List SourceClause
  cutDepth : Nat
  frames : List (ReturnFrameCore σ Instruction)

/-- The established pure-LP clause cursor. -/
abbrev ClauseCursor (σ : LPSignature) :=
  ClauseCursorCore σ (RuntimeAtom σ.scoped) (Clause σ)

/-- A saved control continuation, corresponding to SWI-Prolog's `CHP_JUMP`.
It owns the checkpoint at which the alternative was created and the complete
backtrackable control to resume after restoring that checkpoint. -/
structure BranchChoiceCore (σ : LPSignature) (Instruction : Type*) where
  checkpoint : Memory.Checkpoint
  control : ControlCore σ Instruction

/-- Exhaustion delimiter and detached answer store for one `findall/3`.
The outer continuation is transferred here once; generated alternatives sit
above this sentinel on the same canonical choice stack. -/
structure CollectionChoiceCore (σ : LPSignature) (Instruction : Type*) where
  checkpoint : Memory.Checkpoint
  template : Addr
  bag : Addr
  encoding : CollectionEncoding σ
  continuation : List Instruction
  callerCutDepth : Nat
  outerFrames : List (ReturnFrameCore σ Instruction)
  reversed : List (Term σ.scoped) := []

/-- Frozen cursor shared by `retract/1` and `clause/3`. `checkpoint` denotes
the normalized clause-pattern state shared by every candidate; `control` is
the already-consumed caller continuation. -/
structure DatabaseClauseCursorCore (σ : LPSignature) (Instruction : Type*) where
  checkpoint : Memory.Checkpoint
  pattern : Addr
  candidates : List (DatabaseClauseCandidate σ)
  control : ControlCore σ Instruction
  action : DatabaseClauseAction σ

/-- The single newest-first alternative stack.  Clause retries and structured
control branches are different resource kinds, but share restoration, DFS
ordering, and cut ownership. -/
inductive ChoicePointCore (σ : LPSignature)
    (Instruction SourceClause : Type*) where
  | clause (cursor : ClauseCursorCore σ Instruction SourceClause)
  | branch (alternative : BranchChoiceCore σ Instruction)
  /-- The else alternative of soft if-then-else.  Its distinct constructor
  lets the success frame remove exactly this delimiter while preserving all
  condition alternatives above it. -/
  | softElse (alternative : BranchChoiceCore σ Instruction)
  /-- Backtracking to this sentinel means the generator is exhausted. -/
  | collection (boundary : CollectionChoiceCore σ Instruction)
  /-- Later reflected clauses retained by `retract/1` or `clause/3`. -/
  | databaseClause (cursor : DatabaseClauseCursorCore σ Instruction)

/-- The established pure-LP choice-point type.  Pure LP execution constructs
only `clause` alternatives. -/
abbrev ChoicePoint (σ : LPSignature) :=
  ChoicePointCore σ (RuntimeAtom σ.scoped) (Clause σ)

/-- Post-success authority attached by an engine-owned unification entry.
Ordinary clause/control unification merely continues. A retract candidate may
request erasure of exactly its stable snapshot reference; no classifier or
session-side matcher can substitute another occurrence. -/
inductive AttemptSuccess where
  | continue
  | eraseRef (reference : Nat)
deriving DecidableEq, Repr

/-- Information retained while the graph unifier executes one selected head. -/
structure AttemptCore (σ : LPSignature) (Instruction : Type*) where
  body : List Instruction
  cutDepth : Nat
  frames : List (ReturnFrameCore σ Instruction)
  onSuccess : AttemptSuccess := .continue

/-- The established pure-LP unification attempt. -/
abbrev Attempt (σ : LPSignature) :=
  AttemptCore σ (RuntimeAtom σ.scoped)

/-- Query phases are explicit so retry, restore, and every unification
microstep remain resumable. -/
inductive PhaseCore (σ : LPSignature) (Instruction SourceClause : Type*) where
  | dispatch
  | select (cursor : ClauseCursorCore σ Instruction SourceClause)
  | unifying (attempt : AttemptCore σ Instruction)
      (machine : RuntimeUnification.Machine σ.scoped)
  | raising (packet : RuntimeException.Packet σ)
  | catchSelecting (selection : CatchSelectionCore σ Instruction)
      (machine : RuntimeUnification.Machine σ.scoped)
  | catchRecovering (selection : CatchSelectionCore σ Instruction)
      (machine : RuntimeUnification.Machine σ.scoped)
  | databaseClauseSelect (cursor : DatabaseClauseCursorCore σ Instruction)
  | backtrack
  | afterAnswer

/-- The established pure-LP query phase. -/
abbrev Phase (σ : LPSignature) :=
  PhaseCore σ (RuntimeAtom σ.scoped) (Clause σ)

/-- One live query.  `nextScope` is persistent across choice restoration; the
heap, control, and choice stack are the backtrackable lane. -/
structure StateCore (σ : LPSignature) (Instruction SourceClause : Type*) where
  memory : Memory σ.scoped
  control : ControlCore σ Instruction
  choices : List (ChoicePointCore σ Instruction SourceClause)
  queryCheckpoint : Memory.Checkpoint
  queryVarMap : List (ScopedVar σ.vars × Addr)
  nextScope : Nat
  phase : PhaseCore σ Instruction SourceClause

/-- The established pure-LP query state.  Existing execution and soundness
theorems continue to use this exact specialization. -/
abbrev State (σ : LPSignature) :=
  StateCore σ (RuntimeAtom σ.scoped) (Clause σ)

/-- A yielded answer keeps the live memory and roots of the source query
variables.  The state returned alongside it is resumed for the next answer. -/
structure Answer (σ : LPSignature) where
  memory : Memory σ.scoped
  queryVarMap : List (ScopedVar σ.vars × Addr)

inductive Observation (σ : LPSignature) where
  | answer (value : Answer σ)

/-- Persistent clause-store operations recognized by a language realization.
The shared engine owns instruction consumption and continuation order, while a
session outside backtrackable state owns the actual database update. -/
inductive DatabaseRequest where
  | asserta (clauseRoot : Addr)
  | assertz (clauseRoot : Addr)
  /-- Assert and bind the caller's fresh output to the inserted occurrence's
  opaque stable identity. -/
  | assertaWithReference (clauseRoot referenceRoot : Addr)
  | assertzWithReference (clauseRoot referenceRoot : Addr)
  /-- Ask the persistent session for the call-time visible clause snapshot.
  Candidate matching remains an engine phase. -/
  | retract (patternRoot : Addr)
  /-- Enumerate the call-time visible clause snapshot without mutating it.
  The engine unifies `Head :- Body` and the opaque stable reference together. -/
  | clause (headRoot bodyRoot referenceRoot : Addr)
  /-- Apply the stable occurrence selected by a successful engine unifier. -/
  | eraseRef (reference : Nat)
deriving DecidableEq, Repr

inductive Terminal (σ : LPSignature) where
  | completed (memory : Memory σ.scoped)
  | raised (packet : RuntimeException.Packet σ) (memory : Memory σ.scoped)
  | runtimeError (error : QueryError) (memory : Memory σ.scoped)

inductive StepResultCore (σ : LPSignature) (Instruction SourceClause : Type*) where
  | next (state : StateCore σ Instruction SourceClause)
      (observation : Option (Observation σ))
  | databaseRequest (request : DatabaseRequest)
      (state : StateCore σ Instruction SourceClause)
  | terminal (result : Terminal σ)

abbrev StepResult (σ : LPSignature) :=
  StepResultCore σ (RuntimeAtom σ.scoped) (Clause σ)

/-- Fuel exhaustion is explicitly open; it never fabricates completion. -/
inductive PullResultCore (σ : LPSignature) (Instruction SourceClause : Type*) where
  | open (state : StateCore σ Instruction SourceClause)
  | answer (value : Answer σ)
      (state : StateCore σ Instruction SourceClause)
  | terminal (result : Terminal σ)

abbrev PullResult (σ : LPSignature) :=
  PullResultCore σ (RuntimeAtom σ.scoped) (Clause σ)

/-! ## Fresh-scope boundary -/

def Cell.scopeBelow {σ : LPSignature}
    (limit : Nat) : Cell σ.scoped → Bool
  | .var identity _ => identity.scope < limit
  | .const _ => true
  | .app _ _ => true

/-- All scoped variable identities already present in a heap are below the
next activation identity supplied by the caller. -/
def heapScopesBelow {σ : LPSignature}
    (heap : Heap σ.scoped) (limit : Nat) : Bool :=
  heap.all (Cell.scopeBelow limit)

/-! ## Ordered clauses and cut pruning -/

/-- Clause selection preserves source order. -/
def clausesFor {σ : LPSignature} [DecidableEq σ.relationSymbols]
    (program : Program σ) (symbol : σ.relationSymbols) : List (Clause σ) :=
  program.filter fun clause => decide (clause.head.symbol = symbol)

@[simp]
theorem clausesFor_append {σ : LPSignature} [DecidableEq σ.relationSymbols]
    (left right : Program σ) (symbol : σ.relationSymbols) :
    clausesFor (left ++ right) symbol =
      clausesFor left symbol ++ clausesFor right symbol := by
  simp [clausesFor]

/-- Keep exactly the oldest `mark` entries of a newest-first choice stack. -/
def retainBottom (mark : Nat) (choices : List α) : List α :=
  choices.drop (choices.length - mark)

theorem retainBottom_length_of_le {mark : Nat} {choices : List α}
    (h : mark ≤ choices.length) :
    (retainBottom mark choices).length = mark := by
  simp [retainBottom, Nat.sub_sub_self h]

@[simp]
theorem retainBottom_all (choices : List α) :
    retainBottom choices.length choices = choices := by
  simp [retainBottom]

/-! ## Opening and closing a query -/

/-- The only data a source-query materializer may supply to the shared query
opener.  It cannot initialize alternatives, frames, phases, or scope state. -/
structure MaterializedQuery (σ : LPSignature) (Instruction : Type*) where
  memory : Memory σ.scoped
  current : List Instruction
  varMap : List (ScopedVar σ.vars × Addr)

/-- Materialize one source query at an explicit scope into the canonical heap. -/
structure QueryMaterializer (σ : LPSignature)
    (Instruction SourceQuery : Type*) where
  materialize : Memory σ.scoped → Nat → SourceQuery →
    Except MemoryError (MaterializedQuery σ Instruction)

/-- The established LP source-query materializer. -/
def lpQueryMaterializer {σ : LPSignature} [DecidableEq σ.vars] :
    QueryMaterializer σ (RuntimeAtom σ.scoped) (List (Atom σ)) where
  materialize memory scope goals :=
    match materializeGoals memory (queryAtScope scope goals) with
    | .error error => .error error
    | .ok result => .ok {
        memory := result.memory
        current := result.goals
        varMap := result.varMap
      }

/-- Shared query opening.  Fresh-scope validation, checkpoint ownership, empty
choice/frame initialization, and the initial dispatch phase are constructed
once here for every instruction language. -/
def openQueryCore {σ : LPSignature}
    (materializer : QueryMaterializer σ Instruction SourceQuery)
    (memory : Memory σ.scoped) (queryScope nextScope : Nat)
    (query : SourceQuery) :
    Except QueryError (StateCore σ Instruction SourceClause) :=
  if queryScope < nextScope then
    if heapScopesBelow memory.heap nextScope then
      match materializer.materialize memory queryScope query with
      | .error error => .error (.memory error)
      | .ok result =>
          .ok {
            memory := result.memory
            control := { current := result.current, cutDepth := 0, frames := [] }
            choices := []
            queryCheckpoint := memory.checkpoint
            queryVarMap := result.varMap
            nextScope
            phase := .dispatch
          }
    else
      .error (.staleScopeSupply queryScope nextScope)
  else
    .error (.staleScopeSupply queryScope nextScope)

/-- Materialize a source query once.  `nextScope` must dominate both the query
scope and every scoped variable already live in the supplied heap. -/
def openQuery {σ : LPSignature} [DecidableEq σ.vars]
    (memory : Memory σ.scoped) (queryScope nextScope : Nat)
    (goals : List (Atom σ)) : Except QueryError (State σ) :=
  openQueryCore (SourceClause := Clause σ) lpQueryMaterializer memory
    queryScope nextScope goals

def closeMemory {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) :
    Except MemoryError (Memory σ.scoped) :=
  state.memory.restore state.queryCheckpoint

def complete {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) :
    StepResultCore σ Instruction SourceClause :=
  match closeMemory state with
  | .ok memory => .terminal (.completed memory)
  | .error error => .terminal (.runtimeError (.memory error) state.memory)

def failWith {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) (error : QueryError) :
    StepResultCore σ Instruction SourceClause :=
  match closeMemory state with
  | .ok memory => .terminal (.runtimeError error memory)
  | .error cleanup =>
      .terminal (.runtimeError (.cleanupFailed error cleanup) state.memory)

/-- Pull-level counterpart of `failWith`, used when an API without a
persistent session encounters a database request.  It performs the same exact
query cleanup and has no unreachable result arm. -/
def failPullWith {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) (error : QueryError) :
    PullResultCore σ Instruction SourceClause :=
  match closeMemory state with
  | .ok memory => .terminal (.runtimeError error memory)
  | .error cleanup =>
      .terminal (.runtimeError (.cleanupFailed error cleanup) state.memory)

/-- Find the nearest still-active catch delimiter.  This is a structural
walk over the one return-frame stack, analogous to SWI's `findCatcher`; it
does not inspect or schedule any language instruction. -/
def findCatchTarget {σ : LPSignature} :
    List (ReturnFrameCore σ Instruction) →
      Option (CatchTargetCore σ Instruction)
  | [] => none
  | frame :: outerFrames =>
      match frame.handler with
      | some handler => some { frame, handler, outerFrames }
      | none => findCatchTarget outerFrames

/-- Close an uncaught exception distinctly from ordinary completion and
runtime corruption.  The detached packet survives exact query cleanup. -/
def raiseUnhandled {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (packet : RuntimeException.Packet σ) :
    StepResultCore σ Instruction SourceClause :=
  match closeMemory state with
  | .ok memory => .terminal (.raised packet memory)
  | .error cleanup =>
      .terminal (.runtimeError (.exceptionCleanupFailed cleanup) state.memory)

/-! ## One query transition -/

def replacementChoices {σ : LPSignature}
    (cursor : ClauseCursorCore σ Instruction SourceClause)
    (remaining : List SourceClause)
    (older : List (ChoicePointCore σ Instruction SourceClause)) :
    List (ChoicePointCore σ Instruction SourceClause) :=
  match remaining with
  | [] => older
  | _ => .clause { cursor with clauses := remaining } :: older

/-- Retain exactly one database-clause cursor when later call-snapshot
candidates remain. The cursor is a normal newest-first choice resource, so
ordinary cut and exception pruning reach it without a second scheduler. -/
def replacementDatabaseClauseChoices {σ : LPSignature}
    (cursor : DatabaseClauseCursorCore σ Instruction)
    (remaining : List (DatabaseClauseCandidate σ))
    (older : List (ChoicePointCore σ Instruction SourceClause)) :
    List (ChoicePointCore σ Instruction SourceClause) :=
  match remaining with
  | [] => older
  | _ => .databaseClause { cursor with candidates := remaining } :: older

@[simp]
theorem replacementDatabaseClauseChoices_nil {σ : LPSignature}
    (cursor : DatabaseClauseCursorCore σ Instruction)
    (older : List (ChoicePointCore σ Instruction SourceClause)) :
    replacementDatabaseClauseChoices cursor [] older = older := rfl

/-- A nonempty remainder is retained as exactly one ordinary choice resource;
the selected occurrence itself is never copied into that resource. -/
@[simp]
theorem replacementDatabaseClauseChoices_cons {σ : LPSignature}
    (cursor : DatabaseClauseCursorCore σ Instruction)
    (candidate : DatabaseClauseCandidate σ)
    (remaining : List (DatabaseClauseCandidate σ))
    (older : List (ChoicePointCore σ Instruction SourceClause)) :
    replacementDatabaseClauseChoices cursor (candidate :: remaining) older =
      .databaseClause { cursor with candidates := candidate :: remaining } :: older :=
  rfl

/-- Normalize one live retract pattern to `Head :- Body`. Existing `(:-)/2`
terms are reused; a fact pattern is wrapped with a freshly allocated `true`.
The engine, not the source classifier or persistent session, owns dereference
and allocation. An unbound top-level pattern fails closed at this first
fragment rather than being allowed to enumerate and bind arbitrary clauses. -/
def normalizeRetractPattern {σ : LPSignature}
    [DecidableEq σ.functionSymbols]
    (encoding : ClauseEncoding σ) (memory : Memory σ.scoped)
    (pattern : Addr) : Except QueryError (Memory σ.scoped × Addr) :=
  match memory.heap.deref pattern with
  | .error error => .error (.memory error)
  | .ok (.variableCycle cycle) =>
      .error (.memory (.variableReferenceCycle cycle))
  | .ok (.root root) =>
      match memory.heap[root]? with
      | none => .error (.memory (.invalidAddress root))
      | some (.var _ none) => .error .invalidDynamicClause
      | some (.app symbol _) =>
          if symbol = encoding.rule then .ok (memory, root)
          else
            match memory.allocate (.const encoding.trueConstant) with
            | .error error => .error (.memory error)
            | .ok (truth, withTruth) =>
                match withTruth.allocate
                    (.app encoding.rule #[root, truth]) with
                | .error error => .error (.memory error)
                | .ok (normalized, result) => .ok (result, normalized)
      | some (.const _) =>
          match memory.allocate (.const encoding.trueConstant) with
          | .error error => .error (.memory error)
          | .ok (truth, withTruth) =>
              match withTruth.allocate (.app encoding.rule #[root, truth]) with
              | .error error => .error (.memory error)
              | .ok (normalized, result) => .ok (result, normalized)
      | some (.var _ (some _)) => .error .invalidDynamicClause

/-- Install the immutable call-time candidate snapshot supplied by the
persistent session. All subsequent selection, copying, unification,
backtracking, and continuation order are owned by the shared engine. -/
def openRetractStep {σ : LPSignature}
    [DecidableEq σ.functionSymbols]
    (encoding : ClauseEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (pattern : Addr) (candidates : List (DatabaseClauseCandidate σ)) :
    StepResultCore σ Instruction SourceClause :=
  match normalizeRetractPattern encoding state.memory pattern with
  | .error error => failWith state error
  | .ok (memory, normalized) =>
      let cursor : DatabaseClauseCursorCore σ Instruction := {
        checkpoint := memory.checkpoint
        pattern := normalized
        candidates
        control := state.control
        action := .retract
      }
      .next {
        state with
        memory
        phase := .databaseClauseSelect cursor
      } none

/-- Reject a wholly unbound `clause/3` head before opening a database cursor.
The shared signature cannot distinguish callable atoms from other constants,
so realization-specific callable/type errors remain a later boundary; this
check nevertheless makes unrestricted database enumeration unrepresentable. -/
def checkDatabaseClauseHead {σ : LPSignature}
    (memory : Memory σ.scoped) (head : Addr) : Except QueryError Unit :=
  match memory.heap.deref head with
  | .error error => .error (.memory error)
  | .ok (.variableCycle cycle) =>
      .error (.memory (.variableReferenceCycle cycle))
  | .ok (.root root) =>
      match memory.heap[root]? with
      | none => .error (.memory (.invalidAddress root))
      | some (.var _ none) => .error .invalidDynamicClause
      | some _ => .ok ()

/-- Open `clause/3` over the same immutable reflected-clause snapshot used by
`retract/1`.  The caller's head and body become one `(:-)/2` pattern in engine
memory; the session never sees bindings and never selects an occurrence. -/
def openClauseStep {σ : LPSignature}
    (encoding : ClauseEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (head body reference : Addr)
    (candidates : List (DatabaseClauseCandidate σ)) :
    StepResultCore σ Instruction SourceClause :=
  match checkDatabaseClauseHead state.memory head with
  | .error error => failWith state error
  | .ok _ =>
      match state.memory.allocate (.app encoding.rule #[head, body]) with
      | .error error => failWith state (.memory error)
      | .ok (pattern, memory) =>
          let cursor : DatabaseClauseCursorCore σ Instruction := {
            checkpoint := memory.checkpoint
            pattern
            candidates
            control := state.control
            action := .inspect reference encoding.referenceConstant
          }
          .next {
            state with
            memory
            phase := .databaseClauseSelect cursor
          } none

/-- Opening inspection performs exactly one engine-owned pattern allocation
and installs the supplied snapshot as a read-only cursor. -/
theorem openClauseStep_of_allocate {σ : LPSignature}
    (encoding : ClauseEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (head body reference pattern : Addr)
    (candidates : List (DatabaseClauseCandidate σ))
    (memory : Memory σ.scoped)
    (hHead : checkDatabaseClauseHead state.memory head = .ok ())
    (hAllocate : state.memory.allocate (.app encoding.rule #[head, body]) =
      .ok (pattern, memory)) :
    openClauseStep encoding state head body reference candidates =
      .next {
        state with
        memory
        phase := .databaseClauseSelect {
          checkpoint := memory.checkpoint
          pattern
          candidates
          control := state.control
          action := .inspect reference encoding.referenceConstant
        }
      } none := by
  simp [openClauseStep, hHead, hAllocate]

/-- The only data a language-specific clause materializer may supply to the
shared selected-clause transition.  The type has no constructors for answers,
effects, alternatives, pruning, or scheduling. -/
structure MaterializedBody (σ : LPSignature) (Instruction : Type*) where
  memory : Memory σ.scoped
  head : RuntimeAtom σ.scoped
  body : List Instruction

/-- Materialize one source clause at an explicit activation scope.  Search
order, cursor retention, fresh-scope advancement, and head entry remain owned
by the shared query transition below. -/
structure ClauseMaterializer (σ : LPSignature)
    (Instruction SourceClause : Type*) where
  materialize : Memory σ.scoped → Nat → SourceClause →
    Except MemoryError (MaterializedBody σ Instruction)

/-- The pure LP clause materializer used by the established runtime. -/
def lpClauseMaterializer {σ : LPSignature} [DecidableEq σ.scoped.vars] :
    ClauseMaterializer σ (RuntimeAtom σ.scoped) (Clause σ) where
  materialize memory scope clause :=
    match RuntimeMaterialize.materializeClause memory (clause.atScope scope) with
    | .error error => .error error
    | .ok result => .ok {
        memory := result.memory
        head := result.clause.head
        body := result.clause.body
      }

/-- Shared selected-clause transition.  It owns source-order cursor advance,
choice retention, persistent scope advance, and entry into the canonical graph
unifier. -/
def selectStep {σ : LPSignature} [DecidableEq σ.relationSymbols]
    (materializer : ClauseMaterializer σ Instruction SourceClause)
    (state : StateCore σ Instruction SourceClause)
    (cursor : ClauseCursorCore σ Instruction SourceClause) :
    StepResultCore σ Instruction SourceClause :=
  match cursor.clauses with
  | [] => .next { state with phase := .backtrack } none
  | clause :: remaining =>
      match materializer.materialize state.memory state.nextScope clause with
      | .error error => failWith state (.memory error)
      | .ok copied =>
          match RuntimeClauseEntry.enter cursor.goal copied.head
              copied.memory copied.body with
          | .error _ => failWith state .predicateMismatch
          | .ok entered =>
              let attempt : AttemptCore σ Instruction := {
                body := entered.body
                cutDepth := cursor.cutDepth
                frames := cursor.frames
              }
              .next {
                state with
                memory := entered.memory
                choices := replacementChoices cursor remaining state.choices
                nextScope := state.nextScope + 1
                phase := .unifying attempt entered.unifier
              } none

/-- Try one frozen database-clause candidate. The candidate is standardized
apart at the persistent scope high-water and compared with the normalized
live pattern by the canonical graph unifier. Inspection additionally unifies
the opaque reference; retraction instead requests erasure of that exact stable
identity after unification succeeds. -/
def databaseClauseSelectStep {σ : LPSignature} [DecidableEq σ.scoped.vars]
    (state : StateCore σ Instruction SourceClause)
    (cursor : DatabaseClauseCursorCore σ Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match cursor.candidates with
  | [] => .next { state with phase := .backtrack } none
  | candidate :: remaining =>
      match RuntimeMaterialize.materializeTerm state.memory
          (candidate.clause.atScope state.nextScope) with
      | .error error => failWith state (.memory error)
      | .ok copied =>
          match cursor.action with
          | .retract =>
              let attempt : AttemptCore σ Instruction := {
                body := cursor.control.current
                cutDepth := cursor.control.cutDepth
                frames := cursor.control.frames
                onSuccess := .eraseRef candidate.reference
              }
              .next {
                state with
                memory := copied.memory
                choices := replacementDatabaseClauseChoices cursor remaining state.choices
                nextScope := state.nextScope + 1
                phase := .unifying attempt
                  (RuntimeUnification.startMany copied.memory
                    [(cursor.pattern, copied.root)])
              } none
          | .inspect referenceRoot referenceConstant =>
              match copied.memory.allocate
                  (.const (referenceConstant candidate.reference)) with
              | .error error => failWith state (.memory error)
              | .ok (copiedReference, memory) =>
                  let attempt : AttemptCore σ Instruction := {
                    body := cursor.control.current
                    cutDepth := cursor.control.cutDepth
                    frames := cursor.control.frames
                  }
                  .next {
                    state with
                    memory
                    choices := replacementDatabaseClauseChoices cursor remaining state.choices
                    nextScope := state.nextScope + 1
                    phase := .unifying attempt
                      (RuntimeUnification.startMany memory
                        [(cursor.pattern, copied.root),
                          (referenceRoot, copiedReference)])
                  } none

/-- Exhausting the frozen retract snapshot enters the same backtracking phase
as an exhausted clause cursor; it cannot manufacture completion or failure. -/
@[simp]
theorem databaseClauseSelectStep_empty {σ : LPSignature}
    [DecidableEq σ.scoped.vars]
    (state : StateCore σ Instruction SourceClause)
    (cursor : DatabaseClauseCursorCore σ Instruction) :
    databaseClauseSelectStep state { cursor with candidates := [] } =
      .next { state with phase := .backtrack } none := rfl

/-- Candidate content and stable identity travel through one constructor
case: after canonical materialization, the unifier compares exactly that
candidate and its success authority names exactly that candidate's reference. -/
theorem databaseClauseSelectStep_retract_cons_of_materialize {σ : LPSignature}
    [DecidableEq σ.scoped.vars]
    (state : StateCore σ Instruction SourceClause)
    (cursor : DatabaseClauseCursorCore σ Instruction)
    (candidate : DatabaseClauseCandidate σ)
    (remaining : List (DatabaseClauseCandidate σ))
    (copied : RuntimeMaterialize.MaterializedTerm σ.scoped)
    (hCandidates : cursor.candidates = candidate :: remaining)
    (hAction : cursor.action = .retract)
    (hMaterialize : RuntimeMaterialize.materializeTerm state.memory
      (candidate.clause.atScope state.nextScope) = .ok copied) :
    databaseClauseSelectStep state cursor =
      .next {
        state with
        memory := copied.memory
        choices := replacementDatabaseClauseChoices cursor remaining state.choices
        nextScope := state.nextScope + 1
        phase := .unifying {
          body := cursor.control.current
          cutDepth := cursor.control.cutDepth
          frames := cursor.control.frames
          onSuccess := .eraseRef candidate.reference
        } (RuntimeUnification.startMany copied.memory
          [(cursor.pattern, copied.root)])
      } none := by
  simp [databaseClauseSelectStep, hCandidates, hAction, hMaterialize]

/-- The read-only arm couples all three observable pieces from the same
snapshot occurrence: its copied clause term, its stable reference, and the
retained tail.  Hence a realization cannot pair a clause from one scan with a
reference or retry cursor from another. -/
theorem databaseClauseSelectStep_inspect_cons_of_materialize_allocate
    {σ : LPSignature} [DecidableEq σ.scoped.vars]
    (state : StateCore σ Instruction SourceClause)
    (cursor : DatabaseClauseCursorCore σ Instruction)
    (candidate : DatabaseClauseCandidate σ)
    (remaining : List (DatabaseClauseCandidate σ))
    (referenceRoot copiedReference : Addr)
    (referenceConstant : Nat → σ.constants)
    (copied : RuntimeMaterialize.MaterializedTerm σ.scoped)
    (memory : Memory σ.scoped)
    (hCandidates : cursor.candidates = candidate :: remaining)
    (hAction : cursor.action = .inspect referenceRoot referenceConstant)
    (hMaterialize : RuntimeMaterialize.materializeTerm state.memory
      (candidate.clause.atScope state.nextScope) = .ok copied)
    (hAllocate : copied.memory.allocate
      (.const (referenceConstant candidate.reference)) =
        .ok (copiedReference, memory)) :
    databaseClauseSelectStep state cursor =
      .next {
        state with
        memory
        choices := replacementDatabaseClauseChoices cursor remaining state.choices
        nextScope := state.nextScope + 1
        phase := .unifying {
          body := cursor.control.current
          cutDepth := cursor.control.cutDepth
          frames := cursor.control.frames
        } (RuntimeUnification.startMany memory
          [(cursor.pattern, copied.root), (referenceRoot, copiedReference)])
      } none := by
  simp [databaseClauseSelectStep, hCandidates, hAction, hMaterialize,
    hAllocate]

/-- Resume after a yielded answer by entering the shared backtracking phase. -/
@[simp]
def afterAnswerStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) :
    StepResultCore σ Instruction SourceClause :=
  .next { state with phase := .backtrack } none

/-- Replace exactly the collection sentinel with `mark` older choices beneath
it, preserving every newer generator alternative and their order. -/
def recordCollectionChoice {σ : LPSignature}
    (mark : Nat) (answer : Term σ.scoped) :
    List (ChoicePointCore σ Instruction SourceClause) →
      Option (List (ChoicePointCore σ Instruction SourceClause))
  | [] => none
  | choice :: older =>
      if older.length = mark then
        match choice with
        | .collection boundary =>
            some (.collection {
              boundary with reversed := answer :: boundary.reversed
            } :: older)
        | _ => none
      else
        match recordCollectionChoice mark answer older with
        | none => none
        | some updated => some (choice :: updated)

/-- A positional collection update reaches exactly its owned sentinel, leaves
every newer generator alternative and older caller alternative in place, and
prepends one detached answer. -/
theorem recordCollectionChoice_marker {σ : LPSignature}
    (newer older : List (ChoicePointCore σ Instruction SourceClause))
    (boundary : CollectionChoiceCore σ Instruction)
    (answer : Term σ.scoped) :
    recordCollectionChoice older.length answer
        (newer ++ .collection boundary :: older) =
      some (newer ++ .collection {
        boundary with reversed := answer :: boundary.reversed
      } :: older) := by
  induction newer with
  | nil => simp [recordCollectionChoice]
  | cons choice newer ih =>
      have hLength : newer.length + (older.length + 1) ≠ older.length := by
        omega
      simp [recordCollectionChoice, hLength, ih]

/-- Privately consume one generator success.  The template is detached from
the live heap and renamed immediately at the persistent high-water, so later
backtracking cannot erase it and distinct solutions cannot share variables. -/
def collectAnswerStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (handler : CollectionHandlerCore σ) :
    StepResultCore σ Instruction SourceClause :=
  match RuntimeException.capture state.memory.heap handler.template with
  | .error error => failWith state (.collectionReadback error)
  | .ok packet =>
      let answer := packet.freshTerm state.nextScope
      match recordCollectionChoice handler.choiceDepth answer state.choices with
      | none => failWith state .missingCollectionBoundary
      | some choices =>
          .next {
            state with
            choices
            nextScope := state.nextScope +
              RuntimeException.scopeCeiling packet.term
            phase := .backtrack
          } none

/-- A successful private capture emits no public observation, advances the
persistent fresh scope by the copied term's exact ceiling, and enters ordinary
backtracking with the uniquely updated collection stack. -/
theorem collectAnswerStep_of_capture {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (handler : CollectionHandlerCore σ)
    (packet : RuntimeException.Packet σ)
    (choices : List (ChoicePointCore σ Instruction SourceClause))
    (hCapture : RuntimeException.capture state.memory.heap handler.template =
      .ok packet)
    (hRecord : recordCollectionChoice handler.choiceDepth
      (packet.freshTerm state.nextScope) state.choices = some choices) :
    collectAnswerStep state handler =
      .next {
        state with
        choices
        nextScope := state.nextScope + RuntimeException.scopeCeiling packet.term
        phase := .backtrack
      } none := by
  simp [collectAnswerStep, hCapture, hRecord]

/-- Resume one checkpointed control alternative. -/
@[simp]
def resumeBranchStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (alternative : BranchChoiceCore σ Instruction)
    (older : List (ChoicePointCore σ Instruction SourceClause)) :
    StepResultCore σ Instruction SourceClause :=
  match state.memory.restore alternative.checkpoint with
  | .error error => failWith state (.memory error)
  | .ok memory =>
      .next {
        state with
        memory
        control := alternative.control
        choices := older
        phase := .dispatch
      } none

/-- Close an exhausted collection: restore its entry checkpoint, materialize
the privately accumulated answers in source order, and unify the caller's bag
through the canonical graph unifier. -/
@[simp]
def finalizeCollectionStep {σ : LPSignature} [DecidableEq σ.scoped.vars]
    (state : StateCore σ Instruction SourceClause)
    (boundary : CollectionChoiceCore σ Instruction)
    (older : List (ChoicePointCore σ Instruction SourceClause)) :
    StepResultCore σ Instruction SourceClause :=
  match state.memory.restore boundary.checkpoint with
  | .error error => failWith state (.memory error)
  | .ok restored =>
      let listTerm := boundary.encoding.listTerm boundary.reversed.reverse
      match RuntimeMaterialize.materializeTerm restored listTerm with
      | .error error => failWith { state with memory := restored } (.memory error)
      | .ok result =>
          let attempt : AttemptCore σ Instruction := {
            body := boundary.continuation
            cutDepth := boundary.callerCutDepth
            frames := boundary.outerFrames
          }
          .next {
            state with
            memory := result.memory
            choices := older
            phase := .unifying attempt
              (RuntimeUnification.startMany result.memory
                [(boundary.bag, result.root)])
          } none

/-- Restore and re-enter the newest retained cursor, finalize a collection
whose generator is exhausted, or close the query when no alternatives remain. -/
@[simp]
def backtrackStep {σ : LPSignature} [DecidableEq σ.scoped.vars]
    (state : StateCore σ Instruction SourceClause) :
    StepResultCore σ Instruction SourceClause :=
  match state.choices with
  | [] => complete state
  | .clause cursor :: older =>
      match state.memory.restore cursor.checkpoint with
      | .error error => failWith state (.memory error)
      | .ok memory =>
          .next {
            state with
            memory
            choices := older
            phase := .select cursor
          } none
  | .branch alternative :: older => resumeBranchStep state alternative older
  | .softElse alternative :: older => resumeBranchStep state alternative older
  | .collection boundary :: older =>
      finalizeCollectionStep state boundary older
  | .databaseClause cursor :: older =>
      match state.memory.restore cursor.checkpoint with
      | .error error => failWith state (.memory error)
      | .ok memory =>
          .next {
            state with
            memory
            choices := older
            phase := .databaseClauseSelect cursor
          } none

/-- Remove the soft-conditional delimiter immediately above the `mark` oldest
choices.  The stack is newest first.  If that delimiter was already removed,
the function is the identity; this is what permits each later condition answer
to pass through the same saved success frame without committing the condition.
-/
def eraseSoftElseAboveBottom (mark : Nat) :
    List (ChoicePointCore σ Instruction SourceClause) →
      List (ChoicePointCore σ Instruction SourceClause)
  | [] => []
  | choice :: older =>
      if older.length = mark then
        match choice with
        | .softElse _ => older
        | _ => choice :: older
      else
        choice :: eraseSoftElseAboveBottom mark older

/-- An empty current goal stack either returns to its caller frame or yields
one answer at the outermost query. -/
@[simp]
def emptyCurrentStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) :
    StepResultCore σ Instruction SourceClause :=
  match state.control.frames with
  | frame :: frames =>
      match frame.collection with
      | some handler => collectAnswerStep state handler
      | none => match frame.commit with
      | .ordinary =>
          .next {
            state with
            control := {
              current := frame.continuation
              cutDepth := frame.callerCutDepth
              frames
            }
          } none
      | .hard mark =>
          if _hDepth : mark ≤ state.choices.length then
            .next {
              state with
              control := {
                current := frame.continuation
                cutDepth := frame.callerCutDepth
                frames
              }
              choices := retainBottom mark state.choices
            } none
          else
            failWith state (.invalidCommitDepth mark state.choices.length)
      | .soft mark =>
          if _hDepth : mark ≤ state.choices.length then
            .next {
              state with
              control := {
                current := frame.continuation
                cutDepth := frame.callerCutDepth
                frames
              }
              choices := eraseSoftElseAboveBottom mark state.choices
            } none
          else
            failWith state (.invalidCommitDepth mark state.choices.length)
  | [] =>
      .next { state with phase := .afterAnswer }
        (some (.answer {
          memory := state.memory
          queryVarMap := state.queryVarMap
        }))

/-- Advance the canonical graph unifier by one microstep or install its
selected body/failure in the shared search state. -/
@[simp]
def unifyingStep {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (attempt : AttemptCore σ Instruction)
    (machine : RuntimeUnification.Machine σ.scoped) :
    StepResultCore σ Instruction SourceClause :=
  match machine with
  | .running _ =>
      match RuntimeUnification.step machine with
      | some next =>
          .next { state with phase := .unifying attempt next } none
      | none => failWith state .stalledUnifier
  | .terminal (.success memory) =>
      let succeeded := {
        state with
        memory
        control := {
          current := attempt.body
          cutDepth := attempt.cutDepth
          frames := attempt.frames
        }
        phase := .dispatch
      }
      match attempt.onSuccess with
      | .continue => .next succeeded none
      | .eraseRef reference =>
          .databaseRequest (.eraseRef reference) succeeded
  | .terminal (.failure memory) =>
      .next { state with memory, phase := .backtrack } none
  | .terminal (.runtimeError error memory) =>
      failWith { state with memory } (.memory error)

/-- Enter the protected goal of `catch/3`.  The guarded goal receives a fresh
local cut boundary at the current choice depth.  The frame stores the exact
heap/trail checkpoint and recovery data needed by exception unwind. -/
@[simp]
def catchStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (guarded : List Instruction) (catcher : Addr)
    (recovery rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  let mark := state.choices.length
  let handler : CatchHandlerCore σ Instruction := {
    checkpoint := state.memory.checkpoint
    choiceDepth := mark
    catcher
    recovery
  }
  let frame : ReturnFrameCore σ Instruction := {
    continuation := rest
    callerCutDepth := state.control.cutDepth
    handler := some handler
  }
  .next {
    state with
    control := {
      current := guarded
      cutDepth := mark
      frames := frame :: state.control.frames
    }
  } none

/-- Capture an ordinary throw-time finite term before any frame or choice is
unwound.  The detached packet, rather than the original heap address, crosses
rollback. -/
def captureThrowStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) (ball : Addr) :
    StepResultCore σ Instruction SourceClause :=
  match RuntimeException.capture state.memory.heap ball with
  | .error error => failWith state (.exceptionReadback error)
  | .ok packet => .next { state with phase := .raising packet } none

/-- Execute `throw/1` through the canonical exception path.  The engine owns
the heap inspection: if the root is an unbound variable, it raises the
language realization's explicit instantiation-error packet when supplied.
The realization cannot inspect memory, unwind a frame, or schedule recovery.
Without that optional capability, the generic typed layer retains its finite
packet behavior. -/
@[simp]
def throwStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) (ball : Addr)
    (unboundError : Option (RuntimeException.Packet σ)) :
    StepResultCore σ Instruction SourceClause :=
  match unboundError with
  | none => captureThrowStep state ball
  | some errorPacket =>
      match state.memory.heap.deref ball with
      | .ok (.root root) =>
          match state.memory.heap[root]? with
          | some (.var _ none) =>
              .next { state with phase := .raising errorPacket } none
          | _ => captureThrowStep state ball
      | _ => captureThrowStep state ball

/-- Continue catcher search at the next outer delimiter without unwinding.
All candidate catchers must observe the same throw-time bindings, matching
SWI's `findCatcher` walk.  Actual restoration and pruning happen only after a
candidate has matched. -/
def passException {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (selection : CatchSelectionCore σ Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match findCatchTarget selection.target.outerFrames with
  | none =>
      raiseUnhandled { state with memory := selection.throwMemory }
        selection.packet
  | some target =>
      let nextSelection := { selection with target }
      .next {
        state with
        memory := selection.throwMemory
        phase := .catchSelecting nextSelection
          (RuntimeUnification.start selection.throwMemory
            target.handler.catcher selection.packetRoot)
      } none

/-- After throw-time catcher selection succeeds, restore the catch-entry
checkpoint, install a fresh copy of the packet, and ask the same graph unifier
to reconstruct the recovery binding in the entry context. -/
def beginCatchRecovery {σ : LPSignature} [DecidableEq σ.scoped.vars]
    (state : StateCore σ Instruction SourceClause)
    (selection : CatchSelectionCore σ Instruction)
    (memory : Memory σ.scoped) :
    StepResultCore σ Instruction SourceClause :=
  let target := selection.target
  if _hDepth : target.handler.choiceDepth ≤ state.choices.length then
    match memory.restore target.handler.checkpoint with
    | .error error => failWith { state with memory } (.memory error)
    | .ok restored =>
        match selection.packet.install restored state.nextScope with
        | .error error => failWith { state with memory := restored } (.memory error)
        | .ok installed =>
            .next {
              state with
              memory := installed.memory
              choices := retainBottom target.handler.choiceDepth state.choices
              nextScope := installed.nextScope
              phase := .catchRecovering selection
                (RuntimeUnification.start installed.memory
                  target.handler.catcher installed.root)
            } none
  else
    failWith { state with memory }
      (.invalidCommitDepth target.handler.choiceDepth state.choices.length)

/-- Locate the nearest catcher and start its throw-time match.  Installing a
fresh packet copy before selection prevents the match from binding the durable
packet itself. -/
def raisingStep {σ : LPSignature} [DecidableEq σ.scoped.vars]
    (state : StateCore σ Instruction SourceClause)
    (packet : RuntimeException.Packet σ) :
    StepResultCore σ Instruction SourceClause :=
  match findCatchTarget state.control.frames with
  | none => raiseUnhandled state packet
  | some target =>
      match packet.install state.memory state.nextScope with
      | .error error => failWith state (.memory error)
      | .ok installed =>
          let selection : CatchSelectionCore σ Instruction := {
            packet
            target
            throwMemory := installed.memory
            packetRoot := installed.root
          }
          .next {
            state with
            memory := installed.memory
            nextScope := installed.nextScope
            phase := .catchSelecting selection
              (RuntimeUnification.start installed.memory
                target.handler.catcher installed.root)
          } none

/-- Advance throw-time catcher selection through the canonical graph unifier.
Failure passes the packet outward; success begins entry-context recovery. -/
def catchSelectingStep {σ : LPSignature} [DecidableEq σ.scoped.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (selection : CatchSelectionCore σ Instruction)
    (machine : RuntimeUnification.Machine σ.scoped) :
    StepResultCore σ Instruction SourceClause :=
  match machine with
  | .running _ =>
      match RuntimeUnification.step machine with
      | some next =>
          .next { state with phase := .catchSelecting selection next } none
      | none => failWith state .stalledUnifier
  | .terminal (.success memory) => beginCatchRecovery state selection memory
  | .terminal (.failure _) => passException state selection
  | .terminal (.runtimeError error memory) =>
      failWith { state with memory } (.memory error)

/-- Advance the second, entry-context unification.  A defensive failure
continues unwinding rather than swallowing the exception; success consumes the
catch delimiter and executes recovery outside it. -/
def catchRecoveringStep {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (selection : CatchSelectionCore σ Instruction)
    (machine : RuntimeUnification.Machine σ.scoped) :
    StepResultCore σ Instruction SourceClause :=
  match machine with
  | .running _ =>
      match RuntimeUnification.step machine with
      | some next =>
          .next { state with phase := .catchRecovering selection next } none
      | none => failWith state .stalledUnifier
  | .terminal (.success memory) =>
      let target := selection.target
      let recoveryFrame : ReturnFrameCore σ Instruction := {
        target.frame with handler := none
      }
      .next {
        state with
        memory
        control := {
          current := target.handler.recovery
          cutDepth := target.handler.choiceDepth
          frames := recoveryFrame :: target.outerFrames
        }
        phase := .dispatch
      } none
  | .terminal (.failure _) => passException state selection
  | .terminal (.runtimeError error memory) =>
      failWith { state with memory } (.memory error)

/-- Execute a validated cut against the choice depth captured by the current
predicate activation.  Instruction classification remains language-specific;
choice ownership and pruning are shared here. -/
@[simp]
def cutStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  if _hDepth : state.control.cutDepth ≤ state.choices.length then
    .next {
      state with
      control := { state.control with current := rest }
      choices := retainBottom state.control.cutDepth state.choices
    } none
  else
    failWith state
      (.invalidCutDepth state.control.cutDepth state.choices.length)

/-- Enter an ordinary predicate call by transferring its source-ordered
clause alternatives into the shared cursor representation.  This transition
does not select or execute a clause. -/
@[simp]
def callStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (goal : RuntimeAtom σ.scoped) (clauses : List SourceClause)
    (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  let frame : ReturnFrameCore σ Instruction := {
    continuation := rest
    callerCutDepth := state.control.cutDepth
  }
  let cursor : ClauseCursorCore σ Instruction SourceClause := {
    checkpoint := state.memory.checkpoint
    goal
    clauses
    cutDepth := state.choices.length
    frames := frame :: state.control.frames
  }
  .next { state with phase := .select cursor } none

/-- Enter a left-first structured branch.  The right branch and the caller's
remaining goals become one checkpointed choice; the left branch executes now.
This is the direct typed analogue of SWI-Prolog's `C_OR`/`CHP_JUMP` path. -/
@[simp]
def branchStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (left right rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  let alternative : BranchChoiceCore σ Instruction := {
    checkpoint := state.memory.checkpoint
    control := {
      current := right ++ rest
      cutDepth := state.control.cutDepth
      frames := state.control.frames
    }
  }
  .next {
    state with
    control := {
      current := left ++ rest
      cutDepth := state.control.cutDepth
      frames := state.control.frames
    }
    choices := .branch alternative :: state.choices
  } none

/-- Enter a hard if-then-else through the same branch choice and success-frame
machinery.  The condition's local cut depth retains the else marker while
pruning choices created inside the condition.  First condition success commits
that marker through `emptyCurrentStep` before entering `thenBranch`. -/
@[simp]
def ifThenElseStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (condition thenBranch elseBranch rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  let mark := state.choices.length
  let alternative : BranchChoiceCore σ Instruction := {
    checkpoint := state.memory.checkpoint
    control := {
      current := elseBranch ++ rest
      cutDepth := state.control.cutDepth
      frames := state.control.frames
    }
  }
  let success : ReturnFrameCore σ Instruction := {
    continuation := thenBranch ++ rest
    callerCutDepth := state.control.cutDepth
    commit := .hard mark
  }
  .next {
    state with
    control := {
      current := condition
      cutDepth := mark + 1
      frames := success :: state.control.frames
    }
    choices := .branch alternative :: state.choices
  } none

/-- Enter soft if-then-else on the same choice stack.  Its else continuation is
tagged as a delimiter.  Each condition success removes only that delimiter,
so other condition alternatives remain available and run the then branch in
source order. -/
@[simp]
def softIfThenElseStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (condition thenBranch elseBranch rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  let mark := state.choices.length
  let alternative : BranchChoiceCore σ Instruction := {
    checkpoint := state.memory.checkpoint
    control := {
      current := elseBranch ++ rest
      cutDepth := state.control.cutDepth
      frames := state.control.frames
    }
  }
  let success : ReturnFrameCore σ Instruction := {
    continuation := thenBranch ++ rest
    callerCutDepth := state.control.cutDepth
    commit := .soft mark
  }
  .next {
    state with
    control := {
      current := condition
      cutDepth := mark + 1
      frames := success :: state.control.frames
    }
    choices := .softElse alternative :: state.choices
  } none

/-- Enter `once/1` as a hard commit without an else marker.  Failure simply
backtracks through the caller's pre-existing alternatives; first success
removes every choice created by the guarded goal and resumes the caller. -/
@[simp]
def onceStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (goals rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  let mark := state.choices.length
  let success : ReturnFrameCore σ Instruction := {
    continuation := rest
    callerCutDepth := state.control.cutDepth
    commit := .hard mark
  }
  .next {
    state with
    control := {
      current := goals
      cutDepth := mark
      frames := success :: state.control.frames
    }
  } none

/-- Enter `findall/3` by transferring the outer continuation into one
collection sentinel on the canonical choice stack.  Generator successes are
consumed by the collection frame; its cut depth retains the sentinel and all
older caller alternatives while permitting cuts to prune only generator-local
choices. -/
@[simp]
def findallStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (template : Addr) (generator : List Instruction) (bag : Addr)
    (encoding : CollectionEncoding σ) (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  let mark := state.choices.length
  let boundary : CollectionChoiceCore σ Instruction := {
    checkpoint := state.memory.checkpoint
    template
    bag
    encoding
    continuation := rest
    callerCutDepth := state.control.cutDepth
    outerFrames := state.control.frames
  }
  let frame : ReturnFrameCore σ Instruction := {
    continuation := rest
    callerCutDepth := state.control.cutDepth
    collection := some { choiceDepth := mark, template }
  }
  .next {
    state with
    control := {
      current := generator
      cutDepth := mark + 1
      frames := frame :: state.control.frames
    }
    choices := .collection boundary :: state.choices
  } none

/-- `findall/3` transfers its continuation into exactly one typed sentinel and
enters the generator with a cut boundary immediately above that sentinel. -/
theorem findallStep_exact {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (template : Addr) (generator : List Instruction) (bag : Addr)
    (encoding : CollectionEncoding σ) (rest : List Instruction) :
    findallStep state template generator bag encoding rest =
      .next {
        state with
        control := {
          current := generator
          cutDepth := state.choices.length + 1
          frames := {
            continuation := rest
            callerCutDepth := state.control.cutDepth
            collection := some {
              choiceDepth := state.choices.length
              template
            }
          } :: state.control.frames
        }
        choices := .collection {
          checkpoint := state.memory.checkpoint
          template
          bag
          encoding
          continuation := rest
          callerCutDepth := state.control.cutDepth
          outerFrames := state.control.frames
        } :: state.choices
      } none := rfl

/-- Enter one dynamically decoded goal under its own predicate-like cut
boundary.  This is the WAM `B0 := B` discipline for meta-call: choices older
than the call survive, while a cut in the decoded goal can prune alternatives
created by that goal.  Decoding is read-only and occurs exactly once. -/
@[simp]
def metaCallStep {σ : LPSignature}
    (decoder : MetaCallDecoder σ Instruction)
    (state : StateCore σ Instruction SourceClause)
    (callable : Addr) (extraArgs : List Addr) (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match decoder.decode state.memory.heap callable extraArgs with
  | .error reason => failWith state reason
  | .ok goals =>
      .next {
        state with
        control := {
          current := goals
          cutDepth := state.choices.length
          frames := {
            continuation := rest
            callerCutDepth := state.control.cutDepth
            commit := .ordinary
          } :: state.control.frames
        }
      } none

/-- Enter body unification through the same canonical graph unifier used for
clause heads.  SWI-Prolog V10.1.9 likewise routes `=/2` through `PL_unify`
(`src/pl-prims.c`) and body unification instructions (`src/pl-vmi.c`). -/
@[simp]
def beginUnifyStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (left right : Addr) (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  let attempt : AttemptCore σ Instruction := {
    body := rest
    cutDepth := state.control.cutDepth
    frames := state.control.frames
  }
  .next {
    state with
    phase := .unifying attempt
      (RuntimeUnification.startMany state.memory [(left, right)])
  } none

/-- Bind a successful database insertion's stable identity through the same
canonical graph unifier as every other Prolog binding.  The session supplies
only the opaque atomic value; it cannot write the heap or schedule the
continuation. -/
def bindDatabaseReferenceStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (referenceRoot : Addr) (reference : σ.constants) :
    StepResultCore σ Instruction SourceClause :=
  match state.memory.allocate (.const reference) with
  | .error error => failWith state (.memory error)
  | .ok (valueRoot, memory) =>
      let attempt : AttemptCore σ Instruction := {
        body := state.control.current
        cutDepth := state.control.cutDepth
        frames := state.control.frames
      }
      .next {
        state with
        memory
        phase := .unifying attempt
          (RuntimeUnification.startMany memory
            [(referenceRoot, valueRoot)])
      } none

/-- Once allocation succeeds, reference binding is exactly one canonical
unifier activation over the caller's output root and the opaque value cell. -/
theorem bindDatabaseReferenceStep_of_allocate {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (referenceRoot valueRoot : Addr) (reference : σ.constants)
    (memory : Memory σ.scoped)
    (hAllocate : state.memory.allocate (.const reference) =
      .ok (valueRoot, memory)) :
    bindDatabaseReferenceStep state referenceRoot reference =
      .next {
        state with
        memory
        phase := .unifying {
          body := state.control.current
          cutDepth := state.control.cutDepth
          frames := state.control.frames
        } (RuntimeUnification.startMany memory
          [(referenceRoot, valueRoot)])
      } none := by
  simp [bindDatabaseReferenceStep, hAllocate]

/-- Apply one shallow term test after engine-owned dereference.  This is the
canonical finite-graph counterpart of SWI-Prolog V10.1.9's `PL_is_variable`,
`PL_is_atom`, `PL_is_atomic`, `PL_is_number`, `PL_is_string`, and
`PL_is_compound` predicates (`src/pl-prims.c`).  A false test enters ordinary
backtracking; corrupt addresses and variable-only cycles remain typed errors. -/
@[simp]
def termTestStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (address : Addr) (test : TermTest σ) (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match state.memory.heap.deref address with
  | .error error => failWith state (.memory error)
  | .ok (.variableCycle cycle) =>
      failWith state (.memory (.variableReferenceCycle cycle))
  | .ok (.root root) =>
      match state.memory.heap[root]? with
      | none => failWith state (.memory (.invalidAddress root))
      | some cell =>
          if test.accepts cell then
            .next {
              state with
              control := { state.control with current := rest }
            } none
          else .next { state with phase := .backtrack } none

/-- An accepted shallow root consumes exactly the current instruction and
continues without changing memory, choices, or frames. -/
theorem termTestStep_accepts {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (address root : Addr) (test : TermTest σ) (rest : List Instruction)
    (cell : Cell σ.scoped)
    (hDeref : state.memory.heap.deref address = .ok (.root root))
    (hCell : state.memory.heap[root]? = some cell)
    (hAccept : test.accepts cell = true) :
    termTestStep state address test rest =
      .next {
        state with
        control := { state.control with current := rest }
      } none := by
  simp [termTestStep, hDeref, hCell, hAccept]

/-- A rejected shallow root enters the ordinary shared backtracking phase;
there is no test-specific failure or restoration path. -/
theorem termTestStep_rejects {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (address root : Addr) (test : TermTest σ) (rest : List Instruction)
    (cell : Cell σ.scoped)
    (hDeref : state.memory.heap.deref address = .ok (.root root))
    (hCell : state.memory.heap[root]? = some cell)
    (hReject : test.accepts cell = false) :
    termTestStep state address test rest =
      .next { state with phase := .backtrack } none := by
  simp [termTestStep, hDeref, hCell, hReject]

/-- Test strict graph identity without binding.  `expected = true` realizes
`==/2`; `expected = false` realizes `\==/2` through the same comparison and
ordinary backtracking path. -/
def termIdentityStep {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (left right : Addr) (expected : Bool) (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match termIdentical state.memory.heap left right with
  | .error error => failWith state error
  | .ok actual =>
      if actual = expected then
        .next {
          state with
          control := { state.control with current := rest }
        } none
      else .next { state with phase := .backtrack } none

/-- A completed identity comparison has exactly the polarity-controlled
shared transition; it cannot bind, trail, emit an answer, or choose work. -/
theorem termIdentityStep_of_result {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (left right : Addr) (expected actual : Bool) (rest : List Instruction)
    (hResult : termIdentical state.memory.heap left right = .ok actual) :
    termIdentityStep state left right expected rest =
      if actual = expected then
        .next {
          state with
          control := { state.control with current := rest }
        } none
      else .next { state with phase := .backtrack } none := by
  simp [termIdentityStep, hResult]

/-- Execute one prepared `=../2` operation through the canonical graph
unifier.  Preparation owns only finite heap inspection/allocation; all binding,
rollback, continuation, and answer behavior remains the shared phase loop. -/
def univStep {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (termRoot listRoot : Addr) (encoding : UnivEncoding σ)
    (rest : List Instruction) : StepResultCore σ Instruction SourceClause :=
  match prepareUniv encoding state.memory termRoot listRoot with
  | .error error => failWith state error
  | .ok prepared =>
      .next {
        state with
        memory := prepared.memory
        phase := .unifying {
          body := rest
          cutDepth := state.control.cutDepth
          frames := state.control.frames
        } (RuntimeUnification.startMany prepared.memory
          [(prepared.left, prepared.right)])
      } none

/-- Successful preparation has one exact effect: start the existing unifier
on its returned pair under the caller's unchanged control delimiters. -/
theorem univStep_of_prepare {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (termRoot listRoot : Addr) (encoding : UnivEncoding σ)
    (rest : List Instruction) (prepared : UnivPrepared σ)
    (hPrepare : prepareUniv encoding state.memory termRoot listRoot =
      .ok prepared) :
    univStep state termRoot listRoot encoding rest =
      .next {
        state with
        memory := prepared.memory
        phase := .unifying {
          body := rest
          cutDepth := state.control.cutDepth
          frames := state.control.frames
        } (RuntimeUnification.startMany prepared.memory
          [(prepared.left, prepared.right)])
      } none := by
  simp [univStep, hPrepare]

/-- Evaluate one integer expression, allocate its canonical constant, and
enter the existing graph unifier against the result root. -/
def integerIsStep {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (resultRoot expressionRoot : Addr)
    (encoding : IntegerArithmeticEncoding σ) (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match evalInteger encoding state.memory.heap expressionRoot with
  | .error error => failWith state error
  | .ok value =>
      match state.memory.allocate (.const (encoding.encodeInteger value)) with
      | .error error => failWith state (.memory error)
      | .ok (valueRoot, memory) =>
          .next {
            state with
            memory
            phase := .unifying {
              body := rest
              cutDepth := state.control.cutDepth
              frames := state.control.frames
            } (RuntimeUnification.startMany memory [(resultRoot, valueRoot)])
          } none

/-- A successful integer evaluation/allocation enters exactly one canonical
unification attempt and preserves the caller's control delimiters. -/
theorem integerIsStep_of_eval_allocate {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (resultRoot expressionRoot valueRoot : Addr) (value : Int)
    (memory : Memory σ.scoped) (encoding : IntegerArithmeticEncoding σ)
    (rest : List Instruction)
    (hEval : evalInteger encoding state.memory.heap expressionRoot = .ok value)
    (hAllocate : state.memory.allocate (.const (encoding.encodeInteger value)) =
      .ok (valueRoot, memory)) :
    integerIsStep state resultRoot expressionRoot encoding rest =
      .next {
        state with
        memory
        phase := .unifying {
          body := rest
          cutDepth := state.control.cutDepth
          frames := state.control.frames
        } (RuntimeUnification.startMany memory [(resultRoot, valueRoot)])
      } none := by
  simp [integerIsStep, hEval, hAllocate]

/-- Numeric comparison evaluates both operands without allocating or binding.
Success consumes the instruction; false comparison enters ordinary
backtracking. -/
def integerCompareStep {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause) (leftRoot rightRoot : Addr)
    (comparison : IntegerComparison) (encoding : IntegerArithmeticEncoding σ)
    (rest : List Instruction) : StepResultCore σ Instruction SourceClause :=
  match evalInteger encoding state.memory.heap leftRoot with
  | .error error => failWith state error
  | .ok left =>
      match evalInteger encoding state.memory.heap rightRoot with
      | .error error => failWith state error
      | .ok right =>
          if comparison.holds left right then
            .next {
              state with control := { state.control with current := rest }
            } none
          else .next { state with phase := .backtrack } none

theorem integerCompareStep_of_eval {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause) (leftRoot rightRoot : Addr)
    (left right : Int) (comparison : IntegerComparison)
    (encoding : IntegerArithmeticEncoding σ) (rest : List Instruction)
    (hLeft : evalInteger encoding state.memory.heap leftRoot = .ok left)
    (hRight : evalInteger encoding state.memory.heap rightRoot = .ok right) :
    integerCompareStep state leftRoot rightRoot comparison encoding rest =
      if comparison.holds left right then
        .next {
          state with control := { state.control with current := rest }
        } none
      else .next { state with phase := .backtrack } none := by
  simp [integerCompareStep, hLeft, hRight]

/-- The complete authority granted to an instruction classifier.  It may name
an ordinary call's source clauses, identify base control, expose
already-materialized control payloads, or carry language-owned finite error
content for a throw operation.  It cannot inspect or mutate memory, emit
answers/effects, select a clause, choose branch order, create checkpoints, or
resume an alternative. -/
inductive DispatchAction (σ : LPSignature)
    (Instruction SourceClause : Type*) where
  | call (goal : RuntimeAtom σ.scoped) (clauses : List SourceClause)
  | fail
  | cut
  | branch (left right : List Instruction)
  | ifThenElse (condition thenBranch elseBranch : List Instruction)
  | softIfThenElse (condition thenBranch elseBranch : List Instruction)
  | once (goals : List Instruction)
  | findall (template : Addr) (generator : List Instruction) (bag : Addr)
      (encoding : CollectionEncoding σ)
  | metaCall (callable : Addr) (extraArgs : List Addr)
  | catch (guarded : List Instruction) (catcher : Addr)
      (recovery : List Instruction)
  | throw (ball : Addr)
      (unboundError : Option (RuntimeException.Packet σ))
  | unify (left right : Addr)
  | termTest (address : Addr) (test : TermTest σ)
  | termIdentity (left right : Addr) (expected : Bool)
  | univ (termRoot listRoot : Addr) (encoding : UnivEncoding σ)
  | integerIs (resultRoot expressionRoot : Addr)
      (encoding : IntegerArithmeticEncoding σ)
  | integerCompare (leftRoot rightRoot : Addr)
      (comparison : IntegerComparison)
      (encoding : IntegerArithmeticEncoding σ)
  | database (request : DatabaseRequest)
  | error (reason : QueryError)

/-- Yield one persistent-store request after consuming exactly the current
instruction.  No database value is present in `StateCore`, so this transition
cannot mutate or roll back the store itself. -/
@[simp]
def databaseRequestStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (request : DatabaseRequest) (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  .databaseRequest request {
    state with
    control := { state.control with current := rest }
  }

/-- The database handshake cannot reorder or manufacture continuation work:
it removes exactly the recognized instruction and otherwise preserves the
canonical query state. -/
theorem databaseRequestStep_exact {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (request : DatabaseRequest) (rest : List Instruction) :
    databaseRequestStep state request rest =
      .databaseRequest request {
        state with
        control := { state.control with current := rest }
      } := rfl

/-- Check the output-only argument of `asserta/2` and `assertz/2` without
changing memory.  This helper is also the compact conservation seam: mapped
instruction representations share the exact same heap and therefore the same
check result. -/
def checkDatabaseReferenceOutput {σ : LPSignature}
    (memory : Memory σ.scoped) (referenceRoot : Addr) :
    Except QueryError Unit :=
  match memory.heap.deref referenceRoot with
  | .error error => .error (.memory error)
  | .ok (.variableCycle cycle) =>
      .error (.memory (.variableReferenceCycle cycle))
  | .ok (.root root) =>
      match memory.heap[root]? with
      | some (.var _ none) => .ok ()
      | some _ => .error .databaseReferenceOutputNotVariable
      | none => .error (.memory (.invalidAddress root))

/-- SWI requires the second argument of `asserta/2` and `assertz/2` to be a
fresh output variable.  The engine checks this before the persistent session
can mutate the database.  Exact ISO error-packet construction remains a
language boundary; this first fragment fails closed with a typed error. -/
def checkedDatabaseRequestStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (request : DatabaseRequest) (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match request with
  | .assertaWithReference _ referenceRoot
  | .assertzWithReference _ referenceRoot =>
      match checkDatabaseReferenceOutput state.memory referenceRoot with
      | .ok _ => databaseRequestStep state request rest
      | .error error => failWith state error
  | _ => databaseRequestStep state request rest

/-- A fresh aliased output reaches the persistent session unchanged and only
after the shared engine has verified its unbound terminal root. -/
theorem checkedDatabaseRequestStep_assertzWithReference_unbound
    {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (clauseRoot referenceRoot root : Addr)
    (identity : σ.scoped.vars) (rest : List Instruction)
    (hDeref : state.memory.heap.deref referenceRoot = .ok (.root root))
    (hCell : state.memory.heap[root]? = some (.var identity none)) :
    checkedDatabaseRequestStep state
        (.assertzWithReference clauseRoot referenceRoot) rest =
      databaseRequestStep state
        (.assertzWithReference clauseRoot referenceRoot) rest := by
  simp [checkedDatabaseRequestStep, checkDatabaseReferenceOutput,
    hDeref, hCell]

/-- A bound second argument is rejected before any database request exists;
the persistent store therefore has no opportunity to insert the clause. -/
theorem checkedDatabaseRequestStep_assertzWithReference_bound
    {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (clauseRoot referenceRoot root : Addr)
    (value : σ.constants) (rest : List Instruction)
    (hDeref : state.memory.heap.deref referenceRoot = .ok (.root root))
    (hCell : state.memory.heap[root]? = some (.const value)) :
    checkedDatabaseRequestStep state
        (.assertzWithReference clauseRoot referenceRoot) rest =
      failWith state .databaseReferenceOutputNotVariable := by
  simp [checkedDatabaseRequestStep, checkDatabaseReferenceOutput,
    hDeref, hCell]

/-- Apply one narrow classification to the canonical state.  The current
instruction has already been removed; `rest` always comes from the live goal
stack rather than from the classifier. -/
@[simp]
def dispatchActionStep {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (decoder : MetaCallDecoder σ Instruction)
    (state : StateCore σ Instruction SourceClause)
    (rest : List Instruction) :
    DispatchAction σ Instruction SourceClause →
      StepResultCore σ Instruction SourceClause
  | .call goal clauses => callStep state goal clauses rest
  | .fail => .next { state with phase := .backtrack } none
  | .cut => cutStep state rest
  | .branch left right => branchStep state left right rest
  | .ifThenElse condition thenBranch elseBranch =>
      ifThenElseStep state condition thenBranch elseBranch rest
  | .softIfThenElse condition thenBranch elseBranch =>
      softIfThenElseStep state condition thenBranch elseBranch rest
  | .once goals => onceStep state goals rest
  | .findall template generator bag encoding =>
      findallStep state template generator bag encoding rest
  | .metaCall callable extraArgs =>
      metaCallStep decoder state callable extraArgs rest
  | .catch guarded catcher recovery =>
      catchStep state guarded catcher recovery rest
  | .throw ball unboundError => throwStep state ball unboundError
  | .unify left right => beginUnifyStep state left right rest
  | .termTest address test => termTestStep state address test rest
  | .termIdentity left right expected =>
      termIdentityStep state left right expected rest
  | .univ termRoot listRoot encoding =>
      univStep state termRoot listRoot encoding rest
  | .integerIs resultRoot expressionRoot encoding =>
      integerIsStep state resultRoot expressionRoot encoding rest
  | .integerCompare leftRoot rightRoot comparison encoding =>
      integerCompareStep state leftRoot rightRoot comparison encoding rest
  | .database request => checkedDatabaseRequestStep state request rest
  | .error reason => failWith state reason

/-- The full phase loop shared by LP atoms and typed Prolog control.  Language
code supplies only clause materialization, read-only callable decoding, and
the narrow instruction classification above (including optional finite error
content); all heap inspection and search transitions remain in this
definition. -/
@[simp]
def stepCoreWithMeta {σ : LPSignature} [DecidableEq σ.scoped.vars]
    [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (materializer : ClauseMaterializer σ Instruction SourceClause)
    (decoder : MetaCallDecoder σ Instruction)
    (classify : Instruction → DispatchAction σ Instruction SourceClause)
    (state : StateCore σ Instruction SourceClause) :
    StepResultCore σ Instruction SourceClause :=
  match state.phase with
  | .afterAnswer => afterAnswerStep state
  | .backtrack => backtrackStep state
  | .dispatch =>
      match state.control.current with
      | [] => emptyCurrentStep state
      | instruction :: rest =>
          dispatchActionStep decoder state rest (classify instruction)
  | .select cursor => selectStep materializer state cursor
  | .unifying attempt machine => unifyingStep state attempt machine
  | .raising packet => raisingStep state packet
  | .catchSelecting selection machine =>
      catchSelectingStep state selection machine
  | .catchRecovering selection machine =>
      catchRecoveringStep state selection machine
  | .databaseClauseSelect cursor => databaseClauseSelectStep state cursor

/-- The established phase loop specialization rejects meta-calls explicitly.
This wrapper keeps the pure LP API stable while delegating every transition to
`stepCoreWithMeta`; runtimes that implement callable decoding use that same
definition with a non-rejecting decoder. -/
def stepCore {σ : LPSignature} [DecidableEq σ.scoped.vars]
    [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (materializer : ClauseMaterializer σ Instruction SourceClause)
    (classify : Instruction → DispatchAction σ Instruction SourceClause)
    (state : StateCore σ Instruction SourceClause) :
    StepResultCore σ Instruction SourceClause :=
  stepCoreWithMeta materializer
    (rejectingMetaCallDecoder σ Instruction) classify state

/-- The legacy specialization is definitionally the full shared loop with its
callable capability disabled. -/
@[simp]
theorem stepCoreWithMeta_rejecting {σ : LPSignature}
    [DecidableEq σ.scoped.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (materializer : ClauseMaterializer σ Instruction SourceClause)
    (classify : Instruction → DispatchAction σ Instruction SourceClause)
    (state : StateCore σ Instruction SourceClause) :
    stepCoreWithMeta materializer
        (rejectingMetaCallDecoder σ Instruction) classify state =
      stepCore materializer classify state := rfl

/-- Classify an established LP runtime atom for the shared phase loop. -/
def lpDispatchAction {σ : LPSignature} [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ)
    (goal : RuntimeAtom σ.scoped) :
    DispatchAction σ (RuntimeAtom σ.scoped) (Clause σ) :=
  if builtins.isCut goal.symbol = true then
    if goal.args.isEmpty then .cut else .error .malformedCut
  else
    .call goal (clausesFor program goal.symbol)

/-- Execute one query transition.  A running graph unifier contributes exactly
one of its own microsteps. -/
def step {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ) (state : State σ) :
    StepResult σ :=
  stepCore lpClauseMaterializer (lpDispatchAction builtins program) state

/-- The public LP step is exactly the canonical phase loop specialization.
This rewrite keeps downstream proofs phrased against the stable public name. -/
@[simp]
theorem lp_stepCore_eq_step {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ) (state : State σ) :
    stepCore lpClauseMaterializer (lpDispatchAction builtins program) state =
      step builtins program state := rfl

/-! ## Local control laws -/

/-- A structured branch contributes exactly one newest choice, executes the
left branch first, and stores the right branch followed by the live
continuation at the current checkpoint. -/
theorem branchStep_exact {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (left right rest : List Instruction) :
    branchStep state left right rest =
      .next {
        state with
        control := {
          current := left ++ rest
          cutDepth := state.control.cutDepth
          frames := state.control.frames
        }
        choices := .branch {
          checkpoint := state.memory.checkpoint
          control := {
            current := right ++ rest
            cutDepth := state.control.cutDepth
            frames := state.control.frames
          }
        } :: state.choices
      } none := rfl

/-- Backtracking through a structured branch restores its owned checkpoint
before installing the saved right-branch control. -/
theorem backtrackStep_branch_of_restore {σ : LPSignature}
    [DecidableEq σ.scoped.vars]
    (state : StateCore σ Instruction SourceClause)
    (alternative : BranchChoiceCore σ Instruction)
    (older : List (ChoicePointCore σ Instruction SourceClause))
    (memory : Memory σ.scoped)
    (hChoices : state.choices = .branch alternative :: older)
    (hRestore : state.memory.restore alternative.checkpoint = .ok memory) :
    backtrackStep state =
      .next {
        state with
        memory
        control := alternative.control
        choices := older
        phase := .dispatch
      } none := by
  simp [backtrackStep, hChoices, hRestore]

/-- Retrying `retract/1` restores the cursor-owned checkpoint, removes that
choice occurrence exactly once, and resumes only its frozen candidate list. -/
theorem backtrackStep_databaseClause_of_restore {σ : LPSignature}
    [DecidableEq σ.scoped.vars]
    (state : StateCore σ Instruction SourceClause)
    (cursor : DatabaseClauseCursorCore σ Instruction)
    (older : List (ChoicePointCore σ Instruction SourceClause))
    (memory : Memory σ.scoped)
    (hChoices : state.choices = .databaseClause cursor :: older)
    (hRestore : state.memory.restore cursor.checkpoint = .ok memory) :
    backtrackStep state =
      .next {
        state with
        memory
        choices := older
        phase := .databaseClauseSelect cursor
      } none := by
  simp [backtrackStep, hChoices, hRestore]

/-- A successful candidate unification exposes exactly the stable occurrence
selected by the engine and installs the already-consumed continuation before
the persistent session handles the request. -/
theorem unifyingStep_eraseRef_success {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (attempt : AttemptCore σ Instruction)
    (reference : Nat) (memory : Memory σ.scoped) :
    unifyingStep state { attempt with onSuccess := .eraseRef reference }
        (.terminal (.success memory)) =
      .databaseRequest (.eraseRef reference) {
        state with
        memory
        control := {
          current := attempt.body
          cutDepth := attempt.cutDepth
          frames := attempt.frames
        }
        phase := .dispatch
      } := rfl

/-- A cut whose captured depth is exactly the older suffix removes a newest
structured branch while retaining every older caller alternative. -/
theorem cutStep_prunes_newest_branch {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (alternative : BranchChoiceCore σ Instruction)
    (older : List (ChoicePointCore σ Instruction SourceClause))
    (rest : List Instruction)
    (hChoices : state.choices = .branch alternative :: older)
    (hDepth : state.control.cutDepth = older.length) :
    cutStep state rest =
      .next {
        state with
        control := { state.control with current := rest }
        choices := older
      } none := by
  simp [cutStep, hChoices, hDepth, retainBottom]

/-- A hard conditional stores its else branch at the current checkpoint, runs
the condition under a local cut depth that retains that branch, and installs a
success frame that will commit to the pre-conditional depth. -/
theorem ifThenElseStep_exact {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (condition thenBranch elseBranch rest : List Instruction) :
    ifThenElseStep state condition thenBranch elseBranch rest =
      .next {
        state with
        control := {
          current := condition
          cutDepth := state.choices.length + 1
          frames := {
            continuation := thenBranch ++ rest
            callerCutDepth := state.control.cutDepth
            commit := .hard state.choices.length
          } :: state.control.frames
        }
        choices := .branch {
          checkpoint := state.memory.checkpoint
          control := {
            current := elseBranch ++ rest
            cutDepth := state.control.cutDepth
            frames := state.control.frames
          }
        } :: state.choices
      } none := rfl

/-- Reaching a hard conditional's success frame commits the else marker and
all condition-local choices before resuming the then continuation. -/
theorem emptyCurrentStep_commit_of_depth {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (frame : ReturnFrameCore σ Instruction)
    (frames : List (ReturnFrameCore σ Instruction))
    (mark : Nat)
    (hFrames : state.control.frames = frame :: frames)
    (hCollection : frame.collection = none)
    (hCommit : frame.commit = .hard mark)
    (hDepth : mark ≤ state.choices.length) :
    emptyCurrentStep state =
      .next {
        state with
        control := {
          current := frame.continuation
          cutDepth := frame.callerCutDepth
          frames
        }
        choices := retainBottom mark state.choices
      } none := by
  simp [emptyCurrentStep, hFrames, hCollection, hCommit, hDepth]

/-- Soft success removes its else marker at the marked boundary but preserves
all choices created by the condition. -/
theorem eraseSoftElseAboveBottom_marker
    (newer older : List (ChoicePointCore σ Instruction SourceClause))
    (alternative : BranchChoiceCore σ Instruction) :
    eraseSoftElseAboveBottom older.length
        (newer ++ .softElse alternative :: older) =
      newer ++ older := by
  induction newer with
  | nil => simp [eraseSoftElseAboveBottom]
  | cons choice newer ih =>
      simp [eraseSoftElseAboveBottom, ih]
      omega

/-- A soft conditional installs the distinguished else marker and a soft
success frame while using the same local-cut boundary as hard conditionals. -/
theorem softIfThenElseStep_exact {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (condition thenBranch elseBranch rest : List Instruction) :
    softIfThenElseStep state condition thenBranch elseBranch rest =
      .next {
        state with
        control := {
          current := condition
          cutDepth := state.choices.length + 1
          frames := {
            continuation := thenBranch ++ rest
            callerCutDepth := state.control.cutDepth
            commit := .soft state.choices.length
          } :: state.control.frames
        }
        choices := .softElse {
          checkpoint := state.memory.checkpoint
          control := {
            current := elseBranch ++ rest
            cutDepth := state.control.cutDepth
            frames := state.control.frames
          }
        } :: state.choices
      } none := rfl

/-- A failed soft condition resumes the tagged else continuation after exact
checkpoint restoration. -/
theorem backtrackStep_softElse_of_restore {σ : LPSignature}
    [DecidableEq σ.scoped.vars]
    (state : StateCore σ Instruction SourceClause)
    (alternative : BranchChoiceCore σ Instruction)
    (older : List (ChoicePointCore σ Instruction SourceClause))
    (memory : Memory σ.scoped)
    (hChoices : state.choices = .softElse alternative :: older)
    (hRestore : state.memory.restore alternative.checkpoint = .ok memory) :
    backtrackStep state =
      .next {
        state with
        memory
        control := alternative.control
        choices := older
        phase := .dispatch
      } none := by
  simp [backtrackStep, resumeBranchStep, hChoices, hRestore]

/-- Each soft-condition success erases exactly the else delimiter.  Newer
condition alternatives and older caller alternatives both survive. -/
theorem emptyCurrentStep_soft_of_marker {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (frame : ReturnFrameCore σ Instruction)
    (frames : List (ReturnFrameCore σ Instruction))
    (newer older : List (ChoicePointCore σ Instruction SourceClause))
    (alternative : BranchChoiceCore σ Instruction)
    (hFrames : state.control.frames = frame :: frames)
    (hCollection : frame.collection = none)
    (hCommit : frame.commit = .soft older.length)
    (hChoices : state.choices = newer ++ .softElse alternative :: older) :
    emptyCurrentStep state =
      .next {
        state with
        control := {
          current := frame.continuation
          cutDepth := frame.callerCutDepth
          frames
        }
        choices := newer ++ older
      } none := by
  simp [emptyCurrentStep, hFrames, hCollection, hCommit, hChoices,
    eraseSoftElseAboveBottom_marker]
  omega

/-- `once/1` installs one hard-success frame at the current choice depth and
does not create an alternative of its own. -/
theorem onceStep_exact {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (goals rest : List Instruction) :
    onceStep state goals rest =
      .next {
        state with
        control := {
          current := goals
          cutDepth := state.choices.length
          frames := {
            continuation := rest
            callerCutDepth := state.control.cutDepth
            commit := .hard state.choices.length
          } :: state.control.frames
        }
      } none := rfl

/-- Successful callable decoding contributes exactly one ordinary return
frame and captures the current choice depth as its local cut boundary. -/
theorem metaCallStep_exact {σ : LPSignature}
    (decoder : MetaCallDecoder σ Instruction)
    (state : StateCore σ Instruction SourceClause)
    (callable : Addr) (extraArgs : List Addr) (rest goals : List Instruction)
    (hDecode : decoder.decode state.memory.heap callable extraArgs = .ok goals) :
    metaCallStep decoder state callable extraArgs rest =
      .next {
        state with
        control := {
          current := goals
          cutDepth := state.choices.length
          frames := {
            continuation := rest
            callerCutDepth := state.control.cutDepth
            commit := .ordinary
          } :: state.control.frames
        }
      } none := by
  simp [metaCallStep, hDecode]

/-- A decoder rejection is an explicit terminal runtime error after exact
query cleanup; it is never reinterpreted as ordinary Prolog failure. -/
theorem metaCallStep_error {σ : LPSignature}
    (decoder : MetaCallDecoder σ Instruction)
    (state : StateCore σ Instruction SourceClause)
    (callable : Addr) (extraArgs : List Addr) (rest : List Instruction)
    (reason : QueryError)
    (hDecode : decoder.decode state.memory.heap callable extraArgs =
      .error reason) :
    metaCallStep decoder state callable extraArgs rest = failWith state reason := by
  simp [metaCallStep, hDecode]

/-- Meta-call decoding is reached through the canonical dispatch phase, not a
wrapper-side resolution path.  The theorem pins the exact executable seam. -/
theorem stepCoreWithMeta_metaCall_of_dispatch {σ : LPSignature}
    [DecidableEq σ.scoped.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (materializer : ClauseMaterializer σ Instruction SourceClause)
    (decoder : MetaCallDecoder σ Instruction)
    (classify : Instruction → DispatchAction σ Instruction SourceClause)
    (state : StateCore σ Instruction SourceClause)
    (instruction : Instruction) (rest : List Instruction)
    (callable : Addr) (extraArgs : List Addr)
    (hPhase : state.phase = .dispatch)
    (hCurrent : state.control.current = instruction :: rest)
    (hClassify : classify instruction = .metaCall callable extraArgs) :
    stepCoreWithMeta materializer decoder classify state =
      metaCallStep decoder state callable extraArgs rest := by
  simp [stepCoreWithMeta, hPhase, hCurrent, hClassify]

/-! ## Exception-delimiter laws -/

/-- Catch installs exactly one handler-bearing return frame.  The protected
goal receives a local cut boundary at the current choice depth; the caller's
cut scope and continuation remain in the frame. -/
theorem catchStep_exact {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (guarded : List Instruction) (catcher : Addr)
    (recovery rest : List Instruction) :
    catchStep state guarded catcher recovery rest =
      .next {
        state with
        control := {
          current := guarded
          cutDepth := state.choices.length
          frames := {
            continuation := rest
            callerCutDepth := state.control.cutDepth
            commit := .ordinary
            handler := some {
              checkpoint := state.memory.checkpoint
              choiceDepth := state.choices.length
              catcher
              recovery
            }
          } :: state.control.frames
        }
      } none := rfl

/-- A successfully captured exception leaves every backtrackable component in
place until the explicit raising phase starts. -/
theorem throwStep_of_capture {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) (ball : Addr)
    (packet : RuntimeException.Packet σ)
    (hCapture : RuntimeException.capture state.memory.heap ball = .ok packet) :
    throwStep state ball none =
      .next { state with phase := .raising packet } none := by
  simp [throwStep, captureThrowStep, hCapture]

/-- An unbound throw root selects the supplied language-level error packet
without changing memory, choices, frames, or the persistent scope supply. -/
theorem throwStep_unbound_override {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause) (ball root : Addr)
    (identity : ScopedVar σ.vars)
    (errorPacket : RuntimeException.Packet σ)
    (hDeref : state.memory.heap.deref ball = .ok (.root root))
    (hCell : state.memory.heap[root]? = some (.var identity none)) :
    throwStep state ball (some errorPacket) =
      .next { state with phase := .raising errorPacket } none := by
  simp [throwStep, hDeref, hCell]

/-- The nearest handler is selected positionally from the head of the one
return-frame stack; equal-valued outer frames cannot be chosen instead. -/
@[simp]
theorem findCatchTarget_head {σ : LPSignature}
    (frame : ReturnFrameCore σ Instruction)
    (handler : CatchHandlerCore σ Instruction)
    (outer : List (ReturnFrameCore σ Instruction)) :
    findCatchTarget ({ frame with handler := some handler } :: outer) =
      some {
        frame := { frame with handler := some handler }
        handler
        outerFrames := outer
      } := rfl

/-- An uncaught packet preserves its terminal tag through exact query cleanup;
it is never collapsed into ordinary completion. -/
theorem raiseUnhandled_of_restore {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (packet : RuntimeException.Packet σ) (memory : Memory σ.scoped)
    (hRestore : state.memory.restore state.queryCheckpoint = .ok memory) :
    raiseUnhandled state packet = .terminal (.raised packet memory) := by
  simp [raiseUnhandled, closeMemory, hRestore]

/-- If no outer delimiter remains, failed catcher selection raises the same
packet from the original throw-time heap and performs ordinary query cleanup. -/
theorem passException_no_outer {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (selection : CatchSelectionCore σ Instruction)
    (hOuter : findCatchTarget selection.target.outerFrames = none) :
    passException state selection =
      raiseUnhandled { state with memory := selection.throwMemory }
        selection.packet := by
  simp [passException, hOuter]

/-- A rejected inner delimiter advances positionally to the next outer
catcher while retaining the exact throw-time heap and packet root. -/
theorem passException_next_outer {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (selection : CatchSelectionCore σ Instruction)
    (target : CatchTargetCore σ Instruction)
    (hOuter : findCatchTarget selection.target.outerFrames = some target) :
    passException state selection =
      .next {
        state with
        memory := selection.throwMemory
        phase := .catchSelecting { selection with target }
          (RuntimeUnification.start selection.throwMemory
            target.handler.catcher selection.packetRoot)
      } none := by
  simp [passException, hOuter]

/-- Successful throw-time selection reconstructs the catcher binding only
after restoring the handler entry and installing a fresh packet copy. -/
theorem beginCatchRecovery_of_restore_install {σ : LPSignature}
    [DecidableEq σ.scoped.vars]
    (state : StateCore σ Instruction SourceClause)
    (selection : CatchSelectionCore σ Instruction)
    (memory restored : Memory σ.scoped)
    (installed : RuntimeException.Installed σ)
    (hDepth : selection.target.handler.choiceDepth ≤ state.choices.length)
    (hRestore : memory.restore selection.target.handler.checkpoint =
      .ok restored)
    (hInstall : selection.packet.install restored state.nextScope =
      .ok installed) :
    beginCatchRecovery state selection memory =
      .next {
        state with
        memory := installed.memory
        choices := retainBottom selection.target.handler.choiceDepth
          state.choices
        nextScope := installed.nextScope
        phase := .catchRecovering selection
          (RuntimeUnification.start installed.memory
            selection.target.handler.catcher installed.root)
      } none := by
  simp [beginCatchRecovery, hDepth, hRestore, hInstall]

/-- Recovery success consumes the handler before executing recovery.  A throw
from recovery therefore cannot be caught again by the same delimiter. -/
theorem catchRecoveringStep_success_exact {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (selection : CatchSelectionCore σ Instruction)
    (memory : Memory σ.scoped) :
    catchRecoveringStep state selection (.terminal (.success memory)) =
      .next {
        state with
        memory
        control := {
          current := selection.target.handler.recovery
          cutDepth := selection.target.handler.choiceDepth
          frames := { selection.target.frame with handler := none } ::
            selection.target.outerFrames
        }
        phase := .dispatch
      } none := rfl

/-- A well-formed cut transition retains exactly the choices older than the
current predicate activation.  The theorem is stated directly about the one
executable transition; there is no mirror control machine. -/
theorem step_cut_of_dispatch {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ) (state : State σ)
    (goal : RuntimeAtom σ.scoped) (rest : List (RuntimeAtom σ.scoped))
    (hPhase : state.phase = .dispatch)
    (hCurrent : state.control.current = goal :: rest)
    (hCut : builtins.isCut goal.symbol = true)
    (hEmpty : goal.args.isEmpty = true)
    (hDepth : state.control.cutDepth ≤ state.choices.length) :
    step builtins program state =
      .next {
        state with
        control := { state.control with current := rest }
        choices := retainBottom state.control.cutDepth state.choices
      } none := by
  simp [step, stepCore, stepCoreWithMeta, lpDispatchAction, hPhase, hCurrent, hCut,
    hEmpty, hDepth]

/-- Consequently, cut leaves exactly the choice depth captured on predicate
entry; neither a nested call's alternatives nor later clauses survive. -/
theorem step_cut_choice_count {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ) (state : State σ)
    (goal : RuntimeAtom σ.scoped) (rest : List (RuntimeAtom σ.scoped))
    (hPhase : state.phase = .dispatch)
    (hCurrent : state.control.current = goal :: rest)
    (hCut : builtins.isCut goal.symbol = true)
    (hEmpty : goal.args.isEmpty = true)
    (hDepth : state.control.cutDepth ≤ state.choices.length) :
    ∃ next,
      step builtins program state = .next next none ∧
      next.choices.length = state.control.cutDepth := by
  let next : State σ := {
    state with
    control := { state.control with current := rest }
    choices := retainBottom state.control.cutDepth state.choices
  }
  refine ⟨next, step_cut_of_dispatch builtins program state goal rest
    hPhase hCurrent hCut hEmpty hDepth, ?_⟩
  simp [next, retainBottom_length_of_le hDepth]

/-- Exhausting the outermost choice stack closes the query by restoring the
entry checkpoint.  Cleanup is part of the executable transition, not a test
fixture postcondition. -/
theorem step_empty_backtrack_completes {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ) (state : State σ)
    (memory : Memory σ.scoped)
    (hPhase : state.phase = .backtrack)
    (hChoices : state.choices = [])
    (hRestore : state.memory.restore state.queryCheckpoint = .ok memory) :
    step builtins program state = .terminal (.completed memory) := by
  simp [step, stepCore, stepCoreWithMeta, hPhase, hChoices, complete,
    closeMemory, hRestore]

/-- Demand-driven iteration of the full shared loop with callable decoding.
Each decoded meta-call remains one present transition; fuel exhaustion stays
open and the returned state resumes the same DFS search. -/
@[simp]
def pullCoreWithMeta {σ : LPSignature} [DecidableEq σ.scoped.vars]
    [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (materializer : ClauseMaterializer σ Instruction SourceClause)
    (decoder : MetaCallDecoder σ Instruction)
    (classify : Instruction → DispatchAction σ Instruction SourceClause) :
    Nat → StateCore σ Instruction SourceClause →
      PullResultCore σ Instruction SourceClause
  | 0, state => .open state
  | fuel + 1, state =>
      match stepCoreWithMeta materializer decoder classify state with
      | .terminal result => .terminal result
      | .next next none =>
          pullCoreWithMeta materializer decoder classify fuel next
      | .next next (some (.answer answer)) => .answer answer next
      | .databaseRequest _ next =>
          failPullWith next .unhandledDatabaseRequest

/-- The established demand-driven API delegates to the one full pull loop
with a rejecting callable decoder. -/
def pullCore {σ : LPSignature} [DecidableEq σ.scoped.vars]
    [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (materializer : ClauseMaterializer σ Instruction SourceClause)
    (classify : Instruction → DispatchAction σ Instruction SourceClause) :
    Nat → StateCore σ Instruction SourceClause →
      PullResultCore σ Instruction SourceClause :=
  pullCoreWithMeta materializer
    (rejectingMetaCallDecoder σ Instruction) classify

/-- The established demand-driven specialization is definitionally the one
full pull loop with callable decoding disabled. -/
theorem pullCoreWithMeta_rejecting {σ : LPSignature}
    [DecidableEq σ.scoped.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (materializer : ClauseMaterializer σ Instruction SourceClause)
    (classify : Instruction → DispatchAction σ Instruction SourceClause)
    (fuel : Nat) (state : StateCore σ Instruction SourceClause) :
    pullCoreWithMeta materializer
        (rejectingMetaCallDecoder σ Instruction) classify fuel state =
      pullCore materializer classify fuel state := rfl

/-- The established pull interface is open at zero fuel.  These public
equations let proofs reason about the specialization without unfolding the
meta-capable recursive loop or duplicating it. -/
@[simp]
theorem pullCore_zero {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.scoped.vars] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (materializer : ClauseMaterializer σ Instruction SourceClause)
    (classify : Instruction → DispatchAction σ Instruction SourceClause)
    (state : StateCore σ Instruction SourceClause) :
    pullCore materializer classify 0 state = .open state := rfl

/-- One demand step of the established interface, exposed through its stable
`stepCore` specialization while `pullCoreWithMeta` remains the sole recursive
implementation. -/
theorem pullCore_succ {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.scoped.vars] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (materializer : ClauseMaterializer σ Instruction SourceClause)
    (classify : Instruction → DispatchAction σ Instruction SourceClause)
    (fuel : Nat) (state : StateCore σ Instruction SourceClause) :
    pullCore materializer classify (fuel + 1) state =
      match stepCore materializer classify state with
      | .terminal result => .terminal result
      | .next next none => pullCore materializer classify fuel next
      | .next next (some (.answer answer)) => .answer answer next
      | .databaseRequest _ next =>
          failPullWith next .unhandledDatabaseRequest := by
  change
    pullCoreWithMeta materializer
        (rejectingMetaCallDecoder σ Instruction) classify (fuel + 1) state = _
  rw [pullCoreWithMeta, stepCoreWithMeta_rejecting]
  cases hStep : stepCore materializer classify state with
  | terminal result => rfl
  | databaseRequest request next => rfl
  | next next observation =>
      cases observation with
      | none =>
          exact pullCoreWithMeta_rejecting materializer classify fuel next
      | some observation => cases observation; rfl

/-- The established LP demand-driven specialization. -/
def pull {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ) :
    Nat → State σ → PullResult σ :=
  pullCore lpClauseMaterializer (lpDispatchAction builtins program)

end RuntimeQuery
end Mettapedia.Logic.LP
