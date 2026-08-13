import Mettapedia.Logic.LP.RuntimeMaterialize
import Mettapedia.Logic.LP.RuntimeClauseEntry
import Mettapedia.Logic.LP.RuntimeException
import Mettapedia.Logic.LP.RuntimeTermHash

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
  | copyTermReadback (error : RuntimeReadback.ReadbackError)
  | dynamicClauseReadback (error : RuntimeReadback.ReadbackError)
  | invalidDynamicClause
  | invalidFormatDestination
  | invalidFormatString
  | invalidFormatArguments
  | unsupportedFormatDirective
  | textConversionUnbound
  | invalidTextValue
  | invalidTextCodes
  | invalidCharacterCode
  | characterTypeUnbound
  | invalidCharacterType
  | numberConversionUnbound
  | invalidNumberValue
  | invalidNumberCodes
  | databaseReferenceOutputNotVariable
  | termIdentityBudgetExhausted
  | termVariantBudgetExhausted
  | termGroundBudgetExhausted
  | termListBudgetExhausted
  | termVariablesBudgetExhausted
  | numberVariablesBudgetExhausted
  | numberVariablesStartUnbound
  | invalidNumberVariablesStart
  | invalidNumberVariablesOptions
  | termHashBudgetExhausted
  | unsupportedTermHashConstant
  | standardOrderBudgetExhausted
  | unsupportedTermOrderReference
  | invalidTermCompareOrder
  | invalidTermCompareOrderType
  | unsupportedSortReference
  | invalidSortKey
  | invalidSortOrder
  | invalidSortList
  | listLengthNeedsEnumeration
  | invalidListLength
  | invalidListLengthValue
  | predicateIndicatorUnbound
  | invalidPredicateIndicator
  | univListUnbound
  | invalidUnivList
  | univFunctorUnbound
  | invalidUnivFunctor
  | functorNameUnbound
  | functorArityUnbound
  | invalidFunctorName
  | invalidFunctorArity
  | zeroArityCompoundFunctor
  | globalVariableNameUnbound
  | invalidGlobalVariableName
  | undefinedGlobalVariable
  | globalValueReadback (error : RuntimeReadback.ReadbackError)
  | textFilePathUnbound
  | invalidTextFilePath
  | invalidTextFileOptions
  | textFileUnavailable
  | arithmeticEvaluationBudgetExhausted
  | arithmeticOperandUnbound
  | invalidArithmeticOperand
  | unsupportedArithmeticFunction
  | arithmeticZeroDivisor
  | dcgBodyUnbound
  | invalidDcgState
  | invalidDcgBody
  | unhandledDatabaseRequest
  | missingCollectionBoundary
  | missingTransactionBoundary
  | transactionStackUnderflow
  | exceptionCleanupFailed (cleanup : MemoryError)
  | cleanupFailed (primary : QueryError) (cleanup : MemoryError)
deriving Repr

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

/-- A read-only DCG decoder may expose either ordinary instructions or a
terminal sequence.  Terminal roots are existing heap identities; constant
terminals are values that the shared engine, not the decoder, allocates.
Neither case carries a continuation, checkpoint, or answer. -/
inductive DcgPlan (σ : LPSignature) (Instruction : Type*) where
  | goals (instructions : List Instruction)
  | addressTerminals (encoding : CollectionEncoding σ) (heads : List Addr)
  | constantTerminals (encoding : CollectionEncoding σ)
      (heads : List σ.constants)

/-- The dynamic-call shapes whose roots a language realization may expose.
The shared engine chooses when to decode and schedule them; this value contains
neither an answer nor a continuation. -/
inductive MetaCallRequest where
  | call (callable : Addr) (extraArgs : List Addr)
  | maplist (closure list : Addr)
  | maplist3 (closure input output : Addr)

/-- Source-language symbols used when the shared engine constructs the
result spine for finite `maplist/3`.  The language supplies names only; the
engine supplies the activation scope, allocation, unification, and control
entry. -/
structure MaplistEncoding (σ : LPSignature) where
  list : CollectionEncoding σ
  freshVariable : Nat → σ.vars
  freshVariable_injective : Function.Injective freshVariable

/-- Read-only dynamic-call plans.  Ordinary decoded goals are unchanged.
The `maplist3` plan keeps the relation's source-specific closure spelling in
the decoder, while the shared engine owns fresh result cells, the list spine,
the output unification, and the predicate-like entry frame. -/
inductive MetaCallPlan (σ : LPSignature) (Instruction : Type*) where
  | fail
  | goals (instructions : List Instruction)
  | maplist3 (encoding : MaplistEncoding σ) (output : Addr)
      (inputs : List Addr) (knownOutputs : Option (List Addr))
      (calls : List Addr → List Instruction)

/-- Read-only interpretation of dynamic callable and DCG heap roots.  The
shared engine owns when either decoder is invoked, every allocation, and the
predicate-like cut boundary installed around decoded goals.  A decoder sees
only the heap, so it cannot mutate the trail or restore checkpoints. -/
structure MetaCallDecoder (σ : LPSignature) (Instruction : Type*) where
  decode : Heap σ.scoped → MetaCallRequest →
    Except QueryError (MetaCallPlan σ Instruction)
  decodeDcg : Heap σ.scoped → Addr → Addr → Addr →
    Except QueryError (DcgPlan σ Instruction) :=
      fun _ _ _ _ => .error .unsupportedInstruction

/-- Pure LP and typed runtimes without dynamic-call support fail closed. -/
def rejectingMetaCallDecoder (σ : LPSignature) (Instruction : Type*) :
    MetaCallDecoder σ Instruction where
  decode _ _ := .error .unsupportedInstruction
  decodeDcg _ _ _ _ := .error .unsupportedInstruction

/-- The two SWI-style formatting call shapes.  A realization classifies only
the call's existing roots; it cannot inspect the heap, choose the text, or
perform the observation. -/
inductive FormatRequest where
  | codes (destination format arguments : Addr)
  | output (format arguments : Addr)

/-- A pure formatting plan.  The decoder may name language-owned list symbols,
constants, existing heap roots, or one text observation, but it carries no
continuation, checkpoint, choice, or answer authority.  The shared engine
performs every allocation, unification, and observable transition. -/
inductive FormatPlan (σ : LPSignature) where
  | codes (encoding : CollectionEncoding σ) (head tail : Addr)
      (values : List σ.constants)
  | output (text : String)

/-- Read-only interpretation of `format/3` roots.  This follows the same
capability boundary as meta-call and DCG decoding: the language may interpret
its own atomic payloads, while the engine retains all mutation and control. -/
structure FormatDecoder (σ : LPSignature) where
  decode : Heap σ.scoped → FormatRequest →
    Except QueryError (FormatPlan σ)

/-- Runtimes without formatted output fail closed. -/
def rejectingFormatDecoder (σ : LPSignature) : FormatDecoder σ where
  decode _ _ := .error .unsupportedInstruction

/-- A read-only host text capability sees only the immutable heap roots that
name a path and an options list.  Its result is one atomic language value;
it cannot allocate, bind, mutate persistent state, schedule work, select a
clause, or emit an answer.  The session and shared engine retain those powers. -/
structure TextFileDecoder (σ : LPSignature) where
  decode : Heap σ.scoped → Addr → Addr → Except QueryError σ.constants

/-- A runtime without an explicitly installed host text capability fails
closed rather than acquiring ambient filesystem authority. -/
def rejectingTextFileDecoder (σ : LPSignature) : TextFileDecoder σ where
  decode _ _ _ := .error .textFileUnavailable

/-- A bidirectional text conversion produces one of two bounded plans.  A
ground text value becomes a fresh proper code list; a ground code list becomes
one fresh language constant.  Neither plan can name control or observations. -/
inductive TextConversionPlan (σ : LPSignature) where
  | codes (encoding : CollectionEncoding σ) (output : Addr)
      (values : List σ.constants)
  | text (output : Addr) (value : σ.constants)

/-- Read-only interpretation of one language text/code predicate.  The
language owns its atomic representation and Unicode conversion; the engine
retains all allocation, unification, restoration, and scheduling. -/
structure TextConversionDecoder (σ : LPSignature) where
  decode : Heap σ.scoped → Addr → Addr →
    Except QueryError (TextConversionPlan σ)

/-- A read-only binary builtin may inspect two existing heap roots and decide
ordinary success or failure.  It cannot allocate, bind, schedule, select a
clause, or emit an answer.  This is the narrow capability used by ground
character-class tests such as the pinned parser's `code_type/2` calls. -/
structure BinaryTestDecoder (σ : LPSignature) where
  decode : Heap σ.scoped → Addr → Addr → Except QueryError Bool

/-- Language-owned atoms representing the three results of ISO `compare/3`.
The shared engine chooses one result from `Ordering`, allocates it, and binds
the caller's output through the canonical graph unifier. -/
structure TermCompareEncoding (σ : LPSignature) where
  less : σ.constants
  equal : σ.constants
  greater : σ.constants

def TermCompareEncoding.constant {σ : LPSignature}
    (encoding : TermCompareEncoding σ) : Ordering → σ.constants
  | .lt => encoding.less
  | .eq => encoding.equal
  | .gt => encoding.greater

/-- Read-only standard-term comparison.  A decoder may inspect the result and
two operand roots and return only an error or `Ordering`; it cannot allocate,
bind, schedule, select a clause, or manufacture an answer. -/
structure TermCompareDecoder (σ : LPSignature) where
  decode : Heap σ.scoped → Addr → Addr → Addr → Except QueryError Ordering

/-- A read-only sorting result contains only existing element roots, one
language-owned proper-list encoding, and the output root to unify.  It cannot
allocate, bind, schedule, select a clause, or emit an answer. -/
structure SortPlan (σ : LPSignature) where
  encoding : CollectionEncoding σ
  output : Addr
  elements : List Addr

/-- Read-only interpretation of one language sorting call.  Term ordering and
key extraction inspect the current heap, while the shared engine retains all
result-spine allocation and canonical unification authority. -/
structure SortDecoder (σ : LPSignature) where
  decode : Heap σ.scoped → Except QueryError (SortPlan σ)

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

/-- Language-owned symbol bridges for ISO `functor/3`.  The shared engine
owns mode selection, heap inspection, fresh argument allocation, and
unification; a realization supplies only representations of names, arities,
and fresh source-variable identities. -/
structure FunctorEncoding (σ : LPSignature) where
  nameConstant : σ.functionSymbols → σ.constants
  functionOf : (constant : σ.constants) → (arity : Nat) →
    Option { symbol : σ.functionSymbols // σ.functionArity symbol = arity }
  arityConstant : Nat → σ.constants
  arityOf : σ.constants → Option Nat
  freshVariable : Nat → σ.vars
  freshVariable_injective : Function.Injective freshVariable

/-- A prepared `functor/3` transition carries only allocation state, an
ordered unification agenda, and the persistent activation high-water. -/
structure FunctorPrepared (σ : LPSignature) where
  memory : Memory σ.scoped
  pairs : List (Addr × Addr)
  nextScope : Nat

/-- Language-owned syntax for ISO `numbervars/3,4`.  The engine discovers
the existing variable roots, allocates `$VAR` cells, and binds them through
the canonical unifier; the realization supplies only its concrete symbols. -/
structure NumberVariablesEncoding (σ : LPSignature) where
  numberedSymbol : σ.functionSymbols
  numberedArity : σ.functionArity numberedSymbol = 1
  indexConstant : Nat → σ.constants
  singletonConstant : σ.constants

/-- A read-only language decoder selects the nonnegative starting index and
the supported singleton policy.  It cannot allocate, bind, or schedule. -/
structure NumberVariablesPlan (σ : LPSignature) where
  encoding : NumberVariablesEncoding σ
  start : Nat
  singletons : Bool

structure NumberVariablesDecoder (σ : LPSignature) where
  decode : Heap σ.scoped → Addr → Option Addr →
    Except QueryError (NumberVariablesPlan σ)

/-- Complete bounded preparation for one numbering action. -/
structure NumberVariablesPrepared (σ : LPSignature) where
  memory : Memory σ.scoped
  pairs : List (Addr × Addr)
  endIndex : Nat

/-- Allocate a proper list whose heads are existing graph roots.  The roots
are reused, not read back and rematerialized, preserving variable identity
and sharing exactly. -/
def allocateAddressList {σ : LPSignature} (encoding : CollectionEncoding σ) :
    Memory σ.scoped → List Addr → Except MemoryError (Addr × Memory σ.scoped)
  | memory, [] => memory.allocate (.const encoding.nil)
  | memory, head :: tail => do
      let (tailRoot, memory) ← allocateAddressList encoding memory tail
      memory.allocate (.app encoding.cons #[head, tailRoot])

/-- A sorted-result list adds exactly one cell per element plus its nil cell,
and construction never writes the trail.  The element graphs are therefore
reused rather than copied. -/
theorem allocateAddressList_size_trail {σ : LPSignature}
    (encoding : CollectionEncoding σ) (memory memory' : Memory σ.scoped)
    (heads : List Addr) (root : Addr)
    (h : allocateAddressList encoding memory heads = .ok (root, memory')) :
    memory'.heap.size = memory.heap.size + heads.length + 1 ∧
      memory'.trailMark = memory.trailMark := by
  induction heads generalizing memory root memory' with
  | nil =>
      simp only [allocateAddressList] at h
      have hSize := Memory.allocate_heap_size_succ h
      have hTrail := Memory.allocate_trailMark h
      simp only [List.length_nil, Nat.add_zero]
      exact ⟨hSize, hTrail⟩
  | cons head tail ih =>
      simp only [allocateAddressList] at h
      cases hTail : allocateAddressList encoding memory tail with
      | error error =>
          rw [hTail] at h
          contradiction
      | ok result =>
          rcases result with ⟨tailRoot, middle⟩
          rw [hTail] at h
          have hIH := ih memory middle tailRoot hTail
          constructor
          · rw [Memory.allocate_heap_size_succ h, hIH.1]
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          · rw [Memory.allocate_trailMark h, hIH.2]

/-- Allocate distinct unbound result cells for one finite `maplist/3`
expansion.  Fresh source names are supplied by the language encoding, while
the shared engine fixes their one activation scope and owns every heap write. -/
def allocateMaplistVariables {σ : LPSignature}
    (encoding : MaplistEncoding σ) (scope : Nat) :
    Memory σ.scoped → List Nat →
      Except MemoryError (List Addr × Memory σ.scoped)
  | memory, [] => .ok ([], memory)
  | memory, index :: indices => do
      let (root, memory) ← memory.allocate
        (.var (ScopedVar.at scope (encoding.freshVariable index)) none)
      let (roots, memory) ← allocateMaplistVariables encoding scope memory indices
      pure (root :: roots, memory)

/-- Allocate a list segment whose final tail is an existing heap root.  Only
the spine is new; element and tail identities are reused exactly. -/
def allocateAddressSegment {σ : LPSignature}
    (encoding : CollectionEncoding σ) :
    Memory σ.scoped → List Addr → Addr →
      Except MemoryError (Addr × Memory σ.scoped)
  | memory, [], tail => .ok (tail, memory)
  | memory, head :: heads, tail => do
      let (tailRoot, memory) ←
        allocateAddressSegment encoding memory heads tail
      memory.allocate (.app encoding.cons #[head, tailRoot])

/-- Allocate atomic terminal values from left to right, returning their fresh
roots without constructing any control state. -/
def allocateConstants {σ : LPSignature} :
    Memory σ.scoped → List σ.constants →
      Except MemoryError (List Addr × Memory σ.scoped)
  | memory, [] => .ok ([], memory)
  | memory, value :: values => do
      let (root, memory) ← memory.allocate (.const value)
      let (roots, memory) ← allocateConstants memory values
      pure (root :: roots, memory)

/-- Segment allocation is bounded exactly by the number of terminals and
never writes the trail. -/
theorem allocateAddressSegment_size_trail {σ : LPSignature}
    (encoding : CollectionEncoding σ) (memory memory' : Memory σ.scoped)
    (heads : List Addr) (tail root : Addr)
    (h : allocateAddressSegment encoding memory heads tail =
      .ok (root, memory')) :
    memory'.heap.size = memory.heap.size + heads.length ∧
      memory'.trailMark = memory.trailMark := by
  induction heads generalizing memory root memory' with
  | nil =>
      simp only [allocateAddressSegment] at h
      cases h
      simp
  | cons head heads ih =>
      simp only [allocateAddressSegment] at h
      cases hSegment : allocateAddressSegment encoding memory heads tail with
      | error error =>
          rw [hSegment] at h
          contradiction
      | ok result =>
          rcases result with ⟨tailRoot, middle⟩
          have hAllocation :
              middle.allocate (.app encoding.cons #[head, tailRoot]) =
                .ok (root, memory') := by
            rw [hSegment] at h
            exact h
          have hIH := ih memory middle tailRoot hSegment
          constructor
          · rw [Memory.allocate_heap_size_succ hAllocation, hIH.1]
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          · rw [Memory.allocate_trailMark hAllocation, hIH.2]

/-- Allocating atomic terminal roots is likewise an exact finite append with
no trail traffic. -/
theorem allocateConstants_size_trail {σ : LPSignature}
    (memory memory' : Memory σ.scoped) (values : List σ.constants)
    (roots : List Addr)
    (h : allocateConstants memory values = .ok (roots, memory')) :
    memory'.heap.size = memory.heap.size + values.length ∧
      memory'.trailMark = memory.trailMark := by
  induction values generalizing memory roots memory' with
  | nil =>
      simp only [allocateConstants] at h
      cases h
      simp
  | cons value values ih =>
      simp only [allocateConstants] at h
      cases hAllocate : memory.allocate (.const value) with
      | error error =>
          rw [hAllocate] at h
          contradiction
      | ok allocated =>
          rcases allocated with ⟨root, middle⟩
          rw [hAllocate] at h
          simp only [Bind.bind, Except.bind] at h
          cases hRest : allocateConstants middle values with
          | error error =>
              rw [hRest] at h
              contradiction
          | ok result =>
              rcases result with ⟨tailRoots, final⟩
              rw [hRest] at h
              injection h with hResult
              injection hResult with hRoots hMemory
              subst roots
              subst memory'
              have hIH := ih middle final tailRoots hRest
              constructor
              · rw [hIH.1, Memory.allocate_heap_size_succ hAllocate]
                simp [Nat.add_assoc, Nat.add_comm]
              · rw [hIH.2, Memory.allocate_trailMark hAllocate]

/-- Allocate distinct unbound argument cells for a constructed compound.
The engine supplies the activation scope; the realization supplies an
injective source-variable naming scheme only. -/
def allocateFunctorVariables {σ : LPSignature}
    (encoding : FunctorEncoding σ) (scope : Nat) :
    Memory σ.scoped → List Nat →
      Except MemoryError (List Addr × Memory σ.scoped)
  | memory, [] => .ok ([], memory)
  | memory, index :: indices => do
      let (root, memory) ← memory.allocate
        (.var (ScopedVar.at scope (encoding.freshVariable index)) none)
      let (roots, memory) ←
        allocateFunctorVariables encoding scope memory indices
      pure (root :: roots, memory)

/-- Fresh functor arguments add exactly one cell per requested position and
never alter the trail. -/
theorem allocateFunctorVariables_size_trail {σ : LPSignature}
    (encoding : FunctorEncoding σ) (scope : Nat)
    (memory memory' : Memory σ.scoped) (indices : List Nat)
    (roots : List Addr)
    (h : allocateFunctorVariables encoding scope memory indices =
      .ok (roots, memory')) :
    roots.length = indices.length ∧
      memory'.heap.size = memory.heap.size + indices.length ∧
      memory'.trailMark = memory.trailMark := by
  induction indices generalizing memory roots memory' with
  | nil =>
      simp only [allocateFunctorVariables] at h
      cases h
      simp
  | cons index indices ih =>
      simp only [allocateFunctorVariables] at h
      cases hAllocate : memory.allocate
          (.var (ScopedVar.at scope (encoding.freshVariable index)) none) with
      | error error =>
          rw [hAllocate] at h
          contradiction
      | ok allocated =>
          rcases allocated with ⟨root, middle⟩
          rw [hAllocate] at h
          simp only [Bind.bind, Except.bind] at h
          cases hRest : allocateFunctorVariables encoding scope middle indices with
          | error error =>
              rw [hRest] at h
              contradiction
          | ok result =>
              rcases result with ⟨tailRoots, final⟩
              rw [hRest] at h
              injection h with hResult
              injection hResult with hRoots hMemory
              subst roots
              subst memory'
              have hIH := ih middle final tailRoots hRest
              constructor
              · simp [hIH.1]
              constructor
              · rw [hIH.2.1, Memory.allocate_heap_size_succ hAllocate]
                simp [Nat.add_assoc, Nat.add_comm]
              · rw [hIH.2.2, Memory.allocate_trailMark hAllocate]

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

/-- Dereference one live root and return its terminal cell.  A linked
variable at the returned root would contradict `Heap.deref`; it is reported
as corruption rather than treated as an unbound variable. -/
def dereferencedRootCell {σ : LPSignature} (heap : Heap σ.scoped)
    (address : Addr) : Except QueryError (Addr × Cell σ.scoped) := do
  let root ← match heap.deref address with
    | .error error => .error (.memory error)
    | .ok (.variableCycle cycle) =>
        .error (.memory (.variableReferenceCycle cycle))
    | .ok (.root root) => .ok root
  match heap[root]? with
  | none => .error (.memory (.invalidAddress root))
  | some (.var _ (some _)) => .error (.memory .illFormedHeap)
  | some cell => .ok (root, cell)

/-- Prepare ISO `functor/3` in the mode selected by the dereferenced first
argument.  Decomposition reuses an atomic root or exposes an application
symbol and arity.  Construction allocates fresh argument variables at the
persistent activation high-water.  All caller-visible binding is deferred to
one ordered canonical-unifier agenda. -/
def prepareFunctor {σ : LPSignature} [DecidableEq σ.constants]
    (encoding : FunctorEncoding σ) (memory : Memory σ.scoped)
    (nextScope : Nat) (termRoot nameRoot arityRoot : Addr) :
    Except QueryError (FunctorPrepared σ) := do
  let (termAddress, termCell) ← dereferencedRootCell memory.heap termRoot
  match termCell with
  | .const _ =>
      let (encodedArity, memory) ←
        match memory.allocate (.const (encoding.arityConstant 0)) with
        | .error error => .error (.memory error)
        | .ok allocated => .ok allocated
      .ok {
        memory
        pairs := [(nameRoot, termAddress), (arityRoot, encodedArity)]
        nextScope
      }
  | .app symbol arguments =>
      if arguments.size = 0 then
        .error .zeroArityCompoundFunctor
      else if arguments.size = σ.functionArity symbol then
        let (encodedName, memory) ←
          match memory.allocate (.const (encoding.nameConstant symbol)) with
          | .error error => .error (.memory error)
          | .ok allocated => .ok allocated
        let (encodedArity, memory) ←
          match memory.allocate (.const
              (encoding.arityConstant arguments.size)) with
          | .error error => .error (.memory error)
          | .ok allocated => .ok allocated
        .ok {
          memory
          pairs := [(nameRoot, encodedName), (arityRoot, encodedArity)]
          nextScope
        }
      else .error (.memory .illShapedCell)
  | .var _ none =>
      let (nameAddress, nameCell) ←
        dereferencedRootCell memory.heap nameRoot
      let name ← match nameCell with
        | .var _ none => .error .functorNameUnbound
        | .const value => .ok value
        | .app _ _ => .error .invalidFunctorName
        | .var _ (some _) => .error (.memory .illFormedHeap)
      let (_, arityCell) ← dereferencedRootCell memory.heap arityRoot
      let arity ← match arityCell with
        | .var _ none => .error .functorArityUnbound
        | .const value =>
            match encoding.arityOf value with
            | some arity => .ok arity
            | none => .error .invalidFunctorArity
        | .app _ _ => .error .invalidFunctorArity
        | .var _ (some _) => .error (.memory .illFormedHeap)
      if arity = 0 then
        .ok { memory, pairs := [(termRoot, nameAddress)], nextScope }
      else
        match encoding.functionOf name arity with
        | none => .error .invalidFunctorName
        | some symbol =>
            let (arguments, memory) ←
              match allocateFunctorVariables encoding nextScope memory
                  (List.range arity) with
              | .error error => .error (.memory error)
              | .ok allocated => .ok allocated
            let (constructed, memory) ←
              match memory.allocate (.app symbol.1 arguments.toArray) with
              | .error error => .error (.memory error)
              | .ok allocated => .ok allocated
            .ok {
              memory
              pairs := [(termRoot, constructed)]
              nextScope := nextScope + 1
            }
  | .var _ (some _) => .error (.memory .illFormedHeap)

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

/-- Language-owned encodings needed by ISO `length/2`.  The shared engine
owns list traversal, integer allocation, and result unification. -/
structure ListLengthEncoding (σ : LPSignature) where
  list : CollectionEncoding σ
  integer : IntegerArithmeticEncoding σ

/-- Language-owned syntax for a predicate indicator such as `name/arity`.
The engine decodes the graph and tests the resulting symbol only against the
actual call-time program snapshot supplied to the transition. -/
structure PredicateIndicatorEncoding (σ : LPSignature) where
  indicator : σ.functionSymbols
  indicator_arity_two : σ.functionArity indicator = 2
  relationOf : σ.constants → σ.constants → Option σ.relationSymbols

/-- The bounded deterministic result of `length/2`: one freshly allocated
integer root to unify with the caller's second argument. -/
structure ListLengthPrepared (σ : LPSignature) where
  memory : Memory σ.scoped
  lengthRoot : Addr
  valueRoot : Addr

/-- Prepare the finite deterministic modes of ISO `length/2`.  A proper list
is counted without copying its elements.  If the length argument is already
bound it must be a nonnegative integer; equality is still decided by the
canonical graph unifier.  Open-list generation is reported explicitly rather
than being collapsed into ordinary failure. -/
def prepareListLength {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (encoding : ListLengthEncoding σ)
    (memory : Memory σ.scoped) (listRoot lengthRoot : Addr) :
    Except QueryError (ListLengthPrepared σ) := do
  let elements ←
    match decodeAddressList encoding.list memory.heap listRoot with
    | .ok elements => .ok elements
    | .error .univListUnbound => .error .listLengthNeedsEnumeration
    | .error .invalidUnivList => .error .invalidListLength
    | .error error => .error error
  let lengthCell ←
    match memory.heap.deref lengthRoot with
    | .error error => .error (.memory error)
    | .ok (.variableCycle cycle) =>
        .error (.memory (.variableReferenceCycle cycle))
    | .ok (.root root) =>
        match memory.heap[root]? with
        | none => .error (.memory (.invalidAddress root))
        | some cell => .ok cell
  match lengthCell with
  | .var _ none => pure ()
  | .const value =>
      match encoding.integer.decodeInteger value with
      | some length =>
          if length < 0 then .error .invalidListLengthValue else pure ()
      | none => .error .invalidListLengthValue
  | _ => .error .invalidListLengthValue
  let (valueRoot, memory) ←
    match memory.allocate
        (.const (encoding.integer.encodeInteger (Int.ofNat elements.length))) with
    | .ok result => .ok result
    | .error error => .error (.memory error)
  pure { memory, lengthRoot, valueRoot }

private def predicateIndicatorConstant {σ : LPSignature}
    (heap : Heap σ.scoped) (address : Addr) : Except QueryError σ.constants := do
  let dereferenced ←
    match heap.deref address with
    | .ok result => .ok result
    | .error error => .error (.memory error)
  match dereferenced with
  | .variableCycle cycle =>
      .error (.memory (.variableReferenceCycle cycle))
  | .root root =>
      match heap[root]? with
      | none => .error (.memory (.invalidAddress root))
      | some (.var _ none) => .error .predicateIndicatorUnbound
      | some (.const value) => .ok value
      | _ => .error .invalidPredicateIndicator

/-- Decode a fully instantiated predicate indicator on the existing heap.
Enumeration of unbound indicators is deliberately a separate future engine
transition; it cannot be mistaken for ordinary failure here. -/
def decodePredicateIndicator {σ : LPSignature}
    [DecidableEq σ.functionSymbols]
    (encoding : PredicateIndicatorEncoding σ) (heap : Heap σ.scoped)
    (address : Addr) : Except QueryError σ.relationSymbols := do
  let dereferenced ←
    match heap.deref address with
    | .ok result => .ok result
    | .error error => .error (.memory error)
  match dereferenced with
  | .variableCycle cycle =>
      .error (.memory (.variableReferenceCycle cycle))
  | .root root =>
      match heap[root]? with
      | none => .error (.memory (.invalidAddress root))
      | some (.var _ none) => .error .predicateIndicatorUnbound
      | some (.app symbol arguments) =>
          if symbol = encoding.indicator ∧ arguments.size = 2 then
            match arguments[0]?, arguments[1]? with
            | some nameRoot, some arityRoot =>
                let name ← predicateIndicatorConstant heap nameRoot
                let arity ← predicateIndicatorConstant heap arityRoot
                match encoding.relationOf name arity with
                | some relation => .ok relation
                | none => .error .invalidPredicateIndicator
            | _, _ => .error (.memory .illFormedHeap)
          else .error .invalidPredicateIndicator
      | _ => .error .invalidPredicateIndicator

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

/-- Whether a term test inspects only the dereferenced root or traverses the
reachable graph looking for an unbound variable. -/
inductive TermTestMode (σ : LPSignature) where
  | shallow
  | ground
  | properList (encoding : CollectionEncoding σ)

/-- A read-only predicate on canonical heap terms.  A language realization may
classify its own constant payloads or select the engine-owned ground traversal,
but it receives no memory, continuation, or answer authority. -/
structure TermTest (σ : LPSignature) where
  mode : TermTestMode σ := .shallow
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

def isGround : TermTest σ where
  mode := .ground
  acceptsVariable := false
  acceptsConstant _ := false
  acceptsApplication := false

def isProperList (encoding : CollectionEncoding σ) : TermTest σ where
  mode := .properList encoding
  acceptsVariable := false
  acceptsConstant _ := false
  acceptsApplication := false

end TermTest

/-! ## Read-only groundness -/

/-- A finite work-list bound for visiting each reachable root and every
outgoing edge once.  Exhaustion remains a typed error until its sufficiency is
proved from heap well-formedness. -/
def termGroundFuel (heap : Heap σ) : Nat :=
  let edges := heap.foldl (fun total cell =>
    total + cell.references.length) 0
  heap.size + edges + 2

/-- Cycle-safe graph groundness.  Rational compounds terminate through the
visited-root set; an unbound variable rejects the test; corrupt references
remain typed memory errors. -/
def termGroundAux {σ : LPSignature} (heap : Heap σ.scoped) :
    Nat -> List Addr -> List Addr -> Except QueryError Bool
  | 0, _, _ => .error .termGroundBudgetExhausted
  | _ + 1, [], _ => .ok true
  | fuel + 1, address :: rest, visited =>
      match heap.deref address with
      | .error error => .error (.memory error)
      | .ok (.variableCycle cycle) =>
          .error (.memory (.variableReferenceCycle cycle))
      | .ok (.root root) =>
          if root ∈ visited then
            termGroundAux heap fuel rest visited
          else
            match heap[root]? with
            | none => .error (.memory (.invalidAddress root))
            | some (.var _ none) => .ok false
            | some (.var _ (some _)) => .error (.memory .illFormedHeap)
            | some (.const _) =>
                termGroundAux heap fuel rest (root :: visited)
            | some (.app _ arguments) =>
                termGroundAux heap fuel (arguments.toList ++ rest)
                  (root :: visited)

def termGround {σ : LPSignature} (heap : Heap σ.scoped) (address : Addr) :
    Except QueryError Bool :=
  termGroundAux heap (termGroundFuel heap) [address] []

/-! ## Read-only proper-list recognition -/

/-- Traverse only the list spine.  Revisiting a spine root witnesses a cyclic
list and therefore returns false; heads are deliberately not inspected. -/
def termProperListAux {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (encoding : CollectionEncoding σ)
    (heap : Heap σ.scoped) : Nat → Addr → List Addr → Except QueryError Bool
  | 0, _, _ => .error .termListBudgetExhausted
  | fuel + 1, address, visited =>
      match heap.deref address with
      | .error error => .error (.memory error)
      | .ok (.variableCycle cycle) =>
          .error (.memory (.variableReferenceCycle cycle))
      | .ok (.root root) =>
          if root ∈ visited then .ok false else
          match heap[root]? with
          | none => .error (.memory (.invalidAddress root))
          | some (.var _ none) => .ok false
          | some (.var _ (some _)) => .error (.memory .illFormedHeap)
          | some (.const value) => .ok (value = encoding.nil)
          | some (.app symbol arguments) =>
              if symbol = encoding.cons ∧ arguments.size = 2 then
                match arguments[1]? with
                | some tail => termProperListAux encoding heap fuel tail
                    (root :: visited)
                | none => .error (.memory .illFormedHeap)
              else .ok false

def termProperList {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (encoding : CollectionEncoding σ)
    (heap : Heap σ.scoped) (address : Addr) : Except QueryError Bool :=
  termProperListAux encoding heap (heap.size + 2) address []

/-! ## Ordered variables of a finite or rational heap term -/

/-- Cycle-safe, left-to-right variable discovery following SWI-Prolog's
`term_variables_loop` work-agenda discipline (`src/pl-prims.c`).  Roots are
deduplicated by heap identity, so repeated occurrences remain one output
variable and rational application cycles terminate. -/
def termVariableRootsAux {σ : LPSignature} (heap : Heap σ.scoped) :
    Nat → List Addr → List Addr → List Addr → Except QueryError (List Addr)
  | 0, _, _, _ => .error .termVariablesBudgetExhausted
  | _ + 1, [], _, found => .ok found
  | fuel + 1, address :: rest, visited, found =>
      match heap.deref address with
      | .error error => .error (.memory error)
      | .ok (.variableCycle cycle) =>
          .error (.memory (.variableReferenceCycle cycle))
      | .ok (.root root) =>
          if root ∈ visited then
            termVariableRootsAux heap fuel rest visited found
          else
            match heap[root]? with
            | none => .error (.memory (.invalidAddress root))
            | some (.var _ none) =>
                termVariableRootsAux heap fuel rest (root :: visited)
                  (found ++ [root])
            | some (.var _ (some _)) => .error (.memory .illFormedHeap)
            | some (.const _) =>
                termVariableRootsAux heap fuel rest (root :: visited) found
            | some (.app _ arguments) =>
                termVariableRootsAux heap fuel (arguments.toList ++ rest)
                  (root :: visited) found

def termVariableRoots {σ : LPSignature} (heap : Heap σ.scoped)
    (address : Addr) : Except QueryError (List Addr) :=
  termVariableRootsAux heap (termGroundFuel heap) [address] [] []

/-- Path-sensitive variable occurrences for singleton-sensitive numbering.
Shared acyclic applications are traversed once per incoming path, matching
SWI's logical occurrence count rather than physical heap-root count.  Only an
application already on the active path witnesses a rational cycle; its edge is
not unfolded, and the returned Bool disables singleton labeling for the whole
term exactly as pinned SWI does. -/
def termVariableOccurrencesAux {σ : LPSignature} (heap : Heap σ.scoped) :
    Nat → Addr → List Addr → Except QueryError (List Addr × Bool)
  | 0, _, _ => .error .numberVariablesBudgetExhausted
  | fuel + 1, address, active =>
      match heap.deref address with
      | .error error => .error (.memory error)
      | .ok (.variableCycle cycle) =>
          .error (.memory (.variableReferenceCycle cycle))
      | .ok (.root root) =>
          match heap[root]? with
          | none => .error (.memory (.invalidAddress root))
          | some (.var _ none) => .ok ([root], true)
          | some (.var _ (some _)) => .error (.memory .illFormedHeap)
          | some (.const _) => .ok ([], true)
          | some (.app _ arguments) =>
              if root ∈ active then .ok ([], false)
              else
                arguments.toList.foldlM (init := ([], true)) fun accumulated child => do
                  let (found, acyclic) ←
                    termVariableOccurrencesAux heap fuel child (root :: active)
                  pure (accumulated.1 ++ found, accumulated.2 && acyclic)
/-- Inspect one finite heap graph for logical variable occurrences and
acyclicity.  Heap size bounds active-path depth; shared DAG paths may be
revisited deliberately because that multiplicity is observable to
`singletons(true)`. -/
def termVariableOccurrences {σ : LPSignature} (heap : Heap σ.scoped)
    (address : Addr) : Except QueryError (List Addr × Bool) :=
  termVariableOccurrencesAux heap (heap.size + 1) address []

/-! ## Read-only strict term identity -/

/-- Count graph edges once to size the read-only pair traversal below.  The
bound follows the counting argument that an application root can be paired
with at most `heap.size` other roots.  Until the general no-exhaustion theorem
is established, exhaustion remains an explicit error rather than inequality. -/
def termGraphRelationFuel (heap : Heap σ) : Nat :=
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
  termIdenticalAux heap (termGraphRelationFuel heap) [(left, right)] []

/-- Reflexivity is reached through real dereference and the nonempty computed
budget; invalid or variable-cycle roots are deliberately outside the premise. -/
theorem termIdentical_same_of_deref {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (heap : Heap σ.scoped) (address root : Addr)
    (hDeref : heap.deref address = .ok (.root root)) :
    termIdentical heap address address = .ok true := by
  simp [termIdentical, termGraphRelationFuel, termIdenticalAux, hDeref]
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

/-! ## Read-only term variance -/

private def relationImage? (pairs : List (Addr × Addr)) (left : Addr) :
    Option Addr :=
  (pairs.find? fun entry => decide (entry.1 = left)).map Prod.snd

private def relationPreimage? (pairs : List (Addr × Addr)) (right : Addr) :
    Option Addr :=
  (pairs.find? fun entry => decide (entry.2 = right)).map Prod.fst

/-- Read-only counterpart of SWI-Prolog V10.1.9's `variant()` traversal
(`src/pl-variant.c`). Unbound roots are related by a partial bijection, so
variable sharing is observable while variable names are not. Compound roots
carry only a left-to-right representative: repeated occurrences are checked
by strict rational-graph identity because compound sharing itself is not a
Prolog term distinction. The heap is never written or trailed. -/
def termVariantAux {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (heap : Heap σ.scoped) :
    Nat → List (Addr × Addr) → List (Addr × Addr) →
      List (Addr × Addr) → Except QueryError Bool
  | _, [], _, _ => .ok true
  | 0, _, _, _ => .error .termVariantBudgetExhausted
  | fuel + 1, (left, right) :: rest, compoundMap, variableMap =>
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
              match heap[leftRoot]?, heap[rightRoot]? with
              | some (.var _ none), some (.var _ none) =>
                  match relationImage? variableMap leftRoot,
                      relationPreimage? variableMap rightRoot with
                  | none, none =>
                      termVariantAux heap fuel rest compoundMap
                        ((leftRoot, rightRoot) :: variableMap)
                  | some mappedRight, some mappedLeft =>
                      if mappedRight = rightRoot ∧ mappedLeft = leftRoot then
                        termVariantAux heap fuel rest compoundMap variableMap
                      else .ok false
                  | _, _ => .ok false
              | some (.var _ none), some _ => .ok false
              | some _, some (.var _ none) => .ok false
              | some (.const leftValue), some (.const rightValue) =>
                  if leftValue = rightValue then
                    termVariantAux heap fuel rest compoundMap variableMap
                  else .ok false
              | some (.app leftSymbol leftArgs),
                  some (.app rightSymbol rightArgs) =>
                  if leftSymbol = rightSymbol ∧
                      leftArgs.size = rightArgs.size then
                    match relationImage? compoundMap leftRoot with
                    | some representative =>
                        match termIdentical heap representative rightRoot with
                        | .error error => .error error
                        | .ok true =>
                            termVariantAux heap fuel rest compoundMap variableMap
                        | .ok false => .ok false
                    | none =>
                        termVariantAux heap fuel
                          (leftArgs.toList.zip rightArgs.toList ++ rest)
                          ((leftRoot, rightRoot) :: compoundMap) variableMap
                  else .ok false
              | some (.var _ (some _)), _ =>
                  .error (.memory .illFormedHeap)
              | _, some (.var _ (some _)) =>
                  .error (.memory .illFormedHeap)
              | some _, some _ => .ok false
              | none, _ => .error (.memory (.invalidAddress leftRoot))
              | _, none => .error (.memory (.invalidAddress rightRoot))

/-- Decide whether two finite or rational heap terms differ only by a
bijection on their unbound variables. Exhaustion is an explicit runtime
error, never ordinary non-variance or fabricated completion. -/
def termVariant {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (heap : Heap σ.scoped)
    (left right : Addr) : Except QueryError Bool :=
  termVariantAux heap (termGraphRelationFuel heap) [(left, right)] [] []

/-- The two read-only graph relations supported by the shared runtime. -/
inductive TermRelation where
  | identity
  | variant
deriving DecidableEq, Repr

def TermRelation.evaluate {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (relation : TermRelation)
    (heap : Heap σ.scoped) (left right : Addr) : Except QueryError Bool :=
  match relation with
  | .identity => termIdentical heap left right
  | .variant => termVariant heap left right

/-- Two reachable unbound variables are variants even when their heap roots
differ. This is the smallest theorem discriminating variance from strict
identity; it reaches the real partial-bijection insertion case. -/
theorem termVariant_unbound_of_deref {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (heap : Heap σ.scoped) (left right leftRoot rightRoot : Addr)
    (leftIdentity rightIdentity : σ.scoped.vars)
    (hLeft : heap.deref left = .ok (.root leftRoot))
    (hRight : heap.deref right = .ok (.root rightRoot))
    (hLeftCell : heap[leftRoot]? =
      some (.var (σ := σ.scoped) leftIdentity none))
    (hRightCell : heap[rightRoot]? =
      some (.var (σ := σ.scoped) rightIdentity none)) :
    termVariant heap left right = .ok true := by
  simp [termVariant, termGraphRelationFuel, termVariantAux, hLeft, hRight,
    hLeftCell, hRightCell, relationImage?, relationPreimage?]

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

/-- Engine-owned delimiter data for one database transaction.  The database
snapshot itself deliberately lives in the persistent session; the shared
query state carries only the checkpoint and positional choice ownership needed
to commit or unwind the protected search. -/
structure TransactionHandlerCore where
  checkpoint : Memory.Checkpoint
  choiceDepth : Nat

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
  transaction : Option TransactionHandlerCore := none

/-- The nearest exception delimiter together with the outer frames that
survive if it handles the packet.  Frames above it are exactly the unwound
protected computation. -/
structure CatchTargetCore (σ : LPSignature) (Instruction : Type*) where
  frame : ReturnFrameCore σ Instruction
  handler : CatchHandlerCore σ Instruction
  outerFrames : List (ReturnFrameCore σ Instruction)

/-- The nearest database-transaction delimiter crossed by exception unwind.
The persistent database snapshot is not present here; it remains exclusively
owned by the session. -/
structure TransactionTargetCore (σ : LPSignature) (Instruction : Type*) where
  frame : ReturnFrameCore σ Instruction
  handler : TransactionHandlerCore
  outerFrames : List (ReturnFrameCore σ Instruction)

/-- The first exception-relevant delimiter in frame order.  A catch may stop
unwind; a transaction must roll back before search can continue outward. -/
inductive ExceptionBoundaryCore (σ : LPSignature) (Instruction : Type*) where
  | catcher (target : CatchTargetCore σ Instruction)
  | transaction (target : TransactionTargetCore σ Instruction)

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

/-- Failure boundary for one database transaction.  Backtracking to this
sentinel restores the transaction-entry memory and caller control before the
persistent session rolls its database snapshot back. -/
structure TransactionChoiceCore (σ : LPSignature) (Instruction : Type*) where
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
  /-- Database transaction rollback sentinel. -/
  | transaction (boundary : TransactionChoiceCore σ Instruction)
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

/-- Clause-head entry policy supplied by a narrow materializer.  Both modes
use the same graph unifier; single-sided entry adds only an engine-owned check
over the writes that the unifier actually performed. -/
inductive HeadMatchMode where
  | unify
  | singleSided
deriving DecidableEq, Repr

/-- Runtime coordinates captured before a single-sided head is entered.
They name the caller-owned heap prefix and the exact start of this match's
trail suffix; neither coordinate can be supplied by source syntax. -/
structure SingleSidedCheck where
  trailMark : Nat
  protectedHeapSize : Nat
deriving DecidableEq, Repr

/-- Information retained while the graph unifier executes one selected head. -/
structure AttemptCore (σ : LPSignature) (Instruction : Type*) where
  body : List Instruction
  cutDepth : Nat
  frames : List (ReturnFrameCore σ Instruction)
  singleSided : Option SingleSidedCheck := none
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
  /-- Monotone heap prefix owned by persistent session resources.  Choice,
  exception, collection, and query checkpoints may unwind bindings in this
  prefix but may never reclaim its cells.  Pure LP leaves the floor at zero. -/
  persistentHeapFloor : Nat := 0
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
  /-- One exact text payload emitted by a shared runtime transition.  Output
  is not an answer and is never elided by the step-level interface. -/
  | output (text : String)

/-- Persistent session operations recognized by a language realization.
The shared engine owns instruction consumption and continuation order, while a
session outside backtrackable state owns database/global updates and invokes
explicitly installed read-only host capabilities.  The historical type name
is retained to avoid a cosmetic migration of every existing proof site. -/
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
  /-- Begin, commit, or roll back the session-owned database snapshot for one
  typed transaction delimiter. -/
  | transactionBegin
  | transactionCommit
  | transactionRollback
  /-- Duplicate a finite value into the session's protected heap prefix and
  replace one non-backtrackable global binding. -/
  | globalSet (nameRoot valueRoot : Addr)
  /-- Unify with the exact stored graph; repeated reads therefore share its
  residual variables rather than manufacturing a fresh copy per read. -/
  | globalGet (nameRoot valueRoot : Addr)
  /-- Remove a non-backtrackable global binding.  Missing names succeed. -/
  | globalDelete (nameRoot : Addr)
  /-- Read one text resource through an explicit session capability and bind
  its atomic result through the canonical engine unifier. -/
  | readTextFile (pathRoot textRoot optionsRoot : Addr)
deriving DecidableEq, Repr

inductive Terminal (σ : LPSignature) where
  | completed (memory : Memory σ.scoped)
  | raised (packet : RuntimeException.Packet σ) (memory : Memory σ.scoped)
  | runtimeError (error : QueryError) (memory : Memory σ.scoped)

namespace Terminal

/-- The cleaned or live memory carried by every terminal tag. -/
def memory : Terminal σ → Memory σ.scoped
  | .completed memory => memory
  | .raised _ memory => memory
  | .runtimeError _ memory => memory

end Terminal

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
  state.memory.restorePreserving state.persistentHeapFloor state.queryCheckpoint

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

/-- Locate the nearest catch or transaction delimiter in strict frame order.
This is the exception-unwind analogue of the one newest-first choice stack;
it never inspects a language instruction or a persistent database. -/
def findExceptionBoundary {σ : LPSignature} :
    List (ReturnFrameCore σ Instruction) →
      Option (ExceptionBoundaryCore σ Instruction)
  | [] => none
  | frame :: outerFrames =>
      match frame.handler with
      | some handler => .some (.catcher { frame, handler, outerFrames })
      | none =>
          match frame.transaction with
          | some handler => .some (.transaction { frame, handler, outerFrames })
          | none => findExceptionBoundary outerFrames

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
  headMatch : HeadMatchMode := .unify

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
                singleSided := match copied.headMatch with
                  | .unify => none
                  | .singleSided => some {
                      trailMark := state.memory.trail.size
                      protectedHeapSize := state.memory.heap.size
                    }
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

/-- Consume exactly the transaction sentinel with `mark` older choices below
it, discarding every protected alternative above it.  A different resource at
the claimed position is rejected rather than silently pruned. -/
def closeTransactionChoice {σ : LPSignature}
    (mark : Nat) :
    List (ChoicePointCore σ Instruction SourceClause) →
      Option (List (ChoicePointCore σ Instruction SourceClause))
  | [] => none
  | choice :: older =>
      if older.length = mark then
        match choice with
        | .transaction _ => some older
        | _ => none
      else closeTransactionChoice mark older

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

/-- A transaction close consumes its uniquely positioned sentinel together
with every protected alternative above it, and cannot touch an older caller
choice.  This is the resource-linearity fact used by both commit and exception
rollback. -/
theorem closeTransactionChoice_marker {σ : LPSignature}
    (newer older : List (ChoicePointCore σ Instruction SourceClause))
    (boundary : TransactionChoiceCore σ Instruction) :
    closeTransactionChoice older.length
        (newer ++ .transaction boundary :: older) = some older := by
  induction newer with
  | nil => simp [closeTransactionChoice]
  | cons choice newer ih =>
      have hLength : newer.length + (older.length + 1) ≠ older.length := by
        omega
      simp [closeTransactionChoice, hLength, ih]

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

/-- Commit a successful transaction exactly once.  Protected alternatives and
the rollback sentinel are consumed together; the live bindings and persistent
database are kept, while the session receives the commit request. -/
def commitTransactionStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (frame : ReturnFrameCore σ Instruction)
    (handler : TransactionHandlerCore)
    (frames : List (ReturnFrameCore σ Instruction)) :
    StepResultCore σ Instruction SourceClause :=
  match closeTransactionChoice handler.choiceDepth state.choices with
  | none => failWith state .missingTransactionBoundary
  | some choices =>
      .databaseRequest .transactionCommit {
        state with
        control := {
          current := frame.continuation
          cutDepth := frame.callerCutDepth
          frames
        }
        choices
        phase := .dispatch
      }

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
  match state.memory.restorePreserving state.persistentHeapFloor
      alternative.checkpoint with
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
  match state.memory.restorePreserving state.persistentHeapFloor
      boundary.checkpoint with
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
      match state.memory.restorePreserving state.persistentHeapFloor
          cursor.checkpoint with
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
  | .transaction boundary :: older =>
      match state.memory.restorePreserving state.persistentHeapFloor
          boundary.checkpoint with
      | .error error => failWith state (.memory error)
      | .ok memory =>
          .databaseRequest .transactionRollback {
            state with
            memory
            control := boundary.control
            choices := older
            phase := .backtrack
          }
  | .databaseClause cursor :: older =>
      match state.memory.restorePreserving state.persistentHeapFloor
          cursor.checkpoint with
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
      | none => match frame.transaction with
      | some handler => commitTransactionStep state frame handler frames
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
      let accepted : Bool := match attempt.singleSided with
        | none => true
        | some check => memory.protectsHeapPrefixSince check.trailMark
            check.protectedHeapSize
      if accepted then
        match attempt.onSuccess with
        | .continue => .next succeeded none
        | .eraseRef reference =>
            .databaseRequest (.eraseRef reference) succeeded
      else
        .next { state with memory, phase := .backtrack } none
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

/-- Roll an exception across one transaction delimiter.  The detached packet
survives restoration; protected bindings and choices are discarded here, and
the database rollback itself remains an explicit persistent-session request. -/
def rollbackTransactionException {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (packet : RuntimeException.Packet σ)
    (target : TransactionTargetCore σ Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match state.memory.restorePreserving state.persistentHeapFloor
      target.handler.checkpoint with
  | .error error => failWith state (.memory error)
  | .ok memory =>
      match closeTransactionChoice target.handler.choiceDepth state.choices with
      | none => failWith { state with memory } .missingTransactionBoundary
      | some choices =>
          .databaseRequest .transactionRollback {
            state with
            memory
            control := {
              current := target.frame.continuation
              cutDepth := target.frame.callerCutDepth
              frames := target.outerFrames
            }
            choices
            phase := .raising packet
          }

/-- Continue exception search at the next outer delimiter.  Rejected catchers
retain the same throw-time memory; crossing a transaction first restores its
entry state and asks the persistent session to roll the database back. -/
def passException {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (selection : CatchSelectionCore σ Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match findExceptionBoundary selection.target.outerFrames with
  | none =>
      raiseUnhandled { state with memory := selection.throwMemory }
        selection.packet
  | some (.transaction target) =>
      rollbackTransactionException { state with memory := selection.throwMemory }
        selection.packet target
  | some (.catcher target) =>
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
    match memory.restorePreserving state.persistentHeapFloor
        target.handler.checkpoint with
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
  match findExceptionBoundary state.control.frames with
  | none => raiseUnhandled state packet
  | some (.transaction target) =>
      rollbackTransactionException state packet target
  | some (.catcher target) =>
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

/-- Enter one database transaction on the same choice/frame stack as ordinary
control.  Search is once-like: the first success commits and discards protected
alternatives; exhaustion or escaping exception restores the entry checkpoint
and requests database rollback.  Only the persistent session owns the actual
database snapshot. -/
@[simp]
def transactionStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (goals rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  let mark := state.choices.length
  let checkpoint := state.memory.checkpoint
  let outerControl : ControlCore σ Instruction := {
    current := rest
    cutDepth := state.control.cutDepth
    frames := state.control.frames
  }
  let boundary : TransactionChoiceCore σ Instruction := {
    checkpoint
    control := outerControl
  }
  let frame : ReturnFrameCore σ Instruction := {
    continuation := rest
    callerCutDepth := state.control.cutDepth
    transaction := some { checkpoint, choiceDepth := mark }
  }
  .databaseRequest .transactionBegin {
    state with
    control := {
      current := goals
      cutDepth := mark + 1
      frames := frame :: state.control.frames
    }
    choices := .transaction boundary :: state.choices
    phase := .dispatch
  }

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

/-- Enter already-decoded goals under one predicate-like cut boundary.  This
is the WAM `B0 := B` discipline shared by ordinary meta-calls and dynamically
decoded DCG bodies. -/
@[simp]
def enterDecodedGoalsStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (goals rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
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

/-- Enter a decoded action whose engine-owned preparation must unify one
freshly constructed root before the decoded continuation begins.  This is the
same meta-call frame as `enterDecodedGoalsStep`; only the canonical unifier
may bind the caller's output root. -/
def enterDecodedUnifyStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (left right : Addr) (goals rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  let entered := {
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
  }
  let attempt : AttemptCore σ Instruction := {
    body := goals
    cutDepth := entered.control.cutDepth
    frames := entered.control.frames
  }
  .next { entered with
    phase := .unifying attempt (RuntimeUnification.startMany entered.memory [(left, right)])
  } none

/-- Execute the engine-owned allocating half of a finite `maplist/3` plan.
Known proper output lists are reused exactly.  An unbound output root instead
receives a fresh same-length spine, then one canonical unification before the
ordinary closure calls run.  Open output spines never masquerade as success:
the read-only decoder rejects them before this transition. -/
def maplist3Step {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (encoding : MaplistEncoding σ) (output : Addr)
    (inputs : List Addr) (knownOutputs : Option (List Addr))
    (calls : List Addr → List Instruction) (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match knownOutputs with
  | some outputs => enterDecodedGoalsStep state (calls outputs) rest
  | none =>
      match allocateMaplistVariables encoding state.nextScope state.memory
          (List.range inputs.length) with
      | .error error => failWith state (.memory error)
      | .ok (outputs, memory) =>
          match allocateAddressList encoding.list memory outputs with
          | .error error => failWith state (.memory error)
          | .ok (listRoot, memory) =>
              enterDecodedUnifyStep {
                state with memory, nextScope := state.nextScope + 1
              } output listRoot (calls outputs) rest

/-- Enter one dynamically decoded goal.  Decoding is read-only and occurs
exactly once; all scheduling remains in `enterDecodedGoalsStep`. -/
@[simp]
def metaCallStep {σ : LPSignature}
    (decoder : MetaCallDecoder σ Instruction)
    (state : StateCore σ Instruction SourceClause)
    (request : MetaCallRequest) (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match decoder.decode state.memory.heap request with
  | .error reason => failWith state reason
  | .ok .fail => .next { state with phase := .backtrack } none
  | .ok (.goals goals) => enterDecodedGoalsStep state goals rest
  | .ok (.maplist3 encoding output inputs knownOutputs calls) =>
      maplist3Step state encoding output inputs knownOutputs calls rest

/-- Allocate one terminal segment above the live heap and unify the DCG input
with its new spine through the canonical graph unifier.  The final tail is the
caller's existing `Rest` root, so no variable identity is copied. -/
def dcgAddressTerminalsStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (encoding : CollectionEncoding σ) (heads : List Addr)
    (input restRoot : Addr) (continuation : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match allocateAddressSegment encoding state.memory heads restRoot with
  | .error error => failWith state (.memory error)
  | .ok (listRoot, memory) =>
      let attempt : AttemptCore σ Instruction := {
        body := continuation
        cutDepth := state.control.cutDepth
        frames := state.control.frames
      }
      .next {
        state with
        memory
        phase := .unifying attempt
          (RuntimeUnification.startMany memory [(input, listRoot)])
      } none

/-- Constant DCG terminals are allocated by the shared engine before the same
address-segment transition.  A language decoder supplies values only. -/
def dcgConstantTerminalsStep {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (encoding : CollectionEncoding σ) (heads : List σ.constants)
    (input restRoot : Addr) (continuation : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match allocateConstants state.memory heads with
  | .error error => failWith state (.memory error)
  | .ok (roots, memory) =>
      dcgAddressTerminalsStep { state with memory } encoding roots input
        restRoot continuation

/-- Interpret one dynamic grammar body through a read-only decoder.  Ordinary
nonterminals and control re-enter the shared instruction loop; terminal
segments use engine-owned allocation and the canonical unifier. -/
def dcgCallStep {σ : LPSignature}
    (decoder : MetaCallDecoder σ Instruction)
    (state : StateCore σ Instruction SourceClause)
    (body input restRoot : Addr) (continuation : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match decoder.decodeDcg state.memory.heap body input restRoot with
  | .error reason => failWith state reason
  | .ok (.goals goals) => enterDecodedGoalsStep state goals continuation
  | .ok (.addressTerminals encoding heads) =>
      dcgAddressTerminalsStep state encoding heads input restRoot continuation
  | .ok (.constantTerminals encoding heads) =>
      dcgConstantTerminalsStep state encoding heads input restRoot continuation

/-- Execute one read-only formatted-output plan.  A codes plan reuses the DCG
constant-segment allocator: values and list cells are fresh, the supplied tail
root is shared, and only the canonical graph unifier may bind the output. -/
def formatStep {σ : LPSignature}
    (decoder : FormatDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (request : FormatRequest)
    (continuation : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match decoder.decode state.memory.heap request with
  | .error reason => failWith state reason
  | .ok (.codes encoding head tail values) =>
      dcgConstantTerminalsStep state encoding values head tail continuation
  | .ok (.output text) =>
      .next { state with control := { state.control with current := continuation } }
        (some (.output text))

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

/-- Execute finite `copy_term/2` on the one canonical heap.  Capture first
materializes the source's current instantiation as an immutable term;
installation then renames every residual variable above the live activation
supply.  Only the existing graph unifier may bind the caller's output. -/
def copyTermStep {σ : LPSignature} [DecidableEq σ.scoped.vars]
    (state : StateCore σ Instruction SourceClause)
    (sourceRoot targetRoot : Addr) (continuation : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match RuntimeException.capture state.memory.heap sourceRoot with
  | .error error => failWith state (.copyTermReadback error)
  | .ok packet =>
      match packet.install state.memory state.nextScope with
      | .error error => failWith state (.memory error)
      | .ok installed =>
          beginUnifyStep {
            state with
            memory := installed.memory
            nextScope := installed.nextScope
          } installed.root targetRoot continuation

/-- A successful finite capture and installation enters exactly one ordinary
unification attempt, preserves the caller's control delimiters, and advances
the persistent scope supply to the installer's certified frontier. -/
theorem copyTermStep_of_capture_install {σ : LPSignature}
    [DecidableEq σ.scoped.vars]
    (state : StateCore σ Instruction SourceClause)
    (sourceRoot targetRoot : Addr) (continuation : List Instruction)
    (packet : RuntimeException.Packet σ)
    (installed : RuntimeException.Installed σ)
    (hCapture : RuntimeException.capture state.memory.heap sourceRoot =
      .ok packet)
    (hInstall : packet.install state.memory state.nextScope = .ok installed) :
    copyTermStep state sourceRoot targetRoot continuation =
      beginUnifyStep {
        state with
        memory := installed.memory
        nextScope := installed.nextScope
      } installed.root targetRoot continuation := by
  simp [copyTermStep, hCapture, hInstall]

/-- Execute `term_variables/2` by discovering existing unbound roots in
left-to-right first-occurrence order, allocating only the result list spine,
and entering the canonical unifier.  The listed variables are the source
variables themselves, never copies. -/
def termVariablesStep {σ : LPSignature} [DecidableEq σ.constants]
    (encoding : CollectionEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (termRoot variablesRoot : Addr) (continuation : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match termVariableRoots state.memory.heap termRoot with
  | .error error => failWith state error
  | .ok variableRoots =>
      match allocateAddressList encoding state.memory variableRoots with
      | .error error => failWith state (.memory error)
      | .ok (listRoot, memory) =>
          beginUnifyStep { state with memory } variablesRoot listRoot continuation

/-- Successful traversal and list allocation enter exactly one ordinary
unification attempt over the source variables in the discovered order. -/
theorem termVariablesStep_of_roots_allocate {σ : LPSignature}
    [DecidableEq σ.constants]
    (encoding : CollectionEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (termRoot variablesRoot : Addr) (continuation : List Instruction)
    (roots : List Addr) (listRoot : Addr) (memory : Memory σ.scoped)
    (hRoots : termVariableRoots state.memory.heap termRoot = .ok roots)
    (hAllocate : allocateAddressList encoding state.memory roots =
      .ok (listRoot, memory)) :
    termVariablesStep encoding state termRoot variablesRoot continuation =
      beginUnifyStep { state with memory } variablesRoot listRoot continuation := by
  simp [termVariablesStep, hRoots, hAllocate]

private def numberVariableAssignments (occurrences : List Addr)
    (singletons : Bool) : Nat → List Addr → List (Addr × Option Nat) × Nat
  | next, [] => ([], next)
  | next, root :: rest =>
      if singletons && occurrences.count root = 1 then
        let (tail, final) := numberVariableAssignments occurrences singletons
          next rest
        ((root, none) :: tail, final)
      else
        let (tail, final) := numberVariableAssignments occurrences singletons
          (next + 1) rest
        ((root, some next) :: tail, final)

/-- Allocate one `$VAR(Payload)` graph per distinct source variable, without
binding the source roots.  `none` denotes SWI's singleton payload `_`; a
numbered payload carries its exact nonnegative index. -/
def allocateNumberVariableCells {σ : LPSignature}
    (encoding : NumberVariablesEncoding σ) :
    Memory σ.scoped → List (Addr × Option Nat) →
      Except MemoryError (List (Addr × Addr) × Memory σ.scoped)
  | memory, [] => .ok ([], memory)
  | memory, (variableRoot, payload) :: rest => do
      let payloadValue := match payload with
        | some index => encoding.indexConstant index
        | none => encoding.singletonConstant
      let (payloadRoot, memory) ← memory.allocate (.const payloadValue)
      let (numberedRoot, memory) ←
        memory.allocate (.app encoding.numberedSymbol #[payloadRoot])
      let (tail, memory) ← allocateNumberVariableCells encoding memory rest
      pure ((variableRoot, numberedRoot) :: tail, memory)

/-- Numbering preparation is finitely bounded: each distinct source variable
adds exactly one payload cell and one `$VAR/1` application, returns one
unification pair, and does not write the trail. -/
theorem allocateNumberVariableCells_size_trail {σ : LPSignature}
    (encoding : NumberVariablesEncoding σ)
    (memory memory' : Memory σ.scoped)
    (assignments : List (Addr × Option Nat))
    (pairs : List (Addr × Addr))
    (h : allocateNumberVariableCells encoding memory assignments =
      .ok (pairs, memory')) :
    pairs.length = assignments.length ∧
      memory'.heap.size = memory.heap.size + 2 * assignments.length ∧
      memory'.trailMark = memory.trailMark := by
  induction assignments generalizing memory pairs memory' with
  | nil =>
      simp only [allocateNumberVariableCells] at h
      cases h
      simp
  | cons assignment assignments ih =>
      rcases assignment with ⟨variableRoot, payload⟩
      cases payload with
      | none =>
          simp only [allocateNumberVariableCells] at h
          cases hPayload : memory.allocate
              (.const encoding.singletonConstant) with
          | error error =>
              rw [hPayload] at h
              simp only [Bind.bind, Except.bind] at h
              contradiction
          | ok allocated =>
              rcases allocated with ⟨payloadRoot, middle₁⟩
              rw [hPayload] at h
              simp only [Bind.bind, Except.bind] at h
              cases hNumbered : middle₁.allocate
                  (.app encoding.numberedSymbol #[payloadRoot]) with
              | error error =>
                  rw [hNumbered] at h
                  dsimp only [Bind.bind, Except.bind] at h
                  contradiction
              | ok allocated =>
                  rcases allocated with ⟨numberedRoot, middle₂⟩
                  rw [hNumbered] at h
                  dsimp only [Bind.bind, Except.bind] at h
                  cases hRest : allocateNumberVariableCells encoding middle₂
                      assignments with
                  | error error =>
                      rw [hRest] at h
                      dsimp only [Functor.map, Except.map] at h
                      contradiction
                  | ok result =>
                      rcases result with ⟨tail, final₁⟩
                      rw [hRest] at h
                      dsimp only [Functor.map, Except.map] at h
                      injection h with hResult
                      injection hResult with hPairs hMemory
                      subst pairs
                      subst memory'
                      have hIH := ih middle₂ final₁ tail hRest
                      constructor
                      · simp [hIH.1]
                      constructor
                      · rw [hIH.2.1,
                          Memory.allocate_heap_size_succ hNumbered,
                          Memory.allocate_heap_size_succ hPayload]
                        simp only [List.length_cons]
                        omega
                      · rw [hIH.2.2,
                          Memory.allocate_trailMark hNumbered,
                          Memory.allocate_trailMark hPayload]
      | some index =>
          simp only [allocateNumberVariableCells] at h
          cases hPayload : memory.allocate
              (.const (encoding.indexConstant index)) with
          | error error =>
              rw [hPayload] at h
              simp only [Bind.bind, Except.bind] at h
              contradiction
          | ok allocated =>
              rcases allocated with ⟨payloadRoot, middle₁⟩
              rw [hPayload] at h
              simp only [Bind.bind, Except.bind] at h
              cases hNumbered : middle₁.allocate
                  (.app encoding.numberedSymbol #[payloadRoot]) with
              | error error =>
                  rw [hNumbered] at h
                  dsimp only [Bind.bind, Except.bind] at h
                  contradiction
              | ok allocated =>
                  rcases allocated with ⟨numberedRoot, middle₂⟩
                  rw [hNumbered] at h
                  dsimp only [Bind.bind, Except.bind] at h
                  cases hRest : allocateNumberVariableCells encoding middle₂
                      assignments with
                  | error error =>
                      rw [hRest] at h
                      dsimp only [Functor.map, Except.map] at h
                      contradiction
                  | ok result =>
                      rcases result with ⟨tail, final₁⟩
                      rw [hRest] at h
                      dsimp only [Functor.map, Except.map] at h
                      injection h with hResult
                      injection hResult with hPairs hMemory
                      subst pairs
                      subst memory'
                      have hIH := ih middle₂ final₁ tail hRest
                      constructor
                      · simp [hIH.1]
                      constructor
                      · rw [hIH.2.1,
                          Memory.allocate_heap_size_succ hNumbered,
                          Memory.allocate_heap_size_succ hPayload]
                        simp only [List.length_cons]
                        omega
                      · rw [hIH.2.2,
                          Memory.allocate_trailMark hNumbered,
                          Memory.allocate_trailMark hPayload]

/-- Read the source graph, decide singleton labels, allocate every numbered
term and the final index, and return only a canonical unification agenda. -/
def prepareNumberVariables {σ : LPSignature}
    (plan : NumberVariablesPlan σ) (memory : Memory σ.scoped)
    (termRoot endRoot : Addr) :
    Except QueryError (NumberVariablesPrepared σ) := do
  let (occurrences, acyclic) ← termVariableOccurrences memory.heap termRoot
  let uniqueRoots := occurrences.eraseDups
  let useSingletons := plan.singletons && acyclic
  let (assignments, endIndex) :=
    numberVariableAssignments occurrences useSingletons plan.start uniqueRoots
  let (pairs, memory) ←
    (allocateNumberVariableCells plan.encoding memory assignments).mapError .memory
  let (endValueRoot, memory) ←
    (memory.allocate (.const (plan.encoding.indexConstant endIndex))).mapError
      .memory
  pure { memory, pairs := pairs ++ [(endRoot, endValueRoot)], endIndex }

/-- Execute `numbervars/3,4` as a read-only plan, bounded canonical allocation,
and one ordinary unifier run.  All variable bindings are therefore trailed and
undo through the same choice-point restoration as clause-head unification. -/
def numberVariablesStep {σ : LPSignature}
    (decoder : NumberVariablesDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (termRoot startRoot endRoot : Addr) (optionsRoot : Option Addr)
    (continuation : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match decoder.decode state.memory.heap startRoot optionsRoot with
  | .error error => failWith state error
  | .ok plan =>
      match prepareNumberVariables plan state.memory termRoot endRoot with
      | .error error => failWith state error
      | .ok prepared =>
          .next {
            state with
            memory := prepared.memory
            phase := .unifying {
              body := continuation
              cutDepth := state.control.cutDepth
              frames := state.control.frames
            } (RuntimeUnification.startMany prepared.memory prepared.pairs)
          } none

/-- Successful decoding and preparation determine the entire transition and
cannot directly emit an answer. -/
theorem numberVariablesStep_of_decode_prepare {σ : LPSignature}
    (decoder : NumberVariablesDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (termRoot startRoot endRoot : Addr) (optionsRoot : Option Addr)
    (continuation : List Instruction) (plan : NumberVariablesPlan σ)
    (prepared : NumberVariablesPrepared σ)
    (hDecode : decoder.decode state.memory.heap startRoot optionsRoot = .ok plan)
    (hPrepare : prepareNumberVariables plan state.memory termRoot endRoot =
      .ok prepared) :
    numberVariablesStep decoder state termRoot startRoot endRoot optionsRoot
        continuation =
      .next {
        state with
        memory := prepared.memory
        phase := .unifying {
          body := continuation
          cutDepth := state.control.cutDepth
          frames := state.control.frames
        } (RuntimeUnification.startMany prepared.memory prepared.pairs)
      } none := by
  simp [numberVariablesStep, hDecode, hPrepare]

def termHashError : RuntimeTermHash.Error → QueryError
  | .memory error => .memory error
  | .budgetExhausted => .termHashBudgetExhausted
  | .unsupportedConstant => .unsupportedTermHashConstant

/-- Execute SWI-compatible `term_hash/2` on the canonical heap.  A nonground
term consumes the instruction without binding the output.  A ground hash is
allocated as one atomic cell and bound only through the canonical unifier. -/
def termHashStep {σ : LPSignature}
    (encoding : RuntimeTermHash.Encoding σ)
    (state : StateCore σ Instruction SourceClause)
    (termRoot hashRoot : Addr) (continuation : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match RuntimeTermHash.hash? encoding state.memory.heap termRoot with
  | .error error => failWith state (termHashError error)
  | .ok none =>
      .next {
        state with control := { state.control with current := continuation }
      } none
  | .ok (some hash) =>
      match state.memory.allocate (.const (encoding.resultConstant hash)) with
      | .error error => failWith state (.memory error)
      | .ok (valueRoot, memory) =>
          beginUnifyStep { state with memory } hashRoot valueRoot continuation

/-- A nonground graph is a successful read-only step and leaves the output
root untouched. -/
theorem termHashStep_nonground {σ : LPSignature}
    (encoding : RuntimeTermHash.Encoding σ)
    (state : StateCore σ Instruction SourceClause)
    (termRoot hashRoot : Addr) (continuation : List Instruction)
    (hHash : RuntimeTermHash.hash? encoding state.memory.heap termRoot =
      .ok none) :
    termHashStep encoding state termRoot hashRoot continuation =
      .next {
        state with control := { state.control with current := continuation }
      } none := by
  simp [termHashStep, hHash]

/-- A ground hash enters exactly one ordinary unifier activation after one
atomic allocation. -/
theorem termHashStep_of_hash_allocate {σ : LPSignature}
    (encoding : RuntimeTermHash.Encoding σ)
    (state : StateCore σ Instruction SourceClause)
    (termRoot hashRoot valueRoot : Addr) (hash : UInt32)
    (memory : Memory σ.scoped) (continuation : List Instruction)
    (hHash : RuntimeTermHash.hash? encoding state.memory.heap termRoot =
      .ok (some hash))
    (hAllocate : state.memory.allocate
      (.const (encoding.resultConstant hash)) = .ok (valueRoot, memory)) :
    termHashStep encoding state termRoot hashRoot continuation =
      beginUnifyStep { state with memory } hashRoot valueRoot continuation := by
  simp [termHashStep, hHash, hAllocate]

/-- Execute one bidirectional text/code plan.  Both directions allocate only
fresh canonical cells and enter the ordinary graph unifier; the decoder never
binds an output or decides a mismatching ground result itself. -/
def textConversionStep {σ : LPSignature}
    (decoder : TextConversionDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (text codes : Addr) (continuation : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match decoder.decode state.memory.heap text codes with
  | .error reason => failWith state reason
  | .ok (.codes encoding output values) =>
      match allocateConstants state.memory values with
      | .error error => failWith state (.memory error)
      | .ok (roots, memory) =>
          match allocateAddressList encoding memory roots with
          | .error error => failWith state (.memory error)
          | .ok (listRoot, memory) =>
              beginUnifyStep { state with memory } output listRoot continuation
  | .ok (.text output value) =>
      match state.memory.allocate (.const value) with
      | .error error => failWith state (.memory error)
      | .ok (valueRoot, memory) =>
          beginUnifyStep { state with memory } output valueRoot continuation

/-- Execute one read-only binary test.  The shared engine alone turns the
decoder's Boolean into continuation or backtracking, and converts decoder
errors into the canonical cleanup path. -/
@[simp]
def binaryTestStep {σ : LPSignature}
    (decoder : BinaryTestDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (left right : Addr) (continuation : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match decoder.decode state.memory.heap left right with
  | .error reason => failWith state reason
  | .ok true =>
      .next {
        state with control := { state.control with current := continuation }
      } none
  | .ok false => .next { state with phase := .backtrack } none

/-- Compare two existing term roots read-only, allocate the corresponding
language atom, and bind the output only through the canonical unifier. -/
def termCompareStep {σ : LPSignature}
    (decoder : TermCompareDecoder σ) (encoding : TermCompareEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (result left right : Addr) (continuation : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match decoder.decode state.memory.heap result left right with
  | .error reason => failWith state reason
  | .ok order =>
      match state.memory.allocate (.const (encoding.constant order)) with
      | .error error => failWith state (.memory error)
      | .ok (valueRoot, memory) =>
          beginUnifyStep { state with memory } result valueRoot continuation

/-- A successful decoder result creates exactly one fresh atomic cell and
enters one ordinary unifier activation. -/
theorem termCompareStep_of_decode_allocate {σ : LPSignature}
    (decoder : TermCompareDecoder σ) (encoding : TermCompareEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (result left right valueRoot : Addr) (order : Ordering)
    (memory : Memory σ.scoped) (continuation : List Instruction)
    (hDecode : decoder.decode state.memory.heap result left right = .ok order)
    (hAllocate : state.memory.allocate (.const (encoding.constant order)) =
      .ok (valueRoot, memory)) :
    termCompareStep decoder encoding state result left right continuation =
      beginUnifyStep { state with memory } result valueRoot continuation := by
  simp [termCompareStep, hDecode, hAllocate]

/-- Result validation and comparison failures use the ordinary exact query
cleanup path; they cannot degrade into Prolog failure. -/
theorem termCompareStep_error_of_decode {σ : LPSignature}
    (decoder : TermCompareDecoder σ) (encoding : TermCompareEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (result left right : Addr) (continuation : List Instruction)
    (reason : QueryError)
    (hDecode : decoder.decode state.memory.heap result left right =
      .error reason) :
    termCompareStep decoder encoding state result left right continuation =
      failWith state reason := by
  simp [termCompareStep, hDecode]

/-- Allocate only the proper-list spine named by a certified read-only sort
plan, then bind the output through the canonical graph unifier.  Element roots
are reused exactly, preserving variables and sharing. -/
def sortStep {σ : LPSignature}
    (decoder : SortDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (continuation : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match decoder.decode state.memory.heap with
  | .error reason => failWith state reason
  | .ok plan =>
      match allocateAddressList plan.encoding state.memory plan.elements with
      | .error error => failWith state (.memory error)
      | .ok (listRoot, memory) =>
          beginUnifyStep { state with memory } plan.output listRoot continuation

/-- Count one finite proper list and bind its length through the canonical
graph unifier.  The language realization supplies only list/integer symbols;
it cannot bind, schedule, or emit an answer. -/
def listLengthStep {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (encoding : ListLengthEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (listRoot lengthRoot : Addr) (continuation : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match prepareListLength encoding state.memory listRoot lengthRoot with
  | .error reason => failWith state reason
  | .ok prepared =>
      beginUnifyStep { state with memory := prepared.memory }
        prepared.lengthRoot prepared.valueRoot continuation

/-- Test one ground predicate indicator against the exact call-time program
snapshot.  This is read-only and cannot bind, allocate, or synthesize a
predicate occurrence. -/
def predicateDefinedStep {σ : LPSignature}
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (encoding : PredicateIndicatorEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (indicatorRoot : Addr) (candidates : List σ.relationSymbols)
    (continuation : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match decodePredicateIndicator encoding state.memory.heap indicatorRoot with
  | .error reason => failWith state reason
  | .ok relation =>
      if relation ∈ candidates then
        .next {
          state with control := { state.control with current := continuation }
        } none
      else .next { state with phase := .backtrack } none

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

/-- Apply one read-only term test.  Shallow tests inspect the engine-dereferenced
root; groundness uses the cycle-safe reachable-graph traversal above.  A false
test enters ordinary backtracking; corrupt graphs remain typed errors. -/
@[simp]
def termTestStep {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (address : Addr) (test : TermTest σ) (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match test.mode with
  | .properList encoding =>
      match termProperList encoding state.memory.heap address with
      | .error error => failWith state error
      | .ok accepted =>
          if accepted then
            .next {
              state with
              control := { state.control with current := rest }
            } none
          else .next { state with phase := .backtrack } none
  | .ground =>
      match termGround state.memory.heap address with
      | .error error => failWith state error
      | .ok accepted =>
          if accepted then
            .next {
              state with
              control := { state.control with current := rest }
            } none
          else .next { state with phase := .backtrack } none
  | .shallow =>
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
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (address root : Addr) (test : TermTest σ) (rest : List Instruction)
    (cell : Cell σ.scoped)
    (hMode : test.mode = .shallow)
    (hDeref : state.memory.heap.deref address = .ok (.root root))
    (hCell : state.memory.heap[root]? = some cell)
    (hAccept : test.accepts cell = true) :
    termTestStep state address test rest =
      .next {
        state with
        control := { state.control with current := rest }
      } none := by
  simp [termTestStep, hMode, hDeref, hCell, hAccept]

/-- A rejected shallow root enters the ordinary shared backtracking phase;
there is no test-specific failure or restoration path. -/
theorem termTestStep_rejects {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (address root : Addr) (test : TermTest σ) (rest : List Instruction)
    (cell : Cell σ.scoped)
    (hMode : test.mode = .shallow)
    (hDeref : state.memory.heap.deref address = .ok (.root root))
    (hCell : state.memory.heap[root]? = some cell)
    (hReject : test.accepts cell = false) :
    termTestStep state address test rest =
      .next { state with phase := .backtrack } none := by
  simp [termTestStep, hMode, hDeref, hCell, hReject]

theorem termTestStep_ground_accepts {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (address : Addr) (rest : List Instruction)
    (hGround : termGround state.memory.heap address = .ok true) :
    termTestStep state address (TermTest.isGround : TermTest σ) rest =
      .next {
        state with
        control := { state.control with current := rest }
      } none := by
  simp [termTestStep, TermTest.isGround, hGround]

theorem termTestStep_ground_rejects {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (address : Addr) (rest : List Instruction)
    (hGround : termGround state.memory.heap address = .ok false) :
    termTestStep state address (TermTest.isGround : TermTest σ) rest =
      .next { state with phase := .backtrack } none := by
  simp [termTestStep, TermTest.isGround, hGround]

theorem termTestStep_properList_accepts {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (encoding : CollectionEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (address : Addr) (rest : List Instruction)
    (hList : termProperList encoding state.memory.heap address = .ok true) :
    termTestStep state address (TermTest.isProperList encoding) rest =
      .next {
        state with
        control := { state.control with current := rest }
      } none := by
  simp [termTestStep, TermTest.isProperList, hList]

theorem termTestStep_properList_rejects {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (encoding : CollectionEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (address : Addr) (rest : List Instruction)
    (hList : termProperList encoding state.memory.heap address = .ok false) :
    termTestStep state address (TermTest.isProperList encoding) rest =
      .next { state with phase := .backtrack } none := by
  simp [termTestStep, TermTest.isProperList, hList]

/-- Test one read-only graph relation without binding. `expected` selects the
positive or negative Prolog predicate through the same ordinary backtracking
path. -/
def termRelationStep {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (left right : Addr) (relation : TermRelation) (expected : Bool)
    (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match relation.evaluate state.memory.heap left right with
  | .error error => failWith state error
  | .ok actual =>
      if actual = expected then
        .next {
          state with
          control := { state.control with current := rest }
        } none
      else .next { state with phase := .backtrack } none

/-- A completed graph comparison has exactly the polarity-controlled
shared transition; it cannot bind, trail, emit an answer, or choose work. -/
theorem termRelationStep_of_result {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (left right : Addr) (relation : TermRelation)
    (expected actual : Bool) (rest : List Instruction)
    (hResult : relation.evaluate state.memory.heap left right = .ok actual) :
    termRelationStep state left right relation expected rest =
      if actual = expected then
        .next {
          state with
          control := { state.control with current := rest }
        } none
      else .next { state with phase := .backtrack } none := by
  simp [termRelationStep, hResult]

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

/-- Execute `functor/3` through one preparation followed by the existing
transactional graph unifier.  Constructed argument identities consume one
persistent activation scope before unification, so failure/backtracking can
never recycle them. -/
def functorStep {σ : LPSignature} [DecidableEq σ.constants]
    (encoding : FunctorEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (termRoot nameRoot arityRoot : Addr) (rest : List Instruction) :
    StepResultCore σ Instruction SourceClause :=
  match prepareFunctor encoding state.memory state.nextScope termRoot nameRoot
      arityRoot with
  | .error error => failWith state error
  | .ok prepared =>
      .next {
        state with
        memory := prepared.memory
        nextScope := prepared.nextScope
        phase := .unifying {
          body := rest
          cutDepth := state.control.cutDepth
          frames := state.control.frames
        } (RuntimeUnification.startMany prepared.memory prepared.pairs)
      } none

/-- Successful preparation determines the complete `functor/3` transition;
the action cannot emit an answer or schedule anything outside the canonical
unifier. -/
theorem functorStep_of_prepare {σ : LPSignature}
    [DecidableEq σ.constants]
    (encoding : FunctorEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (termRoot nameRoot arityRoot : Addr) (rest : List Instruction)
    (prepared : FunctorPrepared σ)
    (hPrepare : prepareFunctor encoding state.memory state.nextScope termRoot
      nameRoot arityRoot = .ok prepared) :
    functorStep encoding state termRoot nameRoot arityRoot rest =
      .next {
        state with
        memory := prepared.memory
        nextScope := prepared.nextScope
        phase := .unifying {
          body := rest
          cutDepth := state.control.cutDepth
          frames := state.control.frames
        } (RuntimeUnification.startMany prepared.memory prepared.pairs)
      } none := by
  simp [functorStep, hPrepare]

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
  | transaction (goals : List Instruction)
  | findall (template : Addr) (generator : List Instruction) (bag : Addr)
      (encoding : CollectionEncoding σ)
  | metaCall (request : MetaCallRequest)
  | dcgCall (body input rest : Addr)
  | format (request : FormatRequest) (decoder : FormatDecoder σ)
  | textConversion (text codes : Addr) (decoder : TextConversionDecoder σ)
  | binaryTest (left right : Addr) (decoder : BinaryTestDecoder σ)
  | termCompare (result left right : Addr) (decoder : TermCompareDecoder σ)
      (encoding : TermCompareEncoding σ)
  | sort (decoder : SortDecoder σ)
  | listLength (listRoot lengthRoot : Addr)
      (encoding : ListLengthEncoding σ)
  | predicateDefined (indicatorRoot : Addr)
      (candidates : List σ.relationSymbols)
      (encoding : PredicateIndicatorEncoding σ)
  | catch (guarded : List Instruction) (catcher : Addr)
      (recovery : List Instruction)
  | throw (ball : Addr)
      (unboundError : Option (RuntimeException.Packet σ))
  | unify (left right : Addr)
  | termTest (address : Addr) (test : TermTest σ)
  | termRelation (left right : Addr) (relation : TermRelation)
      (expected : Bool)
  | univ (termRoot listRoot : Addr) (encoding : UnivEncoding σ)
  | copyTerm (sourceRoot targetRoot : Addr)
  | termVariables (termRoot variablesRoot : Addr)
      (encoding : CollectionEncoding σ)
  | numberVariables (termRoot startRoot endRoot : Addr)
      (optionsRoot : Option Addr) (decoder : NumberVariablesDecoder σ)
  | termHash (termRoot hashRoot : Addr) (encoding : RuntimeTermHash.Encoding σ)
  | functor (termRoot nameRoot arityRoot : Addr)
      (encoding : FunctorEncoding σ)
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
def dispatchActionStep {σ : LPSignature} [DecidableEq σ.scoped.vars]
    [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
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
  | .transaction goals => transactionStep state goals rest
  | .findall template generator bag encoding =>
      findallStep state template generator bag encoding rest
  | .metaCall request => metaCallStep decoder state request rest
  | .dcgCall body input restRoot =>
      dcgCallStep decoder state body input restRoot rest
  | .format request formatDecoder =>
      formatStep formatDecoder state request rest
  | .textConversion text codes textDecoder =>
      textConversionStep textDecoder state text codes rest
  | .binaryTest left right testDecoder =>
      binaryTestStep testDecoder state left right rest
  | .termCompare result left right compareDecoder encoding =>
      termCompareStep compareDecoder encoding state result left right rest
  | .sort sortDecoder => sortStep sortDecoder state rest
  | .listLength listRoot lengthRoot encoding =>
      listLengthStep encoding state listRoot lengthRoot rest
  | .predicateDefined indicatorRoot candidates encoding =>
      predicateDefinedStep encoding state indicatorRoot candidates rest
  | .catch guarded catcher recovery =>
      catchStep state guarded catcher recovery rest
  | .throw ball unboundError => throwStep state ball unboundError
  | .unify left right => beginUnifyStep state left right rest
  | .termTest address test => termTestStep state address test rest
  | .termRelation left right relation expected =>
      termRelationStep state left right relation expected rest
  | .univ termRoot listRoot encoding =>
      univStep state termRoot listRoot encoding rest
  | .copyTerm sourceRoot targetRoot =>
      copyTermStep state sourceRoot targetRoot rest
  | .termVariables termRoot variablesRoot encoding =>
      termVariablesStep encoding state termRoot variablesRoot rest
  | .numberVariables termRoot startRoot endRoot optionsRoot decoder =>
      numberVariablesStep decoder state termRoot startRoot endRoot optionsRoot rest
  | .termHash termRoot hashRoot encoding =>
      termHashStep encoding state termRoot hashRoot rest
  | .functor termRoot nameRoot arityRoot encoding =>
      functorStep encoding state termRoot nameRoot arityRoot rest
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
    (hRestore : state.memory.restorePreserving state.persistentHeapFloor
      alternative.checkpoint = .ok memory) :
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
    (hRestore : state.memory.restorePreserving state.persistentHeapFloor
      cursor.checkpoint = .ok memory) :
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
    unifyingStep state { attempt with
        singleSided := none
        onSuccess := .eraseRef reference }
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
      } := by simp [unifyingStep]

/-- A successful ordinary head unification enters its already-materialized
body exactly as before the single-sided extension. -/
theorem unifyingStep_ordinary_success {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (attempt : AttemptCore σ Instruction) (memory : Memory σ.scoped) :
    unifyingStep state { attempt with
        singleSided := none
        onSuccess := .continue }
        (.terminal (.success memory)) =
      .next {
        state with
        memory
        control := {
          current := attempt.body
          cutDepth := attempt.cutDepth
          frames := attempt.frames
        }
        phase := .dispatch
      } none := by
  simp [unifyingStep]

/-- A single-sided match whose new trail suffix touches the caller prefix is
converted to ordinary clause mismatch/backtracking before its body can run. -/
theorem unifyingStep_singleSided_rejects_caller_write {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (attempt : AttemptCore σ Instruction) (check : SingleSidedCheck)
    (memory : Memory σ.scoped)
    (hProtected : memory.protectsHeapPrefixSince check.trailMark
      check.protectedHeapSize = false) :
    unifyingStep state { attempt with singleSided := some check }
        (.terminal (.success memory)) =
      .next { state with memory, phase := .backtrack } none := by
  simp [unifyingStep, hProtected]

/-- If every new binding is confined to the fresh clause-copy suffix, the
single-sided check enters the same body/control state as ordinary matching. -/
theorem unifyingStep_singleSided_accepts_fresh_writes {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (state : StateCore σ Instruction SourceClause)
    (attempt : AttemptCore σ Instruction) (check : SingleSidedCheck)
    (memory : Memory σ.scoped)
    (hProtected : memory.protectsHeapPrefixSince check.trailMark
      check.protectedHeapSize = true) :
    unifyingStep state { attempt with
        singleSided := some check
        onSuccess := .continue }
        (.terminal (.success memory)) =
      .next {
        state with
        memory
        control := {
          current := attempt.body
          cutDepth := attempt.cutDepth
          frames := attempt.frames
        }
        phase := .dispatch
      } none := by
  simp [unifyingStep, hProtected]

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
    (hTransaction : frame.transaction = none)
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
  simp [emptyCurrentStep, hFrames, hCollection, hTransaction, hCommit, hDepth]

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
    (hRestore : state.memory.restorePreserving state.persistentHeapFloor
      alternative.checkpoint = .ok memory) :
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
    (hTransaction : frame.transaction = none)
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
  simp [emptyCurrentStep, hFrames, hCollection, hTransaction, hCommit, hChoices,
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
    (request : MetaCallRequest) (rest goals : List Instruction)
    (hDecode : decoder.decode state.memory.heap request = .ok (.goals goals)) :
    metaCallStep decoder state request rest =
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
    (request : MetaCallRequest) (rest : List Instruction)
    (reason : QueryError)
    (hDecode : decoder.decode state.memory.heap request = .error reason) :
    metaCallStep decoder state request rest = failWith state reason := by
  simp [metaCallStep, hDecode]

/-- A decoded relational mismatch is ordinary search failure, not a malformed
operation.  In particular finite `maplist/3` uses this arm when two closed
lists have unequal lengths. -/
theorem metaCallStep_fail {σ : LPSignature}
    (decoder : MetaCallDecoder σ Instruction)
    (state : StateCore σ Instruction SourceClause)
    (request : MetaCallRequest) (rest : List Instruction)
    (hDecode : decoder.decode state.memory.heap request = .ok .fail) :
    metaCallStep decoder state request rest =
      .next { state with phase := .backtrack } none := by
  simp [metaCallStep, hDecode]

/-- Dynamic DCG decoding cannot schedule around the shared entry transition:
an ordinary-goal plan is installed exactly as one meta-call body. -/
theorem dcgCallStep_goals_of_decode {σ : LPSignature}
    (decoder : MetaCallDecoder σ Instruction)
    (state : StateCore σ Instruction SourceClause)
    (body input restRoot : Addr) (continuation goals : List Instruction)
    (hDecode : decoder.decodeDcg state.memory.heap body input restRoot =
      .ok (.goals goals)) :
    dcgCallStep decoder state body input restRoot continuation =
      enterDecodedGoalsStep state goals continuation := by
  simp [dcgCallStep, hDecode]

/-- A decoded terminal-address plan reaches only the engine-owned spine
allocator and canonical-unifier entry. -/
theorem dcgCallStep_addressTerminals_of_decode {σ : LPSignature}
    (decoder : MetaCallDecoder σ Instruction)
    (state : StateCore σ Instruction SourceClause)
    (body input restRoot : Addr) (continuation : List Instruction)
    (encoding : CollectionEncoding σ) (heads : List Addr)
    (hDecode : decoder.decodeDcg state.memory.heap body input restRoot =
      .ok (.addressTerminals encoding heads)) :
    dcgCallStep decoder state body input restRoot continuation =
      dcgAddressTerminalsStep state encoding heads input restRoot
        continuation := by
  simp [dcgCallStep, hDecode]

/-- Constant terminal plans likewise pass through engine-owned allocation;
the decoder has no direct memory authority. -/
theorem dcgCallStep_constantTerminals_of_decode {σ : LPSignature}
    (decoder : MetaCallDecoder σ Instruction)
    (state : StateCore σ Instruction SourceClause)
    (body input restRoot : Addr) (continuation : List Instruction)
    (encoding : CollectionEncoding σ) (heads : List σ.constants)
    (hDecode : decoder.decodeDcg state.memory.heap body input restRoot =
      .ok (.constantTerminals encoding heads)) :
    dcgCallStep decoder state body input restRoot continuation =
      dcgConstantTerminalsStep state encoding heads input restRoot
        continuation := by
  simp [dcgCallStep, hDecode]

/-- Decoder rejection is a visible runtime error with exact query cleanup;
it is never weakened to ordinary grammar failure. -/
theorem dcgCallStep_error_of_decode {σ : LPSignature}
    (decoder : MetaCallDecoder σ Instruction)
    (state : StateCore σ Instruction SourceClause)
    (body input restRoot : Addr) (continuation : List Instruction)
    (reason : QueryError)
    (hDecode : decoder.decodeDcg state.memory.heap body input restRoot =
      .error reason) :
    dcgCallStep decoder state body input restRoot continuation =
      failWith state reason := by
  simp [dcgCallStep, hDecode]

/-- A decoded codes plan reaches only engine-owned allocation and canonical
unification.  In particular, the decoder cannot install its own answer or
continuation. -/
theorem formatStep_codes_of_decode {σ : LPSignature}
    (decoder : FormatDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (request : FormatRequest) (head tail : Addr)
    (continuation : List Instruction) (encoding : CollectionEncoding σ)
    (values : List σ.constants)
    (hDecode : decoder.decode state.memory.heap request =
      .ok (.codes encoding head tail values)) :
    formatStep decoder state request continuation =
      dcgConstantTerminalsStep state encoding values head tail continuation := by
  simp [formatStep, hDecode]

/-- A decoded default-stream format emits exactly one text observation while
continuing at the supplied shared-engine continuation. -/
theorem formatStep_output_of_decode {σ : LPSignature}
    (decoder : FormatDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (request : FormatRequest) (continuation : List Instruction) (text : String)
    (hDecode : decoder.decode state.memory.heap request = .ok (.output text)) :
    formatStep decoder state request continuation =
      .next { state with control := { state.control with current := continuation } }
        (some (.output text)) := by
  simp [formatStep, hDecode]

/-- Formatter rejection remains a typed runtime error and cannot become
ordinary Prolog failure. -/
theorem formatStep_error_of_decode {σ : LPSignature}
    (decoder : FormatDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (request : FormatRequest)
    (continuation : List Instruction) (reason : QueryError)
    (hDecode : decoder.decode state.memory.heap request =
      .error reason) :
    formatStep decoder state request continuation =
      failWith state reason := by
  simp [formatStep, hDecode]

theorem textConversionStep_codes_of_decode_allocate {σ : LPSignature}
    (decoder : TextConversionDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (text codes output listRoot : Addr) (continuation : List Instruction)
    (encoding : CollectionEncoding σ) (values : List σ.constants)
    (roots : List Addr) (memory₁ memory₂ : Memory σ.scoped)
    (hDecode : decoder.decode state.memory.heap text codes =
      .ok (.codes encoding output values))
    (hValues : allocateConstants state.memory values = .ok (roots, memory₁))
    (hList : allocateAddressList encoding memory₁ roots =
      .ok (listRoot, memory₂)) :
    textConversionStep decoder state text codes continuation =
      beginUnifyStep { state with memory := memory₂ }
        output listRoot continuation := by
  simp [textConversionStep, hDecode, hValues, hList]

theorem textConversionStep_text_of_decode_allocate {σ : LPSignature}
    (decoder : TextConversionDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (text codes output valueRoot : Addr) (continuation : List Instruction)
    (value : σ.constants) (memory : Memory σ.scoped)
    (hDecode : decoder.decode state.memory.heap text codes =
      .ok (.text output value))
    (hValue : state.memory.allocate (.const value) = .ok (valueRoot, memory)) :
    textConversionStep decoder state text codes continuation =
      beginUnifyStep { state with memory } output valueRoot continuation := by
  simp [textConversionStep, hDecode, hValue]

theorem textConversionStep_error_of_decode {σ : LPSignature}
    (decoder : TextConversionDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (text codes : Addr) (continuation : List Instruction) (reason : QueryError)
    (hDecode : decoder.decode state.memory.heap text codes = .error reason) :
    textConversionStep decoder state text codes continuation =
      failWith state reason := by
  simp [textConversionStep, hDecode]

theorem binaryTestStep_accepts {σ : LPSignature}
    (decoder : BinaryTestDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (left right : Addr) (continuation : List Instruction)
    (hDecode : decoder.decode state.memory.heap left right = .ok true) :
    binaryTestStep decoder state left right continuation =
      .next {
        state with control := { state.control with current := continuation }
      } none := by
  simp [binaryTestStep, hDecode]

theorem binaryTestStep_rejects {σ : LPSignature}
    (decoder : BinaryTestDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (left right : Addr) (continuation : List Instruction)
    (hDecode : decoder.decode state.memory.heap left right = .ok false) :
    binaryTestStep decoder state left right continuation =
      .next { state with phase := .backtrack } none := by
  simp [binaryTestStep, hDecode]

theorem binaryTestStep_error_of_decode {σ : LPSignature}
    (decoder : BinaryTestDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (left right : Addr) (continuation : List Instruction) (reason : QueryError)
    (hDecode : decoder.decode state.memory.heap left right = .error reason) :
    binaryTestStep decoder state left right continuation =
      failWith state reason := by
  simp [binaryTestStep, hDecode]

/-- A successful read-only sort plan reaches only engine-owned list
allocation and the canonical unifier. -/
theorem sortStep_of_decode_allocate {σ : LPSignature}
    (decoder : SortDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (continuation : List Instruction)
    (encoding : CollectionEncoding σ) (output listRoot : Addr)
    (elements : List Addr) (memory : Memory σ.scoped)
    (hDecode : decoder.decode state.memory.heap =
      .ok { encoding, output, elements })
    (hList : allocateAddressList encoding state.memory elements =
      .ok (listRoot, memory)) :
    sortStep decoder state continuation =
      beginUnifyStep { state with memory } output listRoot continuation := by
  simp [sortStep, hDecode, hList]

/-- Sort decoding failure uses the canonical typed-error cleanup path and
cannot become ordinary Prolog failure. -/
theorem sortStep_error_of_decode {σ : LPSignature}
    (decoder : SortDecoder σ)
    (state : StateCore σ Instruction SourceClause)
    (continuation : List Instruction) (reason : QueryError)
    (hDecode : decoder.decode state.memory.heap = .error reason) :
    sortStep decoder state continuation = failWith state reason := by
  simp [sortStep, hDecode]

/-- A prepared finite list length reaches exactly one canonical unifier
activation; the helper cannot manufacture control or observations. -/
theorem listLengthStep_of_prepare {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (encoding : ListLengthEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (listRoot lengthRoot : Addr) (continuation : List Instruction)
    (prepared : ListLengthPrepared σ)
    (hPrepare : prepareListLength encoding state.memory listRoot lengthRoot =
      .ok prepared) :
    listLengthStep encoding state listRoot lengthRoot continuation =
      beginUnifyStep { state with memory := prepared.memory }
        prepared.lengthRoot prepared.valueRoot continuation := by
  simp [listLengthStep, hPrepare]

/-- Unsupported or malformed list-length modes use the typed-error cleanup
path and cannot masquerade as Prolog failure. -/
theorem listLengthStep_error_of_prepare {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (encoding : ListLengthEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (listRoot lengthRoot : Addr) (continuation : List Instruction)
    (reason : QueryError)
    (hPrepare : prepareListLength encoding state.memory listRoot lengthRoot =
      .error reason) :
    listLengthStep encoding state listRoot lengthRoot continuation =
      failWith state reason := by
  simp [listLengthStep, hPrepare]

/-- A decoded indicator present in the call-time candidate set advances the
existing continuation without changing memory or search ownership. -/
theorem predicateDefinedStep_accepts {σ : LPSignature}
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (encoding : PredicateIndicatorEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (indicatorRoot : Addr) (candidates : List σ.relationSymbols)
    (continuation : List Instruction) (relation : σ.relationSymbols)
    (hDecode : decodePredicateIndicator encoding state.memory.heap
      indicatorRoot = .ok relation)
    (hMember : relation ∈ candidates) :
    predicateDefinedStep encoding state indicatorRoot candidates continuation =
      .next {
        state with control := { state.control with current := continuation }
      } none := by
  simp [predicateDefinedStep, hDecode, hMember]

/-- A decoded but absent indicator is ordinary Prolog failure. -/
theorem predicateDefinedStep_rejects {σ : LPSignature}
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (encoding : PredicateIndicatorEncoding σ)
    (state : StateCore σ Instruction SourceClause)
    (indicatorRoot : Addr) (candidates : List σ.relationSymbols)
    (continuation : List Instruction) (relation : σ.relationSymbols)
    (hDecode : decodePredicateIndicator encoding state.memory.heap
      indicatorRoot = .ok relation)
    (hMissing : relation ∉ candidates) :
    predicateDefinedStep encoding state indicatorRoot candidates continuation =
      .next { state with phase := .backtrack } none := by
  simp [predicateDefinedStep, hDecode, hMissing]

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
    (instruction : Instruction) (rest : List Instruction) (request : MetaCallRequest)
    (hPhase : state.phase = .dispatch)
    (hCurrent : state.control.current = instruction :: rest)
    (hClassify : classify instruction = .metaCall request) :
    stepCoreWithMeta materializer decoder classify state =
      metaCallStep decoder state request rest := by
  simp [stepCoreWithMeta, hPhase, hCurrent, hClassify]

/-- Dynamic grammar decoding is reached through the same canonical dispatch
phase; no source/session wrapper can execute it out of band. -/
theorem stepCoreWithMeta_dcgCall_of_dispatch {σ : LPSignature}
    [DecidableEq σ.scoped.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (materializer : ClauseMaterializer σ Instruction SourceClause)
    (decoder : MetaCallDecoder σ Instruction)
    (classify : Instruction → DispatchAction σ Instruction SourceClause)
    (state : StateCore σ Instruction SourceClause)
    (instruction : Instruction) (continuation : List Instruction)
    (body input restRoot : Addr)
    (hPhase : state.phase = .dispatch)
    (hCurrent : state.control.current = instruction :: continuation)
    (hClassify : classify instruction = .dcgCall body input restRoot) :
    stepCoreWithMeta materializer decoder classify state =
      dcgCallStep decoder state body input restRoot continuation := by
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
    (hRestore : state.memory.restorePreserving state.persistentHeapFloor
      state.queryCheckpoint = .ok memory) :
    raiseUnhandled state packet = .terminal (.raised packet memory) := by
  simp [raiseUnhandled, closeMemory, hRestore]

/-- If no outer delimiter remains, failed catcher selection raises the same
packet from the original throw-time heap and performs ordinary query cleanup. -/
theorem passException_no_outer {σ : LPSignature}
    (state : StateCore σ Instruction SourceClause)
    (selection : CatchSelectionCore σ Instruction)
    (hOuter : findExceptionBoundary selection.target.outerFrames = none) :
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
    (hOuter : findExceptionBoundary selection.target.outerFrames =
      some (.catcher target)) :
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
    (hRestore : memory.restorePreserving state.persistentHeapFloor
      selection.target.handler.checkpoint =
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
    (hRestore : state.memory.restorePreserving state.persistentHeapFloor
      state.queryCheckpoint = .ok memory) :
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
      /- `pull` is the answer-only convenience interface. Step consumers see
      output observations directly; answer iteration advances past them. -/
      | .next next (some (.output _)) =>
          pullCoreWithMeta materializer decoder classify fuel next
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
      | .next next (some (.output _)) => pullCore materializer classify fuel next
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
      | some observation => cases observation <;> rfl

/-- The established LP demand-driven specialization. -/
def pull {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ) :
    Nat → State σ → PullResult σ :=
  pullCore lpClauseMaterializer (lpDispatchAction builtins program)

end RuntimeQuery
end Mettapedia.Logic.LP
