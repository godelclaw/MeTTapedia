import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Union

/-!
# Call-time choice: the core calculus and its natural semantics

A call-by-push-value core with nondeterminism, memoized suspensions and
resampling. Values and computations are separate syntactic classes:

* value expressions (`VExp`) and runtime values (`Val`) are symbols,
  applications and references to cells;
* computations (`Comp`) return values, sequence (`seq`, the CBPV `to`),
  suspend (`need`, `delay`), force, match, call equations, choose and emit.

A cell is a suspended computation: its origin (code and environment) never
changes; its cache moves from `pending` to `evaluating` to `done`. A value
`need ℓ` is a memoized thunk: `force` reads the cache or fills it. A value
`thunk ℓ` is an ordinary thunk: `force` runs its origin again (resampling).
The store, cells and event trace together, is threaded through each
alternative separately: every alternative starts from the store of its
parent, so a memo written in one branch is never visible in another.

The semantics `Derives` is a natural (big-step) semantics in the style of
heap-based semantics for lazy evaluation and for call-time choice. Its
observation is the ordered list of results with multiplicity: every
alternative contributes its own results in program order, and a failing
alternative contributes an explicit `fail` result rather than vanishing.
Forcing a cell that is under evaluation yields `blackhole`.

`run` is an executable interpreter with fuel. `run_sound` states that every
answer list it computes is derivable, and `Derives.deterministic` that a
goal has at most one derivable answer list.

Equations are rules `head arity body`; a call dispatches to every rule with
that head and arity in program order (`candidates`). `callRule i` runs only
the rule at position `i`. Rule head `normHead` is reserved for the consumer
normalization program `normRule`, which forces a value and all its fields to
a constructor term; `observe` runs a computation and then normalizes its
result in the same branch.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

/-! ## Syntax -/

/-- Value expressions: variables (de Bruijn indices), constructor symbols and
binary application. A constructor applied to fields is the spine
`app (... (app (sym c) f₁) ...) fₖ`. -/
inductive VExp where
  | var (index : Nat)
  | sym (name : Nat)
  | app (head arg : VExp)
  deriving DecidableEq, Repr

/-- Runtime values over a type of cell names. `need` is a memoized
suspension and `thunk` an ordinary one: both are implicit suspensions, which
`force` evaluates. `code` is an explicit suspension (a quoted computation): it is
a weak head normal form, which only activation (`run`) executes. All three name
a cell of the store. -/
inductive Val (Cell : Type) where
  | sym (name : Nat)
  | app (head arg : Val Cell)
  | need (cell : Cell)
  | thunk (cell : Cell)
  | code (cell : Cell)
  deriving DecidableEq, Repr

namespace Val

variable {Cell : Type}

/-- Whether a value is an implicit suspension rather than a weak head normal form. -/
def isCell : Val Cell → Bool
  | .need _ => true
  | .thunk _ => true
  | _ => false

/-- The head symbol and fields of a constructor spine. -/
def spine : Val Cell → Option (Nat × List (Val Cell))
  | .sym c => some (c, [])
  | .app f x => (spine f).map fun p => (p.1, p.2 ++ [x])
  | _ => none

/-- Match a constructor pattern `c` with `k` fields. -/
def matchCon (w : Val Cell) (c k : Nat) : Option (List (Val Cell)) :=
  match w.spine with
  | some (c', args) => if c' = c ∧ args.length = k then some args else none
  | none => none

/-- Match an application node. -/
def matchApp : Val Cell → Option (Val Cell × Val Cell)
  | .app f x => some (f, x)
  | _ => none

/-- Rename the cells of a value. -/
def mapCells {Cell' : Type} (f : Cell → Cell') : Val Cell → Val Cell'
  | .sym c => .sym c
  | .app g x => .app (g.mapCells f) (x.mapCells f)
  | .need c => .need (f c)
  | .thunk c => .thunk (f c)
  | .code c => .code (f c)

/-- A value with no implicit suspension anywhere: a normal form. Explicit code
values may occur; they are data. -/
def noSusp : Val Cell → Bool
  | .sym _ => true
  | .app f x => f.noSusp && x.noSusp
  | .need _ => false
  | .thunk _ => false
  | .code _ => true

/-- A value that mentions no cell: a constructor term. -/
def cellFree : Val Cell → Bool
  | .sym _ => true
  | .app f x => f.cellFree && x.cellFree
  | _ => false

/-- A predicate on every cell referenced by the value, including opaque code.
Structural readiness alone does not establish that those references are live. -/
def referencesSatisfy (p : Cell → Prop) : Val Cell → Prop
  | .sym _ => True
  | .app f x => f.referencesSatisfy p ∧ x.referencesSatisfy p
  | .need c => p c
  | .thunk c => p c
  | .code c => p c

theorem referencesSatisfy_mono {p q : Cell → Prop}
    (implies : ∀ c, p c → q c) {value : Val Cell}
    (valid : value.referencesSatisfy p) : value.referencesSatisfy q := by
  induction value with
  | sym => trivial
  | app f x ihf ihx => exact ⟨ihf valid.1, ihx valid.2⟩
  | need c => exact implies c valid
  | thunk c => exact implies c valid
  | code c => exact implies c valid

/-- Cell renaming transports the reference predicate through the same map;
it does not turn an implicit reference into code or into constructor data. -/
theorem referencesSatisfy_mapCells {Cell' : Type} (rename : Cell → Cell')
    (p : Cell' → Prop) (value : Val Cell) :
    (value.mapCells rename).referencesSatisfy p ↔
      value.referencesSatisfy (fun c => p (rename c)) := by
  induction value <;> simp_all [mapCells, referencesSatisfy]

/-- Finite strong-reference support for tracing. This set forgets repeated
address occurrences; the value itself retains their positions and roles. -/
def referenceSet [DecidableEq Cell] : Val Cell → Finset Cell
  | .sym _ => ∅
  | .app f x => f.referenceSet ∪ x.referenceSet
  | .need cell | .thunk cell | .code cell => {cell}

/-- The independent support enumeration agrees with the structural predicate,
including opaque code carriers without activating their bodies. -/
theorem referencesSatisfy_iff_referenceSet [DecidableEq Cell] (p : Cell → Prop) (value : Val Cell) :
    value.referencesSatisfy p ↔ ∀ cell ∈ value.referenceSet, p cell := by
  induction value <;> simp_all [referencesSatisfy, referenceSet, or_imp, forall_and]

end Val

/-- Every cell referenced from an environment satisfies the given predicate. -/
abbrev EnvReferencesSatisfy {Cell : Type} (p : Cell → Prop) (env : List (Val Cell)) : Prop :=
  ∀ value ∈ env, value.referencesSatisfy p

theorem EnvReferencesSatisfy.mono {Cell : Type} {p q : Cell → Prop}
    (implies : ∀ c, p c → q c) {env : List (Val Cell)}
    (valid : EnvReferencesSatisfy p env) : EnvReferencesSatisfy q env :=
  fun value member => Val.referencesSatisfy_mono implies (valid value member)

theorem EnvReferencesSatisfy.cons {Cell : Type} {p : Cell → Prop}
    {value : Val Cell} {env : List (Val Cell)}
    (head : value.referencesSatisfy p) (tail : EnvReferencesSatisfy p env) :
    EnvReferencesSatisfy p (value :: env) := by
  intro next member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail next member

theorem EnvReferencesSatisfy.append {Cell : Type} {p : Cell → Prop}
    {left right : List (Val Cell)} (first : EnvReferencesSatisfy p left)
    (second : EnvReferencesSatisfy p right) : EnvReferencesSatisfy p (left ++ right) := by
  intro value member
  rcases List.mem_append.mp member with member | member
  · exact first value member
  · exact second value member

/-- The union of the strong-reference supports in a captured environment. -/
def envReferenceSet {Cell : Type} [DecidableEq Cell] : List (Val Cell) → Finset Cell
  | [] => ∅
  | value :: rest => value.referenceSet ∪ envReferenceSet rest

theorem mem_envReferenceSet_iff {Cell : Type} [DecidableEq Cell]
    (env : List (Val Cell)) (cell : Cell) :
    cell ∈ envReferenceSet env ↔ ∃ value ∈ env, cell ∈ value.referenceSet := by
  induction env with
  | nil => simp [envReferenceSet]
  | cons value rest ih => simp [envReferenceSet, ih]

theorem EnvReferencesSatisfy_iff_referenceSet {Cell : Type} [DecidableEq Cell]
    (p : Cell → Prop) (env : List (Val Cell)) :
    EnvReferencesSatisfy p env ↔ ∀ cell ∈ envReferenceSet env, p cell := by
  constructor
  · intro valid cell member
    obtain ⟨value, captured, reference⟩ := (mem_envReferenceSet_iff env cell).mp member
    exact (value.referencesSatisfy_iff_referenceSet p).mp (valid value captured) cell reference
  · intro valid value captured
    apply (value.referencesSatisfy_iff_referenceSet p).mpr
    intro cell reference
    exact valid cell ((mem_envReferenceSet_iff env cell).mpr ⟨value, captured, reference⟩)

/-- Evaluate a value expression in an environment. An index outside the
environment reads the symbol `0`. -/
def VExp.eval {Cell : Type} (ρ : List (Val Cell)) : VExp → Val Cell
  | .var i => ρ.getD i (.sym 0)
  | .sym c => .sym c
  | .app f x => .app (f.eval ρ) (x.eval ρ)

/-- Evaluation of a value expression introduces no new cell reference. -/
theorem VExp.eval_referencesSatisfy {Cell : Type} {p : Cell → Prop}
    {env : List (Val Cell)} (valid : EnvReferencesSatisfy p env) (value : VExp) :
    (value.eval env).referencesSatisfy p := by
  induction value with
  | var i =>
      simp only [VExp.eval, List.getD_eq_getElem?_getD]
      cases lookup : env[i]? with
      | none => trivial
      | some found =>
          exact valid found (List.mem_of_getElem? lookup)
  | sym => trivial
  | app f x ihf ihx => exact ⟨ihf, ihx⟩

theorem VExp.evalList_referencesSatisfy {Cell : Type} {p : Cell → Prop}
    {env : List (Val Cell)} (valid : EnvReferencesSatisfy p env) (values : List VExp) :
    EnvReferencesSatisfy p (values.map (·.eval env)) := by
  intro value member
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
  exact source.eval_referencesSatisfy valid

/-- Taking apart a constructor preserves the validity of all its fields. -/
theorem Val.spine_referencesSatisfy {Cell : Type} {p : Cell → Prop}
    {value : Val Cell} (valid : value.referencesSatisfy p)
    {name : Nat} {fields : List (Val Cell)} (matched : value.spine = some (name, fields)) :
    EnvReferencesSatisfy p fields := by
  induction value generalizing name fields with
  | sym c => cases matched; intro value member; cases member
  | app f x ihf _ =>
      simp only [Val.spine, Option.map_eq_some_iff] at matched
      obtain ⟨⟨head, previous⟩, first, equal⟩ := matched
      cases equal
      exact (ihf valid.1 first).append
        (EnvReferencesSatisfy.cons valid.2 (by intro value member; cases member))
  | need => simp [Val.spine] at matched
  | thunk => simp [Val.spine] at matched
  | code => simp [Val.spine] at matched

theorem Val.matchCon_referencesSatisfy {Cell : Type} {p : Cell → Prop}
    {value : Val Cell} (valid : value.referencesSatisfy p)
    {name arity : Nat} {fields : List (Val Cell)}
    (matched : value.matchCon name arity = some fields) : EnvReferencesSatisfy p fields := by
  unfold Val.matchCon at matched
  cases spine : value.spine with
  | none => simp [spine] at matched
  | some found =>
      obtain ⟨head, previous⟩ := found
      simp only [spine] at matched
      split at matched
      · cases matched
        exact value.spine_referencesSatisfy valid spine
      · simp at matched

theorem Val.matchApp_referencesSatisfy {Cell : Type} {p : Cell → Prop}
    {value head argument : Val Cell} (valid : value.referencesSatisfy p)
    (matched : value.matchApp = some (head, argument)) :
    head.referencesSatisfy p ∧ argument.referencesSatisfy p := by
  cases value <;> simp_all [Val.matchApp, Val.referencesSatisfy]

/-- Primitive operations: functions of the argument values they are given.
`eq yes no` compares two values structurally and answers the symbol `yes` or
`no`; it stands for kernel judgments and native calls, which inspect terms. -/
inductive Prim where
  | eq (yes no : Nat)
  deriving DecidableEq, Repr

/-- Apply a primitive to argument values; `none` is a failure (wrong arity). -/
def Prim.apply {Cell : Type} [DecidableEq Cell] : Prim → List (Val Cell) → Option (Val Cell)
  | .eq yes no, [a, b] => some (.sym (if a = b then yes else no))
  | .eq _ _, _ => none

/-- The head symbol of the residual left by activating a value that is not code. -/
def unquoteHead : Nat := 0

/-- Computations. `seq m n` runs `m` and binds its value at index `0` in `n`.
`need m n` and `delay m n` allocate a cell for `m` in the current environment
and bind `need ℓ` (respectively `thunk ℓ`) at index `0` in `n`. `caseCon v c k`
binds the `k` fields of a match (first field at index `0`); `caseApp v` binds
the head at index `0` and the argument at index `1`. `quote m` allocates a cell
for `m` and returns the code value naming it. `run v` and `prim op args` act on
the values they are given, without forcing them: `run` executes a code value
afresh and leaves any other value as the residual `unquoteHead v`; `prim`
applies the primitive. Their strict uses, which force first, are the derived
forms `strictRun` and `strictPrim`. -/
inductive Comp where
  | ret (value : VExp)
  | seq (first rest : Comp)
  | need (producer body : Comp)
  | delay (producer body : Comp)
  | force (value : VExp)
  | caseCon (scrutinee : VExp) (name arity : Nat) (hit miss : Comp)
  | caseApp (scrutinee : VExp) (hit miss : Comp)
  | call (function : Nat) (args : List VExp)
  | callRule (rule : Nat) (args : List VExp)
  | choose (left right : Comp)
  | fail
  | emit (event : Nat) (next : Comp)
  | quote (code : Comp)
  | run (value : VExp)
  | prim (op : Prim) (args : List VExp)
  deriving DecidableEq, Repr

/-- An equation `head x₀ … x_{arity-1} = body`; the body sees argument `i` at
index `i`. -/
structure Rule where
  head : Nat
  arity : Nat
  body : Comp
  deriving DecidableEq, Repr

/-- A program is an ordered list of rule occurrences; equal rules at two
positions are two occurrences. -/
abbrev Program := List Rule

/-- The rules a call `f` with `n` arguments dispatches to, in program order. -/
def candidates (P : Program) (f n : Nat) : List Rule :=
  P.filter fun r => r.head == f && r.arity == n

/-! ## Stores -/

/-- The cache of a cell. -/
inductive Memo where
  | pending
  | evaluating
  | done (value : Val Nat)
  deriving DecidableEq, Repr

/-- A cell: its immutable origin and its cache. -/
structure Suspension where
  code : Comp
  env : List (Val Nat)
  memo : Memo
  deriving DecidableEq, Repr

/-- A branch-local store: the cells (cell `ℓ` at position `ℓ`) and the
events emitted in this branch, oldest first. -/
structure Store where
  cells : List Suspension
  trace : List Nat
  deriving DecidableEq, Repr

namespace Store

def empty : Store := ⟨[], []⟩

/-- Allocate a pending cell at position `σ.cells.length`. -/
def alloc (σ : Store) (code : Comp) (env : List (Val Nat)) : Store :=
  { σ with cells := σ.cells ++ [⟨code, env, .pending⟩] }

/-- Replace the cache of cell `ℓ`, keeping its origin. -/
def setMemo (σ : Store) (ℓ : Nat) (k : Memo) : Store :=
  { σ with cells := σ.cells.modify ℓ fun c => { c with memo := k } }

/-- Record an event. -/
def emit (σ : Store) (e : Nat) : Store :=
  { σ with trace := σ.trace ++ [e] }

end Store

/-- Cached values retain the same reference obligation as ordinary values. -/
def Memo.referencesSatisfy (p : Nat → Prop) : Memo → Prop
  | .pending => True
  | .evaluating => True
  | .done value => value.referencesSatisfy p

def Suspension.referencesSatisfy (p : Nat → Prop) (cell : Suspension) : Prop :=
  EnvReferencesSatisfy p cell.env ∧ cell.memo.referencesSatisfy p

theorem Suspension.referencesSatisfy_mono {p q : Nat → Prop}
    (implies : ∀ c, p c → q c) {cell : Suspension}
    (valid : cell.referencesSatisfy p) : cell.referencesSatisfy q := by
  refine ⟨valid.1.mono implies, ?_⟩
  cases memo : cell.memo with
  | pending => trivial
  | evaluating => trivial
  | done value =>
      exact Val.referencesSatisfy_mono implies
        (by simpa only [Memo.referencesSatisfy, memo] using valid.2)

/-- Every reference in a captured environment or a cache names an allocated
cell of this store. This is a heap-closure property, not an ownership license. -/
def Store.referencesClosed (store : Store) : Prop :=
  ∀ cell ∈ store.cells, cell.referencesSatisfy (fun i => i < store.cells.length)

theorem Store.referencesClosed_empty : Store.empty.referencesClosed := by
  simp [Store.referencesClosed, Store.empty]

theorem Store.referencesClosed_lookup {store : Store} (closed : store.referencesClosed)
    {index : Nat} {cell : Suspension} (lookup : store.cells[index]? = some cell) :
    cell.referencesSatisfy (fun i => i < store.cells.length) :=
  closed cell (List.mem_of_getElem? lookup)

theorem Store.referencesClosed_alloc {store : Store} (closed : store.referencesClosed)
    (code : Comp) {env : List (Val Nat)}
    (captured : EnvReferencesSatisfy (fun i => i < store.cells.length) env) :
    (store.alloc code env).referencesClosed := by
  intro cell member
  simp only [Store.alloc, List.length_append, List.length_singleton]
  simp only [Store.alloc, List.mem_append, List.mem_singleton] at member
  rcases member with previous | rfl
  · exact Suspension.referencesSatisfy_mono (fun _ hi => Nat.lt_succ_of_lt hi) (closed cell previous)
  · exact ⟨captured.mono (fun _ hi => Nat.lt_succ_of_lt hi), trivial⟩

theorem Store.referencesClosed_setMemo {store : Store} (closed : store.referencesClosed)
    (index : Nat) {memo : Memo}
    (cached : memo.referencesSatisfy (fun i => i < store.cells.length)) :
    (store.setMemo index memo).referencesClosed := by
  intro cell member
  obtain ⟨position, inRange, same⟩ := List.getElem_of_mem member
  have lookup := List.getElem?_eq_some_iff.mpr ⟨inRange, same⟩
  simp only [Store.setMemo, List.length_modify]
  simp only [Store.setMemo, List.getElem?_modify] at lookup
  by_cases selected : index = position
  · subst position
    cases old : store.cells[index]? with
    | none => simp [old] at lookup
    | some original =>
        simp only [old, if_true, Option.map_eq_map, Option.map_some,
          Option.some.injEq] at lookup
        rw [← lookup]
        exact ⟨(closed original (List.mem_of_getElem? old)).1, cached⟩
  · simp only [selected, if_false, Option.map_eq_map, Option.map_id'] at lookup
    exact closed cell (List.mem_of_getElem? lookup)

theorem Store.referencesClosed_emit {store : Store} (closed : store.referencesClosed)
    (event : Nat) : (store.emit event).referencesClosed := closed

/-- The outcome of one alternative. -/
inductive Outcome where
  | ok (value : Val Nat)
  | fail
  | blackhole
  deriving DecidableEq, Repr

def Outcome.isOk : Outcome → Bool
  | .ok _ => true
  | _ => false

/-- The outcome of a primitive application. -/
def primOutcome (op : Prim) (vs : List (Val Nat)) : Outcome :=
  match op.apply vs with
  | some v => .ok v
  | none => .fail

/-- One alternative's outcome with the store of its branch. -/
abbrev Result := Outcome × Store

/-- Failure outcomes have no value reference. Successful outcomes retain
their own branch's reference obligation. -/
def Outcome.referencesSatisfy (p : Nat → Prop) : Outcome → Prop
  | .ok value => value.referencesSatisfy p
  | .fail => True
  | .blackhole => True

/-- A result retains a closed heap and all referenced cells, and allocation
has not moved backwards from the continuation's captured lower bound. -/
def ResultReferencesClosed (minimum : Nat) (result : Result) : Prop :=
  minimum ≤ result.2.cells.length ∧ result.2.referencesClosed ∧
    result.1.referencesSatisfy (fun i => i < result.2.cells.length)

abbrev ResultsReferencesClosed (minimum : Nat) (results : List Result) : Prop :=
  ∀ result ∈ results, ResultReferencesClosed minimum result

theorem ResultsReferencesClosed.append {minimum : Nat} {left right : List Result}
    (first : ResultsReferencesClosed minimum left)
    (second : ResultsReferencesClosed minimum right) :
    ResultsReferencesClosed minimum (left ++ right) := by
  intro result member
  rcases List.mem_append.mp member with member | member
  · exact first result member
  · exact second result member

theorem ResultsReferencesClosed.lower {minimum smaller : Nat} {results : List Result}
    (bound : smaller ≤ minimum) (valid : ResultsReferencesClosed minimum results) :
    ResultsReferencesClosed smaller results := by
  intro result member
  have current := valid result member
  exact ⟨Nat.le_trans bound current.1, current.2⟩

theorem ResultsReferencesClosed.singleton {minimum : Nat} {store : Store}
    {outcome : Outcome} (bound : minimum ≤ store.cells.length)
    (closed : store.referencesClosed)
    (value : outcome.referencesSatisfy (fun i => i < store.cells.length)) :
    ResultsReferencesClosed minimum [(outcome, store)] := by
  intro result member
  have same := List.mem_singleton.mp member
  subst result
  exact ⟨bound, closed, value⟩

theorem ResultsReferencesClosed.cons {minimum : Nat} {result : Result} {results : List Result}
    (head : ResultReferencesClosed minimum result)
    (tail : ResultsReferencesClosed minimum results) :
    ResultsReferencesClosed minimum (result :: results) := by
  intro next member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail next member

theorem Outcome.referencesSatisfy_of_stop {outcome : Outcome} (stopped : outcome.isOk = false)
    (p : Nat → Prop) : outcome.referencesSatisfy p := by
  cases outcome <;> simp_all [Outcome.isOk, Outcome.referencesSatisfy]

theorem primOutcome_referencesSatisfy (op : Prim) (values : List (Val Nat))
    (p : Nat → Prop) : (primOutcome op values).referencesSatisfy p := by
  cases op with
  | eq yes no =>
      cases values with
      | nil => trivial
      | cons first rest =>
          cases rest with
          | nil => trivial
          | cons second rest =>
              cases rest <;> simp [primOutcome, Prim.apply, Outcome.referencesSatisfy,
                Val.referencesSatisfy]

/-! ## The natural semantics -/

/-- The judgment forms. `eval` runs a computation; `alts` runs alternatives
from one store and concatenates; `seqK`, `commitK` and `followK` continue each
result of an earlier judgment in order; `forceVal` forces a value to weak head
normal form, following memoized indirections. -/
inductive Goal where
  | eval (store : Store) (env : List (Val Nat)) (code : Comp)
  | alts (store : Store) (branches : List (Comp × List (Val Nat)))
  | seqK (rest : Comp) (env : List (Val Nat)) (results : List Result)
  | forceVal (store : Store) (value : Val Nat)
  | commitK (cell : Nat) (results : List Result)
  | followK (results : List Result)

/-- The natural semantics of call-time choice with branch-local memoization. -/
inductive Derives (P : Program) : Goal → List Result → Prop where
  | ret {σ : Store} {ρ : List (Val Nat)} {v : VExp} :
      Derives P (.eval σ ρ (.ret v)) [(.ok (v.eval ρ), σ)]
  | seq {σ : Store} {ρ : List (Val Nat)} {m n : Comp} {L₁ L : List Result} :
      Derives P (.eval σ ρ m) L₁ → Derives P (.seqK n ρ L₁) L →
      Derives P (.eval σ ρ (.seq m n)) L
  | need {σ : Store} {ρ : List (Val Nat)} {m n : Comp} {L : List Result} :
      Derives P (.eval (σ.alloc m ρ) (.need σ.cells.length :: ρ) n) L →
      Derives P (.eval σ ρ (.need m n)) L
  | delay {σ : Store} {ρ : List (Val Nat)} {m n : Comp} {L : List Result} :
      Derives P (.eval (σ.alloc m ρ) (.thunk σ.cells.length :: ρ) n) L →
      Derives P (.eval σ ρ (.delay m n)) L
  | force {σ : Store} {ρ : List (Val Nat)} {v : VExp} {L : List Result} :
      Derives P (.forceVal σ (v.eval ρ)) L → Derives P (.eval σ ρ (.force v)) L
  | caseConHit {σ : Store} {ρ : List (Val Nat)} {v : VExp} {c k : Nat} {hit miss : Comp}
      {args : List (Val Nat)} {L : List Result} :
      (v.eval ρ).matchCon c k = some args →
      Derives P (.eval σ (args ++ ρ) hit) L →
      Derives P (.eval σ ρ (.caseCon v c k hit miss)) L
  | caseConMiss {σ : Store} {ρ : List (Val Nat)} {v : VExp} {c k : Nat} {hit miss : Comp}
      {L : List Result} :
      (v.eval ρ).matchCon c k = none →
      Derives P (.eval σ ρ miss) L →
      Derives P (.eval σ ρ (.caseCon v c k hit miss)) L
  | caseAppHit {σ : Store} {ρ : List (Val Nat)} {v : VExp} {hit miss : Comp}
      {f x : Val Nat} {L : List Result} :
      (v.eval ρ).matchApp = some (f, x) →
      Derives P (.eval σ (f :: x :: ρ) hit) L →
      Derives P (.eval σ ρ (.caseApp v hit miss)) L
  | caseAppMiss {σ : Store} {ρ : List (Val Nat)} {v : VExp} {hit miss : Comp}
      {L : List Result} :
      (v.eval ρ).matchApp = none →
      Derives P (.eval σ ρ miss) L →
      Derives P (.eval σ ρ (.caseApp v hit miss)) L
  | call {σ : Store} {ρ : List (Val Nat)} {f : Nat} {args : List VExp} {L : List Result} :
      candidates P f args.length ≠ [] →
      Derives P (.alts σ ((candidates P f args.length).map
        fun r => (r.body, args.map (·.eval ρ)))) L →
      Derives P (.eval σ ρ (.call f args)) L
  | callNone {σ : Store} {ρ : List (Val Nat)} {f : Nat} {args : List VExp} :
      candidates P f args.length = [] →
      Derives P (.eval σ ρ (.call f args)) [(.fail, σ)]
  | callRule {σ : Store} {ρ : List (Val Nat)} {i : Nat} {args : List VExp} {r : Rule}
      {L : List Result} :
      P[i]? = some r → r.arity = args.length →
      Derives P (.eval σ (args.map (·.eval ρ)) r.body) L →
      Derives P (.eval σ ρ (.callRule i args)) L
  | callRuleNone {σ : Store} {ρ : List (Val Nat)} {i : Nat} {args : List VExp} :
      (∀ r, P[i]? = some r → r.arity ≠ args.length) →
      Derives P (.eval σ ρ (.callRule i args)) [(.fail, σ)]
  | choose {σ : Store} {ρ : List (Val Nat)} {m n : Comp} {L₁ L₂ : List Result} :
      Derives P (.eval σ ρ m) L₁ → Derives P (.eval σ ρ n) L₂ →
      Derives P (.eval σ ρ (.choose m n)) (L₁ ++ L₂)
  | fail {σ : Store} {ρ : List (Val Nat)} :
      Derives P (.eval σ ρ .fail) [(.fail, σ)]
  | emit {σ : Store} {ρ : List (Val Nat)} {e : Nat} {m : Comp} {L : List Result} :
      Derives P (.eval (σ.emit e) ρ m) L → Derives P (.eval σ ρ (.emit e m)) L
  | quote {σ : Store} {ρ : List (Val Nat)} {m : Comp} :
      Derives P (.eval σ ρ (.quote m)) [(.ok (.code σ.cells.length), σ.alloc m ρ)]
  | runCode {σ : Store} {ρ : List (Val Nat)} {v : VExp} {ℓ : Nat} {c : Suspension}
      {L₁ L : List Result} :
      v.eval ρ = .code ℓ → σ.cells[ℓ]? = some c →
      Derives P (.eval σ c.env c.code) L₁ → Derives P (.followK L₁) L →
      Derives P (.eval σ ρ (.run v)) L
  | runOther {σ : Store} {ρ : List (Val Nat)} {v : VExp} :
      (∀ ℓ, v.eval ρ ≠ .code ℓ) →
      Derives P (.eval σ ρ (.run v)) [(.ok (.app (.sym unquoteHead) (v.eval ρ)), σ)]
  | prim {σ : Store} {ρ : List (Val Nat)} {op : Prim} {args : List VExp} :
      Derives P (.eval σ ρ (.prim op args)) [(primOutcome op (args.map (·.eval ρ)), σ)]
  | altsNil {σ : Store} : Derives P (.alts σ []) []
  | altsCons {σ : Store} {m : Comp} {ρ : List (Val Nat)}
      {bs : List (Comp × List (Val Nat))} {L₁ L₂ : List Result} :
      Derives P (.eval σ ρ m) L₁ → Derives P (.alts σ bs) L₂ →
      Derives P (.alts σ ((m, ρ) :: bs)) (L₁ ++ L₂)
  | seqKNil {n : Comp} {ρ : List (Val Nat)} : Derives P (.seqK n ρ []) []
  | seqKOk {n : Comp} {ρ : List (Val Nat)} {w : Val Nat} {σ : Store} {rs L₁ L₂ : List Result} :
      Derives P (.eval σ (w :: ρ) n) L₁ → Derives P (.seqK n ρ rs) L₂ →
      Derives P (.seqK n ρ ((.ok w, σ) :: rs)) (L₁ ++ L₂)
  | seqKStop {n : Comp} {ρ : List (Val Nat)} {o : Outcome} {σ : Store} {rs L₂ : List Result} :
      o.isOk = false → Derives P (.seqK n ρ rs) L₂ →
      Derives P (.seqK n ρ ((o, σ) :: rs)) ((o, σ) :: L₂)
  | forceWhnf {σ : Store} {w : Val Nat} :
      w.isCell = false → Derives P (.forceVal σ w) [(.ok w, σ)]
  | forceDone {σ : Store} {ℓ : Nat} {c : Suspension} {w : Val Nat} {L : List Result} :
      σ.cells[ℓ]? = some c → c.memo = .done w →
      Derives P (.forceVal σ w) L → Derives P (.forceVal σ (.need ℓ)) L
  | forceBlackhole {σ : Store} {ℓ : Nat} {c : Suspension} :
      σ.cells[ℓ]? = some c → c.memo = .evaluating →
      Derives P (.forceVal σ (.need ℓ)) [(.blackhole, σ)]
  | forcePending {σ : Store} {ℓ : Nat} {c : Suspension} {L₁ L : List Result} :
      σ.cells[ℓ]? = some c → c.memo = .pending →
      Derives P (.eval (σ.setMemo ℓ .evaluating) c.env c.code) L₁ →
      Derives P (.commitK ℓ L₁) L → Derives P (.forceVal σ (.need ℓ)) L
  | forceThunk {σ : Store} {ℓ : Nat} {c : Suspension} {L₁ L : List Result} :
      σ.cells[ℓ]? = some c →
      Derives P (.eval σ c.env c.code) L₁ → Derives P (.followK L₁) L →
      Derives P (.forceVal σ (.thunk ℓ)) L
  | commitNil {ℓ : Nat} : Derives P (.commitK ℓ []) []
  | commitOk {ℓ : Nat} {w : Val Nat} {σ : Store} {rs L₁ L₂ : List Result} :
      Derives P (.forceVal (σ.setMemo ℓ (.done w)) w) L₁ →
      Derives P (.commitK ℓ rs) L₂ →
      Derives P (.commitK ℓ ((.ok w, σ) :: rs)) (L₁ ++ L₂)
  | commitStop {ℓ : Nat} {o : Outcome} {σ : Store} {rs L₂ : List Result} :
      o.isOk = false → Derives P (.commitK ℓ rs) L₂ →
      Derives P (.commitK ℓ ((o, σ) :: rs)) ((o, σ.setMemo ℓ .pending) :: L₂)
  | followNil : Derives P (.followK []) []
  | followOk {w : Val Nat} {σ : Store} {rs L₁ L₂ : List Result} :
      Derives P (.forceVal σ w) L₁ → Derives P (.followK rs) L₂ →
      Derives P (.followK ((.ok w, σ) :: rs)) (L₁ ++ L₂)
  | followStop {o : Outcome} {σ : Store} {rs L₂ : List Result} :
      o.isOk = false → Derives P (.followK rs) L₂ →
      Derives P (.followK ((o, σ) :: rs)) ((o, σ) :: L₂)

/-- A singleton successful stage continues in that result's own store and
with its value bound above the caller's environment. -/
theorem Derives.seq_single {P : Program} {σ σ' : Store} {ρ : List (Val Nat)}
    {m n : Comp} {value : Val Nat} {results : List Result}
    (first : Derives P (.eval σ ρ m) [(.ok value, σ')])
    (second : Derives P (.eval σ' (value :: ρ) n) results) :
    Derives P (.eval σ ρ (.seq m n)) results := by
  simpa only [List.append_nil] using Derives.seq first (Derives.seqKOk second Derives.seqKNil)

/-- The ordinary call procedure constructs a one-rule dispatch when its
actual candidate list is a singleton. The body uses the evaluated arguments. -/
theorem Derives.call_single_rule {P : Program} {σ : Store} {ρ : List (Val Nat)}
    {head : Nat} {arguments : List VExp} {rule : Rule} {results : List Result}
    (selected : candidates P head arguments.length = [rule])
    (body : Derives P (.eval σ (arguments.map (·.eval ρ)) rule.body) results) :
    Derives P (.eval σ ρ (.call head arguments)) results := by
  apply Derives.call (by rw [selected]; simp)
  simpa only [selected, List.map_cons, List.map_nil, List.append_nil] using
    Derives.altsCons body Derives.altsNil

/-! ## Retention of cell references -/

/-- The actual judgments preserve their own refined branch stores. A saved
continuation's environment remains valid because allocation never shrinks.
No theorem here grants a right to activate an opaque code reference. -/
def ReferenceMotive : Goal → List Result → Prop
  | .eval store env _, results =>
      store.referencesClosed →
      EnvReferencesSatisfy (fun i => i < store.cells.length) env →
      ResultsReferencesClosed store.cells.length results
  | .alts store branches, results =>
      store.referencesClosed →
      (∀ branch ∈ branches,
        EnvReferencesSatisfy (fun i => i < store.cells.length) branch.2) →
      ResultsReferencesClosed store.cells.length results
  | .seqK _ env previous, results =>
      ∀ minimum, EnvReferencesSatisfy (fun i => i < minimum) env →
        ResultsReferencesClosed minimum previous → ResultsReferencesClosed minimum results
  | .forceVal store value, results =>
      store.referencesClosed → value.referencesSatisfy (fun i => i < store.cells.length) →
      ResultsReferencesClosed store.cells.length results
  | .commitK _ previous, results =>
      ∀ minimum, ResultsReferencesClosed minimum previous → ResultsReferencesClosed minimum results
  | .followK previous, results =>
      ∀ minimum, ResultsReferencesClosed minimum previous → ResultsReferencesClosed minimum results

/-- Every finite derivation retains the references of returned values,
captured environments and caches in its resulting heap. The proof follows
the evaluator's allocation, cache updates and each ordered branch. -/
theorem reference_invariant (program : Program) :
    ∀ goal results, Derives program goal results → ReferenceMotive goal results := by
  intro goal results derivation
  induction derivation with
  | @ret store env value =>
      intro closed captured
      exact ResultsReferencesClosed.singleton (Nat.le_refl _) closed
        (value.eval_referencesSatisfy captured)
  | @seq store env first rest previous results _ _ firstIH restIH =>
      intro closed captured
      exact restIH store.cells.length captured (firstIH closed captured)
  | @need store env producer body results _ ih =>
      intro closed captured
      have nextEnv := EnvReferencesSatisfy.cons
        (show (Val.need store.cells.length).referencesSatisfy
          (fun i => i < (store.alloc producer env).cells.length) from by simp [Store.alloc,
            Val.referencesSatisfy])
        (by simpa only [Store.alloc, List.length_append, List.length_singleton] using
          (captured.mono (fun _ hi => Nat.lt_succ_of_lt hi)))
      exact (ih (Store.referencesClosed_alloc closed producer captured) nextEnv).lower
        (by simp [Store.alloc])
  | @delay store env producer body results _ ih =>
      intro closed captured
      have nextEnv := EnvReferencesSatisfy.cons
        (show (Val.thunk store.cells.length).referencesSatisfy
          (fun i => i < (store.alloc producer env).cells.length) from by simp [Store.alloc,
            Val.referencesSatisfy])
        (by simpa only [Store.alloc, List.length_append, List.length_singleton] using
          (captured.mono (fun _ hi => Nat.lt_succ_of_lt hi)))
      exact (ih (Store.referencesClosed_alloc closed producer captured) nextEnv).lower
        (by simp [Store.alloc])
  | force _ ih =>
      intro closed captured
      exact ih closed (VExp.eval_referencesSatisfy captured _)
  | caseConHit matched _ ih =>
      intro closed captured
      exact ih closed ((Val.matchCon_referencesSatisfy
        (VExp.eval_referencesSatisfy captured _) matched).append captured)
  | caseConMiss _ _ ih => exact ih
  | caseAppHit matched _ ih =>
      intro closed captured
      have fields := Val.matchApp_referencesSatisfy (VExp.eval_referencesSatisfy captured _) matched
      exact ih closed (EnvReferencesSatisfy.cons fields.1 (EnvReferencesSatisfy.cons fields.2 captured))
  | caseAppMiss _ _ ih => exact ih
  | @call store env head args results _ _ ih =>
      intro closed captured
      apply ih closed
      intro branch member
      obtain ⟨rule, _, rfl⟩ := List.mem_map.mp member
      exact VExp.evalList_referencesSatisfy captured args
  | callNone =>
      intro closed _
      exact ResultsReferencesClosed.singleton (Nat.le_refl _) closed trivial
  | @callRule store env index args rule results _ _ _ ih =>
      intro closed captured
      exact ih closed (VExp.evalList_referencesSatisfy captured args)
  | callRuleNone =>
      intro closed _
      exact ResultsReferencesClosed.singleton (Nat.le_refl _) closed trivial
  | choose _ _ leftIH rightIH =>
      intro closed captured
      exact (leftIH closed captured).append (rightIH closed captured)
  | fail =>
      intro closed _
      exact ResultsReferencesClosed.singleton (Nat.le_refl _) closed trivial
  | emit _ ih =>
      intro closed captured
      exact ih (Store.referencesClosed_emit closed _) captured
  | @quote store env body =>
      intro closed captured
      exact ResultsReferencesClosed.singleton (by simp [Store.alloc])
        (Store.referencesClosed_alloc closed body captured)
        (by simp [Outcome.referencesSatisfy, Val.referencesSatisfy, Store.alloc])
  | runCode _ lookup _ _ bodyIH followIH =>
      intro closed _
      exact followIH _ (bodyIH closed (Store.referencesClosed_lookup closed lookup).1)
  | runOther =>
      intro closed captured
      exact ResultsReferencesClosed.singleton (Nat.le_refl _) closed
        ⟨trivial, VExp.eval_referencesSatisfy captured _⟩
  | @prim store env op args =>
      intro closed _
      exact ResultsReferencesClosed.singleton (Nat.le_refl _) closed
        (primOutcome_referencesSatisfy op _ _)
  | altsNil => intro _ _ result member; cases member
  | altsCons _ _ firstIH restIH =>
      intro closed captured
      exact (firstIH closed (captured _ List.mem_cons_self)).append
        (restIH closed (fun branch member => captured branch (List.mem_cons_of_mem _ member)))
  | seqKNil => intro _ _ _ result member; cases member
  | @seqKOk rest env value store previous firstResults restResults _ _ firstIH restIH =>
      intro minimum captured valid
      have first := valid _ List.mem_cons_self
      have nextEnv := EnvReferencesSatisfy.cons first.2.2
        (captured.mono (fun i hi => Nat.lt_of_lt_of_le hi first.1))
      exact (firstIH first.2.1 nextEnv).lower first.1 |>.append
        (restIH minimum captured (fun result member => valid result (List.mem_cons_of_mem _ member)))
  | seqKStop _ _ ih =>
      intro minimum captured valid
      exact ResultsReferencesClosed.cons (valid _ List.mem_cons_self)
        (ih minimum captured (fun result member => valid result (List.mem_cons_of_mem _ member)))
  | forceWhnf =>
      intro closed value
      exact ResultsReferencesClosed.singleton (Nat.le_refl _) closed value
  | forceDone lookup memo _ ih =>
      intro closed _
      apply ih closed
      simpa only [memo, Memo.referencesSatisfy] using (Store.referencesClosed_lookup closed lookup).2
  | forceBlackhole =>
      intro closed _
      exact ResultsReferencesClosed.singleton (Nat.le_refl _) closed trivial
  | @forcePending store cell record previous results lookup _ _ _ bodyIH commitIH =>
      intro closed _
      have nextClosed := Store.referencesClosed_setMemo closed cell
        (show Memo.evaluating.referencesSatisfy (fun i => i < store.cells.length) from trivial)
      have nextEnv := (Store.referencesClosed_lookup closed lookup).1
      have capturedNext : EnvReferencesSatisfy
          (fun i => i < (store.setMemo cell .evaluating).cells.length) record.env := by
        simpa only [Store.setMemo, List.length_modify] using nextEnv
      have evaluated : ResultsReferencesClosed store.cells.length previous := by
        simpa only [Store.setMemo, List.length_modify] using bodyIH nextClosed capturedNext
      exact commitIH _ evaluated
  | forceThunk lookup _ _ bodyIH followIH =>
      intro closed _
      exact followIH _ (bodyIH closed (Store.referencesClosed_lookup closed lookup).1)
  | commitNil => intro _ _ result member; cases member
  | @commitOk cell value store previous firstResults restResults _ _ firstIH restIH =>
      intro minimum valid
      have first := valid _ List.mem_cons_self
      have nextClosed := Store.referencesClosed_setMemo first.2.1 cell
        (memo := .done value) first.2.2
      have nextValue : value.referencesSatisfy
          (fun i => i < (store.setMemo cell (.done value)).cells.length) := by
        simpa only [Store.setMemo, List.length_modify, Outcome.referencesSatisfy] using first.2.2
      have evaluated : ResultsReferencesClosed store.cells.length firstResults := by
        simpa only [Store.setMemo, List.length_modify] using firstIH nextClosed nextValue
      exact evaluated.lower first.1 |>.append
        (restIH minimum (fun result member => valid result (List.mem_cons_of_mem _ member)))
  | @commitStop cell outcome store previous results stopped _ ih =>
      intro minimum valid
      have first := valid _ List.mem_cons_self
      apply ResultsReferencesClosed.cons
      · refine ⟨by simpa only [Store.setMemo, List.length_modify] using first.1,
          Store.referencesClosed_setMemo first.2.1 cell trivial, ?_⟩
        exact Outcome.referencesSatisfy_of_stop stopped _
      · exact ih minimum (fun result member => valid result (List.mem_cons_of_mem _ member))
  | followNil => intro _ _ result member; cases member
  | followOk _ _ firstIH restIH =>
      intro minimum valid
      have first := valid _ List.mem_cons_self
      exact (firstIH first.2.1 first.2.2).lower first.1 |>.append
        (restIH minimum (fun result member => valid result (List.mem_cons_of_mem _ member)))
  | followStop _ _ ih =>
      intro minimum valid
      exact ResultsReferencesClosed.cons (valid _ List.mem_cons_self)
        (ih minimum (fun result member => valid result (List.mem_cons_of_mem _ member)))

/-- Complete evaluation preserves the live carrier of every returned value
and all suspended origins retained in that value's branch. -/
theorem Derives.eval_referencesClosed {program : Program} {store : Store}
    {env : List (Val Nat)} {code : Comp} {results : List Result}
    (executed : Derives program (.eval store env code) results)
    (closed : store.referencesClosed)
    (captured : EnvReferencesSatisfy (fun i => i < store.cells.length) env) :
    ResultsReferencesClosed store.cells.length results :=
  reference_invariant program _ _ executed closed captured

/-! ## An executable interpreter -/

/-- The interpreter with fuel. `none` means the fuel was exhausted or a
dangling cell was met. -/
def run (P : Program) : Nat → Goal → Option (List Result)
  | 0, _ => none
  | fuel + 1, goal =>
    match goal with
    | .eval σ ρ code =>
      match code with
      | .ret v => some [(.ok (v.eval ρ), σ)]
      | .seq m n =>
          (run P fuel (.eval σ ρ m)).bind fun L₁ => run P fuel (.seqK n ρ L₁)
      | .need m n => run P fuel (.eval (σ.alloc m ρ) (.need σ.cells.length :: ρ) n)
      | .delay m n => run P fuel (.eval (σ.alloc m ρ) (.thunk σ.cells.length :: ρ) n)
      | .force v => run P fuel (.forceVal σ (v.eval ρ))
      | .caseCon v c k hit miss =>
          match (v.eval ρ).matchCon c k with
          | some args => run P fuel (.eval σ (args ++ ρ) hit)
          | none => run P fuel (.eval σ ρ miss)
      | .caseApp v hit miss =>
          match (v.eval ρ).matchApp with
          | some (f, x) => run P fuel (.eval σ (f :: x :: ρ) hit)
          | none => run P fuel (.eval σ ρ miss)
      | .call f args =>
          match candidates P f args.length with
          | [] => some [(.fail, σ)]
          | r :: rs =>
              run P fuel (.alts σ ((r :: rs).map fun r => (r.body, args.map (·.eval ρ))))
      | .callRule i args =>
          match P[i]? with
          | some r =>
              if r.arity = args.length then
                run P fuel (.eval σ (args.map (·.eval ρ)) r.body)
              else some [(.fail, σ)]
          | none => some [(.fail, σ)]
      | .choose m n =>
          (run P fuel (.eval σ ρ m)).bind fun L₁ =>
            (run P fuel (.eval σ ρ n)).bind fun L₂ => some (L₁ ++ L₂)
      | .fail => some [(.fail, σ)]
      | .emit e m => run P fuel (.eval (σ.emit e) ρ m)
      | .quote m => some [(.ok (.code σ.cells.length), σ.alloc m ρ)]
      | .run v =>
          match v.eval ρ with
          | .code ℓ =>
              match σ.cells[ℓ]? with
              | none => none
              | some c =>
                  (run P fuel (.eval σ c.env c.code)).bind fun L₁ => run P fuel (.followK L₁)
          | _ => some [(.ok (.app (.sym unquoteHead) (v.eval ρ)), σ)]
      | .prim op args => some [(primOutcome op (args.map (·.eval ρ)), σ)]
    | .alts σ bs =>
      match bs with
      | [] => some []
      | (m, ρ) :: rest =>
          (run P fuel (.eval σ ρ m)).bind fun L₁ =>
            (run P fuel (.alts σ rest)).bind fun L₂ => some (L₁ ++ L₂)
    | .seqK n ρ rs =>
      match rs with
      | [] => some []
      | (.ok w, σ) :: rest =>
          (run P fuel (.eval σ (w :: ρ) n)).bind fun L₁ =>
            (run P fuel (.seqK n ρ rest)).bind fun L₂ => some (L₁ ++ L₂)
      | (.fail, σ) :: rest =>
          (run P fuel (.seqK n ρ rest)).bind fun L₂ => some ((.fail, σ) :: L₂)
      | (.blackhole, σ) :: rest =>
          (run P fuel (.seqK n ρ rest)).bind fun L₂ => some ((.blackhole, σ) :: L₂)
    | .forceVal σ w =>
      match w with
      | .need ℓ =>
          match σ.cells[ℓ]? with
          | none => none
          | some c =>
              match c.memo with
              | .done v => run P fuel (.forceVal σ v)
              | .evaluating => some [(.blackhole, σ)]
              | .pending =>
                  (run P fuel (.eval (σ.setMemo ℓ .evaluating) c.env c.code)).bind
                    fun L₁ => run P fuel (.commitK ℓ L₁)
      | .thunk ℓ =>
          match σ.cells[ℓ]? with
          | none => none
          | some c =>
              (run P fuel (.eval σ c.env c.code)).bind fun L₁ => run P fuel (.followK L₁)
      | .sym c => some [(.ok (.sym c), σ)]
      | .app f x => some [(.ok (.app f x), σ)]
      | .code c => some [(.ok (.code c), σ)]
    | .commitK ℓ rs =>
      match rs with
      | [] => some []
      | (.ok w, σ) :: rest =>
          (run P fuel (.forceVal (σ.setMemo ℓ (.done w)) w)).bind fun L₁ =>
            (run P fuel (.commitK ℓ rest)).bind fun L₂ => some (L₁ ++ L₂)
      | (.fail, σ) :: rest =>
          (run P fuel (.commitK ℓ rest)).bind fun L₂ =>
            some ((.fail, σ.setMemo ℓ .pending) :: L₂)
      | (.blackhole, σ) :: rest =>
          (run P fuel (.commitK ℓ rest)).bind fun L₂ =>
            some ((.blackhole, σ.setMemo ℓ .pending) :: L₂)
    | .followK rs =>
      match rs with
      | [] => some []
      | (.ok w, σ) :: rest =>
          (run P fuel (.forceVal σ w)).bind fun L₁ =>
            (run P fuel (.followK rest)).bind fun L₂ => some (L₁ ++ L₂)
      | (.fail, σ) :: rest =>
          (run P fuel (.followK rest)).bind fun L₂ => some ((.fail, σ) :: L₂)
      | (.blackhole, σ) :: rest =>
          (run P fuel (.followK rest)).bind fun L₂ => some ((.blackhole, σ) :: L₂)

/-- Every answer list the interpreter computes is derivable. -/
theorem run_sound (P : Program) :
    ∀ (fuel : Nat) (g : Goal) (L : List Result), run P fuel g = some L → Derives P g L := by
  intro fuel
  induction fuel with
  | zero => intro g L h; simp [run] at h
  | succ fuel ih =>
    intro g L h
    cases g with
    | eval σ ρ code =>
      cases code with
      | ret v =>
          simp only [run, Option.some.injEq] at h
          subst h; exact .ret
      | seq m n =>
          simp only [run, Option.bind_eq_some_iff] at h
          obtain ⟨L₁, h₁, h₂⟩ := h
          exact .seq (ih _ _ h₁) (ih _ _ h₂)
      | need m n => exact .need (ih _ _ (by simpa only [run] using h))
      | delay m n => exact .delay (ih _ _ (by simpa only [run] using h))
      | force v => exact .force (ih _ _ (by simpa only [run] using h))
      | caseCon v c k hit miss =>
          simp only [run] at h
          cases hm : (v.eval ρ).matchCon c k with
          | some args =>
              rw [hm] at h
              exact .caseConHit hm (ih _ _ h)
          | none =>
              rw [hm] at h
              exact .caseConMiss hm (ih _ _ h)
      | caseApp v hit miss =>
          simp only [run] at h
          cases hm : (v.eval ρ).matchApp with
          | some p =>
              obtain ⟨f, x⟩ := p
              rw [hm] at h
              exact .caseAppHit hm (ih _ _ h)
          | none =>
              rw [hm] at h
              exact .caseAppMiss hm (ih _ _ h)
      | call f args =>
          simp only [run] at h
          cases hc : candidates P f args.length with
          | nil =>
              rw [hc] at h
              simp only [Option.some.injEq] at h
              subst h
              exact .callNone hc
          | cons r rs =>
              rw [hc] at h
              refine .call (by simp [hc]) ?_
              rw [hc]
              exact ih _ _ h
      | callRule i args =>
          simp only [run] at h
          cases hr : P[i]? with
          | none =>
              rw [hr] at h
              simp only [Option.some.injEq] at h
              subst h
              exact .callRuleNone (by simp [hr])
          | some r =>
              rw [hr] at h
              simp only at h
              by_cases ha : r.arity = args.length
              · rw [if_pos ha] at h
                exact .callRule hr ha (ih _ _ h)
              · rw [if_neg ha] at h
                simp only [Option.some.injEq] at h
                subst h
                refine .callRuleNone ?_
                intro r' hr'
                rw [hr] at hr'
                cases hr'
                exact ha
      | choose m n =>
          simp only [run, Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨L₁, h₁, L₂, h₂, rfl⟩ := h
          exact .choose (ih _ _ h₁) (ih _ _ h₂)
      | fail =>
          simp only [run, Option.some.injEq] at h
          subst h; exact .fail
      | emit e m => exact .emit (ih _ _ (by simpa only [run] using h))
      | quote m =>
          simp only [run, Option.some.injEq] at h
          subst h; exact .quote
      | run v =>
          have other : ∀ w, v.eval ρ = w → (∀ ℓ, w ≠ .code ℓ) →
              some [(Outcome.ok (.app (.sym unquoteHead) (v.eval ρ)), σ)] = some L →
              Derives P (.eval σ ρ (.run v)) L := by
            intro w hw hn hs
            simp only [Option.some.injEq] at hs
            subst hs
            exact .runOther (by rw [hw]; exact hn)
          cases hv : v.eval ρ with
          | code ℓ =>
              simp only [run, hv] at h
              cases hc : σ.cells[ℓ]? with
              | none => rw [hc] at h; simp at h
              | some c =>
                  rw [hc] at h
                  simp only [Option.bind_eq_some_iff] at h
                  obtain ⟨L₁, h₁, h₂⟩ := h
                  exact .runCode hv hc (ih _ _ h₁) (ih _ _ h₂)
          | sym c => simp only [run, hv] at h; exact other _ hv (by intro ℓ e; cases e) (by rw [hv]; exact h)
          | app f x => simp only [run, hv] at h; exact other _ hv (by intro ℓ e; cases e) (by rw [hv]; exact h)
          | need ℓ => simp only [run, hv] at h; exact other _ hv (by intro ℓ e; cases e) (by rw [hv]; exact h)
          | thunk ℓ => simp only [run, hv] at h; exact other _ hv (by intro ℓ e; cases e) (by rw [hv]; exact h)
      | prim op args =>
          simp only [run, Option.some.injEq] at h
          subst h; exact .prim
    | alts σ bs =>
      cases bs with
      | nil =>
          simp only [run, Option.some.injEq] at h
          subst h; exact .altsNil
      | cons b rest =>
          obtain ⟨m, ρ⟩ := b
          simp only [run, Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨L₁, h₁, L₂, h₂, rfl⟩ := h
          exact .altsCons (ih _ _ h₁) (ih _ _ h₂)
    | seqK n ρ rs =>
      cases rs with
      | nil =>
          simp only [run, Option.some.injEq] at h
          subst h; exact .seqKNil
      | cons r rest =>
          obtain ⟨o, σ⟩ := r
          cases o with
          | ok w =>
              simp only [run, Option.bind_eq_some_iff, Option.some.injEq] at h
              obtain ⟨L₁, h₁, L₂, h₂, rfl⟩ := h
              exact .seqKOk (ih _ _ h₁) (ih _ _ h₂)
          | fail =>
              simp only [run, Option.bind_eq_some_iff, Option.some.injEq] at h
              obtain ⟨L₂, h₂, rfl⟩ := h
              exact .seqKStop rfl (ih _ _ h₂)
          | blackhole =>
              simp only [run, Option.bind_eq_some_iff, Option.some.injEq] at h
              obtain ⟨L₂, h₂, rfl⟩ := h
              exact .seqKStop rfl (ih _ _ h₂)
    | forceVal σ w =>
      cases w with
      | need ℓ =>
          simp only [run] at h
          cases hc : σ.cells[ℓ]? with
          | none => rw [hc] at h; simp at h
          | some c =>
              rw [hc] at h
              simp only at h
              cases hk : c.memo with
              | done v =>
                  rw [hk] at h
                  exact .forceDone hc hk (ih _ _ h)
              | evaluating =>
                  rw [hk] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  exact .forceBlackhole hc hk
              | pending =>
                  rw [hk] at h
                  simp only [Option.bind_eq_some_iff] at h
                  obtain ⟨L₁, h₁, h₂⟩ := h
                  exact .forcePending hc hk (ih _ _ h₁) (ih _ _ h₂)
      | thunk ℓ =>
          simp only [run] at h
          cases hc : σ.cells[ℓ]? with
          | none => rw [hc] at h; simp at h
          | some c =>
              rw [hc] at h
              simp only [Option.bind_eq_some_iff] at h
              obtain ⟨L₁, h₁, h₂⟩ := h
              exact .forceThunk hc (ih _ _ h₁) (ih _ _ h₂)
      | sym c =>
          simp only [run, Option.some.injEq] at h
          subst h; exact .forceWhnf rfl
      | app f x =>
          simp only [run, Option.some.injEq] at h
          subst h; exact .forceWhnf rfl
      | code c =>
          simp only [run, Option.some.injEq] at h
          subst h; exact .forceWhnf rfl
    | commitK ℓ rs =>
      cases rs with
      | nil =>
          simp only [run, Option.some.injEq] at h
          subst h; exact .commitNil
      | cons r rest =>
          obtain ⟨o, σ⟩ := r
          cases o with
          | ok w =>
              simp only [run, Option.bind_eq_some_iff, Option.some.injEq] at h
              obtain ⟨L₁, h₁, L₂, h₂, rfl⟩ := h
              exact .commitOk (ih _ _ h₁) (ih _ _ h₂)
          | fail =>
              simp only [run, Option.bind_eq_some_iff, Option.some.injEq] at h
              obtain ⟨L₂, h₂, rfl⟩ := h
              exact .commitStop rfl (ih _ _ h₂)
          | blackhole =>
              simp only [run, Option.bind_eq_some_iff, Option.some.injEq] at h
              obtain ⟨L₂, h₂, rfl⟩ := h
              exact .commitStop rfl (ih _ _ h₂)
    | followK rs =>
      cases rs with
      | nil =>
          simp only [run, Option.some.injEq] at h
          subst h; exact .followNil
      | cons r rest =>
          obtain ⟨o, σ⟩ := r
          cases o with
          | ok w =>
              simp only [run, Option.bind_eq_some_iff, Option.some.injEq] at h
              obtain ⟨L₁, h₁, L₂, h₂, rfl⟩ := h
              exact .followOk (ih _ _ h₁) (ih _ _ h₂)
          | fail =>
              simp only [run, Option.bind_eq_some_iff, Option.some.injEq] at h
              obtain ⟨L₂, h₂, rfl⟩ := h
              exact .followStop rfl (ih _ _ h₂)
          | blackhole =>
              simp only [run, Option.bind_eq_some_iff, Option.some.injEq] at h
              obtain ⟨L₂, h₂, rfl⟩ := h
              exact .followStop rfl (ih _ _ h₂)

/-- A completed run retains a closed heap and all captured and returned
references. Failed and blackhole branches keep their own closed stores too. -/
theorem run_eval_referencesClosed {program : Program} {store : Store}
    {env : List (Val Nat)} {code : Comp} {fuel : Nat} {results : List Result}
    (ran : run program fuel (.eval store env code) = some results)
    (closed : store.referencesClosed)
    (captured : EnvReferencesSatisfy (fun i => i < store.cells.length) env) :
    ResultsReferencesClosed store.cells.length results :=
  (run_sound program fuel _ _ ran).eval_referencesClosed closed captured

/-- Starting with no injected references constructs valid carriers at every
successful finite execution, including every allocated explicit code value. -/
theorem run_closed_referencesClosed {program : Program} {code : Comp}
    {fuel : Nat} {results : List Result}
    (ran : run program fuel (.eval Store.empty [] code) = some results) :
    ResultsReferencesClosed 0 results :=
  run_eval_referencesClosed ran Store.referencesClosed_empty (by intro value member; cases member)

/-- A goal has at most one derivable answer list: the semantics is a
function of its configuration, including order and multiplicity. -/
theorem Derives.deterministic {P : Program} {g : Goal} {L₁ L₂ : List Result}
    (h₁ : Derives P g L₁) (h₂ : Derives P g L₂) : L₁ = L₂ := by
  induction h₁ generalizing L₂ with
  | ret => cases h₂; rfl
  | seq _ _ ih₁ ih₂ =>
      cases h₂ with
      | seq a b => cases ih₁ a; exact ih₂ b
  | need _ ih => cases h₂ with | need a => exact ih a
  | delay _ ih => cases h₂ with | delay a => exact ih a
  | force _ ih => cases h₂ with | force a => exact ih a
  | caseConHit hm _ ih =>
      cases h₂ with
      | caseConHit hm' a => rw [hm] at hm'; cases hm'; exact ih a
      | caseConMiss hm' _ => rw [hm] at hm'; cases hm'
  | caseConMiss hm _ ih =>
      cases h₂ with
      | caseConHit hm' _ => rw [hm] at hm'; cases hm'
      | caseConMiss _ a => exact ih a
  | caseAppHit hm _ ih =>
      cases h₂ with
      | caseAppHit hm' a => rw [hm] at hm'; cases hm'; exact ih a
      | caseAppMiss hm' _ => rw [hm] at hm'; cases hm'
  | caseAppMiss hm _ ih =>
      cases h₂ with
      | caseAppHit hm' _ => rw [hm] at hm'; cases hm'
      | caseAppMiss _ a => exact ih a
  | call hc _ ih =>
      cases h₂ with
      | call _ a => exact ih a
      | callNone hc' => exact absurd hc' hc
  | callNone hc =>
      cases h₂ with
      | call hc' _ => exact absurd hc hc'
      | callNone _ => rfl
  | callRule hr ha _ ih =>
      cases h₂ with
      | callRule hr' _ a => rw [hr] at hr'; cases hr'; exact ih a
      | callRuleNone hn => exact absurd ha (hn _ hr)
  | callRuleNone hn =>
      cases h₂ with
      | callRule hr' ha' _ => exact absurd ha' (hn _ hr')
      | callRuleNone _ => rfl
  | choose _ _ ih₁ ih₂ =>
      cases h₂ with
      | choose a b => rw [ih₁ a, ih₂ b]
  | fail => cases h₂; rfl
  | emit _ ih => cases h₂ with | emit a => exact ih a
  | quote => cases h₂; rfl
  | runCode hv hc _ _ ih₁ ih₂ =>
      cases h₂ with
      | runCode hv' hc' a b =>
          rw [hv] at hv'; cases hv'; rw [hc] at hc'; cases hc'; cases ih₁ a; exact ih₂ b
      | runOther hn => exact absurd hv (hn _)
  | runOther hn =>
      cases h₂ with
      | runCode hv' _ _ _ => exact absurd hv' (hn _)
      | runOther _ => rfl
  | prim => cases h₂; rfl
  | altsNil => cases h₂; rfl
  | altsCons _ _ ih₁ ih₂ =>
      cases h₂ with
      | altsCons a b => rw [ih₁ a, ih₂ b]
  | seqKNil => cases h₂; rfl
  | seqKOk _ _ ih₁ ih₂ =>
      cases h₂ with
      | seqKOk a b => rw [ih₁ a, ih₂ b]
      | seqKStop hs _ => simp [Outcome.isOk] at hs
  | seqKStop hs _ ih =>
      cases h₂ with
      | seqKOk _ _ => simp [Outcome.isOk] at hs
      | seqKStop _ b => rw [ih b]
  | forceWhnf hw =>
      cases h₂ with
      | forceWhnf _ => rfl
      | forceDone => simp [Val.isCell] at hw
      | forceBlackhole => simp [Val.isCell] at hw
      | forcePending => simp [Val.isCell] at hw
      | forceThunk => simp [Val.isCell] at hw
  | forceDone hc hk _ ih =>
      cases h₂ with
      | forceWhnf hw => simp [Val.isCell] at hw
      | forceDone hc' hk' a =>
          rw [hc] at hc'; cases hc'; rw [hk] at hk'; cases hk'; exact ih a
      | forceBlackhole hc' hk' => rw [hc] at hc'; cases hc'; rw [hk] at hk'; cases hk'
      | forcePending hc' hk' _ _ => rw [hc] at hc'; cases hc'; rw [hk] at hk'; cases hk'
  | forceBlackhole hc hk =>
      cases h₂ with
      | forceWhnf hw => simp [Val.isCell] at hw
      | forceDone hc' hk' _ => rw [hc] at hc'; cases hc'; rw [hk] at hk'; cases hk'
      | forceBlackhole _ _ => rfl
      | forcePending hc' hk' _ _ => rw [hc] at hc'; cases hc'; rw [hk] at hk'; cases hk'
  | forcePending hc hk _ _ ih₁ ih₂ =>
      cases h₂ with
      | forceWhnf hw => simp [Val.isCell] at hw
      | forceDone hc' hk' _ => rw [hc] at hc'; cases hc'; rw [hk] at hk'; cases hk'
      | forceBlackhole hc' hk' => rw [hc] at hc'; cases hc'; rw [hk] at hk'; cases hk'
      | forcePending hc' _ a b =>
          rw [hc] at hc'; cases hc'; cases ih₁ a; exact ih₂ b
  | forceThunk hc _ _ ih₁ ih₂ =>
      cases h₂ with
      | forceWhnf hw => simp [Val.isCell] at hw
      | forceThunk hc' a b => rw [hc] at hc'; cases hc'; cases ih₁ a; exact ih₂ b
  | commitNil => cases h₂; rfl
  | commitOk _ _ ih₁ ih₂ =>
      cases h₂ with
      | commitOk a b => rw [ih₁ a, ih₂ b]
      | commitStop hs _ => simp [Outcome.isOk] at hs
  | commitStop hs _ ih =>
      cases h₂ with
      | commitOk _ _ => simp [Outcome.isOk] at hs
      | commitStop _ b => rw [ih b]
  | followNil => cases h₂; rfl
  | followOk _ _ ih₁ ih₂ =>
      cases h₂ with
      | followOk a b => rw [ih₁ a, ih₂ b]
      | followStop hs _ => simp [Outcome.isOk] at hs
  | followStop hs _ ih =>
      cases h₂ with
      | followOk _ _ => simp [Outcome.isOk] at hs
      | followStop _ b => rw [ih b]

/-! ## Observation -/

/-- The values among a list of results, in order and with multiplicity. -/
def values (L : List Result) : List (Val Nat) :=
  L.filterMap fun r =>
    match r.1 with
    | .ok w => some w
    | _ => none

/-- The rule head reserved for consumer normalization. -/
def normHead : Nat := 0

/-- Consumer normalization: force the value to weak head normal form; at an
application normalize the head and then the argument, in that order. Every
cell met is forced in the current branch. -/
def normBody : Comp :=
  .seq (.force (.var 0))
    (.caseApp (.var 0)
      (.seq (.call normHead [.var 0])
        (.seq (.call normHead [.var 2]) (.ret (.app (.var 1) (.var 0)))))
      (.ret (.var 0)))

def normRule : Rule := ⟨normHead, 1, normBody⟩

/-- Run `m` and normalize its value: a normalizing strict position. -/
def normalized (m : Comp) : Comp := .seq m (.call normHead [.var 0])

/-- Activation in a strict position: run `m`, force its value to weak head
normal form through any implicit suspension, then execute it if it is code. -/
def strictRun (m : Comp) : Comp :=
  .seq m (.seq (.force (.var 0)) (.run (.var 0)))

/-- Evaluate and normalize argument computations in order (`done` of them are
already bound), then continue with `k` applied to their number. Each argument
computation must be written for the environment it is evaluated in. -/
def normChain : List Comp → (Nat → Comp) → Nat → Comp
  | [], k, done => k done
  | m :: ms, k, done => .seq (normalized m) (normChain ms k (done + 1))

/-- The program extended with consumer normalization. -/
def observed (P : Program) : Program := normRule :: P

/-- Run a computation, then normalize its value in the same branch. -/
def observe (M : Comp) : Comp := .seq M (.call normHead [.var 0])

/-- The observation of a closed computation: its normalized results from the
empty store. -/
def Observes (P : Program) (M : Comp) (L : List Result) : Prop :=
  Derives (observed P) (.eval Store.empty [] (observe M)) L

/-- Executable observation of the values, for concrete programs. -/
def observeValues (P : Program) (fuel : Nat) (M : Comp) : Option (List (Val Nat)) :=
  (run (observed P) fuel (.eval Store.empty [] (observe M))).map values

theorem observeValues_sound {P : Program} {fuel : Nat} {M : Comp} {vs : List (Val Nat)}
    (h : observeValues P fuel M = some vs) :
    ∃ L, Observes P M L ∧ values L = vs := by
  unfold observeValues at h
  cases hr : run (observed P) fuel (.eval Store.empty [] (observe M)) with
  | none => rw [hr] at h; cases h
  | some L =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨L, run_sound _ _ _ _ hr, h⟩

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
