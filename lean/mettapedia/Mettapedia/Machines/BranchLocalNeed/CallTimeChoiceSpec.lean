import Mathlib.Data.List.Basic

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

end Val

/-- Evaluate a value expression in an environment. An index outside the
environment reads the symbol `0`. -/
def VExp.eval {Cell : Type} (ρ : List (Val Cell)) : VExp → Val Cell
  | .var i => ρ.getD i (.sym 0)
  | .sym c => .sym c
  | .app f x => .app (f.eval ρ) (x.eval ρ)

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
