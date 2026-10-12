import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSpec

/-!
# MeTTa-style equations and three argument-passing profiles

The source language has variables, constructor terms, calls of equation-defined
functions, a one-alternative `case` with a fallback, binary choice, failure,
events, quotation of code, activation of code and primitive calls. A call
dispatches to every equation of its head and arity, in program order, so
several matching equations are several alternatives.

The source is given meaning by translation into the core calculus. The three
translations differ only in how a constructor or a call passes its arguments:

* `Profile.need` (call-time choice): each argument occurrence becomes one
  memoized suspension; every use of the bound variable forces it, so all uses
  in one branch see one choice, and an argument that is never used is never
  run;
* `Profile.name` (run-time choice): each argument occurrence becomes an
  ordinary thunk; every use runs it again;
* `Profile.value` (eager): each argument is evaluated, in order, before the
  call or constructor, and the variable is bound to its value.

Neither sharing discipline is built into the core: the core has both `need`
and `delay`, and the profile chooses. Strict positions are the same in every
profile: an activation forces its operand to weak head normal form before
executing it (`strictRun`), and a primitive receives the normal forms of its
arguments (`normalized`), never a suspension. `case e c k hit miss` evaluates `e`;
`hit` sees the `k` fields (first field at index `0`) above the scrutinee
value; `miss` sees the scrutinee value at index `0`.

Source function `f` is core function `f + 1`; head `0` is reserved for
consumer normalization.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

/-- The argument-passing profile of a translation. -/
inductive Profile where
  | value
  | need
  | name
  deriving DecidableEq, Repr

mutual
/-- Source expressions. -/
inductive Expr where
  | var (index : Nat)
  | con (name : Nat) (args : Args)
  | call (function : Nat) (args : Args)
  | case (scrutinee : Expr) (name arity : Nat) (hit miss : Expr)
  | choose (left right : Expr)
  | fail
  | emit (event : Nat) (next : Expr)
  | quote (body : Expr)
  | activate (code : Expr)
  | prim (op : Prim) (args : Args)
/-- Source argument lists. -/
inductive Args where
  | nil
  | cons (head : Expr) (tail : Args)
end

deriving instance DecidableEq for Expr

/-- A source equation `head x₀ … x_{arity-1} = body`. -/
structure SRule where
  head : Nat
  arity : Nat
  body : Expr

abbrev SProgram := List SRule

/-- Bind an argument according to the profile. -/
def bindFor : Profile → Comp → Comp → Comp
  | .value => .seq
  | .need => .need
  | .name => .delay

/-- Use a variable according to the profile. -/
def useVar : Profile → Nat → Comp
  | .value, i => .ret (.var i)
  | .need, i => .force (.var i)
  | .name, i => .force (.var i)

/-- A renaming lifted under `k` binders. -/
def liftRen (k : Nat) (r : Nat → Nat) (i : Nat) : Nat :=
  if i < k then i else r (i - k) + k

/-- The `k` most recent bindings, oldest first. -/
def varsDesc (k : Nat) : List VExp :=
  (List.range k).reverse.map VExp.var

/-- A head applied to fields, as a spine. -/
def spineOf (head : VExp) (fields : List VExp) : VExp :=
  fields.foldl VExp.app head

mutual
/-- Translate an expression whose free variable `i` is core index `r i`. -/
def Expr.toCore (p : Profile) (r : Nat → Nat) : Expr → Comp
  | .var i => useVar p (r i)
  | .con c args => Args.toCore p r 0 args fun k => .ret (spineOf (.sym c) (varsDesc k))
  | .call f args => Args.toCore p r 0 args fun k => .call (f + 1) (varsDesc k)
  | .case e c k hit miss =>
      .seq (Expr.toCore p r e)
        (.caseCon (.var 0) c k (Expr.toCore p (liftRen (k + 1) r) hit)
          (Expr.toCore p (liftRen 1 r) miss))
  | .choose a b => .choose (Expr.toCore p r a) (Expr.toCore p r b)
  | .fail => .fail
  | .emit e m => .emit e (Expr.toCore p r m)
  | .quote e => .quote (Expr.toCore p r e)
  | .activate e => strictRun (Expr.toCore p r e)
  | .prim op args => Args.toCoreStrict p r 0 args fun k => .prim op (varsDesc k)
/-- Bind the arguments left to right; `done` arguments are already bound. -/
def Args.toCore (p : Profile) (r : Nat → Nat) (done : Nat) :
    Args → (Nat → Comp) → Comp
  | .nil, k => k done
  | .cons a rest, k =>
      bindFor p (Expr.toCore p (fun i => r i + done) a) (Args.toCore p r (done + 1) rest k)
/-- Bind the normal forms of the arguments left to right, under every profile:
a primitive's argument positions are strict. -/
def Args.toCoreStrict (p : Profile) (r : Nat → Nat) (done : Nat) :
    Args → (Nat → Comp) → Comp
  | .nil, k => k done
  | .cons a rest, k =>
      .seq (normalized (Expr.toCore p (fun i => r i + done) a))
        (Args.toCoreStrict p r (done + 1) rest k)
end

/-- The argument computations of a strict position, each written for the
environment it runs in. -/
def Args.strictComps (p : Profile) (r : Nat → Nat) : Nat → Args → List Comp
  | _, .nil => []
  | done, .cons a rest =>
      Expr.toCore p (fun i => r i + done) a :: Args.strictComps p r (done + 1) rest

def SRule.toCore (p : Profile) (rule : SRule) : Rule :=
  ⟨rule.head + 1, rule.arity, rule.body.toCore p id⟩

def SProgram.toCore (p : Profile) (P : SProgram) : Program :=
  P.map (SRule.toCore p)

/-- Authored function heads are shifted above the core normalization head.
Every binding profile therefore reserves the same consumer operation. -/
theorem SProgram.toCore_reserved (rules : SProgram) (p : Profile) :
    ∀ rule ∈ rules.toCore p, rule.head ≠ normHead := by
  intro rule member
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
  simp [SRule.toCore, normHead]

/-- The observed values of a closed source expression under a profile. -/
def sourceValues (p : Profile) (P : SProgram) (fuel : Nat) (e : Expr) :
    Option (List (Val Nat)) :=
  observeValues (P.toCore p) fuel (e.toCore p id)

/-- The observation of a closed source expression under a profile. -/
def SourceObserves (p : Profile) (P : SProgram) (e : Expr) (L : List Result) : Prop :=
  Observes (P.toCore p) (e.toCore p id) L

theorem sourceValues_sound {p : Profile} {P : SProgram} {fuel : Nat} {e : Expr}
    {vs : List (Val Nat)} (h : sourceValues p P fuel e = some vs) :
    ∃ L, SourceObserves p P e L ∧ values L = vs :=
  observeValues_sound h

/-! ## Constructor terms -/

/-- A constructor term with a head symbol and fields, as a runtime value. -/
def term (c : Nat) (fields : List (Val Nat)) : Val Nat :=
  fields.foldl Val.app (.sym c)

/-- Source argument list from a list. -/
def Args.ofList : List Expr → Args
  | [] => .nil
  | e :: es => .cons e (Args.ofList es)

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
