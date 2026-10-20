import Mettapedia.GSLT.LanguageDef.MacroExportPlan
import Mettapedia.Languages.C11.IntegerConversion

/-!
# What a macro use does, and what its readable export does

A use of a typed macro evaluates each evaluated argument once, in declared
order, threading the caller's state from one argument to the next; a value
argument yields its value and a place argument yields the location it
designates, captured once. The template then runs with those values and
locations in place of its arguments. `invoke` states this source contract
directly.

The readable export is a block of C. `run` executes such a block with an
ordinary interpreter for the admitted C fragment: declarations, loads,
stores, the integer and pointer operations the libraries use, the overflow
builtins and calls of caller-supplied functions. The interpreter knows
nothing about macros.

`MacroExportTheorem.export_correct` proves that running the lowered block of
any admitted rule, from the same state, yields exactly the source use's
outcome: the same value or fault, the same caller-visible memory, the same
ordered trace of external events, the same consumption of external replies,
and the same private frame.

Modelling choices. Caller code inside arguments is an abstract action on the
caller-visible state: memory, trace and external replies. It cannot reach the
macro's private frame, whose names it cannot write and whose addresses it
never receives. The acquisition locals of an export are never assigned and
their addresses are never taken, so they are values, not objects; the
template's own declared locals are objects in the private frame, at the same
locations in both runs. `&*E` is `E` without evaluating either operator
(C11 6.5.3.2p3), and an argument written `*X` is acquired as `X`, the
address of the place it designates (6.5.3.2p4). An external call consumes the
next reply of the world, a returned value with an effect on caller memory, so
statements quantify over every reply sequence rather than choosing allocator
behavior. The overflow builtins compute at unbounded precision and store the
result converted to the destination's format by the documented two's
complement reduction.

Operands of unsequenced operators are evaluated left to right here.
`MacroExportOrder` states when that choice is unobservable, and every recorded
export is checked against it.
-/

namespace Mettapedia.GSLT.LanguageDef.MacroExportStateful

open Mettapedia.GSLT.LanguageDef.MacroExportPlan
open Mettapedia.Languages.C11

set_option autoImplicit false

/-! ## Values and state -/

inductive Ty where
  | integer (format : IntegerFormat)
  | pointer (target : Ty)
  | function
  deriving DecidableEq, Repr

inductive Region where
  | heap | frame
  deriving DecidableEq, Repr

structure Loc where
  region : Region
  object : Nat
  index : Int
  deriving DecidableEq, Repr

inductive Val where
  | void
  | int (format : IntegerFormat) (value : Int)
  | ptr (target : Loc)
  | null
  | fn (name : String)
  deriving DecidableEq, Repr

structure Cell where
  type : Ty
  value : Option Val
  deriving DecidableEq, Repr

abbrev Memory := Loc → Option Cell

inductive Event where
  | call (callee : String) (arguments : List Val)
  | caller (tag : Nat)
  deriving DecidableEq, Repr

/-- The world's reply to one external call. -/
structure Reply where
  value : Val
  effect : Memory → Memory

/-- What caller code can see and change. -/
structure Public where
  heap : Memory
  trace : List Event
  replies : List Reply

structure State where
  pub : Public
  frame : Memory
  next : Nat

inductive Fault where
  /-- A C undefined behavior of the fragment. -/
  | undefined (reason : String)
  /-- A construct outside the admitted fragment. -/
  | outside (construct : String)
  /-- Caller code faulted. -/
  | caller (reason : String)
  /-- No reply remains for an external call. -/
  | exhausted
  deriving DecidableEq, Repr

abbrev Out (α : Type) := Except Fault α

/-- The selected implementation: formats, the C types of its ABI and their
sizes. These are boundary assumptions about GCC/Clang's target. -/
structure Profile where
  int : IntegerFormat
  unsignedInt : IntegerFormat
  size : IntegerFormat
  types : Atom → Option Ty
  sizeOf : Ty → Option Nat
  signedPolicy : SignedConversionPolicy

/-- Caller code written as an argument. -/
structure Operand where
  value : Public → Out (Val × Public)
  place : Public → Out (Loc × Public)

inductive Param where
  | value (v : Val)
  | place (l : Loc)
  | syntax
  deriving DecidableEq, Repr

structure Ctx where
  profile : Profile
  written : List Atom
  operands : Nat → Operand
  params : Nat → Option Param

inductive Binding where
  | value (v : Val)
  | object (l : Loc)
  deriving DecidableEq, Repr

abbrev Env := List (String × Binding)

/-! ## Memory -/

def State.read (st : State) (l : Loc) : Option Cell :=
  match l.region with
  | .heap => st.pub.heap l
  | .frame => st.frame l

def update (m : Memory) (l : Loc) (c : Cell) : Memory := fun k => if k = l then some c else m k

def State.write (st : State) (l : Loc) (c : Cell) : State :=
  match l.region with
  | .heap => { st with pub := { st.pub with heap := update st.pub.heap l c } }
  | .frame => { st with frame := update st.frame l c }

def State.withPub (st : State) (p : Public) : State := { st with pub := p }

def load (st : State) (l : Loc) : Out Val :=
  match st.read l with
  | some { value := some v, .. } => .ok v
  | some { value := none, .. } => .error (.undefined "indeterminate read")
  | none => .error (.undefined "access outside a live object")

/-- Assignment conversion to an object's type. -/
def convert (profile : Profile) (t : Ty) (v : Val) : Out Val :=
  match t, v with
  | .integer f, .int _ n =>
      match convertInteger profile.signedPolicy n (.integer f) with
      | .value m => .ok (.int f m)
      | .signal _ => .error (.undefined "conversion signal")
  | .pointer _, .ptr l => .ok (.ptr l)
  | .pointer _, .null => .ok .null
  | .function, .fn s => .ok (.fn s)
  | _, _ => .error (.outside "assignment between these types")

def store (profile : Profile) (st : State) (l : Loc) (v : Val) : Out (Val × State) :=
  match st.read l with
  | some c => do
      let w ← convert profile c.type v
      pure (w, st.write l { c with value := some w })
  | none => .error (.undefined "store outside a live object")

/-! ## Constants, truth and arithmetic -/

def digits : List Char → Option Nat
  | [] => none
  | cs => cs.foldl (fun acc c => do
      let a ← acc
      if c.isDigit then some (a * 10 + (c.toNat - 48)) else none) (some 0)

/-- An integer constant as spelled: decimal digits with an optional `u`. -/
def constant (profile : Profile) (s : String) : Option Val :=
  match s.toList.reverse with
  | 'u' :: rest | 'U' :: rest => (digits rest.reverse).map fun n => .int profile.unsignedInt n
  | _ => (digits s.toList).map fun n => .int profile.int n

def truth : Val → Out Bool
  | .int _ n => .ok (n ≠ 0)
  | .ptr _ => .ok true
  | .null => .ok false
  | _ => .error (.outside "truth of this value")

def boolean (profile : Profile) (b : Bool) : Val := .int profile.int (if b then 1 else 0)

/-- Operands of one integer format, or a nonnegative constant of `int` with an
operand whose format represents it. Other mixes are outside the fragment. -/
def common (profile : Profile) : Val → Val → Out (IntegerFormat × Int × Int)
  | .int f a, .int g b =>
      if f = g then .ok (f, a, b)
      else if g = profile.int ∧ 0 ≤ b ∧ f.Represents b then .ok (f, a, b)
      else if f = profile.int ∧ 0 ≤ a ∧ g.Represents a then .ok (g, a, b)
      else .error (.outside "mixed integer formats")
  | _, _ => .error (.outside "arithmetic on these values")

/-- The arithmetic result in a format: unsigned wraps, signed overflow is
undefined. -/
def arith (f : IntegerFormat) (n : Int) : Out Val :=
  match f with
  | .unsigned precision _ => .ok (.int f (n % powerOfTwo precision))
  | .signed _ _ _ => if f.Represents n then .ok (.int f n) else .error (.undefined "signed overflow")

def compare (profile : Profile) (op : String) (a b : Val) : Out Val :=
  match op, a, b with
  | "==", .ptr x, .ptr y => .ok (boolean profile (x = y))
  | "==", .null, .null => .ok (boolean profile true)
  | "==", .ptr _, .null | "==", .null, .ptr _ => .ok (boolean profile false)
  | _, _, _ => do
      let (_, x, y) ← common profile a b
      match op with
      | "==" => pure (boolean profile (x = y))
      | ">" => pure (boolean profile (x > y))
      | "<" => pure (boolean profile (x < y))
      | _ => .error (.outside op)

/-- `__builtin_add_overflow` and `__builtin_mul_overflow`: the exact result,
stored reduced to the destination's format; the value is 1 when that format
cannot represent it. -/
def overflowBuiltin (profile : Profile) (st : State) (op : Int → Int → Int) :
    List Val → Out (Val × State)
  | [.int _ a, .int _ b, .ptr l] =>
      match st.read l with
      | some { type := .integer f, .. } =>
          let exact := op a b
          match convertInteger intervalReductionPolicy exact (.integer f) with
          | .value m =>
              .ok (boolean profile (!decide (f.Represents exact)),
                st.write l { type := .integer f, value := some (.int f m) })
          | .signal _ => .error (.undefined "builtin reduction")
      | _ => .error (.undefined "builtin destination")
  | _ => .error (.outside "builtin arguments")

/-- An external call: the next reply of the world. -/
def external (st : State) (callee : String) (args : List Val) : Out (Val × State) :=
  match st.pub.replies with
  | r :: rest => .ok (r.value, st.withPub
      { heap := r.effect st.pub.heap, trace := st.pub.trace ++ [.call callee args], replies := rest })
  | [] => .error .exhausted

mutual
  /-- A type as written, with arguments filled. -/
  def typeAtom (ctx : Ctx) : Marked → Option Atom
    | .symbol s => some (.symbol s)
    | .text s => some (.text s)
    | .operand i => ctx.written[i]?
    | .arg i => ctx.written[i]?
    | .list items => (typeAtomMany ctx items).map .list
    | _ => none
  def typeAtomMany (ctx : Ctx) : List Marked → Option (List Atom)
    | [] => some []
    | m :: rest => do
        let a ← typeAtom ctx m
        let as ← typeAtomMany ctx rest
        pure (a :: as)
end

def typeOf (ctx : Ctx) (m : Marked) : Out Ty :=
  match (typeAtom ctx m).bind ctx.profile.types with
  | some t => .ok t
  | none => .error (.outside "type")

def lookup (env : Env) (n : String) : Out Binding :=
  match env.lookup n with
  | some b => .ok b
  | none => .error (.outside "unbound name")

/-- Caller code, run on the caller-visible part of the state. -/
def callerValue (ctx : Ctx) (i : Nat) (st : State) : Out (Val × State) :=
  match (ctx.operands i).value st.pub with
  | .ok (v, p) => .ok (v, st.withPub p)
  | .error e => .error e

def callerPlace (ctx : Ctx) (i : Nat) (st : State) : Out (Loc × State) :=
  match (ctx.operands i).place st.pub with
  | .ok (l, p) => .ok (l, st.withPub p)
  | .error e => .error e

/-- Release the private objects created from `start` on. -/
def release (start : Nat) (st : State) : State :=
  { st with frame := fun l => if start ≤ l.object then none else st.frame l }

/-! ## The interpreter -/

mutual
  /-- The value of an expression. -/
  def value (ctx : Ctx) (env : Env) : Marked → State → Out (Val × State)
    | .symbol s, st => match constant ctx.profile s with
      | some v => .ok (v, st)
      | none => .error (.outside "symbol")
    | .name n, st => do
        match ← lookup env n with
        | .value v => pure (v, st)
        | .object l => pure (← load st l, st)
    | .arg i, st => match ctx.params i with
      | some (.value v) => .ok (v, st)
      | some (.place l) => do pure (← load st l, st)
      | some .syntax => callerValue ctx i st
      | none => .error (.outside "argument")
    | .operand i, st => callerValue ctx i st
    | .inner i, st => do
        let (l, st) ← callerPlace ctx i st
        pure (.ptr l, st)
    | .list [.symbol "&", .list [.symbol "*", x]], st => value ctx env x st
    | .list [.symbol "&", x], st => do
        let (l, st) ← place ctx env x st
        pure (.ptr l, st)
    | .list [.symbol "*", x], st => do
        let (l, st) ← place ctx env (.list [.symbol "*", x]) st
        pure (← load st l, st)
    | .list [.symbol "[]", a, b], st => do
        let (l, st) ← place ctx env (.list [.symbol "[]", a, b]) st
        pure (← load st l, st)
    | .list [.symbol "!", x], st => do
        let (v, st) ← value ctx env x st
        pure (boolean ctx.profile !(← truth v), st)
    | .list [.symbol "-", x], st => do
        let (v, st) ← value ctx env x st
        match v with
        | .int f n => pure (← arith f (-n), st)
        | _ => .error (.outside "negation")
    | .list [.symbol "+", a, b], st => do
        let (x, st) ← value ctx env a st
        let (y, st) ← value ctx env b st
        let (f, m, n) ← common ctx.profile x y
        pure (← arith f (m + n), st)
    | .list [.symbol "==", a, b], st => do
        let (x, st) ← value ctx env a st
        let (y, st) ← value ctx env b st
        pure (← compare ctx.profile "==" x y, st)
    | .list [.symbol ">", a, b], st => do
        let (x, st) ← value ctx env a st
        let (y, st) ← value ctx env b st
        pure (← compare ctx.profile ">" x y, st)
    | .list [.symbol "&&", a, b], st => do
        let (x, st) ← value ctx env a st
        if ← truth x then
          let (y, st) ← value ctx env b st
          pure (boolean ctx.profile (← truth y), st)
        else pure (boolean ctx.profile false, st)
    | .list [.symbol "||", a, b], st => do
        let (x, st) ← value ctx env a st
        if ← truth x then pure (boolean ctx.profile true, st)
        else
          let (y, st) ← value ctx env b st
          pure (boolean ctx.profile (← truth y), st)
    | .list [.symbol "?:", c, a, b], st => do
        let (x, st) ← value ctx env c st
        if ← truth x then value ctx env a st else value ctx env b st
    | .list [.symbol ",", a, b], st => do
        let (_, st) ← value ctx env a st
        value ctx env b st
    | .list [.symbol "cast", .symbol "void", x], st => do
        let (_, st) ← value ctx env x st
        pure (.void, st)
    | .list [.symbol "sizeof", .symbol "type", t], st => do
        match ctx.profile.sizeOf (← typeOf ctx t) with
        | some n => pure (.int ctx.profile.size n, st)
        | none => .error (.outside "size")
    | .list [.symbol "=", l, r], st => do
        let (loc, st) ← place ctx env l st
        let (v, st) ← value ctx env r st
        store ctx.profile st loc v
    | .list [.symbol "+=", l, r], st => do
        let (loc, st) ← place ctx env l st
        let (v, st) ← value ctx env r st
        let (f, m, n) ← common ctx.profile (← load st loc) v
        store ctx.profile st loc (← arith f (m + n))
    | .list [.symbol "++", l], st => do
        let (loc, st) ← place ctx env l st
        let (f, m, n) ← common ctx.profile (← load st loc) (.int ctx.profile.int 1)
        store ctx.profile st loc (← arith f (m + n))
    | .list (.symbol "call" :: .symbol "__builtin_add_overflow" :: args), st => do
        let (vs, st) ← values ctx env args st
        overflowBuiltin ctx.profile st (· + ·) vs
    | .list (.symbol "call" :: .symbol "__builtin_mul_overflow" :: args), st => do
        let (vs, st) ← values ctx env args st
        overflowBuiltin ctx.profile st (· * ·) vs
    | .list (.symbol "call" :: callee :: args), st => do
        let (f, st) ← value ctx env callee st
        let (vs, st) ← values ctx env args st
        match f with
        | .fn name => external st name vs
        | _ => .error (.undefined "call of a non-function")
    | .list (.symbol "block" :: items), st => do
        let (_, v, st') ← statements ctx env items st
        pure (v, release st.next st')
    | _, _ => .error (.outside "expression")

  /-- The location an lvalue designates. -/
  def place (ctx : Ctx) (env : Env) : Marked → State → Out (Loc × State)
    | .name n, st => do
        match ← lookup env n with
        | .object l => pure (l, st)
        | .value _ => .error (.outside "assignment to an acquired value")
    | .arg i, st => match ctx.params i with
      | some (.place l) => .ok (l, st)
      | some .syntax => callerPlace ctx i st
      | some (.value _) => .error (.outside "assignment to an acquired value")
      | none => .error (.outside "argument as a place")
    | .operand i, st => callerPlace ctx i st
    | .list [.symbol "*", x], st => do
        let (p, st) ← value ctx env x st
        match p with
        | .ptr l => pure (l, st)
        | _ => .error (.undefined "indirection through a non-pointer")
    | .list [.symbol "[]", a, b], st => do
        let (p, st) ← value ctx env a st
        let (i, st) ← value ctx env b st
        match p, i with
        | .ptr l, .int _ n => pure ({ l with index := l.index + n }, st)
        | _, _ => .error (.undefined "subscript")
    | _, _ => .error (.outside "place")

  /-- Argument values, left to right. -/
  def values (ctx : Ctx) (env : Env) : List Marked → State → Out (List Val × State)
    | [], st => .ok ([], st)
    | a :: rest, st => do
        let (v, st) ← value ctx env a st
        let (vs, st) ← values ctx env rest st
        pure (v :: vs, st)

  /-- One block item: the environment after it, its value and the state. -/
  def statement (ctx : Ctx) (env : Env) : Marked → State → Out (Env × Val × State)
    | .list (.symbol "_Static_assert" :: _), st => .ok (env, .void, st)
    | .list (.symbol "typedef" :: _), st => .ok (env, .void, st)
    | .list [.symbol "var", .symbol "__auto_type", .name n, init], st => do
        let (v, st) ← value ctx env init st
        pure ((n, .value v) :: env, .void, st)
    | .list [.symbol "var", t, .name n], st => do
        let ty ← typeOf ctx t
        let l : Loc := { region := .frame, object := st.next, index := 0 }
        pure ((n, .object l) :: env, .void,
          { st with frame := update st.frame l { type := ty, value := none }, next := st.next + 1 })
    | .list [.symbol "var", t, .list [.symbol "*", .name n]], st => do
        let ty ← typeOf ctx t
        let l : Loc := { region := .frame, object := st.next, index := 0 }
        pure ((n, .object l) :: env, .void,
          { st with frame := update st.frame l { type := .pointer ty, value := none }, next := st.next + 1 })
    | .list [.symbol "var", t, .name n, init], st => do
        let ty ← typeOf ctx t
        let (v, st) ← value ctx env init st
        let l : Loc := { region := .frame, object := st.next, index := 0 }
        let w ← convert ctx.profile ty v
        pure ((n, .object l) :: env, .void,
          { st with frame := update st.frame l { type := ty, value := some w }, next := st.next + 1 })
    | .list [.symbol "if", c, a], st => do
        let (x, st) ← value ctx env c st
        if ← truth x then do
          let (_, _, st) ← statement ctx env a st
          pure (env, .void, st)
        else pure (env, .void, st)
    | .list [.symbol "if", c, a, b], st => do
        let (x, st) ← value ctx env c st
        let (_, _, st) ← if ← truth x then statement ctx env a st else statement ctx env b st
        pure (env, .void, st)
    | .list (.symbol "block" :: items), st => do
        let (_, v, st') ← statements ctx env items st
        pure (env, v, release st.next st')
    | e, st => do
        let (v, st) ← value ctx env e st
        pure (env, v, st)

  /-- Block items in order; the value is the last item's. -/
  def statements (ctx : Ctx) (env : Env) : List Marked → State → Out (Env × Val × State)
    | [], st => .ok (env, .void, st)
    | [item], st => statement ctx env item st
    | item :: rest, st => do
        let (env, _, st) ← statement ctx env item st
        statements ctx env rest st
end

/-! ## The source use and the exported block -/

/-- Evaluated arguments once each, in declared order, from the caller's state;
syntax arguments stay unevaluated. -/
def acquireArguments (profile : Profile) (written : List Atom) (operands : Nat → Operand) :
    List (Nat × Argument) → (Nat → Option Param) → State → Out ((Nat → Option Param) × State)
  | [], params, st => .ok (params, st)
  | (i, a) :: rest, params, st =>
      let ctx : Ctx := { profile, written, operands, params }
      let bind := fun (p : Param) (k : Nat) => if k = i then some p else params k
      match a.category with
      | .syntax => acquireArguments profile written operands rest (bind .syntax) st
      | .value => match callerValue ctx i st with
        | .ok (v, st) => acquireArguments profile written operands rest (bind (.value v)) st
        | .error e => .error e
      | .addressable | .modifiable => match callerPlace ctx i st with
        | .ok (l, st) => acquireArguments profile written operands rest (bind (.place l)) st
        | .error e => .error e

def slotsOf (rule : Rule) : List (Nat × Argument) :=
  List.zip (List.range rule.arguments.length) rule.arguments

/-- A use of `rule`: arguments acquired once in declared order, then the
template with its locals named `locals`. The template's private objects end
with the use. -/
def invoke (profile : Profile) (written : List Atom) (operands : Nat → Operand) (rule : Rule)
    (locals : List String) (st : State) : Out (Val × State) :=
  match acquireArguments profile written operands (slotsOf rule) (fun _ => none) st with
  | .error e => .error e
  | .ok (params, st') =>
      let ctx : Ctx := { profile, written, operands, params }
      let body := instantiate (fun i => .arg i) (fun j => locals.getD j "") rule.body
      let run := if rule.expression then value ctx [] body st'
        else (statement ctx [] body st').map fun (_, _, st) => (.void, st)
      run.map fun (v, s) => (v, release st.next s)

/-- The exported block, run as C. -/
def runBlock (profile : Profile) (written : List Atom) (operands : Nat → Operand) (expression : Bool)
    (block : Marked) (st : State) : Out (Val × State) :=
  let ctx : Ctx := { profile, written, operands, params := fun _ => none }
  if expression then value ctx [] block st
  else (statement ctx [] block st).map fun (_, _, st) => (.void, st)

end Mettapedia.GSLT.LanguageDef.MacroExportStateful
