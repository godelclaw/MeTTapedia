import Mathlib.Logic.Basic

/-!
# Call-by-push-value syntax over the contextual effect signature

Value types and computation types are separate (`VTy`, `CTy`), and so are
value and computation terms (`Val`, `Comp`), as in Levy's call-by-push-value.
Terms are intrinsically typed de Bruijn syntax: a term's index records its
context and type, so renaming and substitution preserve typing by
construction.

The computation formers are those of CBPV (`ret`, `bind` for `M to x. N`,
`force`, `lam`, `app`) together with the effect operations of the existing
contextual programs (`choose`, `read`, `write`, `intent`), pair elimination
`split`, and one kinded no-value operation: `raise kind payload` with the
handler `handle M kind N H` (Benton--Kennedy's `try x ⇐ M in N unless
kind ⇒ H`). Every no-value kind shares one carrier: the payload sort is the
same for all kinds, and the kind is the index.

There is no recursion former here. The calculus is the recursion-free core;
the denotations used with it are finite contextual programs.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV

/-- The ground signature: ground sorts and their data, the sorts carried by
`read`/`write`, `intent` and `raise`, the raise kinds, and pure unary
primitives on ground data. -/
structure Signature where
  Ground : Type
  Data : Ground → Type
  stateSort : Ground
  intentSort : Ground
  payloadSort : Ground
  Kind : Type
  Prim : Ground → Ground → Type
  evalPrim : {source target : Ground} → Prim source target → Data source → Data target

mutual
  /-- Value types. `thunk B` is Levy's `U B`. -/
  inductive VTy (Ground : Type) : Type where
    | ground (sort : Ground)
    | unit
    | prod (first second : VTy Ground)
    | thunk (body : CTy Ground)

  /-- Computation types. `ret A` is Levy's `F A`. -/
  inductive CTy (Ground : Type) : Type where
    | ret (answer : VTy Ground)
    | arrow (domain : VTy Ground) (codomain : CTy Ground)
end

/-- Typed de Bruijn variables. -/
inductive Var {Ground : Type} : List (VTy Ground) → VTy Ground → Type where
  | zero {context : List (VTy Ground)} {type : VTy Ground} : Var (type :: context) type
  | succ {context : List (VTy Ground)} {type other : VTy Ground} :
      Var context type → Var (other :: context) type

mutual
  /-- Values. -/
  inductive Val (sig : Signature) : List (VTy sig.Ground) → VTy sig.Ground → Type where
    | var {context : List (VTy sig.Ground)} {type : VTy sig.Ground}
        (index : Var context type) : Val sig context type
    | const {context : List (VTy sig.Ground)} (sort : sig.Ground) (datum : sig.Data sort) :
        Val sig context (.ground sort)
    | prim {context : List (VTy sig.Ground)} {source target : sig.Ground}
        (operation : sig.Prim source target) (argument : Val sig context (.ground source)) :
        Val sig context (.ground target)
    | unit {context : List (VTy sig.Ground)} : Val sig context .unit
    | pair {context : List (VTy sig.Ground)} {first second : VTy sig.Ground}
        (left : Val sig context first) (right : Val sig context second) :
        Val sig context (.prod first second)
    | thunk {context : List (VTy sig.Ground)} {type : CTy sig.Ground}
        (body : Comp sig context type) : Val sig context (.thunk type)

  /-- Computations. -/
  inductive Comp (sig : Signature) : List (VTy sig.Ground) → CTy sig.Ground → Type where
    | ret {context : List (VTy sig.Ground)} {answer : VTy sig.Ground}
        (value : Val sig context answer) : Comp sig context (.ret answer)
    /-- `bind M N` is `M to x. N`; `x` is variable zero of `N`. -/
    | bind {context : List (VTy sig.Ground)} {answer : VTy sig.Ground} {type : CTy sig.Ground}
        (first : Comp sig context (.ret answer)) (body : Comp sig (answer :: context) type) :
        Comp sig context type
    | force {context : List (VTy sig.Ground)} {type : CTy sig.Ground}
        (suspended : Val sig context (.thunk type)) : Comp sig context type
    | lam {context : List (VTy sig.Ground)} {domain : VTy sig.Ground} {codomain : CTy sig.Ground}
        (body : Comp sig (domain :: context) codomain) :
        Comp sig context (.arrow domain codomain)
    | app {context : List (VTy sig.Ground)} {domain : VTy sig.Ground} {codomain : CTy sig.Ground}
        (function : Comp sig context (.arrow domain codomain)) (argument : Val sig context domain) :
        Comp sig context codomain
    /-- `split V M` binds the second component as variable zero and the first
    as variable one. -/
    | split {context : List (VTy sig.Ground)} {first second : VTy sig.Ground}
        {type : CTy sig.Ground} (pair : Val sig context (.prod first second))
        (body : Comp sig (second :: first :: context) type) : Comp sig context type
    | choose {context : List (VTy sig.Ground)} {type : CTy sig.Ground}
        (left right : Comp sig context type) : Comp sig context type
    /-- `read M` binds the current state as variable zero of `M`. -/
    | read {context : List (VTy sig.Ground)} {type : CTy sig.Ground}
        (body : Comp sig (.ground sig.stateSort :: context) type) : Comp sig context type
    | write {context : List (VTy sig.Ground)} {type : CTy sig.Ground}
        (state : Val sig context (.ground sig.stateSort)) (next : Comp sig context type) :
        Comp sig context type
    | intent {context : List (VTy sig.Ground)} {type : CTy sig.Ground}
        (request : Val sig context (.ground sig.intentSort)) (next : Comp sig context type) :
        Comp sig context type
    | raise {context : List (VTy sig.Ground)} {type : CTy sig.Ground} (kind : sig.Kind)
        (payload : Val sig context (.ground sig.payloadSort)) : Comp sig context type
    /-- `handle M kind N H`: a returned value continues in `N`; a raise of
    `kind` continues in `H` with its payload; other kinds raise again. -/
    | handle {context : List (VTy sig.Ground)} {answer : VTy sig.Ground} {type : CTy sig.Ground}
        (first : Comp sig context (.ret answer)) (kind : sig.Kind)
        (onReturn : Comp sig (answer :: context) type)
        (onRaise : Comp sig (.ground sig.payloadSort :: context) type) : Comp sig context type
end

/-! ## Renaming -/

/-- A renaming of typed variables. -/
abbrev Ren {Ground : Type} (source target : List (VTy Ground)) :=
  (type : VTy Ground) → Var source type → Var target type

namespace Ren

variable {Ground : Type}

/-- Extend a renaming under one binder. -/
def lift {source target : List (VTy Ground)} (ρ : Ren source target) (bound : VTy Ground) :
    Ren (bound :: source) (bound :: target)
  | _, .zero => .zero
  | type, .succ index => .succ (ρ type index)

/-- Weaken by one new outermost-bound variable. -/
def weaken {context : List (VTy Ground)} (bound : VTy Ground) : Ren context (bound :: context) :=
  fun _ index => .succ index

end Ren

variable {sig : Signature}

mutual
  def Val.rename {source target : List (VTy sig.Ground)} (ρ : Ren source target) :
      {type : VTy sig.Ground} → Val sig source type → Val sig target type
    | _, .var index => .var (ρ _ index)
    | _, .const sort datum => .const sort datum
    | _, .prim operation argument => .prim operation (Val.rename ρ argument)
    | _, .unit => .unit
    | _, .pair left right => .pair (Val.rename ρ left) (Val.rename ρ right)
    | _, .thunk body => .thunk (Comp.rename ρ body)

  def Comp.rename {source target : List (VTy sig.Ground)} (ρ : Ren source target) :
      {type : CTy sig.Ground} → Comp sig source type → Comp sig target type
    | _, .ret value => .ret (Val.rename ρ value)
    | _, .bind first body => .bind (Comp.rename ρ first) (Comp.rename (ρ.lift _) body)
    | _, .force suspended => .force (Val.rename ρ suspended)
    | _, .lam body => .lam (Comp.rename (ρ.lift _) body)
    | _, .app function argument => .app (Comp.rename ρ function) (Val.rename ρ argument)
    | _, .split pair body => .split (Val.rename ρ pair) (Comp.rename ((ρ.lift _).lift _) body)
    | _, .choose left right => .choose (Comp.rename ρ left) (Comp.rename ρ right)
    | _, .read body => .read (Comp.rename (ρ.lift _) body)
    | _, .write state next => .write (Val.rename ρ state) (Comp.rename ρ next)
    | _, .intent request next => .intent (Val.rename ρ request) (Comp.rename ρ next)
    | _, .raise kind payload => .raise kind (Val.rename ρ payload)
    | _, .handle first kind onReturn onRaise =>
        .handle (Comp.rename ρ first) kind (Comp.rename (ρ.lift _) onReturn)
          (Comp.rename (ρ.lift _) onRaise)
end

/-! ## Substitution -/

/-- A simultaneous substitution of values for typed variables. -/
abbrev Subst (sig : Signature) (source target : List (VTy sig.Ground)) :=
  (type : VTy sig.Ground) → Var source type → Val sig target type

namespace Subst

/-- Extend a substitution under one binder. -/
def lift {source target : List (VTy sig.Ground)} (σ : Subst sig source target)
    (bound : VTy sig.Ground) : Subst sig (bound :: source) (bound :: target)
  | _, .zero => .var .zero
  | type, .succ index => Val.rename (Ren.weaken bound) (σ type index)

/-- Replace variable zero by a value and lower the others. -/
def single {context : List (VTy sig.Ground)} {bound : VTy sig.Ground}
    (value : Val sig context bound) : Subst sig (bound :: context) context
  | _, .zero => value
  | _, .succ index => .var index

/-- Replace the two newest variables of a `split` body: variable zero by the
second component and variable one by the first. -/
def double {context : List (VTy sig.Ground)} {first second : VTy sig.Ground}
    (left : Val sig context first) (right : Val sig context second) :
    Subst sig (second :: first :: context) context
  | _, .zero => right
  | _, .succ .zero => left
  | _, .succ (.succ index) => .var index

end Subst

mutual
  def Val.subst {source target : List (VTy sig.Ground)} (σ : Subst sig source target) :
      {type : VTy sig.Ground} → Val sig source type → Val sig target type
    | _, .var index => σ _ index
    | _, .const sort datum => .const sort datum
    | _, .prim operation argument => .prim operation (Val.subst σ argument)
    | _, .unit => .unit
    | _, .pair left right => .pair (Val.subst σ left) (Val.subst σ right)
    | _, .thunk body => .thunk (Comp.subst σ body)

  def Comp.subst {source target : List (VTy sig.Ground)} (σ : Subst sig source target) :
      {type : CTy sig.Ground} → Comp sig source type → Comp sig target type
    | _, .ret value => .ret (Val.subst σ value)
    | _, .bind first body => .bind (Comp.subst σ first) (Comp.subst (σ.lift _) body)
    | _, .force suspended => .force (Val.subst σ suspended)
    | _, .lam body => .lam (Comp.subst (σ.lift _) body)
    | _, .app function argument => .app (Comp.subst σ function) (Val.subst σ argument)
    | _, .split pair body => .split (Val.subst σ pair) (Comp.subst ((σ.lift _).lift _) body)
    | _, .choose left right => .choose (Comp.subst σ left) (Comp.subst σ right)
    | _, .read body => .read (Comp.subst (σ.lift _) body)
    | _, .write state next => .write (Val.subst σ state) (Comp.subst σ next)
    | _, .intent request next => .intent (Val.subst σ request) (Comp.subst σ next)
    | _, .raise kind payload => .raise kind (Val.subst σ payload)
    | _, .handle first kind onReturn onRaise =>
        .handle (Comp.subst σ first) kind (Comp.subst (σ.lift _) onReturn)
          (Comp.subst (σ.lift _) onRaise)
end

/-- Open the newest binder of a computation with a value. -/
abbrev Comp.instantiate {context : List (VTy sig.Ground)} {bound : VTy sig.Ground}
    {type : CTy sig.Ground} (body : Comp sig (bound :: context) type)
    (value : Val sig context bound) : Comp sig context type :=
  body.subst (Subst.single value)

/-- Weaken a computation under one new binder placed just outside its own
newest binder (used when an operation's binder moves outward). -/
abbrev Comp.weakenUnder {context : List (VTy sig.Ground)} {bound inner : VTy sig.Ground}
    {type : CTy sig.Ground} (body : Comp sig (inner :: context) type) :
    Comp sig (inner :: bound :: context) type :=
  body.rename ((Ren.weaken bound).lift inner)

end Mettapedia.TypeTheory.ContextualCBPV
