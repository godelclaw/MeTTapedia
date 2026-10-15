import Mathlib.Logic.Equiv.Defs
import PolyFun.IPFunctor.Free.Family
import Mettapedia.OSLF.Syntax.BindingSignature
import Mettapedia.OSLF.Syntax.ScopedBindingSortedSignature
import Mettapedia.GSLT.Poly.SortedSignature

/-!
# Binding terms as the free monad of a context-indexed polynomial

A binding signature determines an indexed polynomial over pairs of a context
and a sort. The head at a pair is an operator of that sort. Each direction is
an argument position, and it lands in the context extended by the sorts that
argument binds.

Variables are the leaves of the free monad, not extra heads. The scoped
constructor encoding reads the same variables as nullary heads. The two
readings agree through the closed-term equivalence of that encoding.

`IFreeM.bind` substitutes leaves and keeps the root index. A substitution
that moves the root into another context is transported from the binding
algebra instead.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.BindingSignature

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ScopedEncoding
open IPFunctor

variable {S : Signature}

/-- Variables of a binding signature, indexed by the context and the sort. -/
abbrev Vars (S : Signature) : Ctx S × S.Srt → Type :=
  fun index => Var index.1 index.2

/-- The context-indexed polynomial of a binding signature. -/
abbrev polynomial (S : Signature) : IPFunctor.Endo (Ctx S × S.Srt) where
  A index := S.Op index.2
  B _ operator := Fin (S.arity operator).length
  src index operator direction :=
    let declaration := (S.arity operator).get direction
    (declaration.1 ++ index.1, declaration.2)

theorem polynomial_head (Γ : Ctx S) (s : S.Srt) :
    (polynomial S).A (Γ, s) = S.Op s :=
  rfl

theorem polynomial_direction (Γ : Ctx S) {s : S.Srt} (operator : S.Op s)
    (direction : Fin (S.arity operator).length) :
    (polynomial S).src (Γ, s) operator direction =
      (((S.arity operator).get direction).1 ++ Γ,
        ((S.arity operator).get direction).2) :=
  rfl

mutual

/-- A binding term as a free-monad tree. Operators are heads and variables
are leaves. -/
def toFree : {Γ : Ctx S} → {s : S.Srt} → Term S Γ s →
    IFreeM (polynomial S) (Vars S) (Γ, s)
  | _, _, .var variable_ => .pure variable_
  | _, _, .op operator arguments => .liftBind operator (toFreeAt arguments)

/-- Argument positions of one operator, each a tree in the context that
position binds. -/
def toFreeAt : {as : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Args S as Γ → (direction : Fin as.length) →
      IFreeM (polynomial S) (Vars S)
        ((as.get direction).1 ++ Γ, (as.get direction).2)
  | _, _, .nil, direction => Fin.elim0 direction
  | _, _, .cons head _tail, ⟨0, _⟩ => toFree head
  | _, _, .cons _head tail, ⟨n + 1, proof⟩ =>
      toFreeAt tail ⟨n, Nat.lt_of_succ_lt_succ proof⟩

end

theorem toFree_var {Γ : Ctx S} {s : S.Srt} (variable_ : Var Γ s) :
    toFree (.var variable_) = .pure variable_ := rfl

theorem toFree_op {Γ : Ctx S} {s : S.Srt} (operator : S.Op s)
    (arguments : Args S (S.arity operator) Γ) :
    toFree (.op operator arguments) = .liftBind operator (toFreeAt arguments) := rfl

theorem toFreeAt_zero {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt}
    {tailDecls : List (List S.Srt × S.Srt)}
    (head : Term S (bs ++ Γ) s) (tail : Args S tailDecls Γ) :
    toFreeAt (.cons head tail) 0 = toFree head := rfl

theorem toFreeAt_succ {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt}
    {tailDecls : List (List S.Srt × S.Srt)}
    (head : Term S (bs ++ Γ) s) (tail : Args S tailDecls Γ)
    (position : Fin tailDecls.length) :
    toFreeAt (.cons head tail) position.succ = toFreeAt tail position := rfl

private theorem finHead {α : Type} {head : α} {tail : List α}
    (proof : 0 < (head :: tail).length) :
    (⟨0, proof⟩ : Fin (head :: tail).length) = 0 :=
  Fin.ext rfl

private theorem finTail {α : Type} {head : α} {tail : List α} {n : Nat}
    (proof : n + 1 < (head :: tail).length) :
    (⟨n + 1, proof⟩ : Fin (head :: tail).length) =
      (⟨n, Nat.lt_of_succ_lt_succ proof⟩ : Fin tail.length).succ :=
  Fin.ext rfl

/-- A free-monad tree as a binding term. -/
def ofFree : {index : Ctx S × S.Srt} →
    IFreeM (polynomial S) (Vars S) index → Term S index.1 index.2
  | _, .pure variable_ => .var variable_
  | (Γ, _), .liftBind operator continuation =>
      .op operator (assembleArguments Γ (S.arity operator)
        fun direction => ofFree (continuation direction))

theorem ofFree_pure {index : Ctx S × S.Srt} (variable_ : Vars S index) :
    ofFree (.pure variable_) = .var variable_ := rfl

theorem ofFree_liftBind {Γ : Ctx S} {s : S.Srt} (operator : S.Op s)
    (continuation : (direction : Fin (S.arity operator).length) →
      IFreeM (polynomial S) (Vars S)
        ((polynomial S).src (Γ, s) operator direction)) :
    ofFree (IFreeM.liftBind (P := polynomial S) (s := (Γ, s)) operator continuation) =
      .op operator (assembleArguments Γ (S.arity operator)
        fun direction => ofFree (continuation direction)) := rfl

private theorem assemble_toFreeAt_cons {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt}
    {tailDecls : List (List S.Srt × S.Srt)}
    (head : Term S (bs ++ Γ) s) (tail : Args S tailDecls Γ) :
    assembleArguments Γ ((bs, s) :: tailDecls)
        (fun direction => ofFree (toFreeAt (Args.cons head tail) direction)) =
      .cons (ofFree (toFree head))
        (assembleArguments Γ tailDecls
          fun position => ofFree (toFreeAt tail position)) := by
  simp only [assembleArguments, toFreeAt_zero, toFreeAt_succ]
  rfl

mutual

theorem ofFree_toFree : ∀ {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s),
    ofFree (toFree term) = term
  | _, _, .var variable_ => by
      simp only [toFree_var, ofFree_pure]
  | _, _, .op operator arguments => by
      rw [toFree_op, ofFree_liftBind, ofFree_toFreeAt arguments]

theorem ofFree_toFreeAt : ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (arguments : Args S as Γ),
    assembleArguments Γ as (fun direction => ofFree (toFreeAt arguments direction)) =
      arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      rw [assemble_toFreeAt_cons head tail, ofFree_toFree head, ofFree_toFreeAt tail]

end

private theorem toFreeAt_assemble (Γ : Ctx S) :
    ∀ (as : List (List S.Srt × S.Srt))
      (continuation : (direction : Fin as.length) →
        IFreeM (polynomial S) (Vars S)
          ((as.get direction).1 ++ Γ, (as.get direction).2)),
      (∀ direction, toFree (ofFree (continuation direction)) = continuation direction) →
        toFreeAt (assembleArguments Γ as (fun direction => ofFree (continuation direction))) =
          continuation
  | [], _, _ => by
      funext direction
      exact Fin.elim0 direction
  | headDecl :: tail, continuation, closed => by
      funext direction
      refine Fin.cases ?zero ?succ direction
      · exact
          (show toFreeAt
              (assembleArguments Γ (headDecl :: tail)
                (fun direction => ofFree (continuation direction))) 0 =
            toFree (ofFree (continuation 0)) from rfl).trans (closed 0)
      · intro previous
        exact
          (show toFreeAt
              (assembleArguments Γ (headDecl :: tail)
                (fun direction => ofFree (continuation direction))) previous.succ =
            toFreeAt
              (assembleArguments Γ tail
                (fun position => ofFree (continuation position.succ))) previous from rfl).trans
          (congrFun
            (toFreeAt_assemble Γ tail (fun position => continuation position.succ)
              fun position => closed position.succ) previous)

theorem toFree_ofFree {index : Ctx S × S.Srt}
    (tree : IFreeM (polynomial S) (Vars S) index) :
    toFree (ofFree tree) = tree := by
  induction tree using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind index operator continuation closed =>
      cases index with
      | mk Γ _ =>
          rw [ofFree_liftBind, toFree_op]
          exact congrArg (IFreeM.liftBind operator)
            (toFreeAt_assemble Γ (S.arity operator) continuation closed)

/-- Binding terms are the free monad of the context-indexed polynomial, with
variables as leaves. -/
def termEquiv (S : Signature) (Γ : Ctx S) (s : S.Srt) :
    Term S Γ s ≃ IFreeM (polynomial S) (Vars S) (Γ, s) where
  toFun := toFree
  invFun := ofFree
  left_inv := ofFree_toFree
  right_inv := toFree_ofFree

mutual

/-- A binding term as a closed constructor term of the scoped encoding.
Variables are nullary heads there. -/
def toScoped {Γ : Ctx S} {s : S.Srt} :
    Term S Γ s → Mettapedia.OSLF.SortedConstructors.Term
      (Mettapedia.OSLF.Binding.ScopedEncoding.signature S) (Γ, s)
  | .var variable_ =>
      @Mettapedia.OSLF.SortedConstructors.Term.node (signature S)
        (Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.variable Γ s variable_)
        (fun direction => Fin.elim0 direction)
  | .op operator arguments =>
      @Mettapedia.OSLF.SortedConstructors.Term.node (signature S)
        (Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.operation Γ s operator)
        (toScopedAt arguments)

/-- Argument positions of one operator, as scoped constructor terms. -/
def toScopedAt {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} :
    Args S as Γ → (direction : Fin as.length) →
      Mettapedia.OSLF.SortedConstructors.Term (signature S)
        ((as.get direction).1 ++ Γ, (as.get direction).2)
  | .nil, direction => Fin.elim0 direction
  | .cons head _tail, ⟨0, _⟩ => toScoped head
  | .cons _head tail, ⟨n + 1, proof⟩ =>
      toScopedAt tail ⟨n, Nat.lt_of_succ_lt_succ proof⟩

end

theorem toScoped_var {Γ : Ctx S} {s : S.Srt} (variable_ : Var Γ s) :
    toScoped (.var variable_) =
      @Mettapedia.OSLF.SortedConstructors.Term.node (signature S)
        (Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.variable Γ s variable_)
        (fun direction => Fin.elim0 direction) := rfl

theorem toScoped_op {Γ : Ctx S} {s : S.Srt} (operator : S.Op s)
    (arguments : Args S (S.arity operator) Γ) :
    toScoped (.op operator arguments) =
      @Mettapedia.OSLF.SortedConstructors.Term.node (signature S)
        (Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.operation Γ s operator)
        (toScopedAt arguments) := rfl

theorem toScopedAt_zero {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt}
    {tailDecls : List (List S.Srt × S.Srt)}
    (head : Term S (bs ++ Γ) s) (tail : Args S tailDecls Γ) :
    toScopedAt (.cons head tail) 0 = toScoped head := rfl

theorem toScopedAt_succ {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt}
    {tailDecls : List (List S.Srt × S.Srt)}
    (head : Term S (bs ++ Γ) s) (tail : Args S tailDecls Γ)
    (position : Fin tailDecls.length) :
    toScopedAt (.cons head tail) position.succ = toScopedAt tail position := rfl

/-- A scoped constructor term as a binding term. -/
def ofScoped {index : Scope S} :
    Mettapedia.OSLF.SortedConstructors.Term
      (Mettapedia.OSLF.Binding.ScopedEncoding.signature S) index →
      Term S index.1 index.2
  | .node constructor arguments =>
      match constructor with
      | Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.variable _ _ position =>
          .var position
      | Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.operation context _ operator =>
          .op operator (assembleArguments context (S.arity operator)
            fun direction => ofScoped (arguments direction))

theorem ofScoped_variable {Γ : Ctx S} {s : S.Srt} (position : Var Γ s)
    (arguments : (direction : Fin ((signature S).arity
        (Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.variable Γ s position))) →
      Mettapedia.OSLF.SortedConstructors.Term (signature S)
        ((signature S).input
          (Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.variable Γ s position)
          direction)) :
    ofScoped
        (@Mettapedia.OSLF.SortedConstructors.Term.node (signature S)
          (Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.variable Γ s position)
          arguments) =
      .var position := rfl

theorem ofScoped_operation {Γ : Ctx S} {s : S.Srt} (operator : S.Op s)
    (arguments : (direction : Fin (S.arity operator).length) →
      Mettapedia.OSLF.SortedConstructors.Term (signature S)
        ((signature S).input
          (Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.operation Γ s operator)
          direction)) :
    ofScoped
        (@Mettapedia.OSLF.SortedConstructors.Term.node (signature S)
          (Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.operation Γ s operator)
          arguments) =
      .op operator (assembleArguments Γ (S.arity operator)
        fun direction => ofScoped (arguments direction)) := rfl

private theorem assemble_toScopedAt_cons {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt}
    {tailDecls : List (List S.Srt × S.Srt)}
    (head : Term S (bs ++ Γ) s) (tail : Args S tailDecls Γ) :
    assembleArguments Γ ((bs, s) :: tailDecls)
        (fun direction => ofScoped (toScopedAt (Args.cons head tail) direction)) =
      .cons (ofScoped (toScoped head))
        (assembleArguments Γ tailDecls
          fun position => ofScoped (toScopedAt tail position)) := by
  simp only [assembleArguments, toScopedAt_zero, toScopedAt_succ]
  rfl

mutual

theorem ofScoped_toScoped : ∀ {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s),
    ofScoped (toScoped term) = term
  | _, _, .var variable_ => by
      rw [toScoped_var, ofScoped_variable variable_]
  | _, _, .op operator arguments => by
      rw [toScoped_op, ofScoped_operation, ofScoped_toScopedAt arguments]

theorem ofScoped_toScopedAt : ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (arguments : Args S as Γ),
    assembleArguments Γ as
        (fun direction => ofScoped (toScopedAt arguments direction)) = arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      rw [assemble_toScopedAt_cons head tail, ofScoped_toScoped head,
        ofScoped_toScopedAt tail]

end

private theorem toScopedAt_assemble (Γ : Ctx S) :
    ∀ (as : List (List S.Srt × S.Srt))
      (arguments : (direction : Fin as.length) →
        Mettapedia.OSLF.SortedConstructors.Term (signature S)
          ((as.get direction).1 ++ Γ, (as.get direction).2)),
      (∀ direction, toScoped (ofScoped (arguments direction)) = arguments direction) →
        toScopedAt (assembleArguments Γ as (fun direction => ofScoped (arguments direction))) =
          arguments
  | [], _, _ => by
      funext direction
      exact Fin.elim0 direction
  | headDecl :: tail, arguments, closed => by
      funext direction
      refine Fin.cases ?zero ?succ direction
      · exact
          (show toScopedAt
              (assembleArguments Γ (headDecl :: tail)
                (fun direction => ofScoped (arguments direction))) 0 =
            toScoped (ofScoped (arguments 0)) from rfl).trans (closed 0)
      · intro previous
        exact
          (show toScopedAt
              (assembleArguments Γ (headDecl :: tail)
                (fun direction => ofScoped (arguments direction))) previous.succ =
            toScopedAt
              (assembleArguments Γ tail
                (fun position => ofScoped (arguments position.succ))) previous from rfl).trans
          (congrFun
            (toScopedAt_assemble Γ tail (fun position => arguments position.succ)
              fun position => closed position.succ) previous)

theorem toScoped_ofScoped {index : Scope S}
    (term : Mettapedia.OSLF.SortedConstructors.Term (signature S) index) :
    toScoped (ofScoped term) = term :=
  Mettapedia.OSLF.SortedConstructors.Term.recOn
    (motive := fun index term => toScoped (ofScoped term) = term) term
    (fun constructor arguments closed => by
      match constructor with
      | Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.variable context sort position =>
          rw [ofScoped_variable position, toScoped_var]
          exact congrArg
            (@Mettapedia.OSLF.SortedConstructors.Term.node (signature S)
              (Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.variable
                context sort position))
            (by
              funext direction
              exact Fin.elim0 direction)
      | Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.operation context sort operator =>
          rw [ofScoped_operation, toScoped_op]
          exact congrArg
            (@Mettapedia.OSLF.SortedConstructors.Term.node (signature S)
              (Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.operation
                context sort operator))
            (toScopedAt_assemble context (S.arity operator) arguments closed))

/-- Binding terms are the closed constructor terms of the scoped encoding. -/
def scopedTermEquiv (S : Signature) (Γ : Ctx S) (s : S.Srt) :
    Term S Γ s ≃
      Mettapedia.OSLF.SortedConstructors.Term (signature S) (Γ, s) where
  toFun := toScoped
  invFun := ofScoped
  left_inv := ofScoped_toScoped
  right_inv := toScoped_ofScoped

/-- Read a variable leaf as the nullary variable head of the scoped encoding,
and an operator head as the corresponding operation head. -/
def embedVars {index : Ctx S × S.Srt} :
    IFreeM (polynomial S) (Vars S) index →
      SortedSignature.ClosedFree (signature S) index
  | .pure variable_ =>
      .liftBind ⟨Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.variable
          index.1 index.2 variable_, rfl⟩
        fun direction => Fin.elim0 direction
  | .liftBind operator continuation =>
      .liftBind ⟨Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.operation
          index.1 index.2 operator, rfl⟩
        fun direction => embedVars (continuation direction)

theorem embedVars_pure {index : Ctx S × S.Srt} (variable_ : Vars S index) :
    embedVars (.pure variable_) =
      .liftBind ⟨Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.variable
          index.1 index.2 variable_, rfl⟩
        fun direction => Fin.elim0 direction := rfl

theorem embedVars_liftBind {index : Ctx S × S.Srt} (operator : S.Op index.2)
    (continuation : (direction : Fin (S.arity operator).length) →
      IFreeM (polynomial S) (Vars S)
        ((polynomial S).src index operator direction)) :
    embedVars (.liftBind operator continuation) =
      .liftBind ⟨Mettapedia.OSLF.Binding.ScopedEncoding.Constructor.operation
          index.1 index.2 operator, rfl⟩
        fun direction => embedVars (continuation direction) := rfl

mutual

theorem embedVars_toFree : ∀ {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s),
    embedVars (toFree term) = SortedSignature.toFree (toScoped term)
  | _, _, .var _ => by
      rw [toFree_var, embedVars_pure, toScoped_var]
      simp only [SortedSignature.toFree]
      apply congrArg
      funext direction
      exact Fin.elim0 direction
  | _, _, .op _ arguments => by
      rw [toFree_op, embedVars_liftBind, toScoped_op]
      simp only [SortedSignature.toFree]
      exact congrArg (IFreeM.liftBind _) (embedVars_toFreeAt arguments)

theorem embedVars_toFreeAt : ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (arguments : Args S as Γ),
    (fun direction => embedVars (toFreeAt arguments direction)) =
      fun direction => SortedSignature.toFree (toScopedAt arguments direction)
  | _, _, .nil => by
      funext direction
      exact Fin.elim0 direction
  | _, _, .cons (bs := bs) (s := s) (as := as) head tail => by
      funext direction
      match direction with
      | ⟨0, proof⟩ =>
          rw [finHead (head := (bs, s)) (tail := as) proof, toFreeAt_zero, toScopedAt_zero]
          exact embedVars_toFree head
      | ⟨n + 1, proof⟩ =>
          rw [finTail (head := (bs, s)) (tail := as) proof, toFreeAt_succ, toScopedAt_succ]
          exact congrFun (embedVars_toFreeAt tail) ⟨n, Nat.lt_of_succ_lt_succ proof⟩

end

/-- The scoped comparison agrees with the free-monad equivalence. Variables
are leaves on the free-monad side and nullary heads on the scoped side. -/
theorem closedTermEquiv_agrees {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s) :
    (SortedSignature.closedTermEquiv (signature S) (Γ, s)) (toScoped term) =
      embedVars ((termEquiv S Γ s) term) :=
  (embedVars_toFree term).symm

/-! ## What `IFreeM.bind` realizes -/

/-- A substitution that `IFreeM.bind` can apply: each variable is replaced by
a term of the same context and the same sort. The root index stays fixed. -/
abbrev IndexPreserving (S : Signature) :=
  ∀ index : Ctx S × S.Srt, Var index.1 index.2 → Term S index.1 index.2

mutual

def substIndex (σ : IndexPreserving S) :
    {Γ : Ctx S} → {s : S.Srt} → Term S Γ s → Term S Γ s
  | Γ, s, .var variable_ => σ (Γ, s) variable_
  | _, _, .op operator arguments => .op operator (substIndexArgs σ arguments)

def substIndexArgs (σ : IndexPreserving S) :
    {as : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      Args S as Γ → Args S as Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (substIndex σ head) (substIndexArgs σ tail)

end

theorem substIndex_var (σ : IndexPreserving S) {Γ : Ctx S} {s : S.Srt}
    (variable_ : Var Γ s) :
    substIndex σ (.var variable_) = σ (Γ, s) variable_ := rfl

theorem substIndex_op (σ : IndexPreserving S) {Γ : Ctx S} {s : S.Srt}
    (operator : S.Op s) (arguments : Args S (S.arity operator) Γ) :
    substIndex σ (.op operator arguments) =
      .op operator (substIndexArgs σ arguments) := rfl

theorem substIndexArgs_cons (σ : IndexPreserving S) {bs : List S.Srt} {s : S.Srt}
    {as : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (head : Term S (bs ++ Γ) s) (tail : Args S as Γ) :
    substIndexArgs σ (.cons head tail) =
      .cons (substIndex σ head) (substIndexArgs σ tail) := rfl

mutual

theorem toFree_substIndex (σ : IndexPreserving S) :
    ∀ {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s),
      toFree (substIndex σ term) =
        (toFree term).bind fun index variable_ => toFree (σ index variable_)
  | _, _, .var variable_ => by
      simp only [substIndex_var, toFree_var, IFreeM.bind_pure]
  | Γ, s, .op operator arguments => by
      rw [substIndex_op, toFree_op, toFree_op, IFreeM.bind_liftBind]
      exact congrArg
        (IFreeM.liftBind (P := polynomial S) (s := (Γ, s)) operator)
        (toFreeAt_substIndex σ arguments)

theorem toFreeAt_substIndex (σ : IndexPreserving S) :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} (arguments : Args S as Γ),
      toFreeAt (substIndexArgs σ arguments) =
        fun direction => (toFreeAt arguments direction).bind
          fun index variable_ => toFree (σ index variable_)
  | _, _, .nil => by
      funext direction
      exact Fin.elim0 direction
  | _, _, .cons (bs := bs) (s := s) (as := as) head tail => by
      funext direction
      match direction with
      | ⟨0, proof⟩ =>
          rw [finHead (head := (bs, s)) (tail := as) proof, substIndexArgs_cons,
            toFreeAt_zero, toFreeAt_zero, toFree_substIndex σ head]
          rfl
      | ⟨n + 1, proof⟩ =>
          rw [finTail (head := (bs, s)) (tail := as) proof, substIndexArgs_cons,
            toFreeAt_succ, toFreeAt_succ]
          exact congrFun (toFreeAt_substIndex σ tail) ⟨n, Nat.lt_of_succ_lt_succ proof⟩

end

/-- `IFreeM.bind` grafts an index-preserving leaf map and keeps the root index. -/
theorem ifreeBind_leaf
    (σ : ∀ index : Ctx S × S.Srt,
      Var index.1 index.2 → IFreeM (polynomial S) (Vars S) index)
    {Γ : Ctx S} {s : S.Srt} (variable_ : Var Γ s) :
    (IFreeM.pure (P := polynomial S) (X := Vars S) variable_).bind σ =
      σ (Γ, s) variable_ :=
  rfl

mutual

theorem substIndex_id : ∀ {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s),
    substIndex (fun _ variable_ => .var variable_) term = term
  | _, _, .var _ => rfl
  | _, _, .op operator arguments => by
      simp only [substIndex_op]
      exact congrArg (Term.op operator) (substIndexArgs_id arguments)

theorem substIndexArgs_id : ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (arguments : Args S as Γ),
    substIndexArgs (fun _ variable_ => .var variable_) arguments = arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [substIndexArgs_cons, substIndex_id head, substIndexArgs_id tail]

end

/-! ## Transport of binding substitution and renaming -/

/-- `bind` on trees. The root moves from `Γ` to `Δ`. `IFreeM.bind` does not. -/
def treeBind {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) {s : S.Srt}
    (tree : IFreeM (polynomial S) (Vars S) (Γ, s)) :
    IFreeM (polynomial S) (Vars S) (Δ, s) :=
  toFree (bind sigma (ofFree tree))

/-- `rename` on trees. -/
def treeRename {Γ Δ : Ctx S} (rho : Ren S Γ Δ) {s : S.Srt}
    (tree : IFreeM (polynomial S) (Vars S) (Γ, s)) :
    IFreeM (polynomial S) (Vars S) (Δ, s) :=
  toFree (rename rho (ofFree tree))

theorem toFree_bind {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) {s : S.Srt}
    (term : Term S Γ s) :
    toFree (bind sigma term) = treeBind sigma (toFree term) := by
  simp only [treeBind, ofFree_toFree]

theorem toFree_rename {Γ Δ : Ctx S} (rho : Ren S Γ Δ) {s : S.Srt}
    (term : Term S Γ s) :
    toFree (rename rho term) = treeRename rho (toFree term) := by
  simp only [treeRename, ofFree_toFree]

theorem treeBind_id {Γ : Ctx S} {s : S.Srt}
    (tree : IFreeM (polynomial S) (Vars S) (Γ, s)) :
    treeBind (fun _ variable_ => .var variable_) tree = tree := by
  simp only [treeBind, bind_id, toFree_ofFree]

theorem treeBind_comp {Γ Δ Θ : Ctx S} (sigma : Sub S Γ Δ) (sigma' : Sub S Δ Θ)
    {s : S.Srt} (tree : IFreeM (polynomial S) (Vars S) (Γ, s)) :
    treeBind sigma' (treeBind sigma tree) =
      treeBind (fun sort variable_ => bind sigma' (sigma sort variable_)) tree := by
  simp only [treeBind, ofFree_toFree, bind_comp]

theorem treeRename_id {Γ : Ctx S} {s : S.Srt}
    (tree : IFreeM (polynomial S) (Vars S) (Γ, s)) :
    treeRename (fun _ variable_ => variable_) tree = tree := by
  simp only [treeRename, rename_id, toFree_ofFree]

theorem treeRename_comp {Γ Δ Θ : Ctx S} (rho : Ren S Γ Δ) (rho' : Ren S Δ Θ)
    {s : S.Srt} (tree : IFreeM (polynomial S) (Vars S) (Γ, s)) :
    treeRename rho' (treeRename rho tree) =
      treeRename (fun sort variable_ => rho' sort (rho sort variable_)) tree := by
  simp only [treeRename, ofFree_toFree, rename_comp]

theorem treeBind_var {Γ Δ : Ctx S} (rho : Ren S Γ Δ) {s : S.Srt}
    (tree : IFreeM (polynomial S) (Vars S) (Γ, s)) :
    treeBind (fun sort variable_ => .var (rho sort variable_)) tree =
      treeRename rho tree := by
  simp only [treeBind, treeRename, bind_var_eq_rename]

/-! ## A one-sorted illustration -/

inductive DemoSort where
  | star
  deriving DecidableEq

inductive DemoOp : DemoSort → Type where
  | unit : DemoOp .star
  | lam : DemoOp .star

def demo : Signature where
  Srt := DemoSort
  Op := DemoOp
  arity
    | .unit => []
    | .lam => [([.star], .star)]

def demoUnit : Term demo [] .star := .op .unit .nil

def demoBody : Term demo [.star] .star := .var .zero

def demoLam : Term demo [] .star := .op .lam (.cons demoBody .nil)

theorem demo_direction :
    (polynomial demo).src ([], .star) .lam ⟨0, by decide⟩ = ([.star], .star) :=
  rfl

theorem demo_var_is_leaf :
    toFree demoBody = .pure (P := polynomial demo) .zero :=
  rfl

theorem demo_lam_is_head :
    toFree demoLam =
      IFreeM.liftBind (P := polynomial demo) (s := ([], DemoSort.star)) DemoOp.lam
        (toFreeAt (Args.cons (S := demo) (bs := [DemoSort.star]) (s := DemoSort.star)
          (as := []) (Γ := []) demoBody Args.nil)) :=
  rfl

theorem demo_lam_leaf :
    toFreeAt (Args.cons (S := demo) (bs := [DemoSort.star]) (s := DemoSort.star)
        (as := []) (Γ := []) demoBody Args.nil) 0 =
      IFreeM.pure (P := polynomial demo) (Var.zero : Var [DemoSort.star] DemoSort.star) :=
  rfl

/-- A nullary head is not the binding head. -/
theorem demo_unit_ne_lam : toFree demoUnit ≠ toFree demoLam := by
  intro same
  have image : demoUnit = demoLam :=
    (ofFree_toFree demoUnit).symm.trans
      ((congrArg ofFree same).trans (ofFree_toFree demoLam))
  unfold demoUnit demoLam at image
  cases image

/-- Closing the bound variable moves the root from the one-element context to
the empty context. -/
theorem demo_bind_closes :
    bind (fun _ _ => demoUnit) demoBody = demoUnit :=
  rfl

/-- The same closing step on the tree changes the root index. -/
theorem demo_treeBind_closes :
    treeBind (fun _ _ => demoUnit) (toFree demoBody) = toFree demoUnit :=
  (toFree_bind (fun _ _ => demoUnit) demoBody).symm.trans
    (congrArg toFree demo_bind_closes)

end Mettapedia.GSLT.Poly.BindingSignature
