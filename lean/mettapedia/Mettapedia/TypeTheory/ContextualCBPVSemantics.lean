import Mettapedia.TypeTheory.ContextualCBPVSyntax
import Mettapedia.TypeTheory.ContextualAlgebraSequencing

/-!
# Denotation of contextual CBPV in the existing computation algebras

A value type denotes a type. A computation type denotes an Eilenberg--Moore
algebra of the existing contextual program monad (`inducedMonad`), so the
model is the existing one, not a new evaluator:

* `ret A` denotes the free algebra on `⟦A⟧ ⊕ Raised`: a returner's programs
  end either in an answer or in a raised no-value of some kind;
* `arrow A B` denotes the power algebra `⟦A⟧ → ⟦B⟧`
  (`ContextualComputationAlgebraProducts.power`);
* `thunk B` denotes the carrier of `⟦B⟧`: a thunk is its computation.

Effect operations act through the algebra map; `raise` is interpreted by
the raise map `CTy.raiseAt`, which is pointwise on functions. Sequencing
`M to x. N` and handling use `ContextualAlgebraSequencing.sequence`.

The two substitution lemmas (`Comp.den_rename`, `Comp.den_subst`) make the
denotation compositional; the operational laws are proved from them.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV

open CategoryTheory
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualKleisliAdjunction (inducedMonad)
open Mettapedia.TypeTheory.ContextualComputationAlgebraProducts (power)

variable (sig : Signature)

/-- The state read and written by the effect operations. -/
abbrev State := sig.Data sig.stateSort

/-- A deferred external request. -/
abbrev Request := sig.Data sig.intentSort

/-- A raised no-value: its kind and its payload. Every kind shares this one
carrier; the kind is the index. -/
abbrev Raised := sig.Kind × sig.Data sig.payloadSort

/-- The existing computation algebras of the contextual program monad. -/
abbrev Alg := Monad.Algebra (inducedMonad (State sig) (Request sig))

mutual
  /-- Value types denote types. -/
  def VTy.den : VTy sig.Ground → Type
    | .ground sort => sig.Data sort
    | .unit => Unit
    | .prod first second => VTy.den first × VTy.den second
    | .thunk body => (CTy.alg body).A

  /-- Computation types denote algebras of the existing contextual monad. -/
  def CTy.alg : CTy sig.Ground → Alg sig
    | .ret answer =>
        (inducedMonad (State sig) (Request sig)).free.obj (VTy.den answer ⊕ Raised sig)
    | .arrow domain codomain => power (VTy.den domain) (CTy.alg codomain)
end

/-- The carrier of a returner type is the contextual program type. -/
theorem CTy.alg_ret_carrier (answer : VTy sig.Ground) :
    (CTy.alg sig (.ret answer)).A =
      Program (State sig) (VTy.den sig answer ⊕ Raised sig) (Request sig) := rfl

/-- The carrier of a function type is the function type of carriers. -/
theorem CTy.alg_arrow_carrier (domain : VTy sig.Ground) (codomain : CTy sig.Ground) :
    (CTy.alg sig (.arrow domain codomain)).A =
      (VTy.den sig domain → (CTy.alg sig codomain).A) := rfl

/-- Ground data as an element of its ground type's denotation. -/
def VTy.ofData {sort : sig.Ground} (datum : sig.Data sort) : VTy.den sig (.ground sort) := datum

/-- An element of a ground type's denotation as ground data. -/
def VTy.toData {sort : sig.Ground} (value : VTy.den sig (.ground sort)) : sig.Data sort := value

@[simp] theorem VTy.toData_ofData {sort : sig.Ground} (datum : sig.Data sort) :
    VTy.toData sig (VTy.ofData sig datum) = datum := rfl

@[simp] theorem VTy.ofData_toData {sort : sig.Ground} (value : VTy.den sig (.ground sort)) :
    VTy.ofData sig (VTy.toData sig value) = value := rfl

/-- A returner's carrier element as the contextual program it is. -/
def CTy.asProgram {answer : VTy sig.Ground} (carrier : (CTy.alg sig (.ret answer)).A) :
    Program (State sig) (VTy.den sig answer ⊕ Raised sig) (Request sig) := carrier

/-- Raising at an arbitrary computation type: a returner ends in the raised
no-value, and a function raises at every argument. -/
def CTy.raiseAt : (type : CTy sig.Ground) → Raised sig → (CTy.alg sig type).A
  | .ret _, raised =>
      (Program.pure (Sum.inr raised) :
        Program (State sig) (_ ⊕ Raised sig) (Request sig))
  | .arrow _ codomain, raised => fun _ => CTy.raiseAt codomain raised

/-- Continue the answers of a returner program into a computation algebra.
Raised no-values go to `onRaise`. -/
def CTy.continue (type : CTy sig.Ground) {Answer : Type}
    (program : Program (State sig) (Answer ⊕ Raised sig) (Request sig))
    (next : Answer → (CTy.alg sig type).A)
    (onRaise : Raised sig → (CTy.alg sig type).A) : (CTy.alg sig type).A :=
  ContextualAlgebraSequencing.sequence (CTy.alg sig type) program (Sum.elim next onRaise)

/-- Value environments. -/
abbrev Env (context : List (VTy sig.Ground)) :=
  (type : VTy sig.Ground) → Var context type → VTy.den sig type

namespace Env

variable {sig}

/-- The empty environment. -/
def empty : Env sig [] := fun _ index => nomatch index

/-- Bind the newest variable. -/
def extend {context : List (VTy sig.Ground)} {bound : VTy sig.Ground}
    (value : VTy.den sig bound) (η : Env sig context) : Env sig (bound :: context)
  | _, .zero => value
  | type, .succ index => η type index

end Env

variable {sig}

namespace Env

theorem extend_lift {source target : List (VTy sig.Ground)} (ρ : Ren source target)
    {bound : VTy sig.Ground} (value : VTy.den sig bound) (η : Env sig target) :
    (fun type index => (η.extend value) type (ρ.lift bound type index)) =
      Env.extend value (fun type index => η type (ρ type index)) := by
  funext type index
  cases index <;> rfl

theorem extend_weaken {context : List (VTy sig.Ground)} {bound : VTy sig.Ground}
    (value : VTy.den sig bound) (η : Env sig context) :
    (fun type index => (η.extend value) type (Ren.weaken bound type index)) = η := rfl

end Env

variable [DecidableEq sig.Kind]

mutual
  /-- Denotation of values. -/
  def Val.den : {context : List (VTy sig.Ground)} → {type : VTy sig.Ground} →
      Val sig context type → Env sig context → VTy.den sig type
    | _, _, .var index, η => η _ index
    | _, _, .const _ datum, _ => VTy.ofData sig datum
    | _, _, .prim operation argument, η =>
        VTy.ofData sig (sig.evalPrim operation (VTy.toData sig (Val.den argument η)))
    | _, _, .unit, _ => ()
    | _, _, .pair left right, η => (Val.den left η, Val.den right η)
    | _, _, .thunk body, η => Comp.den body η

  /-- Denotation of computations. -/
  def Comp.den : {context : List (VTy sig.Ground)} → {type : CTy sig.Ground} →
      Comp sig context type → Env sig context → (CTy.alg sig type).A
    | _, _, .ret value, η =>
        (Program.pure (Sum.inl (Val.den value η)) :
          Program (State sig) (_ ⊕ Raised sig) (Request sig))
    | _, type, .bind first body, η =>
        CTy.continue sig type (Comp.den first η) (fun answer => Comp.den body (η.extend answer))
          (CTy.raiseAt sig type)
    | _, _, .force suspended, η => Val.den suspended η
    | _, _, .lam body, η => fun argument => Comp.den body (η.extend argument)
    | _, _, .app function argument, η => Comp.den function η (Val.den argument η)
    | _, _, .split pair body, η =>
        Comp.den body ((η.extend (Val.den pair η).1).extend (Val.den pair η).2)
    | _, type, .choose left right, η =>
        (CTy.alg sig type).a (Program.choose (.pure (Comp.den left η)) (.pure (Comp.den right η)))
    | _, type, .read body, η =>
        (CTy.alg sig type).a (Program.read fun state =>
          .pure (Comp.den body (η.extend (VTy.ofData sig state))))
    | _, type, .write state next, η =>
        (CTy.alg sig type).a
          (Program.write (VTy.toData sig (Val.den state η)) (.pure (Comp.den next η)))
    | _, type, .intent request next, η =>
        (CTy.alg sig type).a
          (Program.intent (VTy.toData sig (Val.den request η)) (.pure (Comp.den next η)))
    | _, type, .raise kind payload, η =>
        CTy.raiseAt sig type (kind, VTy.toData sig (Val.den payload η))
    | _, type, .handle first kind onReturn onRaise, η =>
        CTy.continue sig type (Comp.den first η)
          (fun answer => Comp.den onReturn (η.extend answer))
          (fun raised => if raised.1 = kind then Comp.den onRaise (η.extend (VTy.ofData sig raised.2))
            else CTy.raiseAt sig type raised)
end

/-! ## Compositionality -/


mutual
  theorem Val.den_rename {source target : List (VTy sig.Ground)} (ρ : Ren source target) :
      {type : VTy sig.Ground} → (value : Val sig source type) → (η : Env sig target) →
        (value.rename ρ).den η = value.den (fun type index => η type (ρ type index))
    | _, .var _, _ => rfl
    | _, .const _ _, _ => rfl
    | _, .prim operation argument, η => by
        simp only [Val.rename, Val.den]
        rw [Val.den_rename ρ argument η]
    | _, .unit, _ => rfl
    | _, .pair left right, η => by
        simp only [Val.rename, Val.den]
        rw [Val.den_rename ρ left η, Val.den_rename ρ right η]
    | _, .thunk body, η => by
        simp only [Val.rename, Val.den]
        exact Comp.den_rename ρ body η

  theorem Comp.den_rename {source target : List (VTy sig.Ground)} (ρ : Ren source target) :
      {type : CTy sig.Ground} → (code : Comp sig source type) → (η : Env sig target) →
        (code.rename ρ).den η = code.den (fun type index => η type (ρ type index))
    | _, .ret value, η => by
        simp only [Comp.rename, Comp.den]
        rw [Val.den_rename ρ value η]
    | _, .bind first body, η => by
        simp only [Comp.rename, Comp.den]
        rw [Comp.den_rename ρ first η]
        congr 1
        funext answer
        rw [Comp.den_rename (ρ.lift _) body (η.extend answer), Env.extend_lift]
    | _, .force suspended, η => by
        simp only [Comp.rename, Comp.den]
        exact Val.den_rename ρ suspended η
    | _, .lam body, η => by
        simp only [Comp.rename, Comp.den]
        funext argument
        rw [Comp.den_rename (ρ.lift _) body (η.extend argument), Env.extend_lift]
    | _, .app function argument, η => by
        simp only [Comp.rename, Comp.den]
        rw [Comp.den_rename ρ function η, Val.den_rename ρ argument η]
    | _, .split pair body, η => by
        simp only [Comp.rename, Comp.den]
        rw [Comp.den_rename ((ρ.lift _).lift _) body, Env.extend_lift, Env.extend_lift,
          Val.den_rename ρ pair η]
    | _, .choose left right, η => by
        simp only [Comp.rename, Comp.den]
        rw [Comp.den_rename ρ left η, Comp.den_rename ρ right η]
    | _, .read body, η => by
        simp only [Comp.rename, Comp.den]
        congr 2
        funext state
        rw [Comp.den_rename (ρ.lift _) body (η.extend (VTy.ofData sig state)), Env.extend_lift]
    | _, .write state next, η => by
        simp only [Comp.rename, Comp.den]
        rw [Val.den_rename ρ state η, Comp.den_rename ρ next η]
    | _, .intent request next, η => by
        simp only [Comp.rename, Comp.den]
        rw [Val.den_rename ρ request η, Comp.den_rename ρ next η]
    | _, .raise kind payload, η => by
        simp only [Comp.rename, Comp.den]
        rw [Val.den_rename ρ payload η]
    | _, .handle first kind onReturn onRaise, η => by
        simp only [Comp.rename, Comp.den]
        rw [Comp.den_rename ρ first η]
        congr 1
        · funext answer
          rw [Comp.den_rename (ρ.lift _) onReturn (η.extend answer), Env.extend_lift]
        · funext raised
          rw [Comp.den_rename (ρ.lift _) onRaise (η.extend (VTy.ofData sig raised.2)),
            Env.extend_lift]
end

/-- The environment a substitution induces. -/
def Subst.den {source target : List (VTy sig.Ground)} (σ : Subst sig source target)
    (η : Env sig target) : Env sig source :=
  fun type index => (σ type index).den η

theorem Subst.den_lift {source target : List (VTy sig.Ground)} (σ : Subst sig source target)
    {bound : VTy sig.Ground} (value : VTy.den sig bound) (η : Env sig target) :
    (σ.lift bound).den (η.extend value) = Env.extend value (σ.den η) := by
  funext type index
  cases index with
  | zero => rfl
  | succ index =>
      change (Val.rename (Ren.weaken bound) (σ type index)).den (η.extend value) = _
      rw [Val.den_rename, Env.extend_weaken]
      rfl

mutual
  theorem Val.den_subst {source target : List (VTy sig.Ground)} (σ : Subst sig source target) :
      {type : VTy sig.Ground} → (value : Val sig source type) → (η : Env sig target) →
        (value.subst σ).den η = value.den (σ.den η)
    | _, .var _, _ => rfl
    | _, .const _ _, _ => rfl
    | _, .prim operation argument, η => by
        simp only [Val.subst, Val.den]
        rw [Val.den_subst σ argument η]
    | _, .unit, _ => rfl
    | _, .pair left right, η => by
        simp only [Val.subst, Val.den]
        rw [Val.den_subst σ left η, Val.den_subst σ right η]
    | _, .thunk body, η => by
        simp only [Val.subst, Val.den]
        exact Comp.den_subst σ body η

  theorem Comp.den_subst {source target : List (VTy sig.Ground)} (σ : Subst sig source target) :
      {type : CTy sig.Ground} → (code : Comp sig source type) → (η : Env sig target) →
        (code.subst σ).den η = code.den (σ.den η)
    | _, .ret value, η => by
        simp only [Comp.subst, Comp.den]
        rw [Val.den_subst σ value η]
    | _, .bind first body, η => by
        simp only [Comp.subst, Comp.den]
        rw [Comp.den_subst σ first η]
        congr 1
        funext answer
        rw [Comp.den_subst (σ.lift _) body (η.extend answer), Subst.den_lift]
    | _, .force suspended, η => by
        simp only [Comp.subst, Comp.den]
        exact Val.den_subst σ suspended η
    | _, .lam body, η => by
        simp only [Comp.subst, Comp.den]
        funext argument
        rw [Comp.den_subst (σ.lift _) body (η.extend argument), Subst.den_lift]
    | _, .app function argument, η => by
        simp only [Comp.subst, Comp.den]
        rw [Comp.den_subst σ function η, Val.den_subst σ argument η]
    | _, .split pair body, η => by
        simp only [Comp.subst, Comp.den]
        rw [Comp.den_subst ((σ.lift _).lift _) body, Subst.den_lift, Subst.den_lift,
          Val.den_subst σ pair η]
    | _, .choose left right, η => by
        simp only [Comp.subst, Comp.den]
        rw [Comp.den_subst σ left η, Comp.den_subst σ right η]
    | _, .read body, η => by
        simp only [Comp.subst, Comp.den]
        congr 2
        funext state
        rw [Comp.den_subst (σ.lift _) body (η.extend (VTy.ofData sig state)), Subst.den_lift]
    | _, .write state next, η => by
        simp only [Comp.subst, Comp.den]
        rw [Val.den_subst σ state η, Comp.den_subst σ next η]
    | _, .intent request next, η => by
        simp only [Comp.subst, Comp.den]
        rw [Val.den_subst σ request η, Comp.den_subst σ next η]
    | _, .raise kind payload, η => by
        simp only [Comp.subst, Comp.den]
        rw [Val.den_subst σ payload η]
    | _, .handle first kind onReturn onRaise, η => by
        simp only [Comp.subst, Comp.den]
        rw [Comp.den_subst σ first η]
        congr 1
        · funext answer
          rw [Comp.den_subst (σ.lift _) onReturn (η.extend answer), Subst.den_lift]
        · funext raised
          rw [Comp.den_subst (σ.lift _) onRaise (η.extend (VTy.ofData sig raised.2)),
            Subst.den_lift]
end

theorem Subst.den_single {context : List (VTy sig.Ground)} {bound : VTy sig.Ground}
    (value : Val sig context bound) (η : Env sig context) :
    (Subst.single value).den η = Env.extend (value.den η) η := by
  funext type index
  cases index <;> rfl

theorem Subst.den_double {context : List (VTy sig.Ground)} {first second : VTy sig.Ground}
    (left : Val sig context first) (right : Val sig context second) (η : Env sig context) :
    (Subst.double left right).den η = (η.extend (left.den η)).extend (right.den η) := by
  funext type index
  rcases index with _ | ⟨_ | index⟩ <;> rfl

/-- Opening a binder with a value denotes extending the environment. -/
theorem Comp.den_instantiate {context : List (VTy sig.Ground)} {bound : VTy sig.Ground}
    {type : CTy sig.Ground} (body : Comp sig (bound :: context) type)
    (value : Val sig context bound) (η : Env sig context) :
    (body.instantiate value).den η = body.den (η.extend (value.den η)) := by
  rw [Comp.instantiate, Comp.den_subst, Subst.den_single]

theorem Comp.den_weakenUnder {context : List (VTy sig.Ground)} {bound inner : VTy sig.Ground}
    {type : CTy sig.Ground} (body : Comp sig (inner :: context) type)
    (outer : VTy.den sig bound) (value : VTy.den sig inner) (η : Env sig context) :
    (Comp.weakenUnder (bound := bound) body).den ((η.extend outer).extend value) =
      body.den (η.extend value) := by
  rw [Comp.weakenUnder, Comp.den_rename, Env.extend_lift, Env.extend_weaken]

end Mettapedia.TypeTheory.ContextualCBPV
