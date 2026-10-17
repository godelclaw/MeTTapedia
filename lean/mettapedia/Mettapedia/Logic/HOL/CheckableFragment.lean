import Mettapedia.Logic.HOL.ConversionTiers

/-!
# Knowing the fragment: hinted raw certificates and a decidable fragment test

A certificate arrives as raw, well-scoped syntax (`Raw`). Its only hints are the
types of its binders, in the style of Church. Raw beta reduction (`RawStep`)
is untyped, so raw conversion can diverge: the self-application `Ω`
reduces only to itself (`omega_step_iff`) and leftmost-outermost reduction
stays at `Ω` for every budget (`rawNormalize_omega`).

The hints make membership in the simply typed fragment decidable by one
syntax-directed pass with no search (`elaborate?`). The pass is exact:

* it returns the unique intrinsically typed term whose erasure is the
  certificate (`elaborate?_sound`, `elaborate?_erase`);
* erasure simulates and reflects beta steps (`erase_step`, `erase_step_inv`).

Inside the fragment, strong normalization and confluence of typed beta make
conversion decidable with computable budgets, and the checker `check` decides
raw convertibility exactly (`check_accepted_iff`). Outside it, the checker
refuses before running any conversion (`check_outside`); for `Ω` with any
hint this is the only answer (`omega_outside`). Refusal outside the fragment is
not a claim that the certificate is wrong: it says the certificate carries no
evidence that conversion terminates.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.CheckableFragment

open Mettapedia.Logic.HOL.ContextualTrinity
open Mettapedia.Logic.HOL.BetaNormalization
open Mettapedia.Logic.HOL.ConversionTiers

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Variables as positions -/

/-- The position of a typed variable in its context. -/
def _root_.Mettapedia.Logic.HOL.Var.toFin {Γ : Ctx Base} {τ : Ty Base} :
    Var Γ τ → Fin Γ.length
  | .vz => ⟨0, by simp⟩
  | .vs index => index.toFin.succ

/-- The typed variable at a position of a context. -/
def _root_.Mettapedia.Logic.HOL.Var.ofFin : (Γ : Ctx Base) → (position : Fin Γ.length) →
    Var Γ (Γ.get position)
  | _ :: _, ⟨0, _⟩ => .vz
  | _ :: Γ, ⟨position + 1, bound⟩ => .vs (Var.ofFin Γ ⟨position, Nat.lt_of_succ_lt_succ bound⟩)

theorem Var.get_toFin {Γ : Ctx Base} {τ : Ty Base} (index : Var Γ τ) :
    Γ.get index.toFin = τ := by
  induction index with
  | vz => rfl
  | vs index ih => simpa [Var.toFin] using ih

theorem Var.ofFin_toFin {Γ : Ctx Base} {τ : Ty Base} (index : Var Γ τ) :
    HEq (Var.ofFin Γ index.toFin) index := by
  induction index with
  | vz => rfl
  | @vs Γ τ σ index ih =>
      change HEq (Var.vs (σ := σ) (Var.ofFin Γ index.toFin)) (Var.vs index)
      have types := Var.get_toFin index
      revert ih
      generalize Var.ofFin Γ index.toFin = found
      revert found
      rw [types]
      intro found same
      cases same
      rfl

theorem Var.toFin_injective {Γ : Ctx Base} {τ : Ty Base} {first second : Var Γ τ}
    (same : first.toFin = second.toFin) : first = second := by
  have firstBack := Var.ofFin_toFin first
  have secondBack := Var.ofFin_toFin second
  rw [same] at firstBack
  exact eq_of_heq (firstBack.symm.trans secondBack)

/-! ## Raw certificates -/

variable (Base Const) in
/-- Raw, well-scoped certificate syntax. Binders carry their types as hints;
applications, variables and equations carry none. -/
inductive Raw : Nat → Type (max u v) where
  | var {n : Nat} : Fin n → Raw n
  | const {n : Nat} (τ : Ty Base) : Const τ → Raw n
  | app {n : Nat} : Raw n → Raw n → Raw n
  | lam {n : Nat} : Ty Base → Raw (n + 1) → Raw n
  | top {n : Nat} : Raw n
  | bot {n : Nat} : Raw n
  | and {n : Nat} : Raw n → Raw n → Raw n
  | or {n : Nat} : Raw n → Raw n → Raw n
  | imp {n : Nat} : Raw n → Raw n → Raw n
  | not {n : Nat} : Raw n → Raw n
  | eq {n : Nat} : Raw n → Raw n → Raw n
  | all {n : Nat} : Ty Base → Raw (n + 1) → Raw n
  | ex {n : Nat} : Ty Base → Raw (n + 1) → Raw n

namespace Raw

/-- Rename the variables of a raw term. -/
def rename : {n m : Nat} → (Fin n → Fin m) → Raw Base Const n → Raw Base Const m
  | _, _, ρ, .var index => .var (ρ index)
  | _, _, _, .const τ constant => .const τ constant
  | _, _, ρ, .app function argument => .app (rename ρ function) (rename ρ argument)
  | _, _, ρ, .lam σ body => .lam σ (rename (Fin.cases 0 (fun index => (ρ index).succ)) body)
  | _, _, _, .top => .top
  | _, _, _, .bot => .bot
  | _, _, ρ, .and left right => .and (rename ρ left) (rename ρ right)
  | _, _, ρ, .or left right => .or (rename ρ left) (rename ρ right)
  | _, _, ρ, .imp left right => .imp (rename ρ left) (rename ρ right)
  | _, _, ρ, .not operand => .not (rename ρ operand)
  | _, _, ρ, .eq left right => .eq (rename ρ left) (rename ρ right)
  | _, _, ρ, .all σ body => .all σ (rename (Fin.cases 0 (fun index => (ρ index).succ)) body)
  | _, _, ρ, .ex σ body => .ex σ (rename (Fin.cases 0 (fun index => (ρ index).succ)) body)

/-- Lift a raw substitution under a binder. -/
def liftSubst {n m : Nat} (θ : Fin n → Raw Base Const m) : Fin (n + 1) → Raw Base Const (m + 1) :=
  Fin.cases (.var 0) (fun index => rename Fin.succ (θ index))

/-- Substitute raw terms for the variables of a raw term. -/
def subst : {n m : Nat} → (Fin n → Raw Base Const m) → Raw Base Const n → Raw Base Const m
  | _, _, θ, .var index => θ index
  | _, _, _, .const τ constant => .const τ constant
  | _, _, θ, .app function argument => .app (subst θ function) (subst θ argument)
  | _, _, θ, .lam σ body => .lam σ (subst (liftSubst θ) body)
  | _, _, _, .top => .top
  | _, _, _, .bot => .bot
  | _, _, θ, .and left right => .and (subst θ left) (subst θ right)
  | _, _, θ, .or left right => .or (subst θ left) (subst θ right)
  | _, _, θ, .imp left right => .imp (subst θ left) (subst θ right)
  | _, _, θ, .not operand => .not (subst θ operand)
  | _, _, θ, .eq left right => .eq (subst θ left) (subst θ right)
  | _, _, θ, .all σ body => .all σ (subst (liftSubst θ) body)
  | _, _, θ, .ex σ body => .ex σ (subst (liftSubst θ) body)

/-- Instantiate the outermost bound variable. -/
def instantiate {n : Nat} (argument : Raw Base Const n) (body : Raw Base Const (n + 1)) :
    Raw Base Const n :=
  subst (Fin.cases argument .var) body

end Raw

/-- Untyped beta reduction of raw certificates, at any position. -/
inductive RawStep : {n : Nat} → Raw Base Const n → Raw Base Const n → Prop where
  | beta {n : Nat} (σ : Ty Base) (body : Raw Base Const (n + 1)) (argument : Raw Base Const n) :
      RawStep (.app (.lam σ body) argument) (Raw.instantiate argument body)
  | appFun {n : Nat} {function function' : Raw Base Const n} (argument : Raw Base Const n) :
      RawStep function function' → RawStep (.app function argument) (.app function' argument)
  | appArg {n : Nat} (function : Raw Base Const n) {argument argument' : Raw Base Const n} :
      RawStep argument argument' → RawStep (.app function argument) (.app function argument')
  | lam {n : Nat} (σ : Ty Base) {body body' : Raw Base Const (n + 1)} :
      RawStep body body' → RawStep (.lam σ body) (.lam σ body')
  | andLeft {n : Nat} {left left' : Raw Base Const n} (right : Raw Base Const n) :
      RawStep left left' → RawStep (.and left right) (.and left' right)
  | andRight {n : Nat} (left : Raw Base Const n) {right right' : Raw Base Const n} :
      RawStep right right' → RawStep (.and left right) (.and left right')
  | orLeft {n : Nat} {left left' : Raw Base Const n} (right : Raw Base Const n) :
      RawStep left left' → RawStep (.or left right) (.or left' right)
  | orRight {n : Nat} (left : Raw Base Const n) {right right' : Raw Base Const n} :
      RawStep right right' → RawStep (.or left right) (.or left right')
  | impLeft {n : Nat} {left left' : Raw Base Const n} (right : Raw Base Const n) :
      RawStep left left' → RawStep (.imp left right) (.imp left' right)
  | impRight {n : Nat} (left : Raw Base Const n) {right right' : Raw Base Const n} :
      RawStep right right' → RawStep (.imp left right) (.imp left right')
  | not {n : Nat} {operand operand' : Raw Base Const n} :
      RawStep operand operand' → RawStep (.not operand) (.not operand')
  | eqLeft {n : Nat} {left left' : Raw Base Const n} (right : Raw Base Const n) :
      RawStep left left' → RawStep (.eq left right) (.eq left' right)
  | eqRight {n : Nat} (left : Raw Base Const n) {right right' : Raw Base Const n} :
      RawStep right right' → RawStep (.eq left right) (.eq left right')
  | all {n : Nat} (σ : Ty Base) {body body' : Raw Base Const (n + 1)} :
      RawStep body body' → RawStep (.all σ body) (.all σ body')
  | ex {n : Nat} (σ : Ty Base) {body body' : Raw Base Const (n + 1)} :
      RawStep body body' → RawStep (.ex σ body) (.ex σ body')

/-- Raw convertibility witnessed by a common reduct. -/
def RawJoinable {n : Nat} (left right : Raw Base Const n) : Prop :=
  ∃ meet, Relation.ReflTransGen RawStep left meet ∧ Relation.ReflTransGen RawStep right meet

/-! ## Erasure of typed terms -/

/-- Forget the types of a typed term, keeping its binder hints. -/
def erase : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Raw Base Const Γ.length
  | _, _, .var index => .var index.toFin
  | _, τ, .const constant => .const τ constant
  | _, _, .app function argument => .app (erase function) (erase argument)
  | _, .arr σ _, .lam body => .lam σ (erase body)
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, _, .and left right => .and (erase left) (erase right)
  | _, _, .or left right => .or (erase left) (erase right)
  | _, _, .imp left right => .imp (erase left) (erase right)
  | _, _, .not operand => .not (erase operand)
  | _, _, .eq left right => .eq (erase left) (erase right)
  | _, _, .all (σ := σ) body => .all σ (erase body)
  | _, _, .ex (σ := σ) body => .ex σ (erase body)

theorem erase_rename {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) :
    ∀ {Δ : Ctx Base} (ρ : Rename Base Γ Δ) (ρ' : Fin Γ.length → Fin Δ.length),
      (∀ {σ : Ty Base} (index : Var Γ σ), (ρ index).toFin = ρ' index.toFin) →
        erase (rename ρ term) = Raw.rename ρ' (erase term) := by
  induction term with
  | var index => intro Δ ρ ρ' agree; simp [erase, rename, Raw.rename, agree index]
  | lam body ih =>
      intro Δ ρ ρ' agree
      simp only [erase, rename, Raw.rename]
      congr 1
      refine ih _ _ (fun index => ?_)
      cases index with
      | vz => rfl
      | vs index => simp [Rename.lift, Var.toFin, agree index]
  | all body ih =>
      intro Δ ρ ρ' agree
      simp only [erase, rename, Raw.rename]
      congr 1
      refine ih _ _ (fun index => ?_)
      cases index with
      | vz => rfl
      | vs index => simp [Rename.lift, Var.toFin, agree index]
  | ex body ih =>
      intro Δ ρ ρ' agree
      simp only [erase, rename, Raw.rename]
      congr 1
      refine ih _ _ (fun index => ?_)
      cases index with
      | vz => rfl
      | vs index => simp [Rename.lift, Var.toFin, agree index]
  | _ => intro Δ ρ ρ' agree; simp_all [erase, rename, Raw.rename]

theorem erase_subst {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) :
    ∀ {Δ : Ctx Base} (θ : Subst Const Γ Δ) (θ' : Fin Γ.length → Raw Base Const Δ.length),
      (∀ {σ : Ty Base} (index : Var Γ σ), erase (θ index) = θ' index.toFin) →
        erase (HOL.subst θ term) = Raw.subst θ' (erase term) := by
  have lifted : ∀ {Γ Δ : Ctx Base} {ρ : Ty Base} (θ : Subst Const Γ Δ)
      (θ' : Fin Γ.length → Raw Base Const Δ.length),
      (∀ {σ : Ty Base} (index : Var Γ σ), erase (θ index) = θ' index.toFin) →
        ∀ {σ : Ty Base} (index : Var (ρ :: Γ) σ),
          erase (Subst.lift θ index) = Raw.liftSubst θ' index.toFin := by
    intro Γ Δ ρ θ θ' agree σ index
    cases index with
    | vz => rfl
    | vs index =>
        simp only [Subst.lift, Var.toFin, Raw.liftSubst, Fin.cases_succ]
        rw [erase_rename _ _ Fin.succ (fun _ => rfl), agree index]
  induction term with
  | var index => intro Δ θ θ' agree; exact agree index
  | lam body ih =>
      intro Δ θ θ' agree
      simp only [erase, HOL.subst, Raw.subst]
      exact congrArg _ (ih _ _ (lifted θ θ' agree))
  | all body ih =>
      intro Δ θ θ' agree
      simp only [erase, HOL.subst, Raw.subst]
      exact congrArg _ (ih _ _ (lifted θ θ' agree))
  | ex body ih =>
      intro Δ θ θ' agree
      simp only [erase, HOL.subst, Raw.subst]
      exact congrArg _ (ih _ _ (lifted θ θ' agree))
  | const constant => intro Δ θ θ' agree; rfl
  | top => intro Δ θ θ' agree; rfl
  | bot => intro Δ θ θ' agree; rfl
  | app function argument functionIh argumentIh =>
      intro Δ θ θ' agree
      simp only [erase, HOL.subst, Raw.subst]
      rw [functionIh θ θ' agree, argumentIh θ θ' agree]
  | and left right leftIh rightIh =>
      intro Δ θ θ' agree
      simp only [erase, HOL.subst, Raw.subst]
      rw [leftIh θ θ' agree, rightIh θ θ' agree]
  | or left right leftIh rightIh =>
      intro Δ θ θ' agree
      simp only [erase, HOL.subst, Raw.subst]
      rw [leftIh θ θ' agree, rightIh θ θ' agree]
  | imp left right leftIh rightIh =>
      intro Δ θ θ' agree
      simp only [erase, HOL.subst, Raw.subst]
      rw [leftIh θ θ' agree, rightIh θ θ' agree]
  | eq left right leftIh rightIh =>
      intro Δ θ θ' agree
      simp only [erase, HOL.subst, Raw.subst]
      rw [leftIh θ θ' agree, rightIh θ θ' agree]
  | not operand ih =>
      intro Δ θ θ' agree
      simp only [erase, HOL.subst, Raw.subst]
      rw [ih θ θ' agree]

theorem erase_instantiate {Γ : Ctx Base} {σ τ : Ty Base} (argument : Term Const Γ σ)
    (body : Term Const (σ :: Γ) τ) :
    erase (instantiate argument body) = Raw.instantiate (erase argument) (erase body) := by
  unfold instantiate Raw.instantiate
  refine erase_subst body _ _ (fun index => ?_)
  cases index with
  | vz => rfl
  | vs index => rfl

/-- **Erasure simulates beta.** -/
theorem erase_step {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (step : BetaStep source target) : RawStep (erase source) (erase target) := by
  induction step with
  | beta body argument =>
      rw [erase_instantiate]
      exact .beta _ _ _
  | appFun argument _ ih => exact .appFun _ ih
  | appArg function _ ih => exact .appArg _ ih
  | lam _ ih => exact .lam _ ih
  | andLeft right _ ih => exact .andLeft _ ih
  | andRight left _ ih => exact .andRight _ ih
  | orLeft right _ ih => exact .orLeft _ ih
  | orRight left _ ih => exact .orRight _ ih
  | impLeft right _ ih => exact .impLeft _ ih
  | impRight left _ ih => exact .impRight _ ih
  | not _ ih => exact .not ih
  | eqLeft right _ ih => exact .eqLeft _ ih
  | eqRight left _ ih => exact .eqRight _ ih
  | all _ ih => exact .all _ ih
  | ex _ ih => exact .ex _ ih

/-- **Erasure reflects beta.** Every raw step of an erased term is the erasure of
a typed step. -/
theorem erase_step_inv {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) :
    ∀ {target : Raw Base Const Γ.length}, RawStep (erase term) target →
      ∃ target', Reduces term target' ∧ erase target' = target := by
  induction term with
  | var index => intro target step; cases step
  | const constant => intro target step; cases step
  | top => intro target step; cases step
  | bot => intro target step; cases step
  | app function argument functionIh argumentIh =>
      intro target step
      change RawStep (.app (erase function) (erase argument)) target at step
      generalize erasedFunction : erase function = rawFunction at step
      cases step with
      | beta σ body _ =>
          cases function with
          | lam typedBody =>
              simp only [erase, Raw.lam.injEq] at erasedFunction
              obtain ⟨rfl, rfl⟩ := erasedFunction
              exact ⟨instantiate argument typedBody, ⟨.beta typedBody argument⟩,
                erase_instantiate _ _⟩
          | _ => simp [erase] at erasedFunction
      | appFun _ inner =>
          subst erasedFunction
          obtain ⟨function', ⟨s⟩, rfl⟩ := functionIh inner
          exact ⟨.app function' argument, ⟨.appFun argument s⟩, rfl⟩
      | appArg _ inner =>
          subst erasedFunction
          obtain ⟨argument', ⟨s⟩, rfl⟩ := argumentIh inner
          exact ⟨.app function argument', ⟨.appArg function s⟩, rfl⟩
  | lam body ih =>
      intro target step
      cases step with
      | lam _ inner =>
          obtain ⟨body', ⟨s⟩, rfl⟩ := ih inner
          exact ⟨.lam body', ⟨.lam s⟩, rfl⟩
  | and left right leftIh rightIh =>
      intro target step
      cases step with
      | andLeft _ inner =>
          obtain ⟨left', ⟨s⟩, rfl⟩ := leftIh inner
          exact ⟨.and left' right, ⟨.andLeft right s⟩, rfl⟩
      | andRight _ inner =>
          obtain ⟨right', ⟨s⟩, rfl⟩ := rightIh inner
          exact ⟨.and left right', ⟨.andRight left s⟩, rfl⟩
  | or left right leftIh rightIh =>
      intro target step
      cases step with
      | orLeft _ inner =>
          obtain ⟨left', ⟨s⟩, rfl⟩ := leftIh inner
          exact ⟨.or left' right, ⟨.orLeft right s⟩, rfl⟩
      | orRight _ inner =>
          obtain ⟨right', ⟨s⟩, rfl⟩ := rightIh inner
          exact ⟨.or left right', ⟨.orRight left s⟩, rfl⟩
  | imp left right leftIh rightIh =>
      intro target step
      cases step with
      | impLeft _ inner =>
          obtain ⟨left', ⟨s⟩, rfl⟩ := leftIh inner
          exact ⟨.imp left' right, ⟨.impLeft right s⟩, rfl⟩
      | impRight _ inner =>
          obtain ⟨right', ⟨s⟩, rfl⟩ := rightIh inner
          exact ⟨.imp left right', ⟨.impRight left s⟩, rfl⟩
  | not operand ih =>
      intro target step
      cases step with
      | not inner =>
          obtain ⟨operand', ⟨s⟩, rfl⟩ := ih inner
          exact ⟨.not operand', ⟨.not s⟩, rfl⟩
  | eq left right leftIh rightIh =>
      intro target step
      cases step with
      | eqLeft _ inner =>
          obtain ⟨left', ⟨s⟩, rfl⟩ := leftIh inner
          exact ⟨.eq left' right, ⟨.eqLeft right s⟩, rfl⟩
      | eqRight _ inner =>
          obtain ⟨right', ⟨s⟩, rfl⟩ := rightIh inner
          exact ⟨.eq left right', ⟨.eqRight left s⟩, rfl⟩
  | all body ih =>
      intro target step
      cases step with
      | all _ inner =>
          obtain ⟨body', ⟨s⟩, rfl⟩ := ih inner
          exact ⟨.all body', ⟨.all s⟩, rfl⟩
  | ex body ih =>
      intro target step
      cases step with
      | ex _ inner =>
          obtain ⟨body', ⟨s⟩, rfl⟩ := ih inner
          exact ⟨.ex body', ⟨.ex s⟩, rfl⟩

theorem erase_star {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (many : ReducesStar source target) :
    Relation.ReflTransGen RawStep (erase source) (erase target) := by
  induction many with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (let ⟨s⟩ := step; erase_step s)

theorem erase_star_inv {Γ : Ctx Base} {τ : Ty Base} {source : Term Const Γ τ}
    {target : Raw Base Const Γ.length} (many : Relation.ReflTransGen RawStep (erase source) target) :
    ∃ target', ReducesStar source target' ∧ erase target' = target := by
  induction many with
  | refl => exact ⟨source, .refl, rfl⟩
  | tail _ step ih =>
      obtain ⟨middle, toMiddle, rfl⟩ := ih
      obtain ⟨target', reduces, rfl⟩ := erase_step_inv middle step
      exact ⟨target', toMiddle.tail reduces, rfl⟩

/-! ## The fragment test -/

section Elaboration

variable [DecidableEq Base]

/-- Apply a typed function to a typed argument when the types fit. -/
def applyChecked {Γ : Ctx Base} : (functionType : Ty Base) → Term Const Γ functionType →
    (argumentType : Ty Base) → Term Const Γ argumentType → Option (Σ τ : Ty Base, Term Const Γ τ)
  | .arr domain codomain, function, argumentType, argument =>
      if same : argumentType = domain then some ⟨codomain, .app function (same ▸ argument)⟩
      else none
  | _, _, _, _ => none

/-- A typed term read as a formula, when its type is the proposition type. -/
def asFormula {Γ : Ctx Base} : (Σ τ : Ty Base, Term Const Γ τ) → Option (Formula Const Γ)
  | ⟨.prop, formula⟩ => some formula
  | _ => none

/-- Two typed terms of one type, when their types agree. -/
def equation {Γ : Ctx Base} : (Σ τ : Ty Base, Term Const Γ τ) → (Σ τ : Ty Base, Term Const Γ τ) →
    Option (Formula Const Γ)
  | ⟨leftType, left⟩, ⟨rightType, right⟩ =>
      if same : rightType = leftType then some (.eq left (same ▸ right)) else none

/-- **The fragment test.** One syntax-directed pass reads the binder hints and
either returns the typed term whose erasure is the certificate or refuses. -/
def elaborate? : (Γ : Ctx Base) → Raw Base Const Γ.length → Option (Σ τ : Ty Base, Term Const Γ τ)
  | Γ, .var position => some ⟨Γ.get position, .var (Var.ofFin Γ position)⟩
  | _, .const τ constant => some ⟨τ, .const constant⟩
  | Γ, .app function argument => do
      let ⟨functionType, typedFunction⟩ ← elaborate? Γ function
      let ⟨argumentType, typedArgument⟩ ← elaborate? Γ argument
      applyChecked functionType typedFunction argumentType typedArgument
  | Γ, .lam σ body => do
      let ⟨bodyType, typedBody⟩ ← elaborate? (σ :: Γ) body
      some ⟨σ ⇒ bodyType, .lam typedBody⟩
  | _, .top => some ⟨.prop, .top⟩
  | _, .bot => some ⟨.prop, .bot⟩
  | Γ, .and left right => do
      let left ← (elaborate? Γ left).bind asFormula
      let right ← (elaborate? Γ right).bind asFormula
      some ⟨.prop, .and left right⟩
  | Γ, .or left right => do
      let left ← (elaborate? Γ left).bind asFormula
      let right ← (elaborate? Γ right).bind asFormula
      some ⟨.prop, .or left right⟩
  | Γ, .imp left right => do
      let left ← (elaborate? Γ left).bind asFormula
      let right ← (elaborate? Γ right).bind asFormula
      some ⟨.prop, .imp left right⟩
  | Γ, .not operand => do
      let operand ← (elaborate? Γ operand).bind asFormula
      some ⟨.prop, .not operand⟩
  | Γ, .eq left right => do
      let left ← elaborate? Γ left
      let right ← elaborate? Γ right
      let formula ← equation left right
      some ⟨.prop, formula⟩
  | Γ, .all σ body => do
      let body ← (elaborate? (σ :: Γ) body).bind asFormula
      some ⟨.prop, .all body⟩
  | Γ, .ex σ body => do
      let body ← (elaborate? (σ :: Γ) body).bind asFormula
      some ⟨.prop, .ex body⟩

omit [DecidableEq Base] in
theorem Var.toFin_ofFin : (Γ : Ctx Base) → (position : Fin Γ.length) →
    (Var.ofFin Γ position).toFin = position
  | _ :: _, ⟨0, _⟩ => rfl
  | _ :: Γ, ⟨position + 1, bound⟩ => by
      simp only [Var.ofFin, Var.toFin]
      rw [Var.toFin_ofFin Γ ⟨position, Nat.lt_of_succ_lt_succ bound⟩]
      rfl

omit [DecidableEq Base] in
theorem erase_cast {Γ : Ctx Base} {σ τ : Ty Base} (same : σ = τ) (term : Term Const Γ σ) :
    erase (same ▸ term) = erase term := by
  subst same
  rfl

theorem applyChecked_sound {Γ : Ctx Base} {functionType argumentType : Ty Base}
    {function : Term Const Γ functionType} {argument : Term Const Γ argumentType}
    {result : Σ τ : Ty Base, Term Const Γ τ}
    (checked : applyChecked functionType function argumentType argument = some result) :
    erase result.2 = .app (erase function) (erase argument) := by
  cases functionType with
  | arr domain codomain =>
      simp only [applyChecked] at checked
      split at checked
      · rename_i same
        simp only [Option.some.injEq] at checked
        subst checked
        simp only [erase, erase_cast]
      · simp at checked
  | _ => simp [applyChecked] at checked

omit [DecidableEq Base] in
theorem asFormula_sound {Γ : Ctx Base} {typed : Σ τ : Ty Base, Term Const Γ τ}
    {formula : Formula Const Γ} (read : asFormula typed = some formula) :
    erase formula = erase typed.2 := by
  obtain ⟨τ, term⟩ := typed
  cases τ with
  | prop =>
      simp only [asFormula, Option.some.injEq] at read
      subst read
      rfl
  | _ => simp [asFormula] at read

theorem equation_sound {Γ : Ctx Base} {left right : Σ τ : Ty Base, Term Const Γ τ}
    {formula : Formula Const Γ} (formed : equation left right = some formula) :
    erase formula = .eq (erase left.2) (erase right.2) := by
  obtain ⟨leftType, left⟩ := left
  obtain ⟨rightType, right⟩ := right
  simp only [equation] at formed
  split at formed
  · rename_i same
    simp only [Option.some.injEq] at formed
    subst formed
    simp only [erase, erase_cast]
  · simp at formed

/-- **The test is sound.** An elaborated term erases to the certificate. -/
theorem elaborate?_sound (Γ : Ctx Base) (raw : Raw Base Const Γ.length) :
    ∀ {result : Σ τ : Ty Base, Term Const Γ τ}, elaborate? Γ raw = some result →
      erase result.2 = raw := by
  induction Γ, raw using elaborate?.induct with
  | case1 Γ position =>
      intro result elaborated
      simp only [elaborate?, Option.some.injEq] at elaborated
      subst elaborated
      exact congrArg Raw.var (Var.toFin_ofFin Γ position)
  | case2 Γ τ constant =>
      intro result elaborated
      simp only [elaborate?, Option.some.injEq] at elaborated
      subst elaborated
      rfl
  | case3 Γ function argument functionIh argumentIh =>
      intro result elaborated
      simp only [elaborate?, Option.bind_eq_bind, Option.bind_eq_some_iff] at elaborated
      obtain ⟨⟨functionType, typedFunction⟩, functionElaborated, ⟨argumentType, typedArgument⟩,
        argumentElaborated, applied⟩ := elaborated
      rw [applyChecked_sound applied, functionIh functionElaborated, argumentIh argumentElaborated]
  | case4 Γ σ body ih =>
      intro result elaborated
      simp only [elaborate?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
        at elaborated
      obtain ⟨⟨bodyType, typedBody⟩, bodyElaborated, rfl⟩ := elaborated
      exact congrArg (Raw.lam σ) (ih bodyElaborated)
  | case5 Γ =>
      intro result elaborated
      simp only [elaborate?, Option.some.injEq] at elaborated
      subst elaborated
      rfl
  | case6 Γ =>
      intro result elaborated
      simp only [elaborate?, Option.some.injEq] at elaborated
      subst elaborated
      rfl
  | case7 Γ left right leftIh rightIh | case8 Γ left right leftIh rightIh
  | case9 Γ left right leftIh rightIh =>
      intro result elaborated
      simp only [elaborate?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
        at elaborated
      obtain ⟨leftFormula, ⟨leftTyped, leftElaborated, leftRead⟩, rightFormula,
        ⟨rightTyped, rightElaborated, rightRead⟩, rfl⟩ := elaborated
      simp only [erase, asFormula_sound leftRead, asFormula_sound rightRead,
        leftIh leftElaborated, rightIh rightElaborated]
  | case10 Γ operand ih =>
      intro result elaborated
      simp only [elaborate?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
        at elaborated
      obtain ⟨formula, ⟨typed, elaboratedOperand, read⟩, rfl⟩ := elaborated
      simp only [erase, asFormula_sound read, ih elaboratedOperand]
  | case11 Γ left right leftIh rightIh =>
      intro result elaborated
      simp only [elaborate?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
        at elaborated
      obtain ⟨leftTyped, leftElaborated, rightTyped, rightElaborated, formula, formed, rfl⟩ :=
        elaborated
      simp only [equation_sound formed, leftIh leftElaborated, rightIh rightElaborated]
  | case12 Γ σ body ih | case13 Γ σ body ih =>
      intro result elaborated
      simp only [elaborate?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
        at elaborated
      obtain ⟨formula, ⟨typed, elaboratedBody, read⟩, rfl⟩ := elaborated
      simp only [erase, asFormula_sound read, ih elaboratedBody]

/-- **The test is complete for erasures.** Every typed term passes the test on
its own erasure and is recovered exactly. -/
theorem elaborate?_erase {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) :
    elaborate? Γ (erase term) = some ⟨τ, term⟩ := by
  induction term with
  | var index =>
      simp only [erase, elaborate?]
      apply congrArg some
      have types := Var.get_toFin index
      have recovered := Var.ofFin_toFin index
      revert recovered
      generalize Var.ofFin _ index.toFin = found
      revert found
      rw [types]
      intro found same
      cases same
      rfl
  | const constant => simp [erase, elaborate?]
  | app function argument functionIh argumentIh =>
      simp [erase, elaborate?, functionIh, argumentIh, applyChecked]
  | lam body ih => simp [erase, elaborate?, ih]
  | top => simp [erase, elaborate?]
  | bot => simp [erase, elaborate?]
  | and left right leftIh rightIh => simp [erase, elaborate?, leftIh, rightIh, asFormula]
  | or left right leftIh rightIh => simp [erase, elaborate?, leftIh, rightIh, asFormula]
  | imp left right leftIh rightIh => simp [erase, elaborate?, leftIh, rightIh, asFormula]
  | not operand ih => simp [erase, elaborate?, ih, asFormula]
  | eq left right leftIh rightIh => simp [erase, elaborate?, leftIh, rightIh, equation]
  | all body ih => simp [erase, elaborate?, ih, asFormula]
  | ex body ih => simp [erase, elaborate?, ih, asFormula]

/-- Erasure is injective on terms of one type. -/
theorem erase_injective {Γ : Ctx Base} {τ : Ty Base} {first second : Term Const Γ τ}
    (same : erase first = erase second) : first = second := by
  have firstBack := elaborate?_erase first
  rw [same, elaborate?_erase second] at firstBack
  exact (eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj firstBack)).2).symm

end Elaboration

/-! ## The fragment-aware checker -/

/-- The verdict of the fragment-aware checker. -/
inductive Verdict where
  | accepted
  | refused
  | outsideFragment
  deriving DecidableEq, Repr

section Checker

variable [DecidableEq Base] [∀ τ, DecidableEq (Const τ)]

omit [∀ τ, DecidableEq (Const τ)] in
/-- Typed terms are convertible exactly when their erasures are. -/
theorem rawJoinable_erase_iff {Γ : Ctx Base} {τ : Ty Base} (left right : Term Const Γ τ) :
    RawJoinable (erase left) (erase right) ↔ Joinable left right := by
  constructor
  · rintro ⟨meet, leftMeet, rightMeet⟩
    obtain ⟨leftEnd, leftMany, leftErased⟩ := erase_star_inv leftMeet
    obtain ⟨rightEnd, rightMany, rightErased⟩ := erase_star_inv rightMeet
    have same := erase_injective (leftErased.trans rightErased.symm)
    subst same
    exact ⟨leftEnd, star_execution leftMany, star_execution rightMany⟩
  · rintro ⟨meet, ⟨leftRun⟩, ⟨rightRun⟩⟩
    exact ⟨erase meet, erase_star (execution_star leftRun), erase_star (execution_star rightRun)⟩

omit [∀ τ, DecidableEq (Const τ)] in
/-- Terms of different types have no common raw reduct. -/
theorem not_rawJoinable_of_types {Γ : Ctx Base} {σ τ : Ty Base} (different : σ ≠ τ)
    (left : Term Const Γ σ) (right : Term Const Γ τ) :
    ¬ RawJoinable (erase left) (erase right) := by
  rintro ⟨meet, leftMeet, rightMeet⟩
  obtain ⟨leftEnd, _, leftErased⟩ := erase_star_inv leftMeet
  obtain ⟨rightEnd, _, rightErased⟩ := erase_star_inv rightMeet
  have leftBack := elaborate?_erase leftEnd
  have rightBack := elaborate?_erase rightEnd
  rw [leftErased] at leftBack
  rw [rightErased, leftBack] at rightBack
  exact different (Sigma.mk.inj_iff.mp (Option.some.inj rightBack)).1

/-- Decide a raw conversion claim. Inside the simply typed fragment the normal
forms are computed with the least budgets; outside it the checker refuses
before any conversion is attempted. -/
def check (Γ : Ctx Base) (left right : Raw Base Const Γ.length) : Verdict :=
  match elaborate? Γ left, elaborate? Γ right with
  | some ⟨leftType, leftTerm⟩, some ⟨rightType, rightTerm⟩ =>
      if same : rightType = leftType then
        if normalForm leftTerm = normalForm (same ▸ rightTerm) then .accepted else .refused
      else .refused
  | _, _ => .outsideFragment

theorem check_outside {Γ : Ctx Base} {left right : Raw Base Const Γ.length} :
    check Γ left right = .outsideFragment ↔
      elaborate? Γ left = none ∨ elaborate? Γ right = none := by
  unfold check
  split
  · rename_i leftType leftTerm rightType rightTerm leftElaborated rightElaborated
    simp only [leftElaborated, rightElaborated, reduceCtorEq, or_self, iff_false]
    split
    · split <;> simp
    · simp
  · rename_i notBoth
    simp only [true_iff]
    by_contra both
    push Not at both
    obtain ⟨⟨leftType, leftTerm⟩, leftElaborated⟩ := Option.ne_none_iff_exists'.mp both.1
    obtain ⟨⟨rightType, rightTerm⟩, rightElaborated⟩ := Option.ne_none_iff_exists'.mp both.2
    exact notBoth leftType leftTerm rightType rightTerm leftElaborated rightElaborated

/-- **Inside the fragment the checker decides raw convertibility.** -/
theorem check_accepted_iff {Γ : Ctx Base} {left right : Raw Base Const Γ.length}
    (leftTyped : (elaborate? Γ left).isSome) (rightTyped : (elaborate? Γ right).isSome) :
    check Γ left right = .accepted ↔ RawJoinable left right := by
  obtain ⟨⟨leftType, leftTerm⟩, leftElaborated⟩ := Option.isSome_iff_exists.mp leftTyped
  obtain ⟨⟨rightType, rightTerm⟩, rightElaborated⟩ := Option.isSome_iff_exists.mp rightTyped
  have leftErased := elaborate?_sound Γ left leftElaborated
  have rightErased := elaborate?_sound Γ right rightElaborated
  simp only at leftErased rightErased
  subst leftErased rightErased
  unfold check
  rw [leftElaborated, rightElaborated]
  simp only
  split
  · rename_i same
    subst same
    rw [rawJoinable_erase_iff, joinable_iff_normalForm]
    split <;> simp_all
  · rename_i different
    simp only [reduceCtorEq, false_iff]
    exact not_rawJoinable_of_types (Ne.symm different) leftTerm rightTerm

/-- **Acceptance is sound for raw conversion,** with no assumption. -/
theorem check_sound {Γ : Ctx Base} {left right : Raw Base Const Γ.length}
    (accepted : check Γ left right = .accepted) : RawJoinable left right := by
  have inside : ¬ (elaborate? Γ left = none ∨ elaborate? Γ right = none) := by
    rw [← check_outside, accepted]
    exact fun same => nomatch same
  push Not at inside
  exact (check_accepted_iff (Option.isSome_iff_ne_none.mpr inside.1)
    (Option.isSome_iff_ne_none.mpr inside.2)).mp accepted

/-- **Refusal inside the fragment is a disproof of raw convertibility.** -/
theorem check_refused {Γ : Ctx Base} {left right : Raw Base Const Γ.length}
    (refused : check Γ left right = .refused) : ¬ RawJoinable left right := by
  have inside : ¬ (elaborate? Γ left = none ∨ elaborate? Γ right = none) := by
    rw [← check_outside, refused]
    exact fun same => nomatch same
  push Not at inside
  intro joinable
  have accepted := (check_accepted_iff (Option.isSome_iff_ne_none.mpr inside.1)
    (Option.isSome_iff_ne_none.mpr inside.2)).mpr joinable
  rw [refused] at accepted
  exact nomatch accepted

end Checker

/-! ## Controls -/

namespace Controls

open ContextualTrinity.Controls (NoConstant)

instance : ∀ τ, DecidableEq (NoConstant τ) := fun _ => inferInstanceAs (DecidableEq Empty)

abbrev ι : Ty Unit := .base ()

/-- `λx:σ. x x`. -/
abbrev selfApplication (σ : Ty Unit) : Raw Unit NoConstant 0 := .lam σ (.app (.var 0) (.var 0))

/-- `(λx:σ. x x) (λx:σ. x x)`. -/
abbrev omega (σ : Ty Unit) : Raw Unit NoConstant 0 := .app (selfApplication σ) (selfApplication σ)

theorem arr_ne_left (σ τ : Ty Unit) : σ ⇒ τ ≠ σ := by
  intro same
  have sizes := congrArg sizeOf same
  simp at sizes
  omega

/-- No hint types the self-application. -/
theorem selfApplication_untypable (σ : Ty Unit) : elaborate? [] (selfApplication σ) = none := by
  cases σ with
  | arr domain codomain =>
      have different : domain ⇒ codomain ≠ domain := arr_ne_left domain codomain
      simp [elaborate?, applyChecked, different]
  | _ => simp [elaborate?, applyChecked]

theorem omega_untypable (σ : Ty Unit) : elaborate? [] (omega σ) = none := by
  simp [elaborate?, selfApplication_untypable]

/-- **`Ω` reduces only to itself.** -/
theorem omega_step_iff (σ : Ty Unit) (target : Raw Unit NoConstant 0) :
    RawStep (omega σ) target ↔ target = omega σ := by
  constructor
  · intro step
    cases step with
    | beta => rfl
    | appFun _ inner =>
        cases inner with
        | lam _ body =>
            cases body with
            | appFun _ variable_ => cases variable_
            | appArg _ variable_ => cases variable_
    | appArg _ inner =>
        cases inner with
        | lam _ body =>
            cases body with
            | appFun _ variable_ => cases variable_
            | appArg _ variable_ => cases variable_
  · rintro rfl
    exact .beta _ _ _

/-- **Raw conversion of `Ω` diverges.** Every reduct of `Ω` is `Ω` and reduces
again, so no budget reaches a normal form. -/
theorem omega_diverges (σ : Ty Unit) {target : Raw Unit NoConstant 0}
    (many : Relation.ReflTransGen RawStep (omega σ) target) :
    target = omega σ ∧ RawStep target (omega σ) := by
  induction many with
  | refl => exact ⟨rfl, (omega_step_iff σ _).mpr rfl⟩
  | tail _ step ih =>
      obtain ⟨rfl, _⟩ := ih
      have same := (omega_step_iff σ _).mp step
      subst same
      exact ⟨rfl, (omega_step_iff σ _).mpr rfl⟩

/-- **`Ω` is refused before any conversion is attempted, whatever its hint.** -/
theorem omega_outside (σ : Ty Unit) (other : Raw Unit NoConstant 0) :
    check [] (omega σ) other = .outsideFragment :=
  check_outside.mpr (.inl (omega_untypable σ))

/-- `(λp:prop. p) ⊤` -/
abbrev identityRedex : Raw Unit NoConstant 0 := .app (.lam .prop (.var 0)) .top

/-- **Positive control.** A hinted redex is accepted against its contractum. -/
theorem identityRedex_accepted : check [] identityRedex .top = .accepted :=
  (check_accepted_iff (by simp [elaborate?, applyChecked]) (by simp [elaborate?])).mpr
    ⟨.top, .single (.beta _ _ _), .refl⟩

/-- A typed claim that does not hold is refused inside the fragment. -/
theorem top_bot_refused : check (Const := NoConstant) [] .top .bot = .refused := by
  have notJoinable : ¬ RawJoinable (Base := Unit) (Const := NoConstant) (n := 0) .top .bot := by
    rintro ⟨meet, topMeet, botMeet⟩
    have topStays : meet = .top := by
      cases topMeet.cases_head with
      | inl same => exact same.symm
      | inr more => obtain ⟨_, step, _⟩ := more; cases step
    have botStays : meet = .bot := by
      cases botMeet.cases_head with
      | inl same => exact same.symm
      | inr more => obtain ⟨_, step, _⟩ := more; cases step
    rw [topStays] at botStays
    exact nomatch botStays
  have inside : (elaborate? (Const := NoConstant) [] .top).isSome ∧
      (elaborate? (Const := NoConstant) [] .bot).isSome := by simp [elaborate?]
  cases verdict : check (Const := NoConstant) [] .top .bot with
  | accepted => exact absurd (check_sound verdict) notJoinable
  | refused => rfl
  | outsideFragment =>
      rcases check_outside.mp verdict with untyped | untyped <;> simp [elaborate?] at untyped

/-- **Hints matter.** A wrong binder hint puts an ordinary redex outside the
fragment, although its raw reduction terminates. -/
theorem wrongHint_outside :
    check [] (.app (.lam ι (.var 0)) .top : Raw Unit NoConstant 0) .top = .outsideFragment ∧
      RawStep (.app (.lam ι (.var 0)) .top : Raw Unit NoConstant 0) .top := by
  refine ⟨check_outside.mpr (.inl ?_), .beta _ _ _⟩
  simp [elaborate?, applyChecked]

end Controls

#print axioms elaborate?_sound
#print axioms elaborate?_erase
#print axioms check_accepted_iff
#print axioms check_sound
#print axioms check_refused
#print axioms Controls.omega_diverges
#print axioms Controls.omega_outside
#print axioms Controls.identityRedex_accepted
#print axioms Controls.top_bot_refused
#print axioms Controls.wrongHint_outside

end Mettapedia.Logic.HOL.CheckableFragment

