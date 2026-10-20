import Mettapedia.Logic.HOL.Syntax.Closed

/-!
# Full type structures over an arbitrary logical interpretation

Many semantics of the HOL calculus have one shape: a function type denotes the
full function space, a base type denotes a given carrier, the proposition type
denotes a carrier of truth values, and each logical term former denotes an
operation on that carrier (a quantifier receives the predicate on the carrier
of the bound type).  This file states that shape once, defines denotation by
structural recursion on terms, and proves that denotation commutes with
renaming and substitution.

None of these lemmas uses a property of the operations, so they hold for
two-valued, Kripke, and Heyting-valued readings alike.  Which elements a
quantifier ranges over is part of the operation `all`/`ex`, not of the carrier.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Full function-space carriers over truth values `P` and base carriers `C`. -/
def Ty.full (P : Type w) (C : Base → Type w) : Ty Base → Type w
  | .prop => P
  | .base b => C b
  | .arr σ τ => Ty.full P C σ → Ty.full P C τ

/-- An interpretation of the HOL term formers over full function spaces: truth
values, base carriers, one operation for each logical term former, and the
denotations of the constants. -/
structure FullTypeStructure (Base : Type u) (Const : Ty Base → Type v) where
  Truth : Type w
  Carrier : Base → Type w
  top : Truth
  bot : Truth
  and : Truth → Truth → Truth
  or : Truth → Truth → Truth
  imp : Truth → Truth → Truth
  not : Truth → Truth
  eq : (τ : Ty Base) → Ty.full Truth Carrier τ → Ty.full Truth Carrier τ → Truth
  all : (σ : Ty Base) → (Ty.full Truth Carrier σ → Truth) → Truth
  ex : (σ : Ty Base) → (Ty.full Truth Carrier σ → Truth) → Truth
  const : {τ : Ty Base} → Const τ → Ty.full Truth Carrier τ

namespace FullTypeStructure

variable (S : FullTypeStructure.{u, v, w} Base Const)

/-- The carrier of a type. -/
abbrev Den (τ : Ty Base) : Type w := Ty.full S.Truth S.Carrier τ

/-- Valuations of a context. -/
abbrev Valuation (Γ : Ctx Base) := ∀ {τ}, Var Γ τ → S.Den τ

/-- Extend a valuation by a value for the newest variable. -/
def extend {Γ : Ctx Base} {σ : Ty Base} (ρ : S.Valuation Γ) (d : S.Den σ) :
    S.Valuation (σ :: Γ)
  | _, .vz => d
  | _, .vs v => ρ v

@[simp] theorem extend_vz {Γ : Ctx Base} {σ : Ty Base} (ρ : S.Valuation Γ)
    (d : S.Den σ) : S.extend ρ d Var.vz = d := rfl

@[simp] theorem extend_vs {Γ : Ctx Base} {σ τ : Ty Base} (ρ : S.Valuation Γ)
    (d : S.Den σ) (v : Var Γ τ) : S.extend ρ d (Var.vs v) = ρ v := rfl

/-- The valuation of the empty context. -/
def emptyVal : S.Valuation [] := fun v => nomatch v

/-- Denotation, by structural recursion on terms. -/
def denote : {Γ : Ctx Base} → {τ : Ty Base} →
    Term Const Γ τ → S.Valuation Γ → S.Den τ
  | _, _, .var v, ρ => ρ v
  | _, _, .const c, _ => S.const c
  | _, _, .app f t, ρ => (denote f ρ) (denote t ρ)
  | _, _, .lam t, ρ => fun d => denote t (S.extend ρ d)
  | _, _, .top, _ => S.top
  | _, _, .bot, _ => S.bot
  | _, _, .and φ ψ, ρ => S.and (denote φ ρ) (denote ψ ρ)
  | _, _, .or φ ψ, ρ => S.or (denote φ ρ) (denote ψ ρ)
  | _, _, .imp φ ψ, ρ => S.imp (denote φ ρ) (denote ψ ρ)
  | _, _, .not φ, ρ => S.not (denote φ ρ)
  | _, _, .eq (τ := τ) t u, ρ => S.eq τ (denote t ρ) (denote u ρ)
  | _, _, .all (σ := σ) φ, ρ => S.all σ (fun d => denote φ (S.extend ρ d))
  | _, _, .ex (σ := σ) φ, ρ => S.ex σ (fun d => denote φ (S.extend ρ d))

section Equations

variable {Γ : Ctx Base} (ρ : S.Valuation Γ)

@[simp] theorem denote_var {τ : Ty Base} (v : Var Γ τ) :
    S.denote (.var v : Term Const Γ τ) ρ = ρ v := rfl

@[simp] theorem denote_const {τ : Ty Base} (c : Const τ) :
    S.denote (.const c : Term Const Γ τ) ρ = S.const c := rfl

@[simp] theorem denote_app {σ τ : Ty Base} (f : Term Const Γ (σ ⇒ τ))
    (t : Term Const Γ σ) :
    S.denote (.app f t) ρ = (S.denote f ρ) (S.denote t ρ) := rfl

@[simp] theorem denote_lam {σ τ : Ty Base} (t : Term Const (σ :: Γ) τ) :
    S.denote (.lam t) ρ = fun d => S.denote t (S.extend ρ d) := rfl

@[simp] theorem denote_top : S.denote (.top : Formula Const Γ) ρ = S.top := rfl

@[simp] theorem denote_bot : S.denote (.bot : Formula Const Γ) ρ = S.bot := rfl

@[simp] theorem denote_and (φ ψ : Formula Const Γ) :
    S.denote (.and φ ψ) ρ = S.and (S.denote φ ρ) (S.denote ψ ρ) := rfl

@[simp] theorem denote_or (φ ψ : Formula Const Γ) :
    S.denote (.or φ ψ) ρ = S.or (S.denote φ ρ) (S.denote ψ ρ) := rfl

@[simp] theorem denote_imp (φ ψ : Formula Const Γ) :
    S.denote (.imp φ ψ) ρ = S.imp (S.denote φ ρ) (S.denote ψ ρ) := rfl

@[simp] theorem denote_not (φ : Formula Const Γ) :
    S.denote (.not φ) ρ = S.not (S.denote φ ρ) := rfl

@[simp] theorem denote_eq {τ : Ty Base} (t u : Term Const Γ τ) :
    S.denote (.eq t u) ρ = S.eq τ (S.denote t ρ) (S.denote u ρ) := rfl

@[simp] theorem denote_all {σ : Ty Base} (φ : Formula Const (σ :: Γ)) :
    S.denote (.all φ) ρ = S.all σ (fun d => S.denote φ (S.extend ρ d)) := rfl

@[simp] theorem denote_ex {σ : Ty Base} (φ : Formula Const (σ :: Γ)) :
    S.denote (.ex φ) ρ = S.ex σ (fun d => S.denote φ (S.extend ρ d)) := rfl

end Equations

/-! ## The substitution kit -/

/-- Denotation depends only on the values of the valuation. -/
theorem denote_ext {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    ∀ {ρ₁ ρ₂ : S.Valuation Γ}, (∀ {σ} (v : Var Γ σ), ρ₁ v = ρ₂ v) →
      S.denote t ρ₁ = S.denote t ρ₂ := by
  have hext : ∀ {Γ : Ctx Base} {σ : Ty Base} {ρ₁ ρ₂ : S.Valuation Γ},
      (∀ {τ} (v : Var Γ τ), ρ₁ v = ρ₂ v) →
        ∀ (d : S.Den σ) {τ} (v : Var (σ :: Γ) τ),
        S.extend ρ₁ d v = S.extend ρ₂ d v := by
    intro Γ σ ρ₁ ρ₂ h d τ v
    cases v with
    | vz => rfl
    | vs v => exact h v
  induction t with
  | var v => intro ρ₁ ρ₂ h; exact h v
  | const c => intro ρ₁ ρ₂ _; rfl
  | app f t ihf iht => intro ρ₁ ρ₂ h; simp only [denote_app, ihf h, iht h]
  | lam t iht => intro ρ₁ ρ₂ h; funext d; exact iht (hext h d)
  | top => intro ρ₁ ρ₂ _; rfl
  | bot => intro ρ₁ ρ₂ _; rfl
  | and φ ψ ihφ ihψ =>
      intro ρ₁ ρ₂ h
      show S.and _ _ = S.and _ _
      exact congr (congrArg S.and (ihφ h)) (ihψ h)
  | or φ ψ ihφ ihψ =>
      intro ρ₁ ρ₂ h
      show S.or _ _ = S.or _ _
      exact congr (congrArg S.or (ihφ h)) (ihψ h)
  | imp φ ψ ihφ ihψ =>
      intro ρ₁ ρ₂ h
      show S.imp _ _ = S.imp _ _
      exact congr (congrArg S.imp (ihφ h)) (ihψ h)
  | not φ ihφ => intro ρ₁ ρ₂ h; exact congrArg S.not (ihφ h)
  | eq t u iht ihu =>
      intro ρ₁ ρ₂ h
      show S.eq _ _ _ = S.eq _ _ _
      exact congr (congrArg (S.eq _) (iht h)) (ihu h)
  | all φ ihφ =>
      intro ρ₁ ρ₂ h
      simp only [denote_all]
      exact congrArg _ (funext fun d => ihφ (hext h d))
  | ex φ ihφ =>
      intro ρ₁ ρ₂ h
      simp only [denote_ex]
      exact congrArg _ (funext fun d => ihφ (hext h d))

/-- Denotation commutes with renaming. -/
theorem denote_rename {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    ∀ {Δ : Ctx Base} (r : Rename Base Γ Δ) (ρ : S.Valuation Δ),
      S.denote (rename r t) ρ = S.denote t (fun v => ρ (r v)) := by
  have hlift : ∀ {Γ Δ : Ctx Base} {σ : Ty Base} (r : Rename Base Γ Δ)
      (ρ : S.Valuation Δ) (d : S.Den σ) {τ} (v : Var (σ :: Γ) τ),
        S.extend ρ d (Rename.lift r v) = S.extend (fun v => ρ (r v)) d v := by
    intro Γ Δ σ r ρ d τ v
    cases v <;> rfl
  induction t with
  | var v => intro Δ r ρ; rfl
  | const c => intro Δ r ρ; rfl
  | app f t ihf iht =>
      intro Δ r ρ
      simp only [rename, denote_app, ihf r ρ, iht r ρ]
  | lam t iht =>
      intro Δ r ρ
      funext d
      exact (iht (Rename.lift r) (S.extend ρ d)).trans
        (S.denote_ext t (hlift r ρ d))
  | top => intro Δ r ρ; rfl
  | bot => intro Δ r ρ; rfl
  | and φ ψ ihφ ihψ =>
      intro Δ r ρ; show S.and _ _ = S.and _ _; exact congr (congrArg S.and (ihφ r ρ)) (ihψ r ρ)
  | or φ ψ ihφ ihψ =>
      intro Δ r ρ; show S.or _ _ = S.or _ _; exact congr (congrArg S.or (ihφ r ρ)) (ihψ r ρ)
  | imp φ ψ ihφ ihψ =>
      intro Δ r ρ; show S.imp _ _ = S.imp _ _; exact congr (congrArg S.imp (ihφ r ρ)) (ihψ r ρ)
  | not φ ihφ =>
      intro Δ r ρ; exact congrArg S.not (ihφ r ρ)
  | eq t u iht ihu =>
      intro Δ r ρ; show S.eq _ _ _ = S.eq _ _ _; exact congr (congrArg (S.eq _) (iht r ρ)) (ihu r ρ)
  | all φ ihφ =>
      intro Δ r ρ
      simp only [rename, denote_all]
      exact congrArg _ (funext fun d =>
        (ihφ (Rename.lift r) (S.extend ρ d)).trans (S.denote_ext φ (hlift r ρ d)))
  | ex φ ihφ =>
      intro Δ r ρ
      simp only [rename, denote_ex]
      exact congrArg _ (funext fun d =>
        (ihφ (Rename.lift r) (S.extend ρ d)).trans (S.denote_ext φ (hlift r ρ d)))

/-- A weakened term ignores the newest entry of the valuation. -/
theorem denote_weaken {Γ : Ctx Base} {σ τ : Ty Base}
    (t : Term Const Γ τ) (ρ : S.Valuation Γ) (d : S.Den σ) :
    S.denote (weaken (σ := σ) t) (S.extend ρ d) = S.denote t ρ := by
  unfold weaken
  exact (S.denote_rename t (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))
      (S.extend ρ d)).trans (S.denote_ext t (by intro σ' v; rfl))

/-- Denotation commutes with substitution. -/
theorem denote_subst {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    ∀ {Δ : Ctx Base} (σs : Subst Const Γ Δ) (ρ : S.Valuation Δ),
      S.denote (subst σs t) ρ = S.denote t (fun v => S.denote (σs v) ρ) := by
  have hlift : ∀ {Γ Δ : Ctx Base} {σ : Ty Base} (σs : Subst Const Γ Δ)
      (ρ : S.Valuation Δ) (d : S.Den σ) {τ} (v : Var (σ :: Γ) τ),
        S.denote (Subst.lift σs v) (S.extend ρ d) =
          S.extend (fun v => S.denote (σs v) ρ) d v := by
    intro Γ Δ σ σs ρ d τ v
    cases v with
    | vz => rfl
    | vs v => exact S.denote_weaken (σs v) ρ d
  induction t with
  | var v => intro Δ σs ρ; rfl
  | const c => intro Δ σs ρ; rfl
  | app f t ihf iht =>
      intro Δ σs ρ
      simp only [subst, denote_app, ihf σs ρ, iht σs ρ]
  | lam t iht =>
      intro Δ σs ρ
      funext d
      exact (iht (Subst.lift σs) (S.extend ρ d)).trans
        (S.denote_ext t (hlift σs ρ d))
  | top => intro Δ σs ρ; rfl
  | bot => intro Δ σs ρ; rfl
  | and φ ψ ihφ ihψ =>
      intro Δ σs ρ; show S.and _ _ = S.and _ _; exact congr (congrArg S.and (ihφ σs ρ)) (ihψ σs ρ)
  | or φ ψ ihφ ihψ =>
      intro Δ σs ρ; show S.or _ _ = S.or _ _; exact congr (congrArg S.or (ihφ σs ρ)) (ihψ σs ρ)
  | imp φ ψ ihφ ihψ =>
      intro Δ σs ρ; show S.imp _ _ = S.imp _ _; exact congr (congrArg S.imp (ihφ σs ρ)) (ihψ σs ρ)
  | not φ ihφ =>
      intro Δ σs ρ; exact congrArg S.not (ihφ σs ρ)
  | eq t u iht ihu =>
      intro Δ σs ρ
      show S.eq _ _ _ = S.eq _ _ _
      exact congr (congrArg (S.eq _) (iht σs ρ)) (ihu σs ρ)
  | all φ ihφ =>
      intro Δ σs ρ
      simp only [subst, denote_all]
      exact congrArg _ (funext fun d =>
        (ihφ (Subst.lift σs) (S.extend ρ d)).trans (S.denote_ext φ (hlift σs ρ d)))
  | ex φ ihφ =>
      intro Δ σs ρ
      simp only [subst, denote_ex]
      exact congrArg _ (funext fun d =>
        (ihφ (Subst.lift σs) (S.extend ρ d)).trans (S.denote_ext φ (hlift σs ρ d)))

/-- Instantiating the newest variable denotes as extending the valuation by
the denotation of the instantiating term. -/
theorem denote_instantiate {Γ : Ctx Base} {σ τ : Ty Base}
    (t : Term Const Γ σ) (u : Term Const (σ :: Γ) τ) (ρ : S.Valuation Γ) :
    S.denote (instantiate t u) ρ = S.denote u (S.extend ρ (S.denote t ρ)) := by
  unfold instantiate
  exact (S.denote_subst u (Subst.single t) ρ).trans
    (S.denote_ext u (by intro σ' v; cases v <;> rfl))

/-- The closed form of `denote_instantiate`. -/
theorem denote_instantiate_closed {σ τ : Ty Base}
    (t : ClosedTerm Const σ) (u : Term Const [σ] τ) :
    S.denote (instantiate t u) S.emptyVal =
      S.denote u (S.extend S.emptyVal (S.denote t S.emptyVal)) :=
  S.denote_instantiate t u S.emptyVal

end FullTypeStructure

end Mettapedia.Logic.HOL
