import Mettapedia.Logic.HOL.BetaNormalization
import Mettapedia.Logic.HOL.Soundness

/-!
# η and βη-conversion of HOL terms

An η-step contracts `λ x. f x` to `f`, where `f` does not mention `x` (it is a
weakening), at every position of an intrinsically typed term (`EtaStep`).  A
βη-step is a β-step or an η-step (`BetaEtaStep`), and βη-conversion is its
equivalence closure (`BetaEtaConv`).

**Soundness.**  Function types denote function spaces in a Henkin model, so
both steps preserve denotation (`denote_of_betaStep`, `denote_of_etaStep`), and
βη-convertible terms have equal denotations under every valuation
(`denote_of_betaEtaConv`).  So a model in which two terms differ separates them:
they are not βη-convertible.

**Controls.**  `λ x. f x` and `f` are βη-convertible (`eta_betaEtaConv`), and two
distinct variables are not (`distinct_variables_not_betaEtaConv`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.EtaConversion

open Mettapedia.Logic.HOL.ContextualTrinity (BetaStep)

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- One η-step, `λ x. f x ↦ f` for a term `f` that does not mention `x`, at every
position. -/
inductive EtaStep : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Term Const Γ τ → Prop where
  | eta {Γ : Ctx Base} {σ τ : Ty Base} (function : Term Const Γ (σ ⇒ τ)) :
      EtaStep (.lam (.app (weaken (σ := σ) function) (.var .vz))) function
  | appFun {Γ : Ctx Base} {σ τ : Ty Base} {function function' : Term Const Γ (σ ⇒ τ)}
      (argument : Term Const Γ σ) :
      EtaStep function function' → EtaStep (.app function argument) (.app function' argument)
  | appArg {Γ : Ctx Base} {σ τ : Ty Base} (function : Term Const Γ (σ ⇒ τ))
      {argument argument' : Term Const Γ σ} :
      EtaStep argument argument' → EtaStep (.app function argument) (.app function argument')
  | lam {Γ : Ctx Base} {σ τ : Ty Base} {body body' : Term Const (σ :: Γ) τ} :
      EtaStep body body' → EtaStep (.lam body) (.lam body')
  | andLeft {Γ : Ctx Base} {left left' : Formula Const Γ} (right : Formula Const Γ) :
      EtaStep left left' → EtaStep (.and left right) (.and left' right)
  | andRight {Γ : Ctx Base} (left : Formula Const Γ) {right right' : Formula Const Γ} :
      EtaStep right right' → EtaStep (.and left right) (.and left right')
  | orLeft {Γ : Ctx Base} {left left' : Formula Const Γ} (right : Formula Const Γ) :
      EtaStep left left' → EtaStep (.or left right) (.or left' right)
  | orRight {Γ : Ctx Base} (left : Formula Const Γ) {right right' : Formula Const Γ} :
      EtaStep right right' → EtaStep (.or left right) (.or left right')
  | impLeft {Γ : Ctx Base} {left left' : Formula Const Γ} (right : Formula Const Γ) :
      EtaStep left left' → EtaStep (.imp left right) (.imp left' right)
  | impRight {Γ : Ctx Base} (left : Formula Const Γ) {right right' : Formula Const Γ} :
      EtaStep right right' → EtaStep (.imp left right) (.imp left right')
  | not {Γ : Ctx Base} {operand operand' : Formula Const Γ} :
      EtaStep operand operand' → EtaStep (.not operand) (.not operand')
  | eqLeft {Γ : Ctx Base} {τ : Ty Base} {left left' : Term Const Γ τ} (right : Term Const Γ τ) :
      EtaStep left left' → EtaStep (.eq left right) (.eq left' right)
  | eqRight {Γ : Ctx Base} {τ : Ty Base} (left : Term Const Γ τ) {right right' : Term Const Γ τ} :
      EtaStep right right' → EtaStep (.eq left right) (.eq left right')
  | all {Γ : Ctx Base} {σ : Ty Base} {body body' : Formula Const (σ :: Γ)} :
      EtaStep body body' → EtaStep (.all body) (.all body')
  | ex {Γ : Ctx Base} {σ : Ty Base} {body body' : Formula Const (σ :: Γ)} :
      EtaStep body body' → EtaStep (.ex body) (.ex body')

/-- One βη-step: a β-step or an η-step. -/
def BetaEtaStep {Γ : Ctx Base} {τ : Ty Base} (source target : Term Const Γ τ) : Prop :=
  BetaNormalization.Reduces source target ∨ EtaStep source target

/-- βη-conversion: the equivalence closure of βη-steps. -/
abbrev BetaEtaConv {Γ : Ctx Base} {τ : Ty Base} : Term Const Γ τ → Term Const Γ τ → Prop :=
  Relation.EqvGen BetaEtaStep

/-! ## Soundness in Henkin models -/

section Soundness

variable (M : HenkinModel.{u, v, w} Base Const)

/-- **A β-step preserves denotation.** -/
theorem denote_of_betaStep {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (step : BetaStep s t) : ∀ ρ : HenkinModel.Valuation M Γ, M.denote s ρ = M.denote t ρ := by
  induction step with
  | beta body argument =>
      intro ρ
      rw [Soundness.denote_instantiate_term]
      rfl
  | appFun _ _ ih => intro ρ; simp only [HenkinModel.denote, PreModel.denote] at ih ⊢; rw [ih]
  | appArg _ _ ih => intro ρ; simp only [HenkinModel.denote, PreModel.denote] at ih ⊢; rw [ih]
  | lam _ ih =>
      intro ρ
      simp only [HenkinModel.denote, PreModel.denote] at ih ⊢
      funext x
      exact ih _
  | andLeft _ _ ih | andRight _ _ ih | orLeft _ _ ih | orRight _ _ ih | impLeft _ _ ih
  | impRight _ _ ih | not _ ih | eqLeft _ _ ih | eqRight _ _ ih =>
      intro ρ; simp only [HenkinModel.denote, PreModel.denote] at ih ⊢; rw [ih]
  | all _ ih | ex _ ih =>
      intro ρ
      simp only [HenkinModel.denote, PreModel.denote] at ih ⊢
      simp only [ih]
      try rfl

/-- **An η-step preserves denotation**: function types denote function spaces. -/
theorem denote_of_etaStep {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (step : EtaStep s t) : ∀ ρ : HenkinModel.Valuation M Γ, M.denote s ρ = M.denote t ρ := by
  induction step with
  | eta function =>
      intro ρ
      funext x
      exact congrFun (Soundness.denote_weaken M function ρ x) x
  | appFun _ _ ih => intro ρ; simp only [HenkinModel.denote, PreModel.denote] at ih ⊢; rw [ih]
  | appArg _ _ ih => intro ρ; simp only [HenkinModel.denote, PreModel.denote] at ih ⊢; rw [ih]
  | lam _ ih =>
      intro ρ
      simp only [HenkinModel.denote, PreModel.denote] at ih ⊢
      funext x
      exact ih _
  | andLeft _ _ ih | andRight _ _ ih | orLeft _ _ ih | orRight _ _ ih | impLeft _ _ ih
  | impRight _ _ ih | not _ ih | eqLeft _ _ ih | eqRight _ _ ih =>
      intro ρ; simp only [HenkinModel.denote, PreModel.denote] at ih ⊢; rw [ih]
  | all _ ih | ex _ ih =>
      intro ρ
      simp only [HenkinModel.denote, PreModel.denote] at ih ⊢
      simp only [ih]
      try rfl

/-- **βη-convertible terms have equal denotations**, under every valuation of
every Henkin model. -/
theorem denote_of_betaEtaConv {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (converted : BetaEtaConv s t) (ρ : HenkinModel.Valuation M Γ) :
    M.denote s ρ = M.denote t ρ := by
  induction converted with
  | rel _ _ step =>
      rcases step with beta | eta
      · exact beta.elim fun one => denote_of_betaStep M one ρ
      · exact denote_of_etaStep M eta ρ
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

end Soundness

/-! ## Controls -/

/-- **`λ x. f x` and `f` are βη-convertible.** -/
theorem eta_betaEtaConv {Γ : Ctx Base} {σ τ : Ty Base} (function : Term Const Γ (σ ⇒ τ)) :
    BetaEtaConv (.lam (.app (weaken (σ := σ) function) (.var .vz))) function :=
  .rel _ _ (Or.inr (.eta function))

/-- A signature with one sort and no constant. -/
abbrev NoConst : Ty Unit → Type := fun _ => Empty

/-- A model with two booleans at the one sort. -/
def boolModel : HenkinModel.{0, 0, 0} Unit NoConst where
  Carrier := fun _ => ULift Bool
  adm := fun _ _ => True
  base_mem := fun _ _ => trivial
  prop_mem := fun _ => trivial
  app_mem := fun _ _ => trivial
  constDen := fun c => nomatch c
  const_mem := fun c => nomatch c
  term_closed := fun _ _ _ => trivial

/-- **Two distinct variables are not βη-convertible**: a model sends them to
different values. -/
theorem distinct_variables_not_betaEtaConv :
    ¬ BetaEtaConv (.var .vz : Term NoConst [.base (), .base ()] (.base ())) (.var (.vs .vz)) := by
  intro converted
  let ρ : HenkinModel.Valuation boolModel [.base (), .base ()] := fun v => match v with
    | .vz => ULift.up true
    | .vs .vz => ULift.up false
  have same : (ULift.up true : ULift.{1} Bool) = ULift.up false :=
    denote_of_betaEtaConv boolModel converted ρ
  exact Bool.noConfusion (congrArg ULift.down same)

/-- The η-pair has one denotation, read off `denote_of_betaEtaConv`. -/
theorem eta_denote_eq :
    boolModel.denote (.lam (.app (weaken (σ := .base ()) (.var .vz)) (.var .vz)) :
        Term NoConst [.arr (.base ()) (.base ())] (.arr (.base ()) (.base ())))
        (fun v => match v with | .vz => fun x => x) =
      boolModel.denote (.var .vz : Term NoConst [.arr (.base ()) (.base ())] (.arr (.base ()) (.base ())))
        (fun v => match v with | .vz => fun x => x) :=
  denote_of_betaEtaConv boolModel (eta_betaEtaConv _) _

#print axioms denote_of_betaStep
#print axioms denote_of_etaStep
#print axioms denote_of_betaEtaConv
#print axioms distinct_variables_not_betaEtaConv

end Mettapedia.Logic.HOL.EtaConversion
