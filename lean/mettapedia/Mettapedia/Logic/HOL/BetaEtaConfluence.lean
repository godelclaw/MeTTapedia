import Mettapedia.Logic.HOL.BetaEtaNormalization
import Mettapedia.Logic.HOL.EtaConfluence

/-!
# Confluence of typed beta/eta reduction

Mixed local forks account for contraction inside an eta expansion, contraction
inside a beta body, and the possible duplication of an eta-reduced argument.
The terms keep their intrinsic context and type indices throughout.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.BetaEtaConfluence

open EtaConversion
open ContextualTrinity (BetaStep)

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {gamma : Ctx Base} {type domain result : Ty Base}

abbrev Many {gamma : Ctx Base} {type : Ty Base} :
    Term Const gamma type → Term Const gamma type → Prop :=
  Relation.ReflTransGen BetaEtaStep

private theorem beta_many {source target : Term Const gamma type}
    (steps : BetaNormalization.ReducesStar source target) : Many source target :=
  Relation.ReflTransGen.mono (fun _ _ step => Or.inl step) _ _ steps

private theorem eta_many {source target : Term Const gamma type}
    (steps : EtaPostponement.Star source target) : Many source target :=
  Relation.ReflTransGen.mono (fun _ _ step => Or.inr step) _ _ steps

private theorem eta_root_beta_fork (function : Term Const gamma (domain ⇒ result))
    {other : Term Const gamma (domain ⇒ result)}
    (step : BetaNormalization.Reduces (.lam (.app (weaken function) (.var .vz))) other) :
    Relation.Join Many function other := by
  obtain ⟨body, inner, rfl⟩ := BetaNormalization.lam_cases step
  rcases BetaNormalization.app_cases inner with ⟨nextBody, isLam, rfl⟩ |
      ⟨nextFunction, moved, rfl⟩ | ⟨nextArgument, moved, rfl⟩
  · cases function with
    | lam original =>
        simp only [weaken, rename, Term.lam.injEq] at isLam
        subst isLam
        rw [ContextualTrinity.instantiate_vz_rename_lift_weaken]
        exact ⟨_, .refl, .refl⟩
    | var | const | app => simp [weaken, rename] at isLam
  · obtain ⟨next, sourceStep, rfl⟩ :=
      BetaNormalization.reduces_rename_inv function Rename.weaken moved
    exact ⟨next, .single (Or.inl sourceStep), .single (Or.inr (.eta next))⟩
  · exact False.elim (BetaNormalization.var_irreducible _ _ moved)

private theorem beta_root_eta_fork (body : Term Const (domain :: gamma) result)
    (argument : Term Const gamma domain) {other : Term Const gamma result}
    (step : EtaStep (.app (.lam body) argument) other) :
    Relation.Join Many other (instantiate argument body) := by
  cases step with
  | appFun _ inner =>
      cases inner with
      | eta =>
          refine ⟨_, .refl, ?_⟩
          change Many (.app (instantiate argument (weaken _)) argument) _
          rw [instantiate_weaken]
      | lam inner =>
          exact ⟨_, .single (Or.inl ⟨.beta _ argument⟩),
            eta_many (EtaPostponement.star_subst (Subst.single argument) (.single inner))⟩
  | appArg _ inner =>
      exact ⟨_, .single (Or.inl ⟨.beta body _⟩),
        eta_many (EtaPostponement.instantiate_argument body (.single inner))⟩

private theorem lift_join {other : Ctx Base} {first second : Ty Base}
    (wrap : Term Const gamma first → Term Const other second)
    (beta : ∀ {source target}, BetaStep source target → BetaStep (wrap source) (wrap target))
    (eta : ∀ {source target}, EtaStep source target → EtaStep (wrap source) (wrap target))
    {left right : Term Const gamma first} (joined : Relation.Join Many left right) :
    Relation.Join Many (wrap left) (wrap right) := by
  have move {source target} (step : BetaEtaStep source target) :
      BetaEtaStep (wrap source) (wrap target) := by
    rcases step with reduced | step
    · obtain ⟨step⟩ := reduced
      exact Or.inl ⟨beta step⟩
    · exact Or.inr (eta step)
  obtain ⟨common, before, after⟩ := joined
  exact ⟨wrap common, before.lift wrap (fun _ _ step => move step),
    after.lift wrap (fun _ _ step => move step)⟩

/-- Every fork between one eta contraction and one beta contraction joins. -/
theorem eta_beta_fork {source left right : Term Const gamma type}
    (eta : EtaStep source left) (beta : BetaStep source right) :
    Relation.Join Many left right := by
  induction beta with
  | beta body argument => exact beta_root_eta_fork body argument eta
  | appFun _ inner ih =>
      cases eta with
      | appFun _ step =>
          exact lift_join (fun term => .app term _) (fun step => .appFun _ step)
            (fun step => .appFun _ step) (ih step)
      | appArg _ step =>
          exact ⟨_, .single (Or.inl ⟨.appFun _ inner⟩), .single (Or.inr (.appArg _ step))⟩
  | appArg _ inner ih =>
      cases eta with
      | appFun _ step =>
          exact ⟨_, .single (Or.inl ⟨.appArg _ inner⟩), .single (Or.inr (.appFun _ step))⟩
      | appArg _ step =>
          exact lift_join (Term.app _) (fun step => .appArg _ step)
            (fun step => .appArg _ step) (ih step)
  | lam inner ih =>
      cases eta with
      | eta => exact eta_root_beta_fork _ ⟨.lam inner⟩
      | lam step => exact lift_join Term.lam (fun step => .lam step) (fun step => .lam step) (ih step)
  | andLeft _ inner ih =>
      cases eta with
      | andLeft _ step =>
          exact lift_join (fun term => .and term _) (fun step => .andLeft _ step)
            (fun step => .andLeft _ step) (ih step)
      | andRight _ step =>
          exact ⟨_, .single (Or.inl ⟨.andLeft _ inner⟩), .single (Or.inr (.andRight _ step))⟩
  | andRight _ inner ih =>
      cases eta with
      | andLeft _ step =>
          exact ⟨_, .single (Or.inl ⟨.andRight _ inner⟩), .single (Or.inr (.andLeft _ step))⟩
      | andRight _ step =>
          exact lift_join (Term.and _) (fun step => .andRight _ step)
            (fun step => .andRight _ step) (ih step)
  | orLeft _ inner ih =>
      cases eta with
      | orLeft _ step =>
          exact lift_join (fun term => .or term _) (fun step => .orLeft _ step)
            (fun step => .orLeft _ step) (ih step)
      | orRight _ step =>
          exact ⟨_, .single (Or.inl ⟨.orLeft _ inner⟩), .single (Or.inr (.orRight _ step))⟩
  | orRight _ inner ih =>
      cases eta with
      | orLeft _ step =>
          exact ⟨_, .single (Or.inl ⟨.orRight _ inner⟩), .single (Or.inr (.orLeft _ step))⟩
      | orRight _ step =>
          exact lift_join (Term.or _) (fun step => .orRight _ step)
            (fun step => .orRight _ step) (ih step)
  | impLeft _ inner ih =>
      cases eta with
      | impLeft _ step =>
          exact lift_join (fun term => .imp term _) (fun step => .impLeft _ step)
            (fun step => .impLeft _ step) (ih step)
      | impRight _ step =>
          exact ⟨_, .single (Or.inl ⟨.impLeft _ inner⟩), .single (Or.inr (.impRight _ step))⟩
  | impRight _ inner ih =>
      cases eta with
      | impLeft _ step =>
          exact ⟨_, .single (Or.inl ⟨.impRight _ inner⟩), .single (Or.inr (.impLeft _ step))⟩
      | impRight _ step =>
          exact lift_join (Term.imp _) (fun step => .impRight _ step)
            (fun step => .impRight _ step) (ih step)
  | not inner ih =>
      cases eta with
      | not step => exact lift_join Term.not (fun step => .not step) (fun step => .not step) (ih step)
  | eqLeft _ inner ih =>
      cases eta with
      | eqLeft _ step =>
          exact lift_join (fun term => .eq term _) (fun step => .eqLeft _ step)
            (fun step => .eqLeft _ step) (ih step)
      | eqRight _ step =>
          exact ⟨_, .single (Or.inl ⟨.eqLeft _ inner⟩), .single (Or.inr (.eqRight _ step))⟩
  | eqRight _ inner ih =>
      cases eta with
      | eqLeft _ step =>
          exact ⟨_, .single (Or.inl ⟨.eqRight _ inner⟩), .single (Or.inr (.eqLeft _ step))⟩
      | eqRight _ step =>
          exact lift_join (Term.eq _) (fun step => .eqRight _ step)
            (fun step => .eqRight _ step) (ih step)
  | all inner ih =>
      cases eta with
      | all step => exact lift_join Term.all (fun step => .all step) (fun step => .all step) (ih step)
  | ex inner ih =>
      cases eta with
      | ex step => exact lift_join Term.ex (fun step => .ex step) (fun step => .ex step) (ih step)

/-- Every local beta/eta fork joins in the existing typed reduction relation. -/
theorem local_confluence {source left right : Term Const gamma type}
    (first : BetaEtaStep source left) (second : BetaEtaStep source right) :
    Relation.Join Many left right := by
  rcases first with betaFirst | etaFirst
  · obtain ⟨betaFirst⟩ := betaFirst
    rcases second with betaSecond | etaSecond
    · obtain ⟨common, leftSteps, rightSteps⟩ :=
        BetaNormalization.confluent (.single ⟨betaFirst⟩) (.single betaSecond)
      exact ⟨common, beta_many leftSteps, beta_many rightSteps⟩
    · obtain ⟨common, rightSteps, leftSteps⟩ := eta_beta_fork etaSecond betaFirst
      exact ⟨common, leftSteps, rightSteps⟩
  · rcases second with betaSecond | etaSecond
    · obtain ⟨betaSecond⟩ := betaSecond
      exact eta_beta_fork etaFirst betaSecond
    · obtain ⟨common, leftSteps, rightSteps⟩ := EtaConfluence.local_confluence etaFirst etaSecond
      exact ⟨common, eta_many leftSteps, eta_many rightSteps⟩

/-- Arbitrary typed beta/eta paths from one source have a common reduct. -/
theorem confluent : Mettapedia.Logic.Relation.Confluent
    (BetaEtaStep (Const := Const) (Γ := gamma) (τ := type)) :=
  Mettapedia.Logic.Relation.confluent_of_accessible_forks
    BetaEtaNormalization.stronglyNormalizing (fun _ _ _ => local_confluence)

theorem conversion_iff_join {left right : Term Const gamma type} :
    BetaEtaConv left right ↔ Relation.Join Many left right :=
  Mettapedia.Logic.Relation.Confluent.eqvGen_iff_join confluent

/-- Normal forms from different algorithms agree whenever their inputs are
beta/eta convertible. No model or normalization strategy is selected. -/
theorem normal_eq_of_convertible {left right : Term Const gamma type}
    (leftNormal : Mettapedia.Logic.Relation.IsNormal BetaEtaStep left)
    (rightNormal : Mettapedia.Logic.Relation.IsNormal BetaEtaStep right)
    (converted : BetaEtaConv left right) : left = right := by
  obtain ⟨common, leftSteps, rightSteps⟩ := conversion_iff_join.mp converted
  exact (leftNormal.reflTransGen_eq leftSteps).symm.trans
    (rightNormal.reflTransGen_eq rightSteps)

theorem variable_normal (index : Var gamma type) :
    Mettapedia.Logic.Relation.IsNormal BetaEtaStep (Term.var (Const := Const) index) := by
  intro target step
  rcases step with beta | eta
  · obtain ⟨beta⟩ := beta
    cases beta
  · cases eta

/-- Distinct variables remain distinct under the combined conversion. -/
theorem distinct_variables_not_convertible (first second : Var gamma type)
    (distinct : first ≠ second) :
    ¬ BetaEtaConv (Term.var (Const := Const) first) (.var second) := by
  intro converted
  exact distinct (Term.var.inj
    (normal_eq_of_convertible (variable_normal first) (variable_normal second) converted))

#print axioms eta_beta_fork
#print axioms local_confluence
#print axioms confluent
#print axioms conversion_iff_join
#print axioms normal_eq_of_convertible
#print axioms distinct_variables_not_convertible

end Mettapedia.Logic.HOL.BetaEtaConfluence
