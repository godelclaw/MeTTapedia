import Mettapedia.Logic.HOL.EtaNormalization
import Mettapedia.Logic.HOL.CoreReduction

/-!
# Confluence of typed eta contraction

Eta contraction is confluent in every intrinsically typed HOL context. The
overlap between an outer contraction and a contraction inside its function is
resolved by reflecting the inner step through weakening; no inhabitance of
the bound type is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.EtaConfluence

open EtaConversion

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {gamma : Ctx Base} {type domain result : Ty Base}

abbrev Star {gamma : Ctx Base} {type : Ty Base} :
    Term Const gamma type → Term Const gamma type → Prop :=
  Relation.ReflTransGen EtaStep

private theorem root_fork (function : Term Const gamma (domain ⇒ result))
    {other : Term Const gamma (domain ⇒ result)}
    (step : EtaStep (.lam (.app (weaken function) (.var .vz))) other) :
    Relation.Join Star function other := by
  generalize expansion : (.lam (.app (weaken function) (.var .vz)) :
    Term Const gamma (domain ⇒ result)) = expanded at step
  cases step with
  | eta =>
      have functions := eq_of_heq (Term.app.inj (Term.lam.inj expansion)).2.1
      have same := rename_injective Rename.weaken
        (fun _ _ equal => Var.vs.inj equal) function other functions
      subst other
      exact ⟨function, .refl, .refl⟩
  | lam bodyStep =>
      cases Term.lam.inj expansion
      cases bodyStep with
      | appFun _ functionStep =>
          obtain ⟨next, same, moved⟩ := EtaNormalization.weaken_step_inv functionStep
          subst same
          exact ⟨next, .single moved, .single (.eta next)⟩
      | appArg _ argumentStep => cases argumentStep
  | appFun _ _ | appArg _ _ => cases expansion

private theorem lift_join {other : Ctx Base} {first second : Ty Base}
    (wrap : Term Const gamma first → Term Const other second)
    (move : ∀ {source target}, EtaStep source target → EtaStep (wrap source) (wrap target))
    {left right : Term Const gamma first} (joined : Relation.Join Star left right) :
    Relation.Join Star (wrap left) (wrap right) := by
  obtain ⟨common, before, after⟩ := joined
  exact ⟨wrap common, before.lift wrap (fun _ _ step => move step),
    after.lift wrap (fun _ _ step => move step)⟩

/-- Every local eta fork has a common reduct. -/
theorem local_confluence {source left right : Term Const gamma type}
    (first : EtaStep source left) (second : EtaStep source right) :
    Relation.Join Star left right := by
  induction first with
  | eta function => exact root_fork function second
  | appFun _ inner ih =>
      cases second with
      | appFun _ step =>
          exact lift_join (fun term => .app term _) (fun step => .appFun _ step) (ih step)
      | appArg _ step => exact ⟨_, .single (.appArg _ step), .single (.appFun _ inner)⟩
  | appArg _ inner ih =>
      cases second with
      | appFun _ step => exact ⟨_, .single (.appFun _ step), .single (.appArg _ inner)⟩
      | appArg _ step =>
          exact lift_join (Term.app _) (fun step => .appArg _ step) (ih step)
  | lam inner ih =>
      cases second with
      | eta =>
          obtain ⟨common, before, after⟩ := root_fork _ (.lam inner)
          exact ⟨common, after, before⟩
      | lam step => exact lift_join Term.lam (fun step => .lam step) (ih step)
  | andLeft _ inner ih =>
      cases second with
      | andLeft _ step =>
          exact lift_join (fun term => .and term _) (fun step => .andLeft _ step) (ih step)
      | andRight _ step => exact ⟨_, .single (.andRight _ step), .single (.andLeft _ inner)⟩
  | andRight _ inner ih =>
      cases second with
      | andLeft _ step => exact ⟨_, .single (.andLeft _ step), .single (.andRight _ inner)⟩
      | andRight _ step =>
          exact lift_join (Term.and _) (fun step => .andRight _ step) (ih step)
  | orLeft _ inner ih =>
      cases second with
      | orLeft _ step =>
          exact lift_join (fun term => .or term _) (fun step => .orLeft _ step) (ih step)
      | orRight _ step => exact ⟨_, .single (.orRight _ step), .single (.orLeft _ inner)⟩
  | orRight _ inner ih =>
      cases second with
      | orLeft _ step => exact ⟨_, .single (.orLeft _ step), .single (.orRight _ inner)⟩
      | orRight _ step =>
          exact lift_join (Term.or _) (fun step => .orRight _ step) (ih step)
  | impLeft _ inner ih =>
      cases second with
      | impLeft _ step =>
          exact lift_join (fun term => .imp term _) (fun step => .impLeft _ step) (ih step)
      | impRight _ step => exact ⟨_, .single (.impRight _ step), .single (.impLeft _ inner)⟩
  | impRight _ inner ih =>
      cases second with
      | impLeft _ step => exact ⟨_, .single (.impLeft _ step), .single (.impRight _ inner)⟩
      | impRight _ step =>
          exact lift_join (Term.imp _) (fun step => .impRight _ step) (ih step)
  | not inner ih =>
      cases second with
      | not step => exact lift_join Term.not (fun step => .not step) (ih step)
  | eqLeft _ inner ih =>
      cases second with
      | eqLeft _ step =>
          exact lift_join (fun term => .eq term _) (fun step => .eqLeft _ step) (ih step)
      | eqRight _ step => exact ⟨_, .single (.eqRight _ step), .single (.eqLeft _ inner)⟩
  | eqRight _ inner ih =>
      cases second with
      | eqLeft _ step => exact ⟨_, .single (.eqLeft _ step), .single (.eqRight _ inner)⟩
      | eqRight _ step =>
          exact lift_join (Term.eq _) (fun step => .eqRight _ step) (ih step)
  | all inner ih =>
      cases second with
      | all step => exact lift_join Term.all (fun step => .all step) (ih step)
  | ex inner ih =>
      cases second with
      | ex step => exact lift_join Term.ex (fun step => .ex step) (ih step)

/-- Typed eta contraction is confluent, without semantic assumptions. -/
theorem confluent : Mettapedia.Logic.Relation.Confluent
    (EtaStep (Const := Const) (Γ := gamma) (τ := type)) :=
  Mettapedia.Logic.Relation.confluent_of_accessible_forks
    EtaNormalization.stronglyNormalizing (fun _ _ _ => local_confluence)

#print axioms local_confluence
#print axioms confluent

end Mettapedia.Logic.HOL.EtaConfluence
