import Mettapedia.Logic.HOL.BetaEtaConfluence

/-!
# Beta/eta normal forms under context operations

Weakening and the rigid logical constructors preserve beta/eta normality.
Application additionally needs a non-lambda head. Abstraction has a separate
eta boundary: even a normal body can acquire an outer eta contraction.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.BetaEtaNormalForms

open Mettapedia.Logic.HOL EtaConversion

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {gamma : Ctx Base} {type domain result : Ty Base}

theorem weaken_normal {source : Term Const gamma type}
    (normal : Mettapedia.Logic.Relation.IsNormal BetaEtaStep source) :
    Mettapedia.Logic.Relation.IsNormal BetaEtaStep (weaken (σ := domain) source) := by
  intro target step
  rcases step with beta | eta
  · obtain ⟨lowered, before, _⟩ := BetaNormalization.reduces_rename_inv source Rename.weaken beta
    exact normal lowered (Or.inl before)
  · obtain ⟨lowered, _, before⟩ := EtaNormalization.weaken_step_inv eta
    exact normal lowered (Or.inr before)

theorem imp_normal {left right : Formula Const gamma}
    (one : Mettapedia.Logic.Relation.IsNormal BetaEtaStep left)
    (two : Mettapedia.Logic.Relation.IsNormal BetaEtaStep right) :
    Mettapedia.Logic.Relation.IsNormal BetaEtaStep (.imp left right) := by
  intro target step
  rcases step with beta | eta
  · obtain ⟨beta⟩ := beta
    cases beta with
    | impLeft _ inner => exact one _ (Or.inl ⟨inner⟩)
    | impRight _ inner => exact two _ (Or.inl ⟨inner⟩)
  · cases eta with
    | impLeft _ inner => exact one _ (Or.inr inner)
    | impRight _ inner => exact two _ (Or.inr inner)

theorem all_normal {body : Formula Const (domain :: gamma)}
    (normal : Mettapedia.Logic.Relation.IsNormal BetaEtaStep body) :
    Mettapedia.Logic.Relation.IsNormal BetaEtaStep (.all body) := by
  intro target step
  rcases step with beta | eta
  · obtain ⟨beta⟩ := beta
    cases beta with
    | all inner => exact normal _ (Or.inl ⟨inner⟩)
  · cases eta with
    | all inner => exact normal _ (Or.inr inner)

theorem app_normal {function : Term Const gamma (domain ⇒ result)}
    {argument : Term Const gamma domain}
    (functionNormal : Mettapedia.Logic.Relation.IsNormal BetaEtaStep function)
    (argumentNormal : Mettapedia.Logic.Relation.IsNormal BetaEtaStep argument)
    (neutral : BetaNormalization.Neutral function) :
    Mettapedia.Logic.Relation.IsNormal BetaEtaStep (.app function argument) := by
  intro target step
  rcases step with beta | eta
  · obtain ⟨beta⟩ := beta
    cases beta with
    | beta => cases neutral
    | appFun _ inner => exact functionNormal _ (Or.inl ⟨inner⟩)
    | appArg _ inner => exact argumentNormal _ (Or.inl ⟨inner⟩)
  · cases eta with
    | appFun _ inner => exact functionNormal _ (Or.inr inner)
    | appArg _ inner => exact argumentNormal _ (Or.inr inner)

theorem eta_expansion_not_normal (function : Term Const gamma (domain ⇒ result)) :
    ¬ Mettapedia.Logic.Relation.IsNormal BetaEtaStep
      (.lam (.app (weaken function) (.var .vz))) :=
  fun normal => normal function (Or.inr (.eta function))

def etaBody : Term Const [.prop, .prop ⇒ .prop] .prop :=
  .app (.var (.vs .vz)) (.var .vz)

/-- A normal body need not remain normal when abstracted. -/
theorem normal_body_not_normal_abstraction :
    Mettapedia.Logic.Relation.IsNormal BetaEtaStep (etaBody (Const := Const)) ∧
      ¬ Mettapedia.Logic.Relation.IsNormal BetaEtaStep (.lam (etaBody (Const := Const))) := by
  refine ⟨app_normal (BetaEtaConfluence.variable_normal _) (BetaEtaConfluence.variable_normal _)
    (by trivial), ?_⟩
  exact eta_expansion_not_normal (.var .vz)

#print axioms weaken_normal
#print axioms imp_normal
#print axioms all_normal
#print axioms app_normal
#print axioms eta_expansion_not_normal
#print axioms normal_body_not_normal_abstraction

end Mettapedia.Logic.HOL.BetaEtaNormalForms
