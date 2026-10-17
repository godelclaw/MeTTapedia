import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLRules
import Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompleteness
import Mettapedia.Logic.HOL.Soundness

namespace Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSoundness

universe u v w

open Mettapedia.Logic.HOL
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCore (HOLState HOLProvable HOLProvImp HOLProvEq)
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLRules (HOLProvIff)
open Mettapedia.PLN.WorldModel.PLNWorldModel

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Closed HOL theorems are satisfied by every pointed Henkin model. -/
theorem holProvable_models {φ : HOLQuery Const}
    (h : HOLProvable (Const := Const) φ) (M : HenkinModel.{u, v, w} Base Const) :
    HenkinModel.models M φ :=
  _root_.Mettapedia.Logic.HOL.Soundness.theorem_sound h M

/-- Provable HOL implication transports to pointwise semantic implication. -/
theorem holProvImp_implies_pointwise {φ ψ : HOLQuery Const}
    (h : HOLProvImp (Const := Const) φ ψ) :
    ∀ M : HenkinModel.{u, v, w} Base Const,
      HenkinModel.models M φ → HenkinModel.models M ψ := by
  intro M hφ
  have himp := holProvable_models (Const := Const) h M
  exact (HenkinModel.models_imp M).mp himp hφ

/-- Provable HOL implication transports to singleton WM consequence. -/
theorem holProvImp_implies_singletonConsequence {φ ψ : HOLQuery Const}
    (h : HOLProvImp (Const := Const) φ ψ) :
    ∀ M : HenkinModel.{u, v, w} Base Const,
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
          ({M} : HOLState Base Const) φ ≤
        BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
          ({M} : HOLState Base Const) ψ :=
  fun M =>
    (_root_.Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.pointwiseImplies_iff_singletonStrengthLE
      holSatisfies φ ψ).mp (holProvImp_implies_pointwise (Const := Const) h) M trivial

/-- Provable HOL implication transports to multiset WM consequence. -/
theorem holProvImp_implies_multisetConsequence {φ ψ : HOLQuery Const}
    (h : HOLProvImp (Const := Const) φ ψ) :
    ∀ W : HOLState Base Const,
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W φ ≤
        BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W ψ := by
  intro W
  exact _root_.Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.queryStrength_le_of_pointwise
    holSatisfies W φ ψ (holProvImp_implies_pointwise (Const := Const) h)

/-- Provable closed HOL equalities are valid in every pointed Henkin model. -/
theorem holProvEq_models {τ : Ty Base} {t u : Term Const [] τ}
    (h : HOLProvEq (Const := Const) t u) (M : HenkinModel.{u, v, w} Base Const) :
    HenkinModel.Eqv M τ
      (HenkinModel.denote M t (fun v => nomatch v))
      (HenkinModel.denote M u (fun v => nomatch v)) := by
  change HenkinModel.models M (.eq t u)
  exact holProvable_models (Const := Const) (φ := .eq t u) h M

/-- Provable HOL equivalence transports to pointwise semantic equivalence. -/
theorem holProvIff_implies_pointwise {φ ψ : HOLQuery Const}
    (h : HOLProvIff (Const := Const) φ ψ) :
    ∀ M : HenkinModel.{u, v, w} Base Const,
      HenkinModel.models M φ ↔ HenkinModel.models M ψ := by
  intro M
  have hiff := holProvable_models (Const := Const) h M
  have hpairs := (HenkinModel.models_and M).mp hiff
  exact Iff.intro ((HenkinModel.models_imp M).mp hpairs.1) ((HenkinModel.models_imp M).mp hpairs.2)

/-- Provable HOL equivalence transports to WM query equivalence. -/
theorem holProvIff_implies_queryEq {φ ψ : HOLQuery Const}
    (h : HOLProvIff (Const := Const) φ ψ) :
    WMQueryEq (State := HOLState Base Const) (Query := HOLQuery Const) φ ψ :=
  (_root_.Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.pointwiseIff_iff_queryEq
    holSatisfies φ ψ).mp (holProvIff_implies_pointwise (Const := Const) h)

/-- Provable HOL equivalence transports to WM strength equality. -/
theorem holProvIff_implies_strengthEq {φ ψ : HOLQuery Const}
    (h : HOLProvIff (Const := Const) φ ψ) :
    ∀ W : HOLState Base Const,
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W φ =
        BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W ψ := by
  intro W
  exact WMQueryEq.to_queryStrength
    (State := HOLState Base Const) (Query := HOLQuery Const)
    (holProvIff_implies_queryEq (Base := Base) (Const := Const) h) W

end Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSoundness
