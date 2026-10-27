import Mettapedia.Logic.HOL.CurriedPredicates

/-!
# Constructor data and result-index programs

These programs determine constructor tags, field validity and result indices.
They are independent of the description of recursive positions. Fixed and
shape-dependent position interfaces share this constructor layer.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.IndexedConstructorGuards
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open FiniteConstructorEncoding CurriedPredicates
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ : Ctx Base}

structure ConstructorPrograms (Const : Ty Base → Type v) (Γ : Ctx Base) where
  fields : List (List (Ty Base))
  number : Ty Base
  index : Ty Base
  numeral : Nat → Term Const Γ number
  allowed : ConstructorDataPredicates.Conditions Const Γ fields
  result : (occurrence : Fin fields.length) → Term Const Γ (FunctionType (fields.get occurrence) index)

namespace ConstructorPrograms
variable (inventory : ConstructorPrograms Const Γ)

def subst (rho : Subst Const Γ Δ) : ConstructorPrograms Const Δ where
  fields := inventory.fields
  number := inventory.number
  index := inventory.index
  numeral := fun number => HOL.subst rho (inventory.numeral number)
  allowed := fun occurrence => HOL.subst rho (inventory.allowed occurrence)
  result := fun occurrence => HOL.subst rho (inventory.result occurrence)

def shapeCondition (tag : Term Const Γ inventory.number) :
    ConstructorDataPredicates.Conditions Const Γ inventory.fields := fun occurrence =>
  conjoin _ (inventory.allowed occurrence)
    (constant _ (.eq tag (inventory.numeral occurrence.val)))

def resultCondition (index : Term Const Γ inventory.index) :
    ConstructorDataPredicates.Conditions Const Γ inventory.fields := fun occurrence =>
  conjoin _ (inventory.allowed occurrence) (equalTo _ (inventory.result occurrence) index)

def shapeGuard (tag : Term Const Γ inventory.number)
    (payload : Term Const Γ (payloadType inventory.fields)) : Formula Const Γ :=
  ConstructorDataPredicates.guard inventory.fields (inventory.shapeCondition tag) payload

def resultGuard (payload : Term Const Γ (payloadType inventory.fields))
    (index : Term Const Γ inventory.index) : Formula Const Γ :=
  ConstructorDataPredicates.guard inventory.fields (inventory.resultCondition index) payload

variable (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains)

abbrev Data := TypeTheory.FiniteConstructorEncoding.Data (Ty.denote model.Carrier) inventory.fields

def dataAllowed (values : model.Valuation Γ) (data : inventory.Data model) : Prop :=
  holds model _ (inventory.allowed data.1) values data.2

def payloadMatches (values : model.Valuation Γ)
    (payload : Term Const Γ (payloadType inventory.fields)) (data : inventory.Data model) : Prop :=
  payloadEquivalence model inventory.fields (model.denote payload values) =
    TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) inventory.fields data

def resultValue (values : model.Valuation Γ) (data : inventory.Data model) :=
  applyValues model _ (model.denote (inventory.result data.1) values) data.2

include full

theorem shapeCondition_holds (tag : Term Const Γ inventory.number)
    (values : model.Valuation Γ) (data : inventory.Data model) :
    ConstructorDataPredicates.conditionMeaning model inventory.fields (inventory.shapeCondition tag) values data ↔
      inventory.dataAllowed model values data ∧
      model.denote tag values = model.denote (inventory.numeral data.1.val) values := by
  change holds model _ (conjoin _ _ _) _ _ ↔ _
  rw [conjoin_holds, constant_holds]
  change _ ∧ model.Eqv _ _ _ ↔ _
  rw [model.eqv_iff_eq_of_fullDomains full]
  rfl

theorem resultCondition_holds (index : Term Const Γ inventory.index)
    (values : model.Valuation Γ) (data : inventory.Data model) :
    ConstructorDataPredicates.conditionMeaning model inventory.fields (inventory.resultCondition index) values data ↔
      inventory.dataAllowed model values data ∧
      inventory.resultValue model values data = model.denote index values := by
  change holds model _ (conjoin _ _ _) _ _ ↔ _
  rw [conjoin_holds, equalTo_holds model full]
  rfl

theorem shapeGuard_denote (tag : Term Const Γ inventory.number)
    (payload : Term Const Γ (payloadType inventory.fields)) (values : model.Valuation Γ) :
    (model.denote (inventory.shapeGuard tag payload) values).down ↔
      ∃ data : inventory.Data model, (inventory.dataAllowed model values data ∧
        model.denote tag values = model.denote (inventory.numeral data.1.val) values) ∧
        inventory.payloadMatches model values payload data := by
  rw [shapeGuard, ConstructorDataPredicates.guard_denote model full]
  exact exists_congr (fun data => and_congr (inventory.shapeCondition_holds model full tag values data) Iff.rfl)

theorem resultGuard_denote (payload : Term Const Γ (payloadType inventory.fields))
    (index : Term Const Γ inventory.index) (values : model.Valuation Γ) :
    (model.denote (inventory.resultGuard payload index) values).down ↔
      ∃ data : inventory.Data model, (inventory.dataAllowed model values data ∧
        inventory.resultValue model values data = model.denote index values) ∧
        inventory.payloadMatches model values payload data := by
  rw [resultGuard, ConstructorDataPredicates.guard_denote model full]
  exact exists_congr (fun data => and_congr (inventory.resultCondition_holds model full index values data) Iff.rfl)

#print axioms shapeGuard_denote
#print axioms resultGuard_denote

end ConstructorPrograms
end Mettapedia.Logic.HOL.IndexedConstructorGuards
