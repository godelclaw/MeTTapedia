import Mettapedia.Logic.HOL.ConstructorPrograms

/-!
# Fixed finite recursive-position inventories

Each constructor retains its fixed ordered recursive fields and their index
programs. Constructor data, tags and result indices belong to the shared
`ConstructorPrograms` layer. Active slots and child indices quantify over the
original finite field inventory.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.IndexedConstructorGuards
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open FiniteConstructorEncoding CurriedPredicates
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ : Ctx Base}

structure Inventory (Const : Ty Base → Type v) (Γ : Ctx Base) extends ConstructorPrograms Const Γ where
  childCount : Fin fields.length → Nat
  child : (occurrence : Fin fields.length) → Fin (childCount occurrence) →
    Term Const Γ (FunctionType (fields.get occurrence) index)

namespace Inventory
variable (inventory : Inventory Const Γ)

def subst (rho : Subst Const Γ Δ) : Inventory Const Δ where
  toConstructorPrograms := inventory.toConstructorPrograms.subst rho
  childCount := inventory.childCount
  child := fun occurrence position => HOL.subst rho (inventory.child occurrence position)

def activeCondition (slot : Term Const Γ inventory.number) :
    ConstructorDataPredicates.Conditions Const Γ inventory.fields := fun occurrence =>
  conjoin _ (inventory.allowed occurrence)
    (CurriedPredicates.choose _ (fun position : Fin (inventory.childCount occurrence) =>
      constant _ (.eq slot (inventory.numeral position.val))))

def childCondition (slot : Term Const Γ inventory.number) (index : Term Const Γ inventory.index) :
    ConstructorDataPredicates.Conditions Const Γ inventory.fields := fun occurrence =>
  conjoin _ (inventory.allowed occurrence)
    (CurriedPredicates.choose _ (fun position => conjoin _
      (constant _ (.eq slot (inventory.numeral position.val)))
      (equalTo _ (inventory.child occurrence position) index)))

def activeGuard (payload : Term Const Γ (payloadType inventory.fields))
    (slot : Term Const Γ inventory.number) : Formula Const Γ :=
  ConstructorDataPredicates.guard inventory.fields (inventory.activeCondition slot) payload

def childGuard (payload : Term Const Γ (payloadType inventory.fields))
    (slot : Term Const Γ inventory.number) (index : Term Const Γ inventory.index) : Formula Const Γ :=
  ConstructorDataPredicates.guard inventory.fields (inventory.childCondition slot index) payload

variable (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains)

def childValue (values : model.Valuation Γ) (data : inventory.toConstructorPrograms.Data model)
    (position : Fin (inventory.childCount data.1)) :=
  applyValues model _ (model.denote (inventory.child data.1 position) values) data.2

include full

theorem activeCondition_holds (slot : Term Const Γ inventory.number)
    (values : model.Valuation Γ) (data : inventory.toConstructorPrograms.Data model) :
    ConstructorDataPredicates.conditionMeaning model inventory.fields (inventory.activeCondition slot) values data ↔
      inventory.toConstructorPrograms.dataAllowed model values data ∧
      ∃ position : Fin (inventory.childCount data.1),
        model.denote slot values = model.denote (inventory.numeral position.val) values := by
  change holds model _ (conjoin _ _ _) _ _ ↔ _
  rw [conjoin_holds, choose_holds]
  apply and_congr Iff.rfl
  apply exists_congr
  intro position
  rw [constant_holds]
  exact model.eqv_iff_eq_of_fullDomains full _ _

theorem childCondition_holds (slot : Term Const Γ inventory.number) (index : Term Const Γ inventory.index)
    (values : model.Valuation Γ) (data : inventory.toConstructorPrograms.Data model) :
    ConstructorDataPredicates.conditionMeaning model inventory.fields (inventory.childCondition slot index) values data ↔
      inventory.toConstructorPrograms.dataAllowed model values data ∧
      ∃ position : Fin (inventory.childCount data.1),
        model.denote slot values = model.denote (inventory.numeral position.val) values ∧
        inventory.childValue model values data position = model.denote index values := by
  change holds model _ (conjoin _ _ _) _ _ ↔ _
  rw [conjoin_holds, choose_holds]
  apply and_congr Iff.rfl
  apply exists_congr
  intro position
  rw [conjoin_holds, constant_holds, equalTo_holds model full]
  change model.Eqv _ _ _ ∧ _ ↔ _
  rw [model.eqv_iff_eq_of_fullDomains full]
  rfl

theorem activeGuard_denote (payload : Term Const Γ (payloadType inventory.fields))
    (slot : Term Const Γ inventory.number) (values : model.Valuation Γ) :
    (model.denote (inventory.activeGuard payload slot) values).down ↔
      ∃ data : inventory.toConstructorPrograms.Data model, (inventory.toConstructorPrograms.dataAllowed model values data ∧
        ∃ position : Fin (inventory.childCount data.1),
          model.denote slot values = model.denote (inventory.numeral position.val) values) ∧
        inventory.toConstructorPrograms.payloadMatches model values payload data := by
  rw [activeGuard, ConstructorDataPredicates.guard_denote model full]
  exact exists_congr (fun data => and_congr (inventory.activeCondition_holds model full slot values data) Iff.rfl)

theorem childGuard_denote (payload : Term Const Γ (payloadType inventory.fields))
    (slot : Term Const Γ inventory.number) (index : Term Const Γ inventory.index)
    (values : model.Valuation Γ) :
    (model.denote (inventory.childGuard payload slot index) values).down ↔
      ∃ data : inventory.toConstructorPrograms.Data model, (inventory.toConstructorPrograms.dataAllowed model values data ∧
        ∃ position : Fin (inventory.childCount data.1),
          model.denote slot values = model.denote (inventory.numeral position.val) values ∧
          inventory.childValue model values data position = model.denote index values) ∧
        inventory.toConstructorPrograms.payloadMatches model values payload data := by
  rw [childGuard, ConstructorDataPredicates.guard_denote model full]
  exact exists_congr (fun data => and_congr (inventory.childCondition_holds model full slot index values data) Iff.rfl)

#print axioms activeGuard_denote
#print axioms childGuard_denote

end Inventory
end Mettapedia.Logic.HOL.IndexedConstructorGuards
