import Mettapedia.Logic.HOL.IndexedConstructorGuardPrograms

/-!
# Position relations depending on constructor data

A position program relates a numerical slot and child index to the original
constructor fields. The relation can depend on those fields, so it is not
restricted to a fixed number of recursive children. Activity means that a
child index is related at the slot. Field validity and the payload image remain
separate conjuncts. Exactness and functionality are proved by each source
position interpretation rather than assumed by the generic syntax.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.IndexedConstructorGuards
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open FiniteConstructorEncoding CurriedPredicates
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ : Ctx Base}

structure PositionPrograms (constructors : ConstructorPrograms Const Γ) where
  graph : (occurrence : Fin constructors.fields.length) →
    Term Const Γ (constructors.number ⇒ constructors.index ⇒ handlerType (constructors.fields.get occurrence))

namespace PositionPrograms
variable {constructors : ConstructorPrograms Const Γ} (positions : PositionPrograms constructors)

def subst (rho : Subst Const Γ Δ) : PositionPrograms (constructors.subst rho) where
  graph := fun occurrence => HOL.subst rho (positions.graph occurrence)

def childCondition (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index) :
    ConstructorDataPredicates.Conditions Const Γ constructors.fields := fun occurrence =>
  conjoin _ (constructors.allowed occurrence) (.app (.app (positions.graph occurrence) slot) index)

def activeCondition (slot : Term Const Γ constructors.number) :
    ConstructorDataPredicates.Conditions Const Γ constructors.fields := fun occurrence =>
  conjoin _ (constructors.allowed occurrence) (existsValue _ (.app (positions.graph occurrence) slot))

def childGuard (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index) : Formula Const Γ :=
  ConstructorDataPredicates.guard constructors.fields (positions.childCondition slot index) payload

def activeGuard (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) : Formula Const Γ :=
  ConstructorDataPredicates.guard constructors.fields (positions.activeCondition slot) payload

variable (model : HenkinModel.{u,v,w} Base Const)

def related (values : model.Valuation Γ) (data : constructors.Data model)
    (slot : Ty.denote model.Carrier constructors.number) (index : Ty.denote model.Carrier constructors.index) : Prop :=
  (TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) (constructors.fields.get data.1)
    (handlerEquivalence model _ (model.denote (positions.graph data.1) values slot index)) data.2).down

theorem childCondition_holds (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index)
    (values : model.Valuation Γ) (data : constructors.Data model) :
    ConstructorDataPredicates.conditionMeaning model constructors.fields (positions.childCondition slot index) values data ↔
      constructors.dataAllowed model values data ∧
      positions.related model values data (model.denote slot values) (model.denote index values) := by
  change holds model _ (conjoin _ _ _) _ _ ↔ _
  rw [conjoin_holds]
  rfl

variable (full : model.FullDomains)
include full

theorem activeCondition_holds (slot : Term Const Γ constructors.number)
    (values : model.Valuation Γ) (data : constructors.Data model) :
    ConstructorDataPredicates.conditionMeaning model constructors.fields (positions.activeCondition slot) values data ↔
      constructors.dataAllowed model values data ∧
      ∃ index, positions.related model values data (model.denote slot values) index := by
  change holds model _ (conjoin _ _ _) _ _ ↔ _
  rw [conjoin_holds, existsValue_holds model full]
  rfl

theorem childGuard_denote (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index)
    (values : model.Valuation Γ) :
    (model.denote (positions.childGuard payload slot index) values).down ↔
      ∃ data : constructors.Data model, (constructors.dataAllowed model values data ∧
        positions.related model values data (model.denote slot values) (model.denote index values)) ∧
        constructors.payloadMatches model values payload data := by
  rw [childGuard, ConstructorDataPredicates.guard_denote model full]
  exact exists_congr (fun data => and_congr (positions.childCondition_holds model slot index values data) Iff.rfl)

theorem activeGuard_denote (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (values : model.Valuation Γ) :
    (model.denote (positions.activeGuard payload slot) values).down ↔
      ∃ data : constructors.Data model, (constructors.dataAllowed model values data ∧
        ∃ index, positions.related model values data (model.denote slot values) index) ∧
        constructors.payloadMatches model values payload data := by
  rw [activeGuard, ConstructorDataPredicates.guard_denote model full]
  exact exists_congr (fun data => and_congr (positions.activeCondition_holds model full slot values data) Iff.rfl)

theorem child_implies_active (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index)
    (values : model.Valuation Γ)
    (valid : (model.denote (positions.childGuard payload slot index) values).down) :
    (model.denote (positions.activeGuard payload slot) values).down := by
  obtain ⟨data, ⟨allowed, related⟩, agrees⟩ :=
    (positions.childGuard_denote model full payload slot index values).mp valid
  exact (positions.activeGuard_denote model full payload slot values).mpr
    ⟨data, ⟨allowed, model.denote index values, related⟩, agrees⟩

#print axioms activeCondition_holds
#print axioms childGuard_denote
#print axioms activeGuard_denote
#print axioms child_implies_active
end PositionPrograms
end Mettapedia.Logic.HOL.IndexedConstructorGuards
