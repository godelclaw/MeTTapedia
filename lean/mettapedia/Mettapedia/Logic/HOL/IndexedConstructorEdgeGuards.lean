import Mettapedia.Logic.HOL.IndexedConstructorRootGuards
import Mettapedia.Logic.HOL.IndexedConstructorGuards

/-!
# Edges guarded by the parent's computed child index

An edge quantifies over an index, checks the parent's child-index program at
the selected slot, and checks the child's generated root-index predicate at
that same index. Its meaning eliminates the intermediate index witness and
retains the parent data, slot and child equation. Every accepted edge has an
active parent slot.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.Inventory

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open FiniteConstructorEncoding CurriedPredicates
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ : Ctx Base}
variable (inventory : Inventory Const Γ) {space : Ty Base}
  (construct : Term Const Γ (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))

def edgeGuard (payload : Term Const Γ (payloadType inventory.fields))
    (slot : Term Const Γ inventory.number) (child : Term Const Γ space) : Formula Const Γ :=
  let rho : Subst Const Γ (inventory.index :: Γ) := fun index => .var (.vs index)
  let extended := inventory.subst rho
  .ex (.and (extended.childGuard (HOL.subst rho payload) (HOL.subst rho slot) (.var .vz))
    (extended.toConstructorPrograms.rootIndex (HOL.subst rho construct) (HOL.subst rho child) (.var .vz)))

variable (model : HenkinModel.{u,v,w} Base Const)

def edgeMeaning (values : model.Valuation Γ)
    (payload : Ty.denote model.Carrier (payloadType inventory.fields))
    (slot : Ty.denote model.Carrier inventory.number) (child : Ty.denote model.Carrier space) : Prop :=
  ∃ data : inventory.toConstructorPrograms.Data model, inventory.toConstructorPrograms.dataAllowed model values data ∧
    payloadEquivalence model inventory.fields payload =
      TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) inventory.fields data ∧
    ∃ position : Fin (inventory.childCount data.1),
      slot = model.denote (inventory.numeral position.val) values ∧
      inventory.toConstructorPrograms.rootMeaning construct model values child (inventory.childValue model values data position)

variable (full : model.FullDomains)
include full

theorem edgeGuard_denote (payload : Term Const Γ (payloadType inventory.fields))
    (slot : Term Const Γ inventory.number) (child : Term Const Γ space) (values : model.Valuation Γ) :
    (model.denote (inventory.edgeGuard construct payload slot child) values).down ↔
      inventory.edgeMeaning construct model values (model.denote payload values)
        (model.denote slot values) (model.denote child values) := by
  let rho : Subst Const Γ (inventory.index :: Γ) := fun index => .var (.vs index)
  let extended := inventory.subst rho
  have localMeaning (index : Ty.denote model.Carrier inventory.index) :
      (model.denote (extended.childGuard (HOL.subst rho payload) (HOL.subst rho slot) (.var .vz))
        (model.extend values index)).down ∧
      (model.denote (extended.toConstructorPrograms.rootIndex (HOL.subst rho construct) (HOL.subst rho child) (.var .vz))
        (model.extend values index)).down ↔
      (∃ data : inventory.toConstructorPrograms.Data model, (inventory.toConstructorPrograms.dataAllowed model values data ∧
        ∃ position : Fin (inventory.childCount data.1),
          model.denote slot values = model.denote (inventory.numeral position.val) values ∧
          inventory.childValue model values data position = index) ∧
        inventory.toConstructorPrograms.payloadMatches model values payload data) ∧
      inventory.toConstructorPrograms.rootMeaning construct model values (model.denote child values) index := by
    rw [extended.childGuard_denote model full, extended.toConstructorPrograms.rootIndex_denote _ model full]
    simp only [extended, rho, ConstructorPrograms.rootMeaning, ConstructorPrograms.resultValue, ConstructorPrograms.packedData,
      ConstructorPrograms.dataAllowed, childValue, ConstructorPrograms.payloadMatches, Inventory.subst, ConstructorPrograms.subst, holds,
      Soundness.denote_subst, HenkinModel.denote, PreModel.denote,
      HenkinModel.extend, PreModel.extend]
    rfl
  change (∃ index, model.adm _ index ∧ _ ∧ _) ↔ _
  constructor
  · rintro ⟨index, _, parent, child⟩
    obtain ⟨⟨data, ⟨allowed, position, slotSame, indexSame⟩, agrees⟩, root⟩ :=
      (localMeaning index).mp ⟨parent, child⟩
    exact ⟨data, allowed, agrees, position, slotSame, indexSame.symm ▸ root⟩
  · rintro ⟨data, allowed, agrees, position, slotSame, root⟩
    refine ⟨inventory.childValue model values data position, full _ _, ?_⟩
    exact (localMeaning _).mpr
      ⟨⟨data, ⟨allowed, position, slotSame, rfl⟩, agrees⟩, root⟩

theorem edge_implies_active (payload : Term Const Γ (payloadType inventory.fields))
    (slot : Term Const Γ inventory.number) (child : Term Const Γ space) (values : model.Valuation Γ)
    (valid : (model.denote (inventory.edgeGuard construct payload slot child) values).down) :
    (model.denote (inventory.activeGuard payload slot) values).down := by
  obtain ⟨data, allowed, agrees, position, same, _⟩ :=
    (inventory.edgeGuard_denote construct model full payload slot child values).mp valid
  exact (inventory.activeGuard_denote model full payload slot values).mpr
    ⟨data, ⟨allowed, position, same⟩, agrees⟩

#print axioms edgeGuard_denote
#print axioms edge_implies_active

end Mettapedia.Logic.HOL.IndexedConstructorGuards.Inventory
