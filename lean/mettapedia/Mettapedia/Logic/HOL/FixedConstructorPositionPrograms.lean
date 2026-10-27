import Mettapedia.Logic.HOL.ConstructorPositionEdges

/-!
# Fixed recursive fields as position programs

The adapter compiles the original finite child inventory into a typed graph
predicate. Its slot/index relation retains the original child programs. Active,
child-index and edge observations agree with the existing fixed-field guards.
The existing fixed-field programs remain an independently qualified realization.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.Inventory
open FiniteConstructorEncoding CurriedPredicates ConstructorPrograms
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
variable (inventory : Inventory Const Γ)

def toPositionPrograms : PositionPrograms inventory.toConstructorPrograms where
  graph := fun occurrence => .lam (.lam
    (CurriedPredicates.choose (inventory.fields.get occurrence) (fun position => conjoin _
      (constant _ (.eq (.var (.vs .vz)) (HOL.subst beneathTwo (inventory.numeral position.val))))
      (equalTo _ (HOL.subst beneathTwo (inventory.child occurrence position)) (.var .vz)))))

variable (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains)
include full

theorem position_relation (values : model.Valuation Γ)
    (data : inventory.toConstructorPrograms.Data model)
    (slot : Ty.denote model.Carrier inventory.number) (index : Ty.denote model.Carrier inventory.index) :
    inventory.toPositionPrograms.related model values data slot index ↔
      ∃ position : Fin (inventory.childCount data.1),
        slot = model.denote (inventory.numeral position.val) values ∧
        inventory.childValue model values data position = index := by
  change holds model _ (CurriedPredicates.choose _ _) (model.extend (model.extend values slot) index) data.2 ↔ _
  rw [choose_holds]
  apply exists_congr
  intro position
  rw [conjoin_holds, constant_holds, equalTo_holds model full]
  change model.Eqv _ slot _ ∧ _ ↔ _
  rw [model.eqv_iff_eq_of_fullDomains full]
  simp only [Soundness.denote_subst, childValue]
  rfl

theorem active_agreement (payload : Term Const Γ (payloadType inventory.fields))
    (slot : Term Const Γ inventory.number) (values : model.Valuation Γ) :
    (model.denote (inventory.toPositionPrograms.activeGuard payload slot) values).down ↔
      (model.denote (inventory.activeGuard payload slot) values).down := by
  rw [inventory.toPositionPrograms.activeGuard_denote model full, inventory.activeGuard_denote model full]
  constructor
  · rintro ⟨data, ⟨allowed, index, relation⟩, agrees⟩
    obtain ⟨position, same, _⟩ := (inventory.position_relation model full values data _ index).mp relation
    exact ⟨data, ⟨allowed, position, same⟩, agrees⟩
  · rintro ⟨data, ⟨allowed, position, same⟩, agrees⟩
    exact ⟨data, ⟨allowed, inventory.childValue model values data position,
      (inventory.position_relation model full values data _ _).mpr ⟨position, same, rfl⟩⟩, agrees⟩

theorem child_agreement (payload : Term Const Γ (payloadType inventory.fields))
    (slot : Term Const Γ inventory.number) (index : Term Const Γ inventory.index) (values : model.Valuation Γ) :
    (model.denote (inventory.toPositionPrograms.childGuard payload slot index) values).down ↔
      (model.denote (inventory.childGuard payload slot index) values).down := by
  rw [inventory.toPositionPrograms.childGuard_denote model full, inventory.childGuard_denote model full]
  exact exists_congr (fun data => and_congr
    (and_congr Iff.rfl (inventory.position_relation model full values data _ _)) Iff.rfl)

theorem edgeMeaning_agreement {space : Ty Base}
    (construct : Term Const Γ (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (values : model.Valuation Γ) (payload : Ty.denote model.Carrier (payloadType inventory.fields))
    (slot : Ty.denote model.Carrier inventory.number) (child : Ty.denote model.Carrier space) :
    inventory.toPositionPrograms.edgeMeaning construct model values payload slot child ↔
      inventory.edgeMeaning construct model values payload slot child := by
  constructor
  · rintro ⟨data, allowed, agrees, index, relation, root⟩
    obtain ⟨position, same, indexSame⟩ := (inventory.position_relation model full values data _ index).mp relation
    exact ⟨data, allowed, agrees, position, same, indexSame.symm ▸ root⟩
  · rintro ⟨data, allowed, agrees, position, same, root⟩
    exact ⟨data, allowed, agrees, inventory.childValue model values data position,
      (inventory.position_relation model full values data _ _).mpr ⟨position, same, rfl⟩, root⟩

theorem edge_agreement {space : Ty Base}
    (construct : Term Const Γ (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (payload : Term Const Γ (payloadType inventory.fields))
    (slot : Term Const Γ inventory.number) (child : Term Const Γ space) (values : model.Valuation Γ) :
    (model.denote (inventory.toPositionPrograms.edgeGuard construct payload slot child) values).down ↔
      (model.denote (inventory.edgeGuard construct payload slot child) values).down := by
  rw [inventory.toPositionPrograms.edgeGuard_denote construct model full,
    inventory.edgeGuard_denote construct model full]
  exact inventory.edgeMeaning_agreement model full construct values _ _ _

theorem edgeProgram_agreement {space : Ty Base}
    (construct : Term Const Γ (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (values : model.Valuation Γ) (payload : Ty.denote model.Carrier (payloadType inventory.fields))
    (slot : Ty.denote model.Carrier inventory.number) (child : Ty.denote model.Carrier space) :
    (model.denote (inventory.toPositionPrograms.edgeProgram construct) values payload slot child).down ↔
      (model.denote (inventory.edgeProgram construct) values payload slot child).down := by
  rw [inventory.toPositionPrograms.edgeProgram_denote construct model full,
    inventory.edgeProgram_denote construct model full]
  exact inventory.edgeMeaning_agreement model full construct values payload slot child

#print axioms position_relation
#print axioms active_agreement
#print axioms child_agreement
#print axioms edge_agreement
end Mettapedia.Logic.HOL.IndexedConstructorGuards.Inventory
