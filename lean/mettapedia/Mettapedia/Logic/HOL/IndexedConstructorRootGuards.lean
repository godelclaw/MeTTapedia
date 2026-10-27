import Mettapedia.Logic.HOL.ConstructorPrograms

/-!
# Root-index predicates over constructor encodings

The predicate selects one constructor occurrence, quantifies over its original
data fields and complete child function, and checks both the generated result
index and the actual constructor equation. The same data witness supplies all
three observations. Recursive validity of children belongs to the separate
least-predicate operator.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open FiniteConstructorEncoding CurriedPredicates
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ : Ctx Base}

variable (inventory : ConstructorPrograms Const Γ) {space : Ty Base}
  (construct : Term Const Γ (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))

def rootBody (value : Term Const Γ space) (index : Term Const Γ inventory.index)
    (occurrence : Fin inventory.fields.length) : ArgumentBody Const Γ (inventory.fields.get occurrence) :=
  fun rho arguments =>
    .and (applyArguments _ (HOL.subst rho (inventory.allowed occurrence)) arguments)
      (.and (.eq (applyFields _ (HOL.subst rho (inventory.result occurrence)) arguments) (HOL.subst rho index))
        (.ex (σ := inventory.number ⇒ space)
          (.eq (weaken (HOL.subst rho value))
            (.app (.app (.app (weaken (HOL.subst rho construct))
              (weaken (HOL.subst rho (inventory.numeral occurrence.val))))
              (weaken (encode inventory.fields occurrence arguments))) (.var .vz)))))

def rootCondition (value : Term Const Γ space) (index : Term Const Γ inventory.index)
    (occurrence : Fin inventory.fields.length) : Term Const Γ (handlerType (inventory.fields.get occurrence)) :=
  abstractArguments _ (inventory.rootBody construct value index occurrence)

def rootIndex (value : Term Const Γ space) (index : Term Const Γ inventory.index) : Formula Const Γ :=
  any (List.ofFn (fun occurrence => existsArguments _ (inventory.rootCondition construct value index occurrence)))

variable (model : HenkinModel.{u,v,w} Base Const)

def packedData (data : inventory.Data model) : Ty.denote model.Carrier (payloadType inventory.fields) :=
  (payloadEquivalence model inventory.fields).symm
    (TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) inventory.fields data)

theorem encode_packed {Ξ : Ctx Base} (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Ξ (inventory.fields.get occurrence)) (values : model.Valuation Ξ) :
    model.denote (encode inventory.fields occurrence arguments) values =
      inventory.packedData model ⟨occurrence, denoteArguments model _ arguments values⟩ := by
  apply (payloadEquivalence model inventory.fields).injective
  rw [encode_denote]
  exact (payloadEquivalence model inventory.fields).apply_symm_apply _ |>.symm

def rootMeaning (values : model.Valuation Γ) (value : Ty.denote model.Carrier space)
    (index : Ty.denote model.Carrier inventory.index) : Prop :=
  ∃ data : inventory.Data model, inventory.dataAllowed model values data ∧
    inventory.resultValue model values data = index ∧
    ∃ children : Ty.denote model.Carrier (inventory.number ⇒ space),
      value = model.denote construct values
        (model.denote (inventory.numeral data.1.val) values) (inventory.packedData model data) children

theorem packedData_injective : Function.Injective (inventory.packedData model) :=
  (payloadEquivalence model inventory.fields).symm.injective.comp
    (TypeTheory.FiniteConstructorEncoding.encode_injective _ _)

theorem rootMeaning_unique_index (values : model.Valuation Γ)
    (payload_injective : ∀ tag payload children tag' payload' children',
      model.denote construct values tag payload children =
        model.denote construct values tag' payload' children' → payload = payload')
    {value : Ty.denote model.Carrier space} {first second : Ty.denote model.Carrier inventory.index}
    (firstRoot : inventory.rootMeaning construct model values value first)
    (secondRoot : inventory.rootMeaning construct model values value second) : first = second := by
  obtain ⟨firstData, _, firstIndex, firstChildren, firstEquation⟩ := firstRoot
  obtain ⟨secondData, _, secondIndex, secondChildren, secondEquation⟩ := secondRoot
  have same := inventory.packedData_injective model
    (payload_injective _ _ _ _ _ _ (firstEquation.symm.trans secondEquation))
  cases same
  exact firstIndex.symm.trans secondIndex

theorem rootMeaning_refuses_bottom (values : model.Valuation Γ)
    (bottom : Ty.denote model.Carrier space)
    (separation : ∀ tag payload children, model.denote construct values tag payload children ≠ bottom)
    (index : Ty.denote model.Carrier inventory.index) :
    ¬ inventory.rootMeaning construct model values bottom index := by
  rintro ⟨data, _, _, children, equation⟩
  exact separation _ _ _ equation.symm

theorem rootMeaning_subst (rho : Subst Const Γ Δ) (values : model.Valuation Δ)
    (value : Ty.denote model.Carrier space) (index : Ty.denote model.Carrier inventory.index) :
    (inventory.subst rho).rootMeaning (HOL.subst rho construct) model values value index ↔
      inventory.rootMeaning construct model (Soundness.substVal model rho values) value index := by
  simp only [rootMeaning, dataAllowed, resultValue, packedData, ConstructorPrograms.subst, holds,
    Soundness.denote_subst]
  rfl

variable (full : model.FullDomains)
include full

theorem rootCondition_holds (value : Term Const Γ space) (index : Term Const Γ inventory.index)
    (occurrence : Fin inventory.fields.length) (values : model.Valuation Γ)
    (data : Env (Ty.denote model.Carrier) (inventory.fields.get occurrence)) :
    holds model _ (inventory.rootCondition construct value index occurrence) values data ↔
      inventory.dataAllowed model values ⟨occurrence, data⟩ ∧
      inventory.resultValue model values ⟨occurrence, data⟩ = model.denote index values ∧
      ∃ children : Ty.denote model.Carrier (inventory.number ⇒ space),
        model.denote value values = model.denote construct values
          (model.denote (inventory.numeral occurrence.val) values)
          (inventory.packedData model ⟨occurrence, data⟩) children := by
  have law := abstractArguments_denote model _ (inventory.rootBody construct value index occurrence)
    (fun values data => ULift.up
      (inventory.dataAllowed model values ⟨occurrence, data⟩ ∧
       inventory.resultValue model values ⟨occurrence, data⟩ = model.denote index values ∧
       ∃ children : Ty.denote model.Carrier (inventory.number ⇒ space),
         model.denote value values = model.denote construct values
           (model.denote (inventory.numeral occurrence.val) values)
           (inventory.packedData model ⟨occurrence, data⟩) children))
    (by
      intro Ξ rho arguments later
      have admitted : ∀ type value, model.adm type value := full
      apply ULift.ext
      apply propext
      change (model.denote (applyArguments _ (HOL.subst rho (inventory.allowed occurrence)) arguments) later).down ∧
        model.Eqv _ (model.denote (applyFields _ (HOL.subst rho (inventory.result occurrence)) arguments) later)
          (model.denote (HOL.subst rho index) later) ∧
        (∃ children, model.adm _ children ∧ model.Eqv _
          (model.denote (weaken (HOL.subst rho value)) (model.extend later children))
          (model.denote (weaken (HOL.subst rho construct)) (model.extend later children)
            (model.denote (weaken (HOL.subst rho (inventory.numeral occurrence.val))) (model.extend later children))
            (model.denote (weaken (encode inventory.fields occurrence arguments)) (model.extend later children))
            children)) ↔ _
      simp only [applyArguments_denote, applyFields_denote, model.eqv_iff_eq_of_fullDomains full,
        admitted, true_and, Soundness.denote_weaken, Soundness.denote_subst]
      rw [inventory.encode_packed model]
      rfl) values data
  exact Iff.of_eq (congrArg ULift.down law)

theorem rootIndex_denote (value : Term Const Γ space) (index : Term Const Γ inventory.index)
    (values : model.Valuation Γ) :
    (model.denote (inventory.rootIndex construct value index) values).down ↔
      inventory.rootMeaning construct model values (model.denote value values) (model.denote index values) := by
  rw [rootIndex, any_denote]
  constructor
  · rintro ⟨formula, member, valid⟩
    obtain ⟨occurrence, rfl⟩ := List.mem_ofFn.mp member
    obtain ⟨data, valid⟩ := (existsArguments_denote model full _ _ values).mp valid
    exact ⟨⟨occurrence, data⟩, (inventory.rootCondition_holds construct model full value index occurrence values data).mp valid⟩
  · rintro ⟨⟨occurrence, data⟩, valid⟩
    refine ⟨_, List.mem_ofFn.mpr ⟨occurrence, rfl⟩, ?_⟩
    apply (existsArguments_denote model full _ _ values).mpr
    exact ⟨data, (inventory.rootCondition_holds construct model full value index occurrence values data).mpr valid⟩

#print axioms rootCondition_holds
#print axioms rootIndex_denote
#print axioms rootMeaning_unique_index
#print axioms rootMeaning_refuses_bottom

end Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms
