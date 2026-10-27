import Mettapedia.Logic.HOL.FiniteConstructorGuardRestrictions

/-!
# Predicates over encoded constructor data

Each constructor supplies a predicate on its original fields. The generated
payload predicate quantifies over those fields and retains their encoding
equation. On an encoded value it is exactly the selected constructor's field
predicate; injectivity excludes alternative constructors and alternative data.
Introduction constructs a retained proof from the supplied field proof.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ConstructorDataPredicates

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open FiniteConstructorEncoding
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

abbrev Conditions (Const : Ty Base → Type v) (Γ : Ctx Base)
    (signature : List (List (Ty Base))) :=
  (occurrence : Fin signature.length) → Term Const Γ (handlerType (signature.get occurrence))

def guard (signature : List (List (Ty Base))) (conditions : Conditions Const Γ signature)
    (payload : Term Const Γ (payloadType signature)) : Formula Const Γ :=
  any (List.ofFn (fun occurrence => restrictedGuard signature occurrence (conditions occurrence) payload))

variable (model : HenkinModel.{u,v,w} Base Const)

def conditionMeaning (signature : List (List (Ty Base)))
    (conditions : Conditions Const Γ signature) (values : model.Valuation Γ)
    (data : TypeTheory.FiniteConstructorEncoding.Data (Ty.denote model.Carrier) signature) : Prop :=
  (TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) (signature.get data.1)
    (handlerEquivalence model _ (model.denote (conditions data.1) values)) data.2).down

theorem guard_denote (full : model.FullDomains)
    (signature : List (List (Ty Base))) (conditions : Conditions Const Γ signature)
    (payload : Term Const Γ (payloadType signature)) (values : model.Valuation Γ) :
    (model.denote (guard signature conditions payload) values).down ↔
      ∃ data : TypeTheory.FiniteConstructorEncoding.Data (Ty.denote model.Carrier) signature,
        conditionMeaning model signature conditions values data ∧
        payloadEquivalence model signature (model.denote payload values) =
          TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) signature data := by
  rw [guard, any_denote]
  constructor
  · rintro ⟨formula, member, holds⟩
    obtain ⟨occurrence, rfl⟩ := List.mem_ofFn.mp member
    obtain ⟨data, valid, same⟩ :=
      (restrictedGuard_denote model full signature occurrence (conditions occurrence) payload values).mp holds
    exact ⟨⟨occurrence, data⟩, valid, same⟩
  · rintro ⟨⟨occurrence, data⟩, valid, same⟩
    refine ⟨_, List.mem_ofFn.mpr ⟨occurrence, rfl⟩, ?_⟩
    exact (restrictedGuard_denote model full signature occurrence (conditions occurrence) payload values).mpr
      ⟨data, valid, same⟩

theorem guard_on_encoded (full : model.FullDomains)
    (signature : List (List (Ty Base))) (conditions : Conditions Const Γ signature)
    (occurrence : Fin signature.length) (arguments : Arguments Const Γ (signature.get occurrence))
    (values : model.Valuation Γ) :
    (model.denote (guard signature conditions (encode signature occurrence arguments)) values).down ↔
      conditionMeaning model signature conditions values
        ⟨occurrence, denoteArguments model _ arguments values⟩ := by
  rw [guard_denote model full, encode_denote]
  constructor
  · rintro ⟨data, valid, same⟩
    have exactData := TypeTheory.FiniteConstructorEncoding.encode_injective _ _ same
    exact exactData.symm ▸ valid
  · intro valid
    exact ⟨_, valid, rfl⟩

theorem guard_refuses_outside_image (full : model.FullDomains)
    (signature : List (List (Ty Base))) (conditions : Conditions Const Γ signature)
    (payload : Term Const Γ (payloadType signature)) (values : model.Valuation Γ)
    (outside : ¬ TypeTheory.FiniteConstructorEncoding.Valid (Ty.denote model.Carrier) signature
      (payloadEquivalence model signature (model.denote payload values))) :
    ¬ (model.denote (guard signature conditions payload) values).down := by
  intro holds
  obtain ⟨data, _, same⟩ := (guard_denote model full signature conditions payload values).mp holds
  exact outside ⟨data, same.symm⟩

def introduce {assumptions : List (Formula Const Γ)}
    (signature : List (List (Ty Base))) (conditions : Conditions Const Γ signature)
    (occurrence : Fin signature.length) (arguments : Arguments Const Γ (signature.get occurrence))
    (dataProof : ProofSyntax Const assumptions (applyArguments _ (conditions occurrence) arguments)) :
    ProofSyntax Const assumptions (guard signature conditions (encode signature occurrence arguments)) := by
  let formulas := List.ofFn (fun selected =>
    restrictedGuard signature selected (conditions selected) (encode signature occurrence arguments))
  have bound : occurrence.val < formulas.length := by
    simpa only [formulas, List.length_ofFn] using occurrence.isLt
  apply any_introAt formulas ⟨occurrence.val, bound⟩
  apply ProofSyntax.castIndices rfl ?_
    (restrictedGuard_intro signature occurrence (conditions occurrence) arguments dataProof)
  simp only [formulas, List.get_eq_getElem, List.getElem_ofFn]

set_option backward.isDefEq.respectTransparency false in
theorem introduce_free {assumptions : List (Formula Const Γ)}
    (signature : List (List (Ty Base))) (conditions : Conditions Const Γ signature)
    (occurrence : Fin signature.length) (arguments : Arguments Const Γ (signature.get occurrence))
    (dataProof : ProofSyntax Const assumptions (applyArguments _ (conditions occurrence) arguments))
    (free : dataProof.FunctionExtensionalityFree) :
    (introduce signature conditions occurrence arguments dataProof).FunctionExtensionalityFree := by
  unfold introduce
  apply any_introAt_free
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact restrictedGuard_intro_free _ _ _ _ _ free

#print axioms guard_denote
#print axioms guard_on_encoded
#print axioms introduce
#print axioms introduce_free

end Mettapedia.Logic.HOL.ConstructorDataPredicates
