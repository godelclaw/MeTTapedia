import Mettapedia.Logic.HOL.FiniteConstructorGuardProofs

/-!
# Data restrictions in constructor-image predicates

A constructor's data predicate remains an explicit part of its image guard.
This supports proper subcarriers and index conditions without identifying all
ambient HOL values with source values. Introduction consumes an actual proof
of the data predicate and retains the generated equality and existential steps.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding

open Mettapedia.TypeTheory.IndexedPolynomial.Description
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

def restrictedBody (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (payload : Term Const Γ (payloadType signature)) : ArgumentBody Const Γ (signature.get occurrence) :=
  fun substitution arguments =>
    .and (applyArguments (signature.get occurrence) (subst substitution condition) arguments)
      (.eq (subst substitution payload) (encode signature occurrence arguments))

theorem restrictedBody_natural (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (payload : Term Const Γ (payloadType signature)) : NaturalBody (restrictedBody signature occurrence condition payload) := by
  intro Δ Ξ earlier later arguments
  change Term.and
    (subst later (applyArguments (signature.get occurrence) (subst earlier condition) arguments))
    (.eq (subst later (subst earlier payload)) (subst later (encode signature occurrence arguments))) = _
  rw [applyArguments_subst, subst_comp, subst_comp, encode_subst]
  rfl

def restrictedPredicate (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (payload : Term Const Γ (payloadType signature)) : Term Const Γ (handlerType (signature.get occurrence)) :=
  abstractArguments (signature.get occurrence) (restrictedBody signature occurrence condition payload)

def restrictedGuard (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (payload : Term Const Γ (payloadType signature)) : Formula Const Γ :=
  existsArguments (signature.get occurrence) (restrictedPredicate signature occurrence condition payload)

variable (model : HenkinModel.{u,v,w} Base Const)

theorem restrictedPredicate_denote (full : model.FullDomains)
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (payload : Term Const Γ (payloadType signature)) (values : model.Valuation Γ)
    (data : Env (Ty.denote model.Carrier) (signature.get occurrence)) :
    (TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) (signature.get occurrence)
      (handlerEquivalence model _ (model.denote (restrictedPredicate signature occurrence condition payload) values)) data).down ↔
      (TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) (signature.get occurrence)
        (handlerEquivalence model _ (model.denote condition values)) data).down ∧
      payloadEquivalence model signature (model.denote payload values) =
        TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) signature ⟨occurrence, data⟩ := by
  have generated := abstractArguments_denote model (signature.get occurrence)
    (restrictedBody signature occurrence condition payload)
    (fun values data => ULift.up
      ((TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) (signature.get occurrence)
        (handlerEquivalence model _ (model.denote condition values)) data).down ∧
      payloadEquivalence model signature (model.denote payload values) =
        TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) signature ⟨occurrence, data⟩))
    (by
      intro Δ substitution arguments later
      apply congrArg ULift.up
      apply propext
      apply and_congr
      · change (model.denote (applyArguments _ (subst substitution condition) arguments) later).down ↔ _
        rw [applyArguments_denote, Soundness.denote_subst]
        rfl
      · change model.Eqv _ (model.denote (subst substitution payload) later)
          (model.denote (encode signature occurrence arguments) later) ↔ _
        rw [model.eqv_iff_eq_of_fullDomains full, Soundness.denote_subst]
        rw [← (payloadEquivalence model signature).injective.eq_iff, encode_denote]
        rfl) values data
  exact Iff.of_eq (congrArg ULift.down generated)

theorem restrictedGuard_denote (full : model.FullDomains)
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (payload : Term Const Γ (payloadType signature)) (values : model.Valuation Γ) :
    (model.denote (restrictedGuard signature occurrence condition payload) values).down ↔
      ∃ data : Env (Ty.denote model.Carrier) (signature.get occurrence),
        (TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) (signature.get occurrence)
          (handlerEquivalence model _ (model.denote condition values)) data).down ∧
        payloadEquivalence model signature (model.denote payload values) =
          TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) signature ⟨occurrence, data⟩ := by
  rw [restrictedGuard, existsArguments_denote model full]
  exact exists_congr (fun data => restrictedPredicate_denote model full signature occurrence condition payload values data)

def restrictedPredicate_beta {assumptions : List (Formula Const Γ)}
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (payload : Term Const Γ (payloadType signature))
    (arguments : Arguments Const Γ (signature.get occurrence)) :
    ProofSyntax Const assumptions
      (.eq (applyArguments _ (restrictedPredicate signature occurrence condition payload) arguments)
        (.and (applyArguments _ condition arguments) (.eq payload (encode signature occurrence arguments)))) := by
  have generated := abstractArguments_beta (assumptions := assumptions) (signature.get occurrence)
    (restrictedBody signature occurrence condition payload)
    (restrictedBody_natural signature occurrence condition payload) arguments
  apply ProofSyntax.castIndices rfl ?_ generated
  apply congrArg (Term.eq _)
  exact congrArg₂ Term.and
    (congrArg (fun value => applyArguments _ value arguments) (subst_id condition))
    (congrArg (fun value => Term.eq value (encode signature occurrence arguments)) (subst_id payload))

def restrictedGuard_intro {assumptions : List (Formula Const Γ)}
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (arguments : Arguments Const Γ (signature.get occurrence))
    (dataProof : ProofSyntax Const assumptions (applyArguments _ condition arguments)) :
    ProofSyntax Const assumptions (restrictedGuard signature occurrence condition (encode signature occurrence arguments)) :=
  existsArguments_intro _ (restrictedPredicate signature occurrence condition (encode signature occurrence arguments)) arguments
    (.impE (.eqPropER (restrictedPredicate_beta signature occurrence condition (encode signature occurrence arguments) arguments))
      (.andI dataProof (.eqRefl (encode signature occurrence arguments))))

set_option backward.isDefEq.respectTransparency false in
theorem restrictedPredicate_beta_free {assumptions : List (Formula Const Γ)}
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (payload : Term Const Γ (payloadType signature))
    (arguments : Arguments Const Γ (signature.get occurrence)) :
    (restrictedPredicate_beta (assumptions := assumptions) signature occurrence condition payload arguments).FunctionExtensionalityFree := by
  unfold restrictedPredicate_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractArguments_beta_free _ _ _ _

theorem restrictedGuard_intro_free {assumptions : List (Formula Const Γ)}
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (arguments : Arguments Const Γ (signature.get occurrence))
    (dataProof : ProofSyntax Const assumptions (applyArguments _ condition arguments))
    (free : dataProof.FunctionExtensionalityFree) :
    (restrictedGuard_intro signature occurrence condition arguments dataProof).FunctionExtensionalityFree := by
  apply existsArguments_intro_free
  exact ⟨restrictedPredicate_beta_free _ _ _ _ _, free, True.intro⟩

#print axioms restrictedGuard_denote
#print axioms restrictedGuard_intro
#print axioms restrictedGuard_intro_free

end Mettapedia.Logic.HOL.FiniteConstructorEncoding
