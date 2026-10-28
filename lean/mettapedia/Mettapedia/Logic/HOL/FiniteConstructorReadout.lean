import Mettapedia.Logic.HOL.FiniteConstructorGuardProofs

/-!
# Retained observations and field recovery for constructor payloads

Applying an encoded constructor to a typed handler vector computes the
selected handler on the original fields. The retained beta proof follows
the complete constructor inventory and its original occurrence address.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding

open Mettapedia.TypeTheory.IndexedPolynomial.Description
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}

abbrev Handlers (Const : Ty Base → Type v) (Γ : Ctx Base) (signature : List (List (Ty Base))) :=
  Env (fun fields => Term Const Γ (handlerType fields)) signature

def selectHandler : (signature : List (List (Ty Base))) → (occurrence : Fin signature.length) →
    Handlers Const Γ signature → Term Const Γ (handlerType (signature.get occurrence))
  | [], occurrence, _ => Fin.elim0 occurrence
  | _ :: _, ⟨0, _⟩, handlers => handlers.1
  | _ :: rest, ⟨n + 1, bound⟩, handlers => selectHandler rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩ handlers.2

def observe : (signature : List (List (Ty Base))) →
    Term Const Γ (payloadType signature) → Handlers Const Γ signature → Formula Const Γ
  | [], payload, _ => payload
  | _ :: rest, payload, handlers => observe rest (.app payload handlers.1) handlers.2

def substituteHandlers (σ : Subst Const Γ Ξ) : (signature : List (List (Ty Base))) →
    Handlers Const Γ signature → Handlers Const Ξ signature
  | [], _ => PUnit.unit
  | _ :: rest, handlers => (subst σ handlers.1, substituteHandlers σ rest handlers.2)

theorem observe_subst (σ : Subst Const Γ Ξ) (signature : List (List (Ty Base)))
    (payload : Term Const Γ (payloadType signature)) (handlers : Handlers Const Γ signature) :
    subst σ (observe signature payload handlers) = observe signature (subst σ payload) (substituteHandlers σ signature handlers) := by
  induction signature with
  | nil => rfl
  | cons fields rest ih => exact ih (.app payload handlers.1) handlers.2

theorem substituteArguments_single {type : Ty Base} (value : Term Const Γ type)
    (fields : List (Ty Base)) (arguments : Arguments Const Γ fields) :
    substituteArguments (Subst.single value) fields (weakenArguments type fields arguments) = arguments := by
  induction fields with
  | nil => cases arguments; rfl
  | cons field rest ih =>
    change (instantiate value (weaken arguments.1),
      substituteArguments (Subst.single value) rest (weakenArguments type rest arguments.2)) = _
    rw [instantiate_weaken, ih]
    rfl

variable {Δ : List (Formula Const Γ)}

def observe_congr (signature : List (List (Ty Base)))
    (first second : Term Const Γ (payloadType signature)) (handlers : Handlers Const Γ signature)
    (proof : ProofSyntax Const Δ (.eq first second)) :
    ProofSyntax Const Δ (.eq (observe signature first handlers) (observe signature second handlers)) := by
  induction signature with
  | nil => exact proof
  | cons fields rest ih => exact ih (.app first handlers.1) (.app second handlers.1) handlers.2 (.eqApp handlers.1 proof)

theorem observe_congr_free (signature : List (List (Ty Base)))
    (first second : Term Const Γ (payloadType signature)) (handlers : Handlers Const Γ signature)
    (proof : ProofSyntax Const Δ (.eq first second)) (free : proof.FunctionExtensionalityFree) :
    (observe_congr signature first second handlers proof).FunctionExtensionalityFree := by
  induction signature with
  | nil => exact free
  | cons fields rest ih => exact ih _ _ handlers.2 (.eqApp handlers.1 proof) free

def ignoreHandlers_beta (signature : List (List (Ty Base))) (body : Formula Const Γ)
    (handlers : Handlers Const Γ signature) :
    ProofSyntax Const Δ (.eq (observe signature (ignoreHandlers signature body) handlers) body) := by
  induction signature with
  | nil => exact .eqRefl body
  | cons fields rest ih =>
    have erased : ProofSyntax Const Δ (.eq (.app (ignoreHandlers (fields :: rest) body) handlers.1)
        (ignoreHandlers rest body)) := by
      apply ProofSyntax.castIndices rfl ?_ (.beta handlers.1 (ignoreHandlers rest (weaken body)))
      simp only [ignoreHandlers, instantiate, ignoreHandlers_subst]
      exact congrArg (Term.eq _) (congrArg (ignoreHandlers rest) (instantiate_weaken handlers.1 body))
    exact .eqTrans (observe_congr rest _ _ handlers.2 erased) (ih handlers.2)

theorem ignoreHandlers_beta_free (signature : List (List (Ty Base))) (body : Formula Const Γ)
    (handlers : Handlers Const Γ signature) :
    (ignoreHandlers_beta (Δ := Δ) signature body handlers).FunctionExtensionalityFree := by
  induction signature with
  | nil => trivial
  | cons fields rest ih =>
    change (observe_congr _ _ _ _ _).FunctionExtensionalityFree ∧ _
    exact ⟨observe_congr_free _ _ _ _ _ (by simp [ProofSyntax.FunctionExtensionalityFree]), ih handlers.2⟩

/-- The proof computes the selected constructor handler without replacing
the typed encoder by a separately defined observation function. -/
def encode_beta (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence)) (handlers : Handlers Const Γ signature) :
    ProofSyntax Const Δ (.eq (observe signature (encode signature occurrence arguments) handlers)
      (applyArguments (signature.get occurrence) (selectHandler signature occurrence handlers) arguments)) := by
  induction signature with
  | nil => exact Fin.elim0 occurrence
  | cons fields rest ih =>
    rcases occurrence with ⟨index, bound⟩
    cases index with
    | zero =>
      have selected : ProofSyntax Const Δ
          (.eq (.app (encode (fields :: rest) ⟨0, bound⟩ arguments) handlers.1)
            (ignoreHandlers rest (applyArguments fields handlers.1 arguments))) := by
        apply ProofSyntax.castIndices rfl ?_
          (.beta handlers.1 (ignoreHandlers rest (applyArguments fields (.var .vz)
            (weakenArguments (handlerType fields) fields arguments))))
        simp [encode, instantiate, ignoreHandlers_subst, applyArguments_subst,
          subst, Subst.single, substituteArguments_single]
      exact .eqTrans (observe_congr rest _ _ handlers.2 selected)
        (ignoreHandlers_beta rest (applyArguments fields handlers.1 arguments) handlers.2)
    | succ index =>
      let prior : Fin rest.length := ⟨index, Nat.lt_of_succ_lt_succ bound⟩
      have skipped : ProofSyntax Const Δ
          (.eq (.app (encode (fields :: rest) ⟨index + 1, bound⟩ arguments) handlers.1)
            (encode rest prior arguments)) := by
        apply ProofSyntax.castIndices rfl ?_
          (.beta handlers.1 (encode rest prior (weakenArguments (handlerType fields) _ arguments)))
        simp [encode, prior, instantiate, encode_subst, substituteArguments_single]
      exact .eqTrans (observe_congr rest _ _ handlers.2 skipped) (ih prior arguments handlers.2)

theorem encode_beta_free (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence)) (handlers : Handlers Const Γ signature) :
    (encode_beta (Δ := Δ) signature occurrence arguments handlers).FunctionExtensionalityFree := by
  induction signature with
  | nil => exact Fin.elim0 occurrence
  | cons fields rest ih =>
    rcases occurrence with ⟨index, bound⟩
    cases index with
    | zero =>
      change (observe_congr _ _ _ _ _).FunctionExtensionalityFree ∧ _
      exact ⟨observe_congr_free _ _ _ _ _ (by simp [ProofSyntax.FunctionExtensionalityFree]), ignoreHandlers_beta_free _ _ _⟩
    | succ index =>
      change (observe_congr _ _ _ _ _).FunctionExtensionalityFree ∧ _
      exact ⟨observe_congr_free _ _ _ _ _ (by simp [ProofSyntax.FunctionExtensionalityFree]), ih _ arguments handlers.2⟩

def argumentAt {fields : List (Ty Base)} {type : Ty Base} :
    Var fields type → Arguments Const Γ fields → Term Const Γ type
  | .vz, arguments => arguments.1
  | .vs index, arguments => argumentAt index arguments.2

theorem argumentAt_subst (σ : Subst Const Γ Ξ) {fields : List (Ty Base)} {type : Ty Base}
    (index : Var fields type) (arguments : Arguments Const Γ fields) :
    subst σ (argumentAt index arguments) = argumentAt index (substituteArguments σ fields arguments) := by
  induction index with
  | vz => rfl
  | vs index ih => exact ih arguments.2

def fieldHandler {fields : List (Ty Base)} {type : Ty Base} (index : Var fields type)
    (expected : Term Const Γ type) : Term Const Γ (handlerType fields) :=
  abstractArguments fields (fun σ arguments => .eq (argumentAt index arguments) (subst σ expected))

theorem fieldBody_natural {fields : List (Ty Base)} {type : Ty Base}
    (index : Var fields type) (expected : Term Const Γ type) :
    NaturalBody (fun σ arguments => Term.eq (argumentAt index arguments) (subst σ expected)) := by
  intro Ξ Ω earlier later arguments
  change Term.eq (subst later (argumentAt index arguments)) (subst later (subst earlier expected)) = _
  rw [argumentAt_subst, subst_comp]
  rfl

def fieldHandler_beta {fields : List (Ty Base)} {type : Ty Base}
    (index : Var fields type) (expected : Term Const Γ type) (arguments : Arguments Const Γ fields) :
    ProofSyntax Const Δ (.eq (applyArguments fields (fieldHandler index expected) arguments)
      (.eq (argumentAt index arguments) expected)) := by
  apply ProofSyntax.castIndices rfl ?_
    (abstractArguments_beta fields (fun σ arguments => .eq (argumentAt index arguments) (subst σ expected))
      (fieldBody_natural index expected) arguments)
  exact congrArg (Term.eq _) (congrArg (Term.eq _) (subst_id expected))

def falseHandlers : (signature : List (List (Ty Base))) → Handlers Const Γ signature
  | [] => PUnit.unit
  | fields :: rest => (abstractArguments fields (fun _ _ => .bot), falseHandlers rest)

def withHandler : (signature : List (List (Ty Base))) → (occurrence : Fin signature.length) →
    Term Const Γ (handlerType (signature.get occurrence)) → Handlers Const Γ signature
  | [], occurrence, _ => Fin.elim0 occurrence
  | _ :: rest, ⟨0, _⟩, handler => (handler, falseHandlers rest)
  | fields :: rest, ⟨n + 1, bound⟩, handler =>
    (abstractArguments fields (fun _ _ => .bot), withHandler rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩ handler)

theorem select_withHandler (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (handler : Term Const Γ (handlerType (signature.get occurrence))) :
    selectHandler signature occurrence (withHandler signature occurrence handler) = handler := by
  induction signature with
  | nil => exact Fin.elim0 occurrence
  | cons fields rest ih =>
    rcases occurrence with ⟨index, bound⟩
    cases index with
    | zero => rfl
    | succ index => exact ih ⟨index, Nat.lt_of_succ_lt_succ bound⟩ handler

def observe_field (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    {type : Ty Base} (index : Var (signature.get occurrence) type) (expected : Term Const Γ type)
    (arguments : Arguments Const Γ (signature.get occurrence)) :
    ProofSyntax Const Δ (.eq
      (observe signature (encode signature occurrence arguments)
        (withHandler signature occurrence (fieldHandler index expected)))
      (.eq (argumentAt index arguments) expected)) := by
  have observed := encode_beta (Δ := Δ) signature occurrence arguments
    (withHandler signature occurrence (fieldHandler index expected))
  have selected : ProofSyntax Const Δ (.eq
      (observe signature (encode signature occurrence arguments)
        (withHandler signature occurrence (fieldHandler index expected)))
      (applyArguments (signature.get occurrence) (fieldHandler index expected) arguments)) := by
    apply ProofSyntax.castIndices rfl ?_ observed
    rw [select_withHandler]
  exact .eqTrans selected (fieldHandler_beta index expected arguments)

/-- Payload equality implies equality of every original typed field at the
same constructor occurrence. Only application, beta and logical equality
elimination are used; no payload injectivity axiom is supplied. -/
def recover_field (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    {type : Ty Base} (index : Var (signature.get occurrence) type)
    (first second : Arguments Const Γ (signature.get occurrence))
    (same : ProofSyntax Const Δ (.eq (encode signature occurrence first) (encode signature occurrence second))) :
    ProofSyntax Const Δ (.eq (argumentAt index first) (argumentAt index second)) :=
  .impE (.eqPropER (.eqTrans (.eqSymm (observe_field signature occurrence index (argumentAt index second) first))
    (.eqTrans (observe_congr signature _ _ (withHandler signature occurrence
      (fieldHandler index (argumentAt index second))) same)
      (observe_field signature occurrence index (argumentAt index second) second))))
    (.eqRefl (argumentAt index second))

theorem fieldHandler_beta_free {fields : List (Ty Base)} {type : Ty Base}
    (index : Var fields type) (expected : Term Const Γ type) (arguments : Arguments Const Γ fields) :
    (fieldHandler_beta (Δ := Δ) index expected arguments).FunctionExtensionalityFree := by
  unfold fieldHandler_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractArguments_beta_free _ _ _ _

theorem observe_field_free (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    {type : Ty Base} (index : Var (signature.get occurrence) type) (expected : Term Const Γ type)
    (arguments : Arguments Const Γ (signature.get occurrence)) :
    (observe_field (Δ := Δ) signature occurrence index expected arguments).FunctionExtensionalityFree := by
  simp only [observe_field, ProofSyntax.FunctionExtensionalityFree, ProofSyntax.functionExtensionalityFree_castIndices]
  exact ⟨encode_beta_free _ _ _ _, fieldHandler_beta_free _ _ _⟩

theorem recover_field_free (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    {type : Ty Base} (index : Var (signature.get occurrence) type)
    (first second : Arguments Const Γ (signature.get occurrence))
    (same : ProofSyntax Const Δ (.eq (encode signature occurrence first) (encode signature occurrence second)))
    (free : same.FunctionExtensionalityFree) :
    (recover_field signature occurrence index first second same).FunctionExtensionalityFree := by
  simp only [recover_field, ProofSyntax.FunctionExtensionalityFree]
  exact ⟨⟨observe_field_free _ _ _ _ _, ⟨observe_congr_free _ _ _ _ same free, observe_field_free _ _ _ _ _⟩⟩, True.intro⟩

#print axioms encode_beta
#print axioms encode_beta_free
#print axioms recover_field
#print axioms recover_field_free
end Mettapedia.Logic.HOL.FiniteConstructorEncoding
