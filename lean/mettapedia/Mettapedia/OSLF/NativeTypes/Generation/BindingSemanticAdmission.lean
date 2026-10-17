import Mettapedia.OSLF.NativeTypes.Generation.NativeDeclarations
import Mettapedia.GSLT.LanguageDef.BindingSignature
import Mettapedia.OSLF.Syntax.SignatureMorphism

/-!
# Admission of authored parameters to contextual binding semantics

Formation decoding and semantic admission are separate. Ordinary arrow data
is not silently promoted to native function space. Declared binding arguments
may have an arbitrary finite spine of base-sort domains and a base result.
Slots are computed in the actual innermost-first bound-context order, with
the complete authored parameter and its declaration positions retained.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Domains are ordered from the outermost authored lambda to the innermost. -/
inductive BinderSpine : TypeExpr → List String → String → Prop where
  | result (sort : String) : BinderSpine (.base sort) [] sort
  | binder {body : TypeExpr} {domains : List String} {result : String}
      (domain : String) : BinderSpine body domains result →
      BinderSpine (.arrow (.base domain) body) (domain :: domains) result

def binderSpine? : TypeExpr → Option (List String × String)
  | .base sort => some ([], sort)
  | .arrow (.base domain) body => do
      let (domains, result) ← binderSpine? body
      pure (domain :: domains, result)
  | _ => none

theorem binderSpine?_exact (type : TypeExpr) (domains : List String) (result : String) :
    binderSpine? type = some (domains, result) ↔ BinderSpine type domains result := by
  induction type generalizing domains result with
  | base sort =>
      constructor
      · intro decoded
        simp only [binderSpine?, Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        exact .result sort
      · intro supported
        cases supported
        rfl
  | arrow domain body domainIH bodyIH =>
      cases domain with
      | base domain =>
          constructor
          · intro decoded
            simp only [binderSpine?] at decoded
            cases decodedBody : binderSpine? body with
            | none => simp [decodedBody] at decoded
            | some tail =>
                obtain ⟨tailDomains, tailResult⟩ := tail
                simp [decodedBody] at decoded
                obtain ⟨rfl, rfl⟩ := decoded
                exact .binder domain ((bodyIH tailDomains tailResult).mp decodedBody)
          · intro supported
            cases supported with
            | binder domain supported =>
                simp only [binderSpine?, (bodyIH _ _).mpr supported]
                rfl
      | arrow domain codomain =>
          constructor
          · simp [binderSpine?]
          · intro supported; cases supported
      | multiBinder domain =>
          constructor
          · simp [binderSpine?]
          · intro supported; cases supported
      | collection kind element =>
          constructor
          · simp [binderSpine?]
          · intro supported; cases supported
  | multiBinder domain =>
      constructor
      · simp [binderSpine?]
      · intro supported; cases supported
  | collection kind element =>
      constructor
      · simp [binderSpine?]
      · intro supported; cases supported

/-- Independently stated distinction between ordinary data and declared
binding arguments. Source display names remain in the judgment. -/
inductive ParameterMeaning : TermParam → List String → String → Prop where
  | data (name sort : String) : ParameterMeaning (.simple name (.base sort)) [] sort
  | shorthand (binder : Option String) (bodyName sort : String) :
      ParameterMeaning (.abstractionNamed binder bodyName (.base sort)) [sort] sort
  | binding (binder : Option String) (bodyName domain : String)
      {body : TypeExpr} {domains : List String} {result : String} :
      BinderSpine body domains result →
      ParameterMeaning (.abstractionNamed binder bodyName (.arrow (.base domain) body))
        (domain :: domains).reverse result

def parameterMeaning? : TermParam → Option (List String × String)
  | .simple _ (.base sort) => some ([], sort)
  | .abstractionNamed _ _ (.base sort) => some ([sort], sort)
  | .abstractionNamed _ _ (.arrow (.base domain) body) => do
      let (domains, result) ← binderSpine? body
      pure ((domain :: domains).reverse, result)
  | _ => none

theorem parameterMeaning?_exact (parameter : TermParam) (scope : List String) (result : String) :
    parameterMeaning? parameter = some (scope, result) ↔ ParameterMeaning parameter scope result := by
  cases parameter with
  | simple name type =>
      cases type with
      | base sort =>
          constructor
          · intro decoded
            simp only [parameterMeaning?, Option.some.injEq, Prod.mk.injEq] at decoded
            obtain ⟨rfl, rfl⟩ := decoded
            exact .data name sort
          · intro supported; cases supported; rfl
      | arrow domain codomain => constructor; simp [parameterMeaning?]; intro supported; cases supported
      | multiBinder domain => constructor; simp [parameterMeaning?]; intro supported; cases supported
      | collection kind element => constructor; simp [parameterMeaning?]; intro supported; cases supported
  | abstractionNamed binder bodyName type =>
      cases type with
      | base sort =>
          constructor
          · intro decoded
            simp only [parameterMeaning?, Option.some.injEq, Prod.mk.injEq] at decoded
            obtain ⟨rfl, rfl⟩ := decoded
            exact .shorthand binder bodyName sort
          · intro supported; cases supported; rfl
      | arrow domain body =>
          cases domain with
          | base domain =>
              constructor
              · intro decoded
                simp only [parameterMeaning?] at decoded
                cases decodedBody : binderSpine? body with
                | none => simp [decodedBody] at decoded
                | some tail =>
                    obtain ⟨domains, bodyResult⟩ := tail
                    simp [decodedBody] at decoded
                    obtain ⟨rfl, rfl⟩ := decoded
                    simpa only [List.reverse_cons] using
                      ParameterMeaning.binding binder bodyName domain
                        ((binderSpine?_exact body domains bodyResult).mp decodedBody)
              · intro supported
                cases supported with
                | binding binder bodyName domain bodySupported =>
                    simp only [parameterMeaning?, (binderSpine?_exact _ _ _).mpr bodySupported]
                    rfl
          | arrow first last => constructor; simp [parameterMeaning?]; intro supported; cases supported
          | multiBinder type => constructor; simp [parameterMeaning?]; intro supported; cases supported
          | collection kind type => constructor; simp [parameterMeaning?]; intro supported; cases supported
      | multiBinder type => constructor; simp [parameterMeaning?]; intro supported; cases supported
      | collection kind type => constructor; simp [parameterMeaning?]; intro supported; cases supported
  | multiAbstractionNamed binders bodyName type =>
      constructor; simp [parameterMeaning?]; intro supported; cases supported

inductive Reason where
  | ordinaryArrowData
  | unsupportedDataType
  | unsupportedBindingSpine
  | unsupportedMultipleBinderRepresentation
  deriving DecidableEq, Repr

def reason (parameter : TermParam) : Reason :=
  match parameter with
  | .simple _ (.arrow _ _) => .ordinaryArrowData
  | .simple _ _ => .unsupportedDataType
  | .abstractionNamed _ _ _ => .unsupportedBindingSpine
  | .multiAbstractionNamed _ _ _ => .unsupportedMultipleBinderRepresentation

structure Issue where
  declarationIndex : Nat
  parameterIndex : Nat
  parameter : TermParam
  reason : Reason
  deriving DecidableEq, Repr

def issues (language : LanguageDef) : List Issue :=
  language.terms.zipIdx.flatMap fun (declaration, declarationIndex) =>
    declaration.params.zipIdx.filterMap fun (parameter, parameterIndex) =>
      if (parameterMeaning? parameter).isSome then none else
        some ⟨declarationIndex, parameterIndex, parameter, reason parameter⟩

def check (language : LanguageDef) : Bool :=
  language.terms.all fun declaration => declaration.params.all fun parameter =>
    (parameterMeaning? parameter).isSome

def headerSlots? (declaration : GrammarRule) : Option (List (List String × String)) :=
  declaration.params.mapM parameterMeaning?

def languageSlots? (language : LanguageDef) : Option (List (List (List String × String))) :=
  language.terms.mapM headerSlots?

def Admitted (language : LanguageDef) : Prop :=
  ∀ declaration ∈ language.terms, ∀ parameter ∈ declaration.params,
    ∃ scope result, ParameterMeaning parameter scope result

theorem check_exact (language : LanguageDef) : check language = true ↔ Admitted language := by
  simp only [check, List.all_eq_true, Admitted]
  constructor
  · intro checked declaration member parameter parameterMember
    have accepted := checked declaration member parameter parameterMember
    cases decoded : parameterMeaning? parameter with
    | none => simp [decoded] at accepted
    | some slot => exact ⟨slot.1, slot.2, (parameterMeaning?_exact _ _ _).mp decoded⟩
  · intro admitted declaration member parameter parameterMember
    obtain ⟨scope, result, supported⟩ := admitted declaration member parameter parameterMember
    rw [(parameterMeaning?_exact _ _ _).mpr supported]
    rfl

private theorem declared_base_formed {language : LanguageDef} {name : String}
    (declared : name ∈ language.typeNames) :
    NativeSignature.AdmittedType language (.base name) := by
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp declared
  have bound' : index < language.types.length := by
    simpa only [LanguageDef.typeNames, List.length_map] using bound
  have named : language.types[index].name = name := by
    simpa only [LanguageDef.typeNames, List.getElem_map] using same
  exact named ▸ NativeSignature.AdmittedType.sort ⟨index, bound'⟩

private theorem binderSpine_formed {language : LanguageDef} {type : TypeExpr}
    {domains : List String} {result : String} (spine : BinderSpine type domains result)
    (declared : ∀ name ∈ type.baseNames, name ∈ language.typeNames) :
    NativeSignature.AdmittedType language type := by
  induction spine with
  | result sort => exact declared_base_formed (declared sort (List.mem_singleton_self _))
  | binder domain spine inductionHypothesis =>
      apply NativeSignature.AdmittedType.function
      · exact declared_base_formed (declared domain (List.mem_append_left _ (List.mem_singleton_self _)))
      · exact inductionHypothesis (fun name member => declared name (List.mem_append_right _ member))

/-- Validated declared sorts and the independent binding-parameter meaning
supply the original finite native header formation for every constructor. -/
theorem admittedHeaders_of_validate {language : LanguageDef} (valid : language.validate = [])
    (admitted : Admitted language) :
    ∀ index, NativeSignature.AdmittedHeader language index := by
  intro index
  constructor
  · intro parameter member
    obtain ⟨scope, result, meaning⟩ := admitted language.terms[index.val]
      (List.getElem_mem index.isLt) parameter member
    have declared : ∀ name ∈ parameter.typeExpr.baseNames, name ∈ language.typeNames := by
      intro name nameMember
      exact LanguageDef.termParam_baseName_mem_of_validate_eq_nil language valid
        language.terms[index.val] (List.getElem_mem index.isLt) parameter member name nameMember
    cases meaning with
    | data name sort =>
        exact ⟨.base result, rfl, declared_base_formed (declared result (List.mem_singleton_self _))⟩
    | shorthand binder bodyName sort =>
        have formed : NativeSignature.AdmittedType language (.base result) :=
          declared_base_formed (declared result (List.mem_singleton_self _))
        exact ⟨.arrow (.base result) (.base result), rfl, .function formed formed⟩
    | binding binder bodyName domain spine =>
        exact ⟨_, rfl, binderSpine_formed (BinderSpine.binder domain spine) declared⟩
  · have member := LanguageDef.termCategory_mem_of_validate_eq_nil language valid
      language.terms[index.val] (List.getElem_mem index.isLt)
    obtain ⟨position, bound, same⟩ := List.mem_iff_getElem.mp member
    have bound' : position < language.types.length := by
      simpa only [LanguageDef.typeNames, List.length_map] using bound
    exact ⟨⟨position, bound'⟩, by simpa only [LanguageDef.typeNames, List.getElem_map] using same⟩


end Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission


namespace Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Admission uses the independently authored finite sort inventory and all
four original type constructors. It does not inspect a native decoder result. -/
inductive DeclaredType (language : LanguageDef) : TypeExpr → Prop where
  | base (position : Fin language.types.length) :
      DeclaredType language (.base language.types[position.val].name)
  | arrow {domain codomain : TypeExpr} (left : DeclaredType language domain)
      (right : DeclaredType language codomain) : DeclaredType language (.arrow domain codomain)
  | multiBinder {domain : TypeExpr} (formed : DeclaredType language domain) :
      DeclaredType language (.multiBinder domain)
  | collection (kind : CollType) {element : TypeExpr} (formed : DeclaredType language element) :
      DeclaredType language (.collection kind element)


/-- The source sorts remain the original expressions with independent
finite-declaration formation evidence. There is no second type-expression AST. -/
abbrev DeclaredSort (language : LanguageDef) := {source : TypeExpr // DeclaredType language source}

abbrev sourceSignature (language : LanguageDef) : Mettapedia.OSLF.Binding.Signature :=
  (Mettapedia.GSLT.LanguageDef.BindingSyntax.signatureOf language).reindexSorts
    (fun source : DeclaredSort language => source.val)


namespace DeclaredSort

variable {language : LanguageDef}

def arrow (domain codomain : DeclaredSort language) : DeclaredSort language :=
  ⟨.arrow domain.val codomain.val, .arrow domain.property codomain.property⟩

def multiBinder (domain : DeclaredSort language) : DeclaredSort language :=
  ⟨.multiBinder domain.val, .multiBinder domain.property⟩

def collection (kind : CollType) (element : DeclaredSort language) : DeclaredSort language :=
  ⟨.collection kind element.val, .collection kind element.property⟩

end DeclaredSort


/-- Formation of the original type expression is exactly finite declared
base-name support, including beneath arrows, sequences and collections. -/
theorem declaredType_iff_baseNames {language : LanguageDef} (source : TypeExpr) :
    DeclaredType language source ↔
      ∀ name ∈ source.baseNames, name ∈ language.typeNames := by
  constructor
  · intro formed
    induction formed with
    | base position =>
        intro name member
        have same : name = language.types[position.val].name := by
          simpa only [TypeExpr.baseNames, List.mem_singleton] using member
        subst name
        exact List.mem_map.mpr ⟨language.types[position.val], List.getElem_mem position.isLt, rfl⟩
    | arrow domain codomain leftIH rightIH =>
        intro name member
        rcases List.mem_append.mp member with left | right
        · exact leftIH name left
        · exact rightIH name right
    | multiBinder domain ih => exact ih
    | collection kind element ih => exact ih
  · intro supported
    induction source with
    | base name =>
        have present := supported name (List.mem_singleton_self name)
        obtain ⟨row, member, named⟩ := List.mem_map.mp present
        obtain ⟨index, selected⟩ := List.mem_iff_get.mp member
        have formed := DeclaredType.base (language := language) index
        change DeclaredType language (.base (language.types.get index).name) at formed
        rw [selected] at formed
        simpa only [named] using formed
    | arrow domain codomain leftIH rightIH =>
        exact .arrow (leftIH fun name member => supported name (List.mem_append_left _ member))
          (rightIH fun name member => supported name (List.mem_append_right _ member))
    | multiBinder domain ih => exact .multiBinder (ih supported)
    | collection kind element ih => exact .collection kind (ih supported)


/-- Check only the original finite declaration support of every base name. -/
def declaredTypeCheck (language : LanguageDef) (source : TypeExpr) : Bool :=
  source.baseNames.all (fun name => decide (name ∈ language.typeNames))

theorem declaredTypeCheck_exact (language : LanguageDef) (source : TypeExpr) :
    declaredTypeCheck language source = true ↔ DeclaredType language source := by
  rw [declaredType_iff_baseNames]
  simp only [declaredTypeCheck, List.all_eq_true, decide_eq_true_eq]

/-- Source admission retains the literal TypeExpr and never computes a
representation in another calculus. -/
def sort? (language : LanguageDef) (source : TypeExpr) : Option (DeclaredSort language) :=
  if accepted : declaredTypeCheck language source = true then
    some ⟨source, (declaredTypeCheck_exact language source).mp accepted⟩
  else none

theorem sort?_readback {language : LanguageDef} (source : DeclaredSort language) :
    sort? language source.val = some source := by
  unfold sort?
  rw [dif_pos ((declaredTypeCheck_exact language source.val).mpr source.property)]

theorem sort?_source {language : LanguageDef} {source : TypeExpr} {sorted : DeclaredSort language}
    (accepted : sort? language source = some sorted) : sorted.val = source := by
  unfold sort? at accepted
  split at accepted
  · cases accepted
    rfl
  · cases accepted

theorem sort?_exact (language : LanguageDef) (source : TypeExpr) :
    (∃ sorted, sort? language source = some sorted) ↔ DeclaredType language source := by
  constructor
  · rintro ⟨sorted, accepted⟩
    exact sort?_source accepted ▸ sorted.property
  · intro formed
    exact ⟨⟨source, formed⟩, sort?_readback ⟨source, formed⟩⟩

end Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
