import Mettapedia.OSLF.NativeTypes.Generation.NativeDeclarations

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

end Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
