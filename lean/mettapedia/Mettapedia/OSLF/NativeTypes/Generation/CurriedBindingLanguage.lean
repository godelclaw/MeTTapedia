import Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
import Mettapedia.OSLF.NativeTypes.Generation.BindingFreeContextSemantics

/-!
# A computed binding signature for authored curried base binders

Constructor origins are original declaration indices. Every argument scope
comes from semantic parameter decoding, including nested base-sort arrows.
The source readout emits the original constructor and canonical nested
lambda spine, with its authored declaration metadata retained by the origin.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open BindingSemanticAdmission

def slot (parameter : TermParam) : List String × String :=
  (parameterMeaning? parameter).getD ([], "")

def slots (parameters : List TermParam) : List (List String × String) := parameters.map slot

theorem slot_meaning {parameter : TermParam} {scope : List String} {result : String}
    (meaning : ParameterMeaning parameter scope result) : slot parameter = (scope, result) := by
  simp only [slot, (parameterMeaning?_exact _ _ _).mpr meaning, Option.getD_some]

structure Origin (language : LanguageDef) (result : String) where
  index : Fin language.terms.length
  category : language.terms[index.val].category = result
  parameters : ∀ parameter ∈ language.terms[index.val].params,
    ∃ scope result, ParameterMeaning parameter scope result

def signature (language : LanguageDef) : Signature where
  Srt := String
  Op := Origin language
  arity origin := slots language.terms[origin.index.val].params

def originalOperator {language : LanguageDef} (admitted : Admitted language)
    (index : Fin language.terms.length) :
    (signature language).Op language.terms[index.val].category :=
  ⟨index, rfl, admitted _ (List.getElem_mem index.isLt)⟩

def wrap : List String → Pattern → Pattern
  | [], body => body
  | _ :: domains, body => .lambda none (wrap domains body)

def printArgument (parameter : TermParam) (body : Pattern) : Pattern :=
  match parameter with
  | .simple _ _ => body
  | .abstractionNamed _ _ (.base _) => .lambda none body
  | .abstractionNamed _ _ type =>
      match binderSpine? type with
      | some (domains, _) => wrap domains body
      | none => body
  | .multiAbstractionNamed _ _ _ => body

def variableIndex {Srt : Type} {context : List Srt} {sort : Srt} : Var context sort → Nat
  | .zero => 0
  | .succ previous => variableIndex previous + 1

mutual
  def toPattern {language : LanguageDef} {context : List String} {sort : String} :
      Term (signature language) context sort → Pattern
    | .var v => .bvar (variableIndex v)
    | .op origin arguments =>
        .apply language.terms[origin.index.val].label
          (toPatterns language.terms[origin.index.val].params arguments)

  def toPatterns {language : LanguageDef} {context : List String} :
      (parameters : List TermParam) → {arity : List (List String × String)} →
        Args (signature language) arity context → List Pattern
    | [], _, _ => []
    | _ :: _, [], .nil => []
    | parameter :: parameters, _ :: _, .cons body rest =>
        printArgument parameter (toPattern body) :: toPatterns parameters rest
end

theorem variable_lookup {context : List String} {sort : String}
    (v : Var (Srt := String) context sort) :
    (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context)[variableIndex v]? = some (.base sort) := by
  induction v with
  | zero => rfl
  | succ previous ih => simpa only [variableIndex,
      Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.map_cons,
      List.getElem?_cons_succ] using ih

theorem wrap_typed {language : LanguageDef} {free : FreeTypeContext}
    {type : TypeExpr} {domains : List String} {result : String}
    (spine : BinderSpine type domains result) (context : List String) {body : Pattern}
    (typed : HasType language free
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext (domains.reverse ++ context)) body (.base result)) :
    HasType language free (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context)
      (wrap domains body) type := by
  induction spine generalizing context with
  | result sort => simpa only [List.reverse_nil, List.nil_append, wrap] using typed
  | @binder type domains result domain spine ih =>
      have bodyTyped := ih (domain :: context)
        (by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using typed)
      exact .lambda bodyTyped

theorem printArgument_typed {language : LanguageDef} {free : FreeTypeContext}
    {parameter : TermParam} {scope : List String} {result : String}
    (meaning : ParameterMeaning parameter scope result) (context : List String) {body : Pattern}
    (typed : HasType language free
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext (scope ++ context)) body (.base result)) :
    ∃ expected, parameterType? parameter = some expected ∧
      MatchesParameterRepresentation parameter (printArgument parameter body) ∧
      HasType language free (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context)
        (printArgument parameter body) expected := by
  cases meaning with
  | data name sort => exact ⟨.base result, rfl, trivial, typed⟩
  | shorthand binder bodyName sort =>
      exact ⟨.arrow (.base result) (.base result), rfl, trivial, HasType.lambda typed⟩
  | @binding binder bodyName domain bodyType domains result spine =>
      have fullSpine := BinderSpine.binder domain spine
      have decoded := (binderSpine?_exact _ _ _).mpr fullSpine
      refine ⟨.arrow (.base domain) bodyType, rfl, ?_, ?_⟩
      · simp only [printArgument, decoded, wrap]
        trivial
      · simpa only [printArgument, decoded] using wrap_typed fullSpine context typed

theorem ordinary_constructor {language : LanguageDef} {sort : String}
    (origin : Origin language sort) : ¬ UsesBareCollection language.terms[origin.index.val] := by
  rintro ⟨name, kind, element, shape⟩
  have supported := origin.parameters (.simple name (.collection kind element))
    (by rw [shape]; exact List.mem_singleton_self _)
  obtain ⟨scope, result, impossible⟩ := supported
  cases impossible

mutual
  def termSize {language : LanguageDef} {context : List String} {sort : String} :
      Term (signature language) context sort → Nat
    | .var _ => 0
    | .op _ arguments => argsSize arguments + 1

  def argsSize {language : LanguageDef} {context : List String}
      {arity : List (List String × String)} : Args (signature language) arity context → Nat
    | .nil => 0
    | .cons head tail => termSize head + argsSize tail + 1
end

variable {language : LanguageDef}

theorem printSized (n : Nat) :
    (∀ {context : List String} {sort : String} (term : Term (signature language) context sort),
      termSize term < n →
      HasType language FreeTypeContext.empty (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context)
        (toPattern term) (.base sort)) ∧
    (∀ (parameters : List TermParam)
      (_supported : ∀ parameter ∈ parameters, ∃ scope result, ParameterMeaning parameter scope result)
      {context : List String} {arity : List (List String × String)}
      (arguments : Args (signature language) arity context),
      arity = slots parameters → argsSize arguments < n →
      ArgumentsHaveTypes language FreeTypeContext.empty
        (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context)
        (toPatterns parameters arguments) parameters) := by
  induction n with
  | zero => constructor <;> intros <;> omega
  | succ n ih =>
      constructor
      · intro context sort term small
        change Ctx (signature language) at context
        change (signature language).Srt at sort
        cases term with
        | var v => exact .bvar (variable_lookup v)
        | op origin arguments =>
            have argumentSmall : argsSize arguments < n := by simpa only [termSize] using Nat.lt_of_succ_lt_succ small
            have typed := HasType.constructor (List.getElem_mem origin.index.isLt)
              (ordinary_constructor origin)
              (ih.2 _ origin.parameters arguments rfl argumentSmall)
            simpa only [toPattern, origin.category] using typed
      · intro parameters supported context arity arguments aligned small
        change Ctx (signature language) at context
        change List (List (signature language).Srt × (signature language).Srt) at arity
        cases arguments with
        | nil =>
            cases parameters with
            | nil => exact .nil
            | cons parameter parameters => simp [slots] at aligned
        | @cons scope result tail context body rest =>
            cases parameters with
            | nil => simp [slots] at aligned
            | cons parameter parameters =>
                change (scope, result) :: tail = slot parameter :: slots parameters at aligned
                have declarationMatch := List.cons.inj aligned
                obtain ⟨scopeDeclared, resultDeclared, meaning⟩ :=
                  supported parameter List.mem_cons_self
                have matched : scope = scopeDeclared ∧ result = resultDeclared :=
                  Prod.mk.inj (declarationMatch.1.trans (slot_meaning meaning))
                obtain ⟨rfl, rfl⟩ := matched
                have bodySmall : termSize body < n := by simp only [argsSize] at small; omega
                have tailSmall : argsSize rest < n := by simp only [argsSize] at small; omega
                obtain ⟨expected, expectedType, representation, printed⟩ :=
                  printArgument_typed meaning context (ih.1 body bodySmall)
                exact .cons representation expectedType printed
                  (ih.2 parameters (fun next member =>
                    supported next (List.mem_cons_of_mem _ member)) rest declarationMatch.2 tailSmall)

theorem toPattern_typed {context : List String} {sort : String}
    (term : Term (signature language) context sort) :
    HasType language FreeTypeContext.empty (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context)
      (toPattern term) (.base sort) :=
  (printSized (termSize term + 1)).1 term (Nat.lt_succ_self _)

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage
