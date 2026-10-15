import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContexts
import Mathlib.Data.List.Forall2

/-!
# Finite native signatures derived from authored declarations

Sort symbols retain their authored positions. Ordered constructor parameters
are translated to ordinary native types; a single binding parameter becomes
a function type using the independently specified parameter interpretation.
Unknown sorts and variable-arity or collection carriers are rejected rather
than assigned a substitute type.

The resulting finite signature supplies constructor operations and their
graphs to the same dependent syntax used by native certificate checking.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeSignature

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.Calculi.NativeDependent

inductive Carrier (language : LanguageDef) where
  | sort (position : Fin language.types.length)
  | function (domain codomain : Carrier language)
  deriving DecidableEq

def Carrier.source {language : LanguageDef} : Carrier language → TypeExpr
  | .sort position => .base language.types[position.val].name
  | .function domain codomain => .arrow domain.source codomain.source

def findSort? (language : LanguageDef) (name : String) : Option (Fin language.types.length) :=
  (List.finRange language.types.length).find? (fun position => language.types[position.val].name == name)

theorem findSort?_sound {language : LanguageDef} {name : String}
    {position : Fin language.types.length} (found : findSort? language name = some position) :
    language.types[position.val].name = name := by
  have matchFound := List.find?_some (p := fun i : Fin language.types.length =>
    language.types[i].name == name) found
  simpa using matchFound

theorem findSort?_complete {language : LanguageDef} {name : String}
    (declared : ∃ position : Fin language.types.length, language.types[position.val].name = name) :
    ∃ position, findSort? language name = some position := by
  have present : (findSort? language name).isSome := by
    simp only [findSort?, List.find?_isSome]
    obtain ⟨position, named⟩ := declared
    exact ⟨position, List.mem_finRange position, by simp [named]⟩
  cases found : findSort? language name with
  | none => simp [found] at present
  | some position => exact ⟨position, rfl⟩

def decodeType? (language : LanguageDef) : TypeExpr → Option (Carrier language)
  | .base name => (findSort? language name).map Carrier.sort
  | .arrow domain codomain => do
      let domain ← decodeType? language domain
      let codomain ← decodeType? language codomain
      pure (.function domain codomain)
  | .multiBinder _ => none
  | .collection _ _ => none

theorem decodeType?_sound {language : LanguageDef} {type : TypeExpr}
    {carrier : Carrier language} (decoded : decodeType? language type = some carrier) :
    carrier.source = type := by
  induction type generalizing carrier with
  | base name =>
      simp only [decodeType?, Option.map_eq_some_iff] at decoded
      obtain ⟨position, found, rfl⟩ := decoded
      exact congrArg TypeExpr.base (findSort?_sound found)
  | arrow domain codomain domainIH codomainIH =>
      cases left : decodeType? language domain with
      | none => simp [decodeType?, left] at decoded
      | some domainCarrier =>
          cases right : decodeType? language codomain with
          | none => simp [decodeType?, left, right] at decoded
          | some codomainCarrier =>
              simp [decodeType?, left, right] at decoded
              cases decoded
              exact congrArg₂ TypeExpr.arrow (domainIH left) (codomainIH right)
  | multiBinder _ => cases decoded
  | collection _ _ => cases decoded

/-- The admission specification mentions authored sorts and type formation,
independently of the decoder's result. -/
inductive AdmittedType (language : LanguageDef) : TypeExpr → Prop where
  | sort (position : Fin language.types.length) :
      AdmittedType language (.base language.types[position.val].name)
  | function {domain codomain : TypeExpr}
      (domainFormed : AdmittedType language domain)
      (codomainFormed : AdmittedType language codomain) :
      AdmittedType language (.arrow domain codomain)

theorem Carrier.admitted {language : LanguageDef} (carrier : Carrier language) :
    AdmittedType language carrier.source := by
  induction carrier with
  | sort position => exact .sort position
  | function _ _ domainIH codomainIH => exact .function domainIH codomainIH

theorem decodeType?_admitted {language : LanguageDef} {type : TypeExpr}
    {carrier : Carrier language} (decoded : decodeType? language type = some carrier) :
    AdmittedType language type := by
  rw [← decodeType?_sound decoded]
  exact carrier.admitted

theorem decodeType?_complete {language : LanguageDef} {type : TypeExpr}
    (formed : AdmittedType language type) : ∃ carrier, decodeType? language type = some carrier := by
  induction formed with
  | sort position =>
      have present : (findSort? language language.types[position.val].name).isSome := by
        simp only [findSort?, List.find?_isSome]
        exact ⟨position, List.mem_finRange position, by simp⟩
      cases found : findSort? language language.types[position.val].name with
      | none => simp [found] at present
      | some actual => exact ⟨.sort actual, by simp [decodeType?, found]⟩
  | function _ _ domainIH codomainIH =>
      obtain ⟨domain, left⟩ := domainIH
      obtain ⟨codomain, right⟩ := codomainIH
      exact ⟨.function domain codomain, by simp [decodeType?, left, right]⟩

theorem decodeType?_exact (language : LanguageDef) (type : TypeExpr) :
    (∃ carrier, decodeType? language type = some carrier) ↔ AdmittedType language type :=
  ⟨fun ⟨_, decoded⟩ => decodeType?_admitted decoded, decodeType?_complete⟩

/-- Finite left-to-right declaration decoding retains duplicates. -/
def decodeList {α β : Type} (decode : α → Option β) : List α → Option (List β)
  | [] => some []
  | value :: values => do
      let result ← decode value
      let remaining ← decodeList decode values
      pure (result :: remaining)

theorem decodeList_sound {α β : Type} {decode : α → Option β}
    {values : List α} {results : List β}
    (decoded : decodeList decode values = some results) :
    List.Forall₂ (fun value result => decode value = some result) values results := by
  induction values generalizing results with
  | nil => simp [decodeList] at decoded; cases decoded; exact .nil
  | cons value values ih =>
      cases first : decode value with
      | none => simp [decodeList, first] at decoded
      | some result =>
          cases rest : decodeList decode values with
          | none => simp [decodeList, first, rest] at decoded
          | some remaining =>
              simp [decodeList, first, rest] at decoded
              cases decoded
              exact .cons first (ih rest)

theorem decodeList_complete {α β : Type} {decode : α → Option β}
    {values : List α} {results : List β}
    (each : List.Forall₂ (fun value result => decode value = some result) values results) :
    decodeList decode values = some results := by
  induction each with
  | nil => rfl
  | cons first _ ih => simp [decodeList, first, ih]

theorem decodeList_exists {α β : Type} {decode : α → Option β} {values : List α}
    (each : ∀ value ∈ values, ∃ result, decode value = some result) :
    ∃ results, decodeList decode values = some results := by
  induction values with
  | nil => exact ⟨[], rfl⟩
  | cons value values ih =>
      obtain ⟨result, first⟩ := each value (by simp)
      obtain ⟨remaining, rest⟩ := ih (fun item member => each item (by simp [member]))
      exact ⟨result :: remaining, by simp [decodeList, first, rest]⟩

def decodeParameter? (language : LanguageDef) (parameter : TermParam) :
    Option (Carrier language) :=
  (Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter).bind (decodeType? language)

theorem decodeParameter?_sound {language : LanguageDef} {parameter : TermParam}
    {carrier : Carrier language} (decoded : decodeParameter? language parameter = some carrier) :
    Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter = some carrier.source := by
  cases interpretation : Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter with
  | none => simp [decodeParameter?, interpretation] at decoded
  | some type =>
      simp only [decodeParameter?, interpretation, Option.bind_some] at decoded
      rw [decodeType?_sound decoded]

structure Header (language : LanguageDef) where
  origin : Fin language.terms.length
  parameters : List (Carrier language)
  result : Fin language.types.length

def decodeHeader? (language : LanguageDef) (origin : Fin language.terms.length) :
    Option (Header language) := do
  let parameters ← decodeList (decodeParameter? language) language.terms[origin.val].params
  let result ← findSort? language language.terms[origin.val].category
  pure ⟨origin, parameters, result⟩

def decodeHeaders? (language : LanguageDef) : Option (List (Header language)) :=
  decodeList (decodeHeader? language) (List.finRange language.terms.length)

/-- Declaration correctness refers to the independent sorted parameter
interpretation, not to successful execution of the decoder. -/
def HeaderCorrect {language : LanguageDef} (header : Header language) : Prop :=
  List.Forall₂
    (fun parameter carrier => Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter =
      some carrier.source)
    language.terms[header.origin.val].params header.parameters ∧
  language.types[header.result.val].name = language.terms[header.origin.val].category

theorem decodeHeader?_sound {language : LanguageDef} {origin : Fin language.terms.length}
    {header : Header language} (decoded : decodeHeader? language origin = some header) :
    header.origin = origin ∧ HeaderCorrect header := by
  cases parameters : decodeList (decodeParameter? language) language.terms[origin.val].params with
  | none => simp [decodeHeader?, parameters] at decoded
  | some arguments =>
      cases result : findSort? language language.terms[origin.val].category with
      | none => simp [decodeHeader?, parameters, result] at decoded
      | some position =>
          simp [decodeHeader?, parameters, result] at decoded
          cases decoded
          exact ⟨rfl, (decodeList_sound parameters).imp
            (fun _ _ found => decodeParameter?_sound found), findSort?_sound result⟩

theorem decodeHeader?_arity {language : LanguageDef} {origin : Fin language.terms.length}
    {header : Header language} (decoded : decodeHeader? language origin = some header) :
    header.parameters.length = language.terms[origin.val].params.length := by
  obtain ⟨sameOrigin, parameters, _⟩ := decodeHeader?_sound decoded
  rw [← sameOrigin]
  exact parameters.length_eq.symm

theorem decodeHeaders?_length {language : LanguageDef} {headers : List (Header language)}
    (decoded : decodeHeaders? language = some headers) :
    headers.length = language.terms.length := by
  have same := (decodeList_sound decoded).length_eq
  simpa using same.symm

theorem decodeHeaders?_correct {language : LanguageDef} {headers : List (Header language)}
    (decoded : decodeHeaders? language = some headers) :
    List.Forall₂ (fun origin header => header.origin = origin ∧ HeaderCorrect header)
      (List.finRange language.terms.length) headers :=
  (decodeList_sound decoded).imp (fun _ _ found => decodeHeader?_sound found)

/-- Admission is specified by authored parameter typing and declared sorts.
Its proof does not mention the header decoder. -/
def AdmittedHeader (language : LanguageDef) (origin : Fin language.terms.length) : Prop :=
  (∀ parameter ∈ language.terms[origin.val].params,
    ∃ type, Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter = some type ∧
      AdmittedType language type) ∧
  (∃ position : Fin language.types.length,
    language.types[position.val].name = language.terms[origin.val].category)

theorem decodeHeader?_complete {language : LanguageDef} {origin : Fin language.terms.length}
    (formed : AdmittedHeader language origin) :
    ∃ header, decodeHeader? language origin = some header := by
  have each : ∀ parameter ∈ language.terms[origin.val].params,
      ∃ carrier, decodeParameter? language parameter = some carrier := by
    intro parameter member
    obtain ⟨type, interpreted, typed⟩ := formed.1 parameter member
    obtain ⟨carrier, decoded⟩ := decodeType?_complete typed
    exact ⟨carrier, by simp [decodeParameter?, interpreted, decoded]⟩
  obtain ⟨parameters, parameterDecoded⟩ := decodeList_exists each
  obtain ⟨result, resultDecoded⟩ := findSort?_complete formed.2
  exact ⟨⟨origin, parameters, result⟩,
    by simp [decodeHeader?, parameterDecoded, resultDecoded]⟩

theorem decodeHeaders?_complete {language : LanguageDef}
    (formed : ∀ origin, AdmittedHeader language origin) :
    ∃ headers, decodeHeaders? language = some headers :=
  decodeList_exists (fun origin _ => decodeHeader?_complete (formed origin))

abbrev symbols (language : LanguageDef) (headers : List (Header language)) : Refinement.Symbols where
  TypeSymbol := Fin language.types.length
  TermSymbol := Fin headers.length
  PredicateSymbol := Empty
  typeArity _ := 0
  termArity position := headers[position].parameters.length
  predicateArity symbol := nomatch symbol

def Carrier.native {language : LanguageDef} {headers : List (Header language)} :
    {n : Nat} → Carrier language → Refinement.TypeExpr (symbols language headers) n
  | _, .sort position => .family position Fin.elim0
  | _, .function domain codomain => .pi domain.native codomain.native

theorem Carrier.native_rename {language : LanguageDef} {headers : List (Header language)}
    {n m : Nat} (carrier : Carrier language) (mapping : Refinement.Renaming n m) :
    (carrier.native (headers := headers) (n := n)).rename mapping = carrier.native (n := m) := by
  induction carrier generalizing n m with
  | sort position =>
      simp only [Carrier.native, Refinement.TypeExpr.rename]
      congr 1
      funext index
      exact Fin.elim0 index
  | function _ _ domainIH codomainIH =>
      simp only [Carrier.native, Refinement.TypeExpr.rename, domainIH, codomainIH]

theorem Carrier.native_substitute {language : LanguageDef} {headers : List (Header language)}
    {n m : Nat} (carrier : Carrier language)
    (substitution : Refinement.Substitution (symbols language headers) n m) :
    (carrier.native (n := n)).substitute substitution = carrier.native (n := m) := by
  induction carrier generalizing n m with
  | sort position =>
      simp only [Carrier.native, Refinement.TypeExpr.substitute]
      congr 1
      funext index
      exact Fin.elim0 index
  | function _ _ domainIH codomainIH =>
      simp only [Carrier.native, Refinement.TypeExpr.substitute, domainIH, codomainIH]

theorem Carrier.native_before {language : LanguageDef} {headers : List (Header language)}
    (carrier : Carrier language) (n bound : Nat) (positive : 0 < bound) :
    (carrier.native (headers := headers) (n := n)).before
      (fun _ => 0) (fun _ => 1) (fun _ => 2) bound := by
  induction carrier generalizing n with
  | sort position => exact ⟨positive, fun position => Fin.elim0 position⟩
  | function _ _ domainIH codomainIH => exact ⟨domainIH n, codomainIH (n + 1)⟩

/-- Newest-variable order agrees with the ordered primitive argument vector. -/
def telescope {language : LanguageDef} {headers : List (Header language)} :
    (parameters : List (Carrier language)) →
      Refinement.ContextExpr (symbols language headers) parameters.length
  | [] => .nil
  | parameter :: parameters => .snoc (telescope parameters) parameter.native

theorem telescope_lookup {language : LanguageDef} {headers : List (Header language)}
    (parameters : List (Carrier language)) (position : Fin parameters.length) :
    (telescope (headers := headers) parameters).lookup position =
      parameters[position.val].native := by
  induction parameters with
  | nil => exact Fin.elim0 position
  | cons parameter parameters ih =>
      cases position using Fin.cases with
      | zero =>
          simp only [telescope, Refinement.ContextExpr.lookup_zero]
          exact parameter.native_rename Fin.succ
      | succ position =>
          simp only [telescope, Refinement.ContextExpr.lookup_succ]
          rw [ih position]
          exact (parameters[position.val]).native_rename Fin.succ

theorem telescope_before {language : LanguageDef} {headers : List (Header language)}
    (parameters : List (Carrier language)) (bound : Nat) (positive : 0 < bound) :
    (telescope (headers := headers) parameters).before
      (fun _ => 0) (fun _ => 1) (fun _ => 2) bound := by
  induction parameters with
  | nil => trivial
  | cons parameter parameters ih => exact ⟨ih, parameter.native_before _ _ positive⟩

def signature (language : LanguageDef) (headers : List (Header language)) :
    Refinement.Signature (symbols language headers) where
  typeRank _ := 0
  termRank _ := 1
  predicateRank _ := 2
  typeParameters _ := .nil
  termParameters position := telescope headers[position].parameters
  predicateParameters symbol := nomatch symbol
  termResult position := (Carrier.sort headers[position].result).native
  typeParameters_before _ := trivial
  termParameters_before position := telescope_before _ 1 (by decide)
  predicateParameters_before symbol := nomatch symbol
  termResult_before position := (Carrier.sort headers[position].result).native_before _ 1 (by decide)

end Mettapedia.OSLF.NativeTypes.Generation.NativeSignature
