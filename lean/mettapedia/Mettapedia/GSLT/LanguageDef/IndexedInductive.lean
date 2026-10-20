import Mettapedia.GSLT.LanguageDef.Extension
import Mettapedia.TypeTheory.IndexedPolynomialDescription

/-!
# Admission of indexed constructor documents

The existing declaration-document GSLT supplies ordered bundles and their
equations. This layer checks a finite constructor telescope grammar, retaining
its data fields, recursive indices and declaration occurrences. Its semantic
interpretation is the indexed polynomial compiled from those telescopes.

The admitted fragment has first-order recursive fields. Function fields are
explicit source syntax and are refused, including negative recursive domains.
This is not a decision procedure for all strictly positive type expressions.
Data-sort and index-expression interpretation is supplied by `Interface`;
ordinary textual `.module` parsing and guest judgmental authority are separate
interfaces, not inferred from this structural admission.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.GSLT.LanguageDef.Extension

universe u

variable (I : Interface.{u})

/-- Field expressions retained for explicit rejection of unsupported function
fields. In particular `arrow (family i) (ground s)` records a negative family
occurrence, rather than silently interpreting it as a constant field. -/
inductive FieldType (context : List I.SortCode) where
  | ground (sort : I.SortCode)
  | family (index : I.IndexExpr context)
  | arrow (domain codomain : FieldType context)

/-- Scoped constructor source. Data binders extend the index-expression
context; recursive children do not enter it. -/
inductive RawCode : List I.SortCode → Type where
  | result {context} (index : I.IndexExpr context) : RawCode context
  | data {context} (sort : I.SortCode) (body : RawCode (sort :: context)) : RawCode context
  | recursive {context} (index : I.IndexExpr context) (rest : RawCode context) : RawCode context
  | functionField {context} (domain codomain : FieldType I context)
      (rest : RawCode context) : RawCode context

namespace RawCode

def decode {context : List I.SortCode} : RawCode I context → Option (Code I context)
  | .result index => some (.result index)
  | .data sort body => (decode body).map (.data sort)
  | .recursive index rest => (decode rest).map (.recursive index)
  | .functionField _ _ _ => none

def quote {context : List I.SortCode} : Code I context → RawCode I context
  | .result index => .result index
  | .data sort body => .data sort (quote body)
  | .recursive index rest => .recursive index (quote rest)

@[simp] theorem decode_quote {context : List I.SortCode} (code : Code I context) :
    decode I (quote I code) = some code := by
  induction code with
  | result => rfl
  | data sort body ih => simp [quote, decode, ih]
  | recursive index rest ih => simp [quote, decode, ih]

/-- Successful admission recovers the complete source telescope. No field
can disappear, be reordered or change its recursive index during decoding. -/
theorem quote_of_decode {context : List I.SortCode} (raw : RawCode I context)
    (code : Code I context) (accepted : decode I raw = some code) :
    quote I code = raw := by
  induction raw with
  | result index =>
      have same : Code.result index = code := by simpa [decode] using accepted
      subst code
      rfl
  | data sort body ih =>
      cases found : decode I body with
      | none => simp [decode, found] at accepted
      | some decoded =>
          have same : Code.data sort decoded = code := by simpa [decode, found] using accepted
          subst code
          simp [quote, ih decoded found]
  | recursive index rest ih =>
      cases found : decode I rest with
      | none => simp [decode, found] at accepted
      | some decoded =>
          have same : Code.recursive index decoded = code := by simpa [decode, found] using accepted
          subst code
          simp [quote, ih decoded found]
  | functionField => simp [decode] at accepted

theorem negative_field_rejected {context : List I.SortCode}
    (family : I.IndexExpr context) (result : I.SortCode) (rest : RawCode I context) :
    decode I (.functionField (.family family) (.ground result) rest) = none := rfl

end RawCode

structure RawConstructor (context : List I.SortCode) where
  name : String
  body : RawCode I context

variable {I}

def RawConstructor.decode {context : List I.SortCode} (raw : RawConstructor I context) :
    Option (NamedConstructor I context) :=
  (RawCode.decode I raw.body).map fun body => ⟨raw.name, body⟩

def quoteConstructor {context : List I.SortCode} (constructor : NamedConstructor I context) :
    RawConstructor I context := ⟨constructor.name, RawCode.quote I constructor.body⟩

@[simp] theorem decode_quoteConstructor {context : List I.SortCode}
    (constructor : NamedConstructor I context) :
    (quoteConstructor constructor).decode = some constructor := by
  cases constructor
  simp [quoteConstructor, RawConstructor.decode]

theorem quoteConstructor_of_decode {context : List I.SortCode}
    (raw : RawConstructor I context) (constructor : NamedConstructor I context)
    (accepted : raw.decode = some constructor) : quoteConstructor constructor = raw := by
  cases raw with
  | mk name body =>
      cases found : RawCode.decode I body with
      | none => simp [RawConstructor.decode, found] at accepted
      | some code =>
          have same : NamedConstructor.mk name code = constructor := by
            simpa [RawConstructor.decode, found] using accepted
          subst constructor
          simp [quoteConstructor, RawCode.quote_of_decode I body code found]

/-- Admission retains the ordered inventory; unique public names are checked
without quotienting its constructor occurrences. -/
structure Admitted (I : Interface.{u}) (context : List I.SortCode) where
  constructors : List (NamedConstructor I context)
  uniqueNames : (constructors.map (·.name)).Nodup

abbrev Document (I : Interface.{u}) (context : List I.SortCode) :=
  DeclarationDocument (RawConstructor I context)

def admitList? {context : List I.SortCode} (source : List (RawConstructor I context)) :
    Option (Admitted I context) := do
  let constructors ← source.mapM RawConstructor.decode
  if unique : (constructors.map (·.name)).Nodup then
    some ⟨constructors, unique⟩
  else none

def admit? {context : List I.SortCode} (source : Document I context) :
    Option (Admitted I context) := admitList? source.values

def quote {context : List I.SortCode} (admitted : Admitted I context) : Document I context :=
  .bundle ((admitted.constructors.map quoteConstructor).map .declaration)

theorem decodeList_quote {context : List I.SortCode}
    (constructors : List (NamedConstructor I context)) :
    (constructors.map quoteConstructor).mapM RawConstructor.decode = some constructors := by
  induction constructors with
  | nil => rfl
  | cons constructor rest ih => simp [ih]

theorem quoteList_of_decode {context : List I.SortCode}
    (source : List (RawConstructor I context))
    (constructors : List (NamedConstructor I context))
    (accepted : source.mapM RawConstructor.decode = some constructors) :
    constructors.map quoteConstructor = source := by
  induction source generalizing constructors with
  | nil =>
      have same : constructors = [] := by simpa using accepted.symm
      subst constructors
      rfl
  | cons head tail ih =>
      cases headResult : head.decode with
      | none => simp [List.mapM_cons, headResult] at accepted
      | some constructor =>
          cases tailResult : tail.mapM RawConstructor.decode with
          | none => simp [List.mapM_cons, headResult, tailResult] at accepted
          | some rest =>
              have same : constructor :: rest = constructors := by
                simpa [List.mapM_cons, headResult, tailResult] using accepted
              subst constructors
              simp only [List.map_cons, quoteConstructor_of_decode head constructor headResult,
                ih rest tailResult]

/-- Successful admission preserves the complete ordered declaration source,
including all scoped indices and data binders, up to bundle equations. -/
theorem source_of_admit {context : List I.SortCode} (source : Document I context)
    (admitted : Admitted I context) (accepted : admit? source = some admitted) :
    admitted.constructors.map quoteConstructor = source.values := by
  unfold admit? admitList? at accepted
  cases decoded : source.values.mapM RawConstructor.decode with
  | none => simp [decoded] at accepted
  | some constructors =>
      by_cases unique : (constructors.map (·.name)).Nodup
      · have same : (⟨constructors, unique⟩ : Admitted I context) = admitted := by
          simpa [decoded, unique] using accepted
        subst admitted
        exact quoteList_of_decode source.values constructors decoded
      · simp [decoded, unique] at accepted

@[simp] theorem admit_quote {context : List I.SortCode} (admitted : Admitted I context) :
    admit? (quote admitted) = some admitted := by
  cases admitted with
  | mk constructors unique =>
      unfold admit? quote
      rw [DeclarationDocument.values_bundle_map]
      unfold admitList?
      rw [decodeList_quote]
      simp [unique]

/-- Exact admission: no constructor omission, extra field or changed index
can produce the same admitted package. Only document bracketing is erased. -/
theorem admit_iff {context : List I.SortCode} (source : Document I context)
    (admitted : Admitted I context) :
    admit? source = some admitted ↔
      source.values = admitted.constructors.map quoteConstructor := by
  constructor
  · exact fun accepted => (source_of_admit source admitted accepted).symm
  · intro same
    have quoted := admit_quote admitted
    unfold admit? at quoted ⊢
    rw [show (quote admitted).values = admitted.constructors.map quoteConstructor from
      DeclarationDocument.values_bundle_map _] at quoted
    rw [same]
    exact quoted

/-- The coGSLT is the established ordered-document language. Its nontrivial
bundle equations preserve successful admission and the resulting polynomial
inventory. No extra semantic rewrite is asserted for declarations. -/
def layer (I : Interface.{u}) (context : List I.SortCode) : CoGSLTLayer Unit where
  Fiber := fun _ => Admitted I context
  sourceGSLT := fun _ => ExactDeclarationCodec.documentGSLT (RawConstructor I context)
  elaborate := fun _ => admit?
  quote := fun _ => quote
  elaborate_quote := fun _ => admit_quote
  elaborate_equation := by
    intro _ source target same
    change source.values = target.values at same
    simp only [admit?, same]
  elaborate_rewrite := by
    intro _ _ _ impossible
    exact False.elim impossible

end Mettapedia.GSLT.LanguageDef.IndexedInductive
