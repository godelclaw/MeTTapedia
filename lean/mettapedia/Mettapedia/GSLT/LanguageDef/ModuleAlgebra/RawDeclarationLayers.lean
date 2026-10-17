import Mettapedia.GSLT.LanguageDef.ExtendedLanguageDef
import Mettapedia.GSLT.LanguageDef.CettaWireEquality
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.OriginView

/-!
# Exact module-authored raw declaration layers

The physical carrier retains a portable origin, the complete authoring schema,
the selected category and an ordered field list. This codec concerns raw data;
type admission is a separate obligation. In particular it does not license an
arbitrary schema's equations or rewrites as a semantics-preserving elaborator.
Its compositional GSLT is the established declaration-document construction,
not a new primitive in LanguageDef. Two independently authored layers compose
using the existing product authoring GSLT.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.RawDeclarationLayers

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open CettaWire

structure Declaration where
  source : String
  site : String
  schema : Term
  category : String
  fields : List Term
deriving Repr, DecidableEq

def encode (declaration : Declaration) : Term :=
  .application "ModuleLayerV1"
    [.application "SyntaxOriginV1" [.string declaration.source, .string declaration.site],
     declaration.schema, .string declaration.category, encodeList id declaration.fields]

def decode? : Term → Option Declaration
  | .application "ModuleLayerV1"
      [.application "SyntaxOriginV1" [.string source, .string site],
       schema, .string category, fields] =>
      (decodeList some fields).map fun values => ⟨source, site, schema, category, values⟩
  | _ => none

@[simp] theorem decode_encode (declaration : Declaration) :
    decode? (encode declaration) = some declaration := by
  cases declaration
  simp [encode, decode?, decodeList_encodeList]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode? same
  simpa using decoded

private theorem list_reencode {wire : Term} {fields : List Term}
    (decoded : decodeList some wire = some fields) : encodeList id fields = wire := by
  cases wire with
  | symbol name =>
      unfold decodeList at decoded
      split at decoded <;> simp_all [encodeList]
  | string _ => simp [decodeList] at decoded
  | natural _ => simp [decodeList] at decoded
  | application head arguments =>
      unfold decodeList at decoded
      split at decoded
      · rename_i impossible
        cases impossible
      · rename_i first tail shape
        cases shape
        cases rest : decodeList some tail with
        | none => simp [rest] at decoded
        | some values =>
            have same : first :: values = fields := by simpa [rest] using decoded
            subst fields
            simp only [encodeList, id_eq]
            rw [list_reencode rest]
      · simp at decoded
termination_by sizeOf wire

theorem reencode_decoded {wire : Term} {declaration : Declaration}
    (decoded : decode? wire = some declaration) : encode declaration = wire := by
  unfold decode? at decoded
  split at decoded
  · rename_i source site schema category fields
    cases values : decodeList some fields with
    | none => simp [values] at decoded
    | some payload =>
        have same : (⟨source, site, schema, category, payload⟩ : Declaration) = declaration := by
          simpa [values] using decoded
        subst declaration
        simp only [encode]
        rw [list_reencode values]
  · simp at decoded

/-- Only independently decoded physical declarations enter the exact codec. -/
abbrev Source := {wire : Term // (decode? wire).isSome = true}

def codec : ExactDeclarationCodec Source Declaration where
  encode declaration := ⟨encode declaration, by simp⟩
  decode source := (decode? source.val).get source.property
  decode_encode := by intro declaration; simp
  encode_decode := by
    intro source
    apply Subtype.ext
    apply reencode_decoded
    exact (Option.some_get source.property).symm

def declarationLayer : CompositionalLayer LanguageDef := CompositionalLayer.ofCodec LanguageDef codec

/-- Quotation and elaboration retain the complete row list, not its set. -/
theorem elaborate_quote (base : LanguageDef) (rows : List Declaration) :
    declarationLayer.elaborate base (declarationLayer.quote base rows) = some rows :=
  declarationLayer.elaborate_quote base rows

/-- Independent declarations retain both components through product authoring. -/
theorem compose_quote (base : LanguageDef) (left right : List Declaration) :
    (declarationLayer.product declarationLayer).elaborate base
      ((declarationLayer.product declarationLayer).quote base (left, right)) = some (left, right) :=
  (declarationLayer.product declarationLayer).elaborate_quote base (left, right)

def assembled (base : LanguageDef) (left right : List Declaration) :
    ExtendedLanguageDef (declarationLayer.product declarationLayer) :=
  ExtendedLanguageDef.ofProduct base declarationLayer declarationLayer left right

theorem assembled_core (base : LanguageDef) (left right : List Declaration) :
    (assembled base left right).toLanguageDef = base :=
  ExtendedLanguageDef.ofProduct_language base declarationLayer declarationLayer left right

/-- Portable identity is independent of schema/category/field equality. -/
def entry (declaration : Declaration) : Entry (String × String) (String × String) Declaration :=
  { origin := (declaration.source, declaration.site)
    label := (declaration.source, declaration.site)
    body := declaration }

theorem entry_injective : Function.Injective entry := by
  intro first second same
  exact congrArg Entry.body same

/-- Shared origins require the complete same declaration; other origins remain
independent even if they expose equal-valued fields or equal category names. -/
theorem entry_compatible (first second : Declaration) :
    OriginView.entryCompatible (entry first) (entry second) =
      decide ((first.source, first.site) = (second.source, second.site) → first = second) := by
  apply Bool.decide_congr
  constructor
  · intro compatible key
    exact entry_injective (compatible key)
  · intro compatible key
    exact congrArg entry (compatible key)

def join? (left right : List Declaration) :=
  OriginView.orderedJoin? (left.map entry) (right.map entry)

/-- Acceptance is an explicit compatibility condition, not unconditional
concatenation of arbitrary extension declarations. -/
theorem join_accepted_iff (left right : List Declaration) :
    (join? left right).isSome = true ↔
      OriginView.Valid ((left.map entry).toFinset ∪ (right.map entry).toFinset) :=
  OriginView.orderedJoin_isSome_iff (left.map entry) (right.map entry)

/-- Every accepted row comes from an input, and every input row is retained.
Outer sharing is distinct from field-list multiplicity inside each row. -/
theorem join_rows {left right : List Declaration}
    {result : List (Entry (String × String) (String × String) Declaration)}
    (accepted : join? left right = some result) (row : Entry (String × String) (String × String) Declaration) :
    row ∈ result ↔ row ∈ left.map entry ∨ row ∈ right.map entry := by
  have same := OriginView.orderedCheck_toFinset ((left.map entry) ++ (right.map entry)) result accepted
  have member : row ∈ result.toFinset ↔ row ∈ ((left.map entry) ++ (right.map entry)).toFinset := by
    rw [same]
  simpa using member

/-- Equal-valued field occurrences are not collapsed by the physical codec. -/
theorem doubled_fields_distinct (source site category : String) (schema field : Term) :
    encode ⟨source, site, schema, category, [field, field]⟩ ≠
      encode ⟨source, site, schema, category, [field]⟩ := by
  intro same
  have rows := congrArg Declaration.fields (encode_injective same)
  have lengths := congrArg List.length rows
  simp at lengths

/-- A schema difference is retained even when every field value is equal. -/
theorem differing_schemas {first second : Declaration} (different : first.schema ≠ second.schema) :
    encode first ≠ encode second := by
  intro same
  exact different (congrArg Declaration.schema (encode_injective same))

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.RawDeclarationLayers
