import Mettapedia.GSLT.Parsing.SortedCodecMetadataAdmission

/-!
# Preparing finite codec shape tables

The source metadata compiler lowers categories and production arguments once
per shape table. Its prepared lookup has exactly the original schema's result,
including order and refusal for missing sorts. An independently emitted table
can therefore be kernel-checked against `prepare` once, then used for many
template checks. This does not replace metadata admission or prove a native
exporter's correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PreparedSortedCodecSchema

open SortedCanonicalSExprCodec
open SortedCodecMetadataAdmission

structure Entry where
  name : String
  shape : Shape
  deriving DecidableEq, Repr

def prepareRowFrom (constructors : List LoweredConstructor) (row : SortRow) : Entry :=
  ⟨row.name, match row.shape with
    | .token representation _ => .token representation
    | .list element _ => .list element
    | .constructors => .constructors
        ((constructors.filter (fun declaration => declaration.resultSort == row.name)).map
          LoweredConstructor.declaration)⟩

def prepareRow (metadata : Metadata) (row : SortRow) : Entry :=
  prepareRowFrom (constructorRows metadata) row

def prepareUsing (metadata : Metadata) (constructors : List LoweredConstructor) : List Entry :=
  metadata.sorts.map (prepareRowFrom constructors)

def prepare (metadata : Metadata) : List Entry :=
  metadata.sorts.map (prepareRow metadata)

def preparedSchema (entries : List Entry)
    (acceptsToken : String → String → Bool) : Schema where
  shape? name := (lookup? Entry.name entries name).map Entry.shape
  acceptsToken := acceptsToken

theorem lookup_prepared (metadata : Metadata) (rows : List SortRow) (name : String) :
    lookup? Entry.name (rows.map (prepareRow metadata)) name =
      (lookup? SortRow.name rows name).map (prepareRow metadata) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases same : row.name == name
      · simp [lookup?, prepareRow, prepareRowFrom, same]
      · simpa [lookup?, prepareRow, prepareRowFrom, same] using ih

theorem prepared_shape (metadata : Metadata)
    (acceptsToken : String → String → Bool) (name : String) :
    (preparedSchema (prepare metadata) acceptsToken).shape? name =
      (schema metadata acceptsToken).shape? name := by
  simp only [preparedSchema, prepare, lookup_prepared, schema, sort?]
  cases found : lookup? SortRow.name metadata.sorts name with
  | none => rfl
  | some row =>
      have named := (lookup_sound SortRow.name metadata.sorts name row found).2
      cases shaped : row.shape <;> simp [prepareRow, prepareRowFrom, shaped, named]

theorem preparedSchema_eq (metadata : Metadata)
    (acceptsToken : String → String → Bool) :
    preparedSchema (prepare metadata) acceptsToken = schema metadata acceptsToken := by
  apply congrArg (fun shape => Schema.mk shape acceptsToken)
  funext name
  exact prepared_shape metadata acceptsToken name

end Mettapedia.GSLT.Parsing.PreparedSortedCodecSchema
