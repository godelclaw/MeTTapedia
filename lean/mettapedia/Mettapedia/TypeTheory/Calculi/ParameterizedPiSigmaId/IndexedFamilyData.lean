import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedFamilyChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec

/-!
# Inspectable declaration entries and typed computation rows

These codecs expose the existing declaration entries and iota receipts as
data. Every row retains its intrinsic arity, dependent context, endpoints and
type. Reading data supplies no receipt: authority still comes from the
original checked schema and its selected occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Declaration.IndexedFamily.Data

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open PatternCodec PatternCodec.WithScalars

variable {Head : Type}

abbrev Row (Head : Type) :=
  Σ arity : Nat, Ctx Head arity × Tm Head arity × Tm Head arity × Tm Head arity

variable (scalars : ScalarCodecs) (heads : PartialCodec Head Pattern)

def valueData : Option (Tm Head 0) → Pattern
  | none => .apply "Opaque" []
  | some value => .apply "Defined" [WithScalars.encodeTm scalars heads value]

def readValue : Pattern → Option (Option (Tm Head 0))
  | .apply "Opaque" [] => some none
  | .apply "Defined" [value] => some <$> WithScalars.decodeTm? scalars heads 0 value
  | _ => none

@[simp] theorem readValue_valueData (value : Option (Tm Head 0)) :
    readValue scalars heads (valueData scalars heads value) = some value := by
  cases value <;> simp [valueData, readValue]

def entryData (entry : DeclName × Entry Head) : Pattern :=
  .apply "Declaration" [scalars.declaration.encode entry.1,
    WithScalars.encodeTm scalars heads entry.2.type, valueData scalars heads entry.2.value?]

def readEntry : Pattern → Option (DeclName × Entry Head)
  | .apply "Declaration" [name, type, value] => do
      return (← scalars.declaration.decode name,
        ⟨← WithScalars.decodeTm? scalars heads 0 type, ← readValue scalars heads value⟩)
  | _ => none

@[simp] theorem readEntry_entryData (entry : DeclName × Entry Head) :
    readEntry scalars heads (entryData scalars heads entry) = some entry := by
  rcases entry with ⟨name, type, value⟩
  simp [entryData, readEntry, scalars.declaration.decode_encode]

def rowData (row : Row Head) : Pattern :=
  .apply "Computation" [scalars.natural.encode row.1,
    WithScalars.encodeCtx scalars heads row.2.1,
    WithScalars.encodeTm scalars heads row.2.2.1,
    WithScalars.encodeTm scalars heads row.2.2.2.1,
    WithScalars.encodeTm scalars heads row.2.2.2.2]

def readRow : Pattern → Option (Row Head)
  | .apply "Computation" [arity, context, left, right, type] => do
      let arity ← scalars.natural.decode arity
      return ⟨arity, ← WithScalars.decodeCtx? scalars heads arity context,
        ← WithScalars.decodeTm? scalars heads arity left,
        ← WithScalars.decodeTm? scalars heads arity right,
        ← WithScalars.decodeTm? scalars heads arity type⟩
  | _ => none

@[simp] theorem readRow_rowData (row : Row Head) :
    readRow scalars heads (rowData scalars heads row) = some row := by
  rcases row with ⟨arity, context, left, right, type⟩
  simp [rowData, readRow, scalars.natural.decode_encode]

theorem rowData_injective : Function.Injective (rowData scalars heads) := by
  intro first second same
  have read := congrArg (readRow scalars heads) same
  simpa only [readRow_rowData, Option.some.injEq] using read

def entriesData (entries : List (DeclName × Entry Head)) : Pattern :=
  .apply "Declarations" (entries.map (entryData scalars heads))

def readEntries : Pattern → Option (List (DeclName × Entry Head))
  | .apply "Declarations" entries => entries.mapM (readEntry scalars heads)
  | _ => none

@[simp] theorem readEntries_entriesData (entries : List (DeclName × Entry Head)) :
    readEntries scalars heads (entriesData scalars heads entries) = some entries := by
  change (entries.map (entryData scalars heads)).mapM (readEntry scalars heads) = some entries
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp [ih]

def rowsData (rows : List (Row Head)) : Pattern :=
  .apply "Computations" (rows.map (rowData scalars heads))

def readRows : Pattern → Option (List (Row Head))
  | .apply "Computations" rows => rows.mapM (readRow scalars heads)
  | _ => none

@[simp] theorem readRows_rowsData (rows : List (Row Head)) :
    readRows scalars heads (rowsData scalars heads rows) = some rows := by
  change (rows.map (rowData scalars heads)).mapM (readRow scalars heads) = some rows
  induction rows with
  | nil => rfl
  | cons row rest ih => simp [ih]

theorem rowsData_injective : Function.Injective (rowsData scalars heads) := by
  intro first second same
  have read := congrArg (readRows scalars heads) same
  simpa only [readRows_rowsData, Option.some.injEq] using read

def packageData (entries : List (DeclName × Entry Head)) (rows : List (Row Head)) : Pattern :=
  .apply "GeneratedFamily" [entriesData scalars heads entries, rowsData scalars heads rows]

def readPackage : Pattern → Option (List (DeclName × Entry Head) × List (Row Head))
  | .apply "GeneratedFamily" [entries, rows] => do
      return (← readEntries scalars heads entries, ← readRows scalars heads rows)
  | _ => none

@[simp] theorem readPackage_packageData (entries : List (DeclName × Entry Head))
    (rows : List (Row Head)) :
    readPackage scalars heads (packageData scalars heads entries rows) = some (entries, rows) := by
  simp [packageData, readPackage]

theorem packageData_injective {firstEntries secondEntries : List (DeclName × Entry Head)}
    {firstRows secondRows : List (Row Head)}
    (same : packageData scalars heads firstEntries firstRows =
      packageData scalars heads secondEntries secondRows) :
    firstEntries = secondEntries ∧ firstRows = secondRows := by
  have read := congrArg (readPackage scalars heads) same
  simpa only [readPackage_packageData, Option.some.injEq, Prod.mk.injEq] using read

/-- The observation forgets proof terms, while retaining all displayed
judgments in their original order. It does not collapse duplicate rows. -/
def schemaRows {base : Rules Head} {signature : Signature Head}
    {computation : ProofRelevantRootComputation Head}
    (schemas : Checking.Schemas base signature computation) : List (Row Head) :=
  schemas.map fun row => ⟨row.1, row.2.context, row.2.left, row.2.right, row.2.type⟩

theorem schemaRows_length {base : Rules Head} {signature : Signature Head}
    {computation : ProofRelevantRootComputation Head}
    (schemas : Checking.Schemas base signature computation) :
    (schemaRows schemas).length = schemas.length := by simp [schemaRows]

theorem schemaRows_table {base : Rules Head} {signature : Signature Head}
    {computation : ProofRelevantRootComputation Head}
    (schemas : Checking.Schemas base signature computation) :
    (schemaRows schemas).map (fun row => (⟨row.1, row.2.2.1, row.2.2.2.1⟩ :
      Σ n, Tm Head n × Tm Head n)) = Checking.table schemas := by
  simp only [schemaRows, List.map_map, Checking.table, Function.comp_def]

/-- Looking up an inspected row retrieves the actual receipt at that
occurrence. Reading a merely similar row would not suffice. -/
theorem inspected_row_has_receipt {base : Rules Head} {signature : Signature Head}
    {computation : ProofRelevantRootComputation Head}
    (schemas : Checking.Schemas base signature computation)
    {row : Row Head} (member : row ∈ schemaRows schemas) :
    Nonempty (ComputationAuthority.ProofRelevantStepReceipt base signature computation
      row.2.1 row.2.2.1 row.2.2.2.1 row.2.2.2.2) := by
  obtain ⟨original, _, same⟩ := List.mem_map.mp member
  cases same
  exact ⟨original.2.receipt⟩

/-- An encoded row may be read successfully while it has no corresponding
constructor occurrence. Decoding is not publication. -/
theorem readable_outside_empty_table (row : Row Head) :
    readRow scalars heads (rowData scalars heads row) = some row ∧
      row ∉ ([] : List (Row Head)) :=
  ⟨readRow_rowData scalars heads row, List.not_mem_nil⟩

#print axioms readEntry_entryData
#print axioms readRow_rowData
#print axioms rowsData_injective
#print axioms inspected_row_has_receipt

end Declaration.IndexedFamily.Data
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
