import Mathlib.Data.List.Basic
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Nodup
import Mettapedia.GSLT.LanguageDef.MacroExportPlan

/-!
# Declared typed tables

This is the structural layer shared by counter and registry declarations.
Rows retain their written order and supplied numeric identifiers. A dense
policy checks those identifiers; it does not assign new ones. References
point to a declared scalar, singleton primary key, and carry the target's
ordinary scalar value. Composite primary and additional unique keys are
otherwise supported.

Admission checks finite schemas, exact row types and arities, key uniqueness,
dense policies and reference witnesses. It does not establish a counter's
cost law, an operation's effect contract, C emission or a byte-level reader.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeclaredTables

open MacroExportPlan (Atom)

inductive Cell where
  | nat (value : Nat)
  | identifier (value : String)
  | text (value : String)
  | boolean (value : Bool)
  deriving DecidableEq, Repr

inductive ScalarType where
  | nat | identifier | text | boolean
  | enumeration (choices : List String)
  deriving DecidableEq, Repr

inductive ColumnType where
  | scalar (type : ScalarType)
  | reference (table column : String)
  deriving DecidableEq, Repr

structure Column where
  name : String
  type : ColumnType
  deriving DecidableEq, Repr

abbrev Row := List Cell

structure Table where
  name : String
  columns : List Column
  primaryKey : List String
  uniqueKeys : List (List String)
  dense : Option String
  rows : List Row
  deriving DecidableEq, Repr

abbrev Bundle := List Table

def identifierStart (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || c == '_'

def identifierRest (c : Char) : Bool :=
  identifierStart c || ('0' ≤ c && c ≤ '9')

/-- Lexical identifier syntax; keyword spellings remain valid table data. -/
def identifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => identifierStart c && cs.all identifierRest

def uint64Bound : Nat := 2 ^ 64

def ScalarValid : ScalarType → Prop
  | .enumeration choices => choices ≠ [] ∧ choices.Nodup ∧ ∀ s ∈ choices, identifier s = true
  | _ => True

def checkScalar : ScalarType → Bool
  | .enumeration choices => !choices.isEmpty && decide choices.Nodup && choices.all identifier
  | _ => true

theorem checkScalar_iff (type : ScalarType) : checkScalar type = true ↔ ScalarValid type := by
  cases type <;> simp [checkScalar, ScalarValid, List.all_eq_true, and_assoc]

def ScalarCell : ScalarType → Cell → Prop
  | .nat, .nat n => n < uint64Bound
  | .identifier, .identifier s => identifier s = true
  | .text, .text _ => True
  | .boolean, .boolean _ => True
  | .enumeration choices, .identifier s => identifier s = true ∧ s ∈ choices
  | _, _ => False

def checkScalarCell : ScalarType → Cell → Bool
  | .nat, .nat n => decide (n < uint64Bound)
  | .identifier, .identifier s => identifier s
  | .text, .text _ => true
  | .boolean, .boolean _ => true
  | .enumeration choices, .identifier s => identifier s && choices.contains s
  | _, _ => false

theorem checkScalarCell_iff (type : ScalarType) (cell : Cell) :
    checkScalarCell type cell = true ↔ ScalarCell type cell := by
  cases type <;> cases cell <;>
    simp [checkScalarCell, ScalarCell]

def findTable (bundle : Bundle) (name : String) : Option Table :=
  bundle.find? (fun table => table.name == name)

def findColumn (table : Table) (name : String) : Option Column :=
  table.columns.find? (fun column => column.name == name)

/-- Named row fields, in the original column order. -/
def lowerRow (columns : List Column) (row : Row) : List (String × Cell) :=
  (columns.zip row).map fun pair => (pair.1.name, pair.2)

def cellAt (table : Table) (row : Row) (column : String) : Option Cell :=
  (lowerRow table.columns row).lookup column

def project (table : Table) (key : List String) (row : Row) : Option Row :=
  key.mapM (cellAt table row)

/-- A reference cannot use another reference as its target's type. -/
def referenceTarget (bundle : Bundle) (table column : String) : Option (Table × ScalarType) := do
  let target ← findTable bundle table
  if target.primaryKey != [column] then none else do
    let field ← findColumn target column
    match field.type with
    | .scalar type => some (target, type)
    | .reference _ _ => none

def resolveType (bundle : Bundle) : ColumnType → Option ScalarType
  | .scalar type => some type
  | .reference table column => (referenceTarget bundle table column).map Prod.snd

def TypeValid (bundle : Bundle) (type : ColumnType) : Prop :=
  ∃ scalar, resolveType bundle type = some scalar ∧ ScalarValid scalar

def checkType (bundle : Bundle) (type : ColumnType) : Bool :=
  match resolveType bundle type with
  | none => false
  | some scalar => checkScalar scalar

theorem checkType_iff (bundle : Bundle) (type : ColumnType) :
    checkType bundle type = true ↔ TypeValid bundle type := by
  unfold checkType TypeValid
  cases resolveType bundle type <;> simp [checkScalar_iff]

def ReferenceWitness (bundle : Bundle) (table column : String) (value : Cell) : Prop :=
  ∃ target scalar row, referenceTarget bundle table column = some (target, scalar) ∧
    row ∈ target.rows ∧ cellAt target row column = some value

def checkReference (bundle : Bundle) (table column : String) (value : Cell) : Bool :=
  match referenceTarget bundle table column with
  | none => false
  | some (target, _) => target.rows.any fun row => cellAt target row column == some value

theorem checkReference_iff (bundle : Bundle) (table column : String) (value : Cell) :
    checkReference bundle table column value = true ↔ ReferenceWitness bundle table column value := by
  unfold checkReference ReferenceWitness
  cases referenceTarget bundle table column with
  | none => simp
  | some target =>
      rcases target with ⟨target, scalar⟩
      simp [List.any_eq_true]

def CellTyped (bundle : Bundle) (type : ColumnType) (value : Cell) : Prop :=
  (∃ scalar, resolveType bundle type = some scalar ∧ ScalarCell scalar value) ∧
    match type with
    | .scalar _ => True
    | .reference table column => ReferenceWitness bundle table column value

def checkCell (bundle : Bundle) (type : ColumnType) (value : Cell) : Bool :=
  (match resolveType bundle type with
   | none => false
   | some scalar => checkScalarCell scalar value) &&
    match type with
    | .scalar _ => true
    | .reference table column => checkReference bundle table column value

theorem checkCell_iff (bundle : Bundle) (type : ColumnType) (value : Cell) :
    checkCell bundle type value = true ↔ CellTyped bundle type value := by
  unfold checkCell CellTyped
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨typed, referenced⟩
    refine ⟨?_, ?_⟩
    · cases h : resolveType bundle type with
      | none => simp [h] at typed
      | some scalar => exact ⟨scalar, rfl, (checkScalarCell_iff scalar value).mp (by simpa [h] using typed)⟩
    · cases type <;> simp_all [checkReference_iff]
  · rintro ⟨⟨scalar, resolved, typed⟩, referenced⟩
    refine ⟨?_, ?_⟩
    · simpa [resolved] using (checkScalarCell_iff scalar value).mpr typed
    · cases type <;> simp_all [checkReference_iff]

def RowTyped (bundle : Bundle) (columns : List Column) (row : Row) : Prop :=
  List.Forall₂ (fun column cell => CellTyped bundle column.type cell) columns row

def checkRow (bundle : Bundle) : List Column → Row → Bool
  | [], [] => true
  | column :: columns, value :: row => checkCell bundle column.type value && checkRow bundle columns row
  | _, _ => false

theorem checkRow_iff (bundle : Bundle) : ∀ columns row,
    checkRow bundle columns row = true ↔ RowTyped bundle columns row := by
  intro columns
  induction columns with
  | nil => intro row; cases row <;> simp [checkRow, RowTyped]
  | cons column columns ih =>
      intro row
      cases row <;> simp [checkRow, RowTyped, ih, checkCell_iff]

def KeyValid (table : Table) (key : List String) : Prop :=
  key ≠ [] ∧ key.Nodup ∧ ∀ name ∈ key, name ∈ table.columns.map Column.name

def checkKey (table : Table) (key : List String) : Bool :=
  !key.isEmpty && decide key.Nodup && key.all (table.columns.map Column.name).contains

theorem checkKey_iff (table : Table) (key : List String) :
    checkKey table key = true ↔ KeyValid table key := by
  simp [checkKey, KeyValid, List.all_eq_true, and_assoc]

def KeyUnique (table : Table) (key : List String) : Prop :=
  (table.rows.map (project table key)).Nodup

def checkUnique (table : Table) (key : List String) : Bool :=
  decide (table.rows.map (project table key)).Nodup

theorem checkUnique_iff (table : Table) (key : List String) :
    checkUnique table key = true ↔ KeyUnique table key := by simp [checkUnique, KeyUnique]

/-- The sequence already carries the requested natural identifiers. -/
def DenseFrom (table : Table) (column : String) (first : Nat) (rows : List Row) : Prop :=
  ∀ i (hi : i < rows.length), cellAt table rows[i] column = some (.nat (first + i))

def checkDenseFrom (table : Table) (column : String) : Nat → List Row → Bool
  | _, [] => true
  | first, row :: rows =>
      cellAt table row column == some (.nat first) && checkDenseFrom table column (first + 1) rows

theorem checkDenseFrom_iff (table : Table) (column : String) : ∀ first rows,
    checkDenseFrom table column first rows = true ↔ DenseFrom table column first rows := by
  intro first rows
  induction rows generalizing first with
  | nil => simp [checkDenseFrom, DenseFrom]
  | cons row rows ih =>
      simp only [checkDenseFrom, Bool.and_eq_true, beq_iff_eq, ih]
      constructor
      · rintro ⟨head, tail⟩ i hi
        cases i with
        | zero => simpa using head
        | succ i =>
            have ht := tail i (by simpa using hi)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
      · intro h
        refine ⟨h 0 (by simp), ?_⟩
        intro i hi
        have hs := h (i + 1) (by simpa using hi)
        change cellAt table rows[i] column = some (.nat (first + (i + 1))) at hs
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

def DenseValid (table : Table) : Prop :=
  match table.dense with
  | none => True
  | some column => table.primaryKey = [column] ∧
      (∃ field, findColumn table column = some field ∧ field.type = .scalar .nat) ∧
      DenseFrom table column 0 table.rows

def checkDense (table : Table) : Bool :=
  match table.dense with
  | none => true
  | some column => table.primaryKey == [column] &&
      (match findColumn table column with
       | none => false
       | some field => field.type == .scalar .nat) &&
      checkDenseFrom table column 0 table.rows

theorem checkDense_iff (table : Table) : checkDense table = true ↔ DenseValid table := by
  unfold checkDense DenseValid
  cases table.dense with
  | none => simp
  | some column =>
      cases h : findColumn table column <;> simp [h, checkDenseFrom_iff, and_assoc]

structure TableValid (bundle : Bundle) (table : Table) : Prop where
  name : identifier table.name = true
  columns : table.columns ≠ []
  columnNames : (table.columns.map Column.name).Nodup
  columnIdentifiers : ∀ column ∈ table.columns, identifier column.name = true
  columnTypes : ∀ column ∈ table.columns, TypeValid bundle column.type
  primary : KeyValid table table.primaryKey
  additional : ∀ key ∈ table.uniqueKeys, KeyValid table key
  primaryUnique : KeyUnique table table.primaryKey
  additionalUnique : ∀ key ∈ table.uniqueKeys, KeyUnique table key
  dense : DenseValid table
  rows : ∀ row ∈ table.rows, RowTyped bundle table.columns row

def checkTable (bundle : Bundle) (table : Table) : Bool :=
  identifier table.name && !table.columns.isEmpty && decide (table.columns.map Column.name).Nodup &&
    table.columns.all (fun column => identifier column.name && checkType bundle column.type) &&
    checkKey table table.primaryKey && table.uniqueKeys.all (checkKey table) &&
    checkUnique table table.primaryKey && table.uniqueKeys.all (checkUnique table) &&
    checkDense table && table.rows.all (checkRow bundle table.columns)

theorem checkTable_iff (bundle : Bundle) (table : Table) :
    checkTable bundle table = true ↔ TableValid bundle table := by
  simp only [checkTable, Bool.and_eq_true, List.all_eq_true, checkKey_iff,
    checkUnique_iff, checkDense_iff, checkRow_iff, checkType_iff, decide_eq_true_eq,
    Bool.not_eq_true', List.isEmpty_eq_false_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨name, columns⟩, names⟩, columnChecks⟩, primary⟩, additional⟩,
      primaryUnique⟩, additionalUnique⟩, dense⟩, rows⟩
    exact ⟨name, columns, names, fun c hc => (columnChecks c hc).1,
      fun c hc => (columnChecks c hc).2, primary, additional, primaryUnique, additionalUnique, dense, rows⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h.name, h.columns⟩, h.columnNames⟩,
      fun c hc => ⟨h.columnIdentifiers c hc, h.columnTypes c hc⟩⟩, h.primary⟩, h.additional⟩,
      h.primaryUnique⟩, h.additionalUnique⟩, h.dense⟩, h.rows⟩

structure BundleValid (bundle : Bundle) : Prop where
  names : (bundle.map Table.name).Nodup
  tables : ∀ table ∈ bundle, TableValid bundle table

def check (bundle : Bundle) : Bool :=
  decide (bundle.map Table.name).Nodup && bundle.all (checkTable bundle)

theorem check_iff (bundle : Bundle) : check bundle = true ↔ BundleValid bundle := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, checkTable_iff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.names, h.tables⟩⟩

/-- A failed mandatory component refuses the whole bundle without evaluating
unrelated whole-table key checks. -/
theorem check_false_of_dense_failure {bundle : Bundle} {table : Table}
    (member : table ∈ bundle) (failed : checkDense table = false) : check bundle = false := by
  cases checked : check bundle with
  | false => rfl
  | true =>
      have dense := (checkDense_iff table).mpr (((check_iff bundle).mp checked).tables table member).dense
      rw [failed] at dense
      cases dense

/-! ## Lookup, reconstruction and scalable admission components -/

theorem findTable_spec {bundle : Bundle} {name : String} {table : Table}
    (h : findTable bundle name = some table) : table ∈ bundle ∧ table.name = name :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem findColumn_spec {table : Table} {name : String} {column : Column}
    (h : findColumn table name = some column) : column ∈ table.columns ∧ column.name = name :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem findTable_of_mem {bundle : Bundle} (valid : BundleValid bundle) {table : Table}
    (member : table ∈ bundle) : findTable bundle table.name = some table := by
  cases found : findTable bundle table.name with
  | none =>
      have absent := List.find?_eq_none.mp found table member
      simp at absent
  | some target =>
      obtain ⟨targetMember, name⟩ := findTable_spec found
      exact congrArg some (List.inj_on_of_nodup_map valid.names targetMember member name)

theorem findColumn_of_mem {bundle : Bundle} {table : Table} (valid : TableValid bundle table)
    {column : Column} (member : column ∈ table.columns) :
    findColumn table column.name = some column := by
  cases found : findColumn table column.name with
  | none =>
      have absent := List.find?_eq_none.mp found column member
      simp at absent
  | some target =>
      obtain ⟨targetMember, name⟩ := findColumn_spec found
      exact congrArg some (List.inj_on_of_nodup_map valid.columnNames targetMember member name)

theorem referenceTarget_spec {bundle : Bundle} {table column : String} {target : Table}
    {scalar : ScalarType} (h : referenceTarget bundle table column = some (target, scalar)) :
    target ∈ bundle ∧ target.name = table ∧ target.primaryKey = [column] ∧
      ∃ field ∈ target.columns, field.name = column ∧ field.type = .scalar scalar := by
  unfold referenceTarget at h
  cases ht : findTable bundle table with
  | none => simp [ht] at h
  | some found =>
      rw [ht] at h
      change (if found.primaryKey != [column] then none else do
        let field ← findColumn found column
        match field.type with
        | .scalar type => some (found, type)
        | .reference _ _ => none) = some (target, scalar) at h
      split at h
      · simp at h
      · rename_i key
        cases hc : findColumn found column with
        | none => simp [hc] at h
        | some field =>
            rw [hc] at h
            change (match field.type with
              | .scalar type => some (found, type)
              | .reference _ _ => none) = some (target, scalar) at h
            cases hf : field.type with
            | reference _ _ => simp [hf] at h
            | scalar type =>
                simp only [hf, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨member, name⟩ := findTable_spec ht
                obtain ⟨fieldMember, fieldName⟩ := findColumn_spec hc
                exact ⟨member, name, by simpa using key, field, fieldMember, fieldName, hf⟩

theorem RowTyped.length_eq {bundle : Bundle} {columns : List Column} {row : Row}
    (h : RowTyped bundle columns row) : columns.length = row.length := List.Forall₂.length_eq h

/-- Dropping column labels reconstructs every admitted scalar row exactly. -/
theorem lowerRow_reconstruct {columns : List Column} {row : Row}
    (h : columns.length = row.length) : (lowerRow columns row).map Prod.snd = row := by
  simp only [lowerRow, List.map_map, Function.comp_def]
  exact List.map_snd_zip (by omega)

theorem lowerRow_column_order {columns : List Column} {row : Row}
    (h : columns.length = row.length) :
    (lowerRow columns row).map Prod.fst = columns.map Column.name := by
  simp only [lowerRow, List.map_map, Function.comp_def]
  change List.map (Column.name ∘ Prod.fst) (columns.zip row) = columns.map Column.name
  rw [← List.map_map]
  rw [List.map_fst_zip (by omega)]

def lowerRows (table : Table) : List (List (String × Cell)) :=
  table.rows.map (lowerRow table.columns)

theorem lowerRows_reconstruct {bundle : Bundle} {table : Table} (h : TableValid bundle table) :
    (lowerRows table).map (List.map Prod.snd) = table.rows := by
  rw [lowerRows, List.map_map]
  calc
    _ = table.rows.map id := List.map_congr_left fun row hr =>
      lowerRow_reconstruct (h.rows row hr).length_eq
    _ = table.rows := List.map_id _

theorem lowerRows_length (table : Table) : (lowerRows table).length = table.rows.length := by
  simp [lowerRows]

theorem lowerRow_injective {columns : List Column} {left right : Row}
    (hl : columns.length = left.length) (hr : columns.length = right.length)
    (h : lowerRow columns left = lowerRow columns right) : left = right := by
  have := congrArg (List.map Prod.snd) h
  simpa only [lowerRow_reconstruct hl, lowerRow_reconstruct hr] using this

private theorem lookup_of_unique_keys {fields : List (String × Cell)}
    (unique : (fields.map Prod.fst).Nodup) {field : String × Cell} (member : field ∈ fields) :
    fields.lookup field.1 = some field.2 := by
  induction fields with
  | nil => simp at member
  | cons first fields ih =>
      obtain ⟨fresh, tailUnique⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact List.lookup_cons_self
      · have different : field.1 ≠ first.1 := by
          intro same
          exact fresh (List.mem_map.mpr ⟨field, tailMember, same⟩)
        rcases first with ⟨name, value⟩
        simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr different] using ih tailUnique tailMember

private theorem option_mapM_eq_map {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = some (g x)) → xs.mapM f = some (xs.map g) := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro h
      have head := h x (by simp)
      have tail := ih (fun y hy => h y (by simp [hy]))
      simp [head, tail]

theorem project_all_columns {table : Table} {row : Row}
    (lengths : table.columns.length = row.length)
    (unique : (table.columns.map Column.name).Nodup) :
    project table (table.columns.map Column.name) row = some row := by
  have fieldsUnique : ((lowerRow table.columns row).map Prod.fst).Nodup := by
    rw [lowerRow_column_order lengths]
    exact unique
  have rebuilt := option_mapM_eq_map
    (fun field : String × Cell => (lowerRow table.columns row).lookup field.1) Prod.snd
    (lowerRow table.columns row) (fun field hf => lookup_of_unique_keys fieldsUnique hf)
  unfold project cellAt
  rw [← lowerRow_column_order lengths]
  simpa only [List.mapM_map, Function.comp_def, lowerRow_reconstruct lengths] using rebuilt

theorem eq_of_keyUnique {table : Table} {key : List String} (h : KeyUnique table key)
    {left right : Row} (hl : left ∈ table.rows) (hr : right ∈ table.rows)
    (same : project table key left = project table key right) : left = right := by
  exact List.inj_on_of_nodup_map h hl hr same

def lookupRow (table : Table) (key : List String) (value : Row) : Option Row :=
  table.rows.find? fun row => project table key row == some value

theorem lookupRow_spec {table : Table} {key : List String} {value row : Row}
    (h : lookupRow table key value = some row) :
    row ∈ table.rows ∧ project table key row = some value :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem lookupRow_complete {table : Table} {key : List String} (unique : KeyUnique table key)
    {row value : Row} (member : row ∈ table.rows) (projected : project table key row = some value) :
    lookupRow table key value = some row := by
  cases found : lookupRow table key value with
  | none =>
      have absent := (List.find?_eq_none.mp found) row member
      simp [projected] at absent
  | some foundRow =>
      obtain ⟨hm, hp⟩ := lookupRow_spec found
      have same := eq_of_keyUnique unique hm member (hp.trans projected.symm)
      exact congrArg some same

/-- An admitted reference resolves to an actual declared table and row. -/
theorem reference_resolves {bundle : Bundle} {table column : String} {value : Cell}
    (h : CellTyped bundle (.reference table column) value) :
    ∃ target scalar row, target ∈ bundle ∧ target.name = table ∧ target.primaryKey = [column] ∧
      (∃ field ∈ target.columns, field.name = column ∧ field.type = .scalar scalar) ∧
      row ∈ target.rows ∧ cellAt target row column = some value ∧ ScalarCell scalar value := by
  obtain ⟨⟨scalar, resolved, typed⟩, target, targetScalar, row, found, member, cell⟩ := h
  have scalarEq : targetScalar = scalar := by
    simpa [resolveType, found] using resolved
  subst targetScalar
  obtain ⟨tableMember, tableName, key, field⟩ := referenceTarget_spec found
  exact ⟨target, scalar, row, tableMember, tableName, key, field, member, cell, typed⟩

theorem reference_row_unique {bundle : Bundle} (valid : BundleValid bundle)
    {table column : String} {value : Cell} {target : Table} {scalar : ScalarType}
    (found : referenceTarget bundle table column = some (target, scalar))
    {left right : Row} (hl : left ∈ target.rows) (hr : right ∈ target.rows)
    (leftCell : cellAt target left column = some value)
    (rightCell : cellAt target right column = some value) : left = right := by
  obtain ⟨member, _, key, _⟩ := referenceTarget_spec found
  apply eq_of_keyUnique (valid.tables target member).primaryUnique hl hr
  simp [project, key, leftCell, rightCell]

/-- Admitting chunks preserves their concatenation and row order. -/
theorem checkRows_append (bundle : Bundle) (columns : List Column) (left right : List Row) :
    (left ++ right).all (checkRow bundle columns) =
      (left.all (checkRow bundle columns) && right.all (checkRow bundle columns)) := by
  simp

theorem checkRows_flatten (bundle : Bundle) (columns : List Column) (chunks : List (List Row)) :
    chunks.flatten.all (checkRow bundle columns) =
      chunks.all (fun chunk => chunk.all (checkRow bundle columns)) := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih => simp [ih]

theorem rowsTyped_of_chunks {bundle : Bundle} {table : Table} {chunks : List (List Row)}
    (layout : chunks.flatten = table.rows)
    (checked : ∀ chunk ∈ chunks, chunk.all (checkRow bundle table.columns) = true) :
    ∀ row ∈ table.rows, RowTyped bundle table.columns row := by
  have h : chunks.flatten.all (checkRow bundle table.columns) = true := by
    rw [checkRows_flatten]
    exact List.all_eq_true.mpr checked
  rw [layout] at h
  exact fun row hr => (checkRow_iff bundle table.columns row).mp (List.all_eq_true.mp h row hr)

/-- Distinct computed codes imply distinct original keys. No hash trust is
needed: the proof concerns the actual mapped code values. An injective code
also avoids false refusals; existing string-code proofs can supply that law. -/
theorem keyUnique_of_codes {table : Table} {key : List String} (code : Option Row → Nat)
    (checked : (table.rows.map (fun row => code (project table key row))).Nodup) :
    KeyUnique table key := by
  exact List.Nodup.of_map code (by simpa only [List.map_map, Function.comp_def] using checked :
    ((table.rows.map (project table key)).map code).Nodup)

theorem keyCodes_nodup_iff {table : Table} {key : List String} (code : Option Row → Nat)
    (injective : Function.Injective code) :
    (table.rows.map (fun row => code (project table key row))).Nodup ↔ KeyUnique table key := by
  constructor
  · exact keyUnique_of_codes code
  · intro h
    simpa only [List.map_map, Function.comp_def] using h.map injective

/-- Row-code equalities can be kernel-checked in separate chunks. The
whole-table distinctness decision then uses only the supplied numeric codes. -/
theorem keyUnique_of_code_chunks {table : Table} {key : List String} (code : Option Row → Nat)
    (chunks : List (List Row × List Nat))
    (layout : (chunks.map Prod.fst).flatten = table.rows)
    (computed : ∀ chunk ∈ chunks,
      chunk.1.map (fun row => code (project table key row)) = chunk.2)
    (distinct : (chunks.map Prod.snd).flatten.Nodup) : KeyUnique table key := by
  apply keyUnique_of_codes code
  rw [← layout, List.map_flatten, List.map_map]
  have codes : chunks.map (List.map (fun row => code (project table key row)) ∘ Prod.fst) =
      chunks.map Prod.snd := List.map_congr_left computed
  rw [codes]
  exact distinct

theorem checkDenseFrom_append (table : Table) (column : String) (first : Nat)
    (left right : List Row) :
    checkDenseFrom table column first (left ++ right) =
      (checkDenseFrom table column first left &&
        checkDenseFrom table column (first + left.length) right) := by
  induction left generalizing first with
  | nil => simp [checkDenseFrom]
  | cons row rows ih => simp [checkDenseFrom, ih, Bool.and_assoc, Nat.add_comm,
      Nat.add_left_comm]

/-! ## Ordered filtered projections

Views are row sequences, not new admitted tables. In particular a filtered
view inherits neither a dense policy nor an assignment of new identifiers.
Name/type validation for an export manifest is a separate obligation: an
empty selection must not be used to justify a nonexistent requested column.
-/

def rowMatches (table : Table) (predicates : List (String × Cell)) (row : Row) : Bool :=
  predicates.all fun predicate => cellAt table row predicate.1 == some predicate.2

def select (table : Table) (predicates : List (String × Cell)) : List Row :=
  table.rows.filter (rowMatches table predicates)

def view (table : Table) (predicates : List (String × Cell)) (columns : List String) :
    Option (List Row) := (select table predicates).mapM (project table columns)

def PredicateTyped (bundle : Bundle) (table : Table) (predicate : String × Cell) : Prop :=
  ∃ field scalar, findColumn table predicate.1 = some field ∧
    resolveType bundle field.type = some scalar ∧ ScalarCell scalar predicate.2

def checkPredicate (bundle : Bundle) (table : Table) (predicate : String × Cell) : Bool :=
  match findColumn table predicate.1 with
  | none => false
  | some field =>
      match resolveType bundle field.type with
      | none => false
      | some scalar => checkScalarCell scalar predicate.2

theorem checkPredicate_iff (bundle : Bundle) (table : Table) (predicate : String × Cell) :
    checkPredicate bundle table predicate = true ↔ PredicateTyped bundle table predicate := by
  unfold checkPredicate PredicateTyped
  cases findColumn table predicate.1 with
  | none => simp
  | some field =>
      simp only [Option.some.injEq, exists_and_left]
      cases resolved : resolveType bundle field.type <;> simp [resolved, checkScalarCell_iff]

structure ViewNamesValid (bundle : Bundle) (table : Table) (predicates : List (String × Cell))
    (columns : List String) : Prop where
  predicates : ∀ predicate ∈ predicates, PredicateTyped bundle table predicate
  columns : ∀ name ∈ columns, name ∈ table.columns.map Column.name

/-- Validate the manifest even when selection would return no rows.
Predicate values need their scalar type, not a witness that a matching row
exists; a typed query for an absent key is a legitimate empty view. -/
def checkViewNames (bundle : Bundle) (table : Table) (predicates : List (String × Cell))
    (columns : List String) : Bool :=
  predicates.all (checkPredicate bundle table) && columns.all (table.columns.map Column.name).contains

theorem checkViewNames_iff (bundle : Bundle) (table : Table) (predicates : List (String × Cell))
    (columns : List String) : checkViewNames bundle table predicates columns = true ↔
      ViewNamesValid bundle table predicates columns := by
  simp only [checkViewNames, Bool.and_eq_true, List.all_eq_true, checkPredicate_iff,
    List.contains_iff_mem]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.predicates, h.columns⟩⟩

theorem checkViewNames_sound {bundle : Bundle} {table : Table}
    {predicates : List (String × Cell)} {columns : List String}
    (h : checkViewNames bundle table predicates columns = true) :
    (∀ name ∈ columns, ∃ field ∈ table.columns, field.name = name) ∧
      ∀ predicate ∈ predicates, ∃ field ∈ table.columns, ∃ scalar,
        field.name = predicate.1 ∧ resolveType bundle field.type = some scalar ∧
          ScalarCell scalar predicate.2 := by
  have valid := (checkViewNames_iff _ _ _ _).mp h
  refine ⟨fun name hn => List.mem_map.mp (valid.columns name hn), ?_⟩
  intro predicate hp
  obtain ⟨field, scalar, found, resolved, typed⟩ := valid.predicates predicate hp
  obtain ⟨member, name⟩ := findColumn_spec found
  exact ⟨field, member, scalar, name, resolved, typed⟩

theorem rowMatches_iff (table : Table) (predicates : List (String × Cell)) (row : Row) :
    rowMatches table predicates row = true ↔
      ∀ predicate ∈ predicates, cellAt table row predicate.1 = some predicate.2 := by
  simp [rowMatches, List.all_eq_true]

theorem mem_select_iff (table : Table) (predicates : List (String × Cell)) (row : Row) :
    row ∈ select table predicates ↔ row ∈ table.rows ∧
      ∀ predicate ∈ predicates, cellAt table row predicate.1 = some predicate.2 := by
  simp [select, rowMatches_iff]

theorem select_sublist (table : Table) (predicates : List (String × Cell)) :
    List.Sublist (select table predicates) table.rows := List.filter_sublist

theorem select_append (table : Table) (predicates : List (String × Cell)) (left right : List Row) :
    (left ++ right).filter (rowMatches table predicates) =
      left.filter (rowMatches table predicates) ++ right.filter (rowMatches table predicates) := by simp

private theorem option_mapM_forall₂ {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys ↔
      List.Forall₂ (fun x y => f x = some y) xs ys := by
  intro xs
  induction xs with
  | nil => intro ys; cases ys <;> simp
  | cons x xs ih =>
      intro ys
      cases hx : f x with
      | none =>
          cases ys <;> simp [hx]
      | some y =>
          cases ys with
          | nil =>
              cases hs : xs.mapM f <;> simp [hx, hs]
          | cons first rest =>
              cases hs : xs.mapM f with
              | none => simp [hx, hs, ← ih]
              | some values => simp [hx, hs, ← ih, eq_comm]

/-- Every output row has exactly its corresponding ordered source projection. -/
theorem view_iff (table : Table) (predicates : List (String × Cell)) (columns : List String)
    (rows : List Row) : view table predicates columns = some rows ↔
      List.Forall₂ (fun source target => project table columns source = some target)
        (select table predicates) rows := option_mapM_forall₂ _ _ _

def checkView (table : Table) (predicates : List (String × Cell)) (columns : List String)
    (selected projected : List Row) : Bool :=
  selected == select table predicates && view table predicates columns == some projected

theorem checkView_sound {table : Table} {predicates : List (String × Cell)} {columns : List String}
    {selected projected : List Row} (h : checkView table predicates columns selected projected = true) :
    List.Sublist selected table.rows ∧
      (∀ row, row ∈ selected ↔ row ∈ table.rows ∧
        ∀ predicate ∈ predicates, cellAt table row predicate.1 = some predicate.2) ∧
      List.Forall₂ (fun source target => project table columns source = some target) selected projected := by
  simp only [checkView, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, projected⟩
  exact ⟨select_sublist _ _, mem_select_iff _ _, (view_iff _ _ _ _).mp projected⟩

theorem view_length {table : Table} {predicates : List (String × Cell)} {columns : List String}
    {rows : List Row} (h : view table predicates columns = some rows) :
    rows.length = (select table predicates).length :=
  (List.Forall₂.length_eq ((view_iff _ _ _ _).mp h)).symm

def checkViewPlan (bundle : Bundle) (table : Table) (predicates : List (String × Cell))
    (columns : List String) (selected projected : List Row) : Bool :=
  checkViewNames bundle table predicates columns && checkView table predicates columns selected projected

theorem checkViewPlan_sound {bundle : Bundle} {table : Table} {predicates : List (String × Cell)}
    {columns : List String} {selected projected : List Row}
    (h : checkViewPlan bundle table predicates columns selected projected = true) :
    ViewNamesValid bundle table predicates columns ∧ List.Sublist selected table.rows ∧
      (∀ row, row ∈ selected ↔ row ∈ table.rows ∧
        ∀ predicate ∈ predicates, cellAt table row predicate.1 = some predicate.2) ∧
      List.Forall₂ (fun source target => project table columns source = some target) selected projected := by
  simp only [checkViewPlan, Bool.and_eq_true] at h
  exact ⟨(checkViewNames_iff _ _ _ _).mp h.1, checkView_sound h.2⟩

/-! ## Ordered source-Atom adapter

The bundle decoder first reads every schema, then decodes values using their
declared scalar types. Thus the symbol `true` in an Identifier or Enum column
is an identifier, and in a Bool column is a Boolean. References use the same
type-directed decoder as their target. This is an Atom adapter, not a proof
about the lexer or byte escaping of a native reader.
-/

def symbol : Atom → Option String
  | .symbol s => some s
  | _ => none

def decodeScalarType : Atom → Option ScalarType
  | .symbol "Nat" => some .nat
  | .symbol "Identifier" => some .identifier
  | .symbol "Text" => some .text
  | .symbol "Bool" => some .boolean
  | .list (.symbol "Enum" :: choices) => (choices.mapM symbol).map .enumeration
  | _ => none

def decodeColumnType : Atom → Option ColumnType
  | .list [.symbol "Ref", .symbol table, .symbol column] => some (.reference table column)
  | a => (decodeScalarType a).map .scalar

def decodeColumn : Atom → Option Column
  | .list [.symbol "Column", .symbol name, type] => do
      pure ⟨name, ← decodeColumnType type⟩
  | _ => none

def decimalValue : List Char → Option Nat
  | [] => none
  | chars => chars.foldl (fun acc char => do
      let n ← acc
      if char.isDigit then some (10 * n + (char.toNat - '0'.toNat)) else none) (some 0)

/-- Only canonical unsigned decimal symbols are accepted as Nat cells. -/
def decodeNatural (s : String) : Option Nat := do
  let n ← decimalValue s.toList
  if toString n = s then some n else none

def decodeScalarCell : ScalarType → Atom → Option Cell
  | .nat, .symbol s => (decodeNatural s).map .nat
  | .identifier, .symbol s => some (.identifier s)
  | .text, .text s => some (.text s)
  | .boolean, .symbol "true" => some (.boolean true)
  | .boolean, .symbol "false" => some (.boolean false)
  | .enumeration _, .symbol s => some (.identifier s)
  | _, _ => none

def decodeCell (schemas : Bundle) (type : ColumnType) (a : Atom) : Option Cell := do
  let scalar ← resolveType schemas type
  decodeScalarCell scalar a

def decodeRowCells (schemas : Bundle) : List Column → List Atom → Option Row
  | [], [] => some []
  | column :: columns, a :: atoms => do
      pure ((← decodeCell schemas column.type a) :: (← decodeRowCells schemas columns atoms))
  | _, _ => none

def decodeRow (schemas : Bundle) (columns : List Column) : Atom → Option Row
  | .list (.symbol "Row" :: atoms) => decodeRowCells schemas columns atoms
  | _ => none

structure RawTable where
  schema : Table
  rows : List Atom

/-- Fields after Key have the order Unique*, Dense?, Rows. -/
def decodeTail : List Atom → Option (List (List String) × Option String × List Atom)
  | .list (.symbol "Unique" :: columns) :: rest => do
      let key ← columns.mapM symbol
      let (keys, dense, rows) ← decodeTail rest
      pure (key :: keys, dense, rows)
  | [.list (.symbol "Rows" :: rows)] => some ([], none, rows)
  | [.list [.symbol "Dense", .symbol column], .list (.symbol "Rows" :: rows)] =>
      some ([], some column, rows)
  | _ => none

def decodeRawTable : Atom → Option RawTable
  | .list (.symbol "Table" :: .symbol name :: .list (.symbol "Columns" :: columns) ::
      .list (.symbol "Key" :: primary) :: rest) => do
      let fields ← columns.mapM decodeColumn
      let key ← primary.mapM symbol
      let (unique, dense, rows) ← decodeTail rest
      pure ⟨⟨name, fields, key, unique, dense, []⟩, rows⟩
  | _ => none

def decodeBundle : Atom → Option Bundle
  | .list (.symbol "cesta-tables/1" :: tables) => do
      let raw ← tables.mapM decodeRawTable
      let schemas := raw.map RawTable.schema
      raw.mapM fun source => do
        let rows ← source.rows.mapM (decodeRow schemas source.schema.columns)
        pure {source.schema with rows := rows}
  | _ => none

def quoteScalarType : ScalarType → Atom
  | .nat => .symbol "Nat"
  | .identifier => .symbol "Identifier"
  | .text => .symbol "Text"
  | .boolean => .symbol "Bool"
  | .enumeration choices => .list (.symbol "Enum" :: choices.map .symbol)

def quoteColumnType : ColumnType → Atom
  | .scalar type => quoteScalarType type
  | .reference table column => .list [.symbol "Ref", .symbol table, .symbol column]

def quoteColumn (column : Column) : Atom :=
  .list [.symbol "Column", .symbol column.name, quoteColumnType column.type]

def quoteCell : Cell → Atom
  | .nat n => .symbol (toString n)
  | .identifier s => .symbol s
  | .text s => .text s
  | .boolean true => .symbol "true"
  | .boolean false => .symbol "false"

def quoteRow (row : Row) : Atom := .list (.symbol "Row" :: row.map quoteCell)

def quoteTail (uniqueKeys : List (List String)) (dense : Option String) (rows : List Row) : List Atom :=
  uniqueKeys.map (fun key => .list (.symbol "Unique" :: key.map .symbol)) ++
    (match dense with
     | none => []
     | some column => [.list [.symbol "Dense", .symbol column]]) ++
    [.list (.symbol "Rows" :: rows.map quoteRow)]

def quoteTable (table : Table) : Atom :=
  .list (.symbol "Table" :: .symbol table.name ::
    .list (.symbol "Columns" :: table.columns.map quoteColumn) ::
    .list (.symbol "Key" :: table.primaryKey.map .symbol) ::
    quoteTail table.uniqueKeys table.dense table.rows)

def quoteBundle (bundle : Bundle) : Atom :=
  .list (.symbol "cesta-tables/1" :: bundle.map quoteTable)

private theorem decodeSymbols_quote (names : List String) :
    (names.map Atom.symbol).mapM symbol = some names := by
  induction names with
  | nil => rfl
  | cons name names ih => simp [symbol, ih]

private theorem decodeSymbols_comp (names : List String) :
    names.mapM (symbol ∘ Atom.symbol) = some names := by
  simpa only [List.mapM_map] using decodeSymbols_quote names

theorem decodeScalarType_quote (type : ScalarType) :
    decodeScalarType (quoteScalarType type) = some type := by
  cases type <;> simp [decodeScalarType, quoteScalarType, decodeSymbols_comp]

theorem decodeColumnType_quote (type : ColumnType) :
    decodeColumnType (quoteColumnType type) = some type := by
  cases type with
  | reference table column => rfl
  | scalar type =>
      cases type <;> simp [decodeColumnType, quoteColumnType, quoteScalarType, decodeScalarType,
        decodeSymbols_comp]

theorem decodeColumn_quote (column : Column) : decodeColumn (quoteColumn column) = some column := by
  cases column
  simp [decodeColumn, quoteColumn, decodeColumnType_quote]

theorem decodeTail_quote (keys : List (List String)) (dense : Option String) (rows : List Row) :
    decodeTail (quoteTail keys dense rows) = some (keys, dense, rows.map quoteRow) := by
  induction keys with
  | nil => cases dense <;> rfl
  | cons key keys ih =>
      simp only [quoteTail, List.map_cons, List.cons_append]
      change (do
        let names ← (key.map Atom.symbol).mapM symbol
        let (more, selected, atoms) ← decodeTail (quoteTail keys dense rows)
        pure (names :: more, selected, atoms)) = some (key :: keys, dense, rows.map quoteRow)
      rw [decodeSymbols_quote, ih]
      rfl

theorem decodeRawTable_quote (table : Table) :
    decodeRawTable (quoteTable table) =
      some ⟨{table with rows := []}, table.rows.map quoteRow⟩ := by
  have columns : (table.columns.map quoteColumn).mapM decodeColumn = some table.columns :=
    by simpa only [List.mapM_map, List.map_id] using
      option_mapM_eq_map (decodeColumn ∘ quoteColumn) id table.columns
        (fun column _ => decodeColumn_quote column)
  simp [quoteTable, decodeRawTable, columns, decodeSymbols_comp, decodeTail_quote]

def checkSource (source : Atom) : Bool :=
  match decodeBundle source with
  | none => false
  | some bundle => check bundle

theorem checkSource_iff (source : Atom) : checkSource source = true ↔
    ∃ bundle, decodeBundle source = some bundle ∧ BundleValid bundle := by
  unfold checkSource
  cases decodeBundle source <;> simp [check_iff]

theorem decodeNatural_spec {s : String} {n : Nat} (h : decodeNatural s = some n) :
    decimalValue s.toList = some n ∧ toString n = s := by
  unfold decodeNatural at h
  cases parsed : decimalValue s.toList with
  | none => simp [parsed] at h
  | some value =>
      rw [parsed] at h
      change (if toString value = s then some value else none) = some n at h
      split at h
      · rename_i canonical
        cases h
        exact ⟨rfl, canonical⟩
      · simp at h

theorem decodeRowCells_length {schemas : Bundle} : ∀ {columns atoms row},
    decodeRowCells schemas columns atoms = some row → columns.length = row.length := by
  intro columns
  induction columns with
  | nil =>
      intro atoms row h
      cases atoms <;> simp [decodeRowCells] at h
      cases h
      rfl
  | cons column columns ih =>
      intro atoms row h
      cases atoms with
      | nil => simp [decodeRowCells] at h
      | cons a atoms =>
          simp only [decodeRowCells] at h
          cases cell : decodeCell schemas column.type a with
          | none => simp [cell] at h
          | some value =>
              cases rest : decodeRowCells schemas columns atoms with
              | none => simp [cell, rest] at h
              | some tail =>
                  have hr : row = value :: tail := by simpa [cell, rest, eq_comm] using h
                  subst row
                  simpa using ih rest

end Mettapedia.GSLT.LanguageDef.DeclaredTables
