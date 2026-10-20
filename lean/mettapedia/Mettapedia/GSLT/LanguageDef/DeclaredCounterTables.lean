import Mettapedia.GSLT.LanguageDef.DeclaredTables
import Mettapedia.GSLT.LanguageDef.ExportCounterTables

/-!
# Legacy dense counter tables through the shared typed-table schema

The counter's spelling and suffix are Text columns: the legacy dense law
requires a C identifier after prefixing, not necessarily before prefixing.
Numeric IDs are preserved. The additional length bound states the genuine
uint64 restriction of the shared Nat column; the old Dense law by itself
uses unbounded mathematical naturals.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeclaredCounterTables

open DeclaredTables

abbrev CounterRow := ExportCounterTables.Row
abbrev CounterTable := ExportCounterTables.Table

def row (source : CounterRow) : Row :=
  [.nat source.id, .text source.name, .text source.spelling]

def table (source : CounterTable) : Table :=
  ⟨"Counters", [⟨"id", .scalar .nat⟩, ⟨"name", .scalar .text⟩, ⟨"spelling", .scalar .text⟩],
    ["id"], [["name"], ["spelling"]], some "id", source.rows.map row⟩

theorem project_id (source : CounterTable) (r : CounterRow) :
    project (table source) ["id"] (row r) = some [.nat r.id] := by rfl

theorem project_name (source : CounterTable) (r : CounterRow) :
    project (table source) ["name"] (row r) = some [.text r.name] := by rfl

theorem project_spelling (source : CounterTable) (r : CounterRow) :
    project (table source) ["spelling"] (row r) = some [.text r.spelling] := by rfl

theorem ids_eq_range {source : CounterTable} (dense : ExportCounterTables.Dense source) :
    source.rows.map ExportCounterTables.Row.id = List.range source.rows.length := by
  apply List.ext_getElem
  · simp
  · intro i left right
    simpa using dense.ids i (by simpa using left)

theorem id_bound {source : CounterTable} (dense : ExportCounterTables.Dense source)
    (bound : source.rows.length ≤ uint64Bound) {r : CounterRow} (member : r ∈ source.rows) :
    r.id < uint64Bound := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp member
  rw [dense.ids i hi]
  exact Nat.lt_of_lt_of_le hi bound

theorem primary_unique {source : CounterTable} (dense : ExportCounterTables.Dense source) :
    KeyUnique (table source) ["id"] := by
  have ids : (source.rows.map ExportCounterTables.Row.id).Nodup := by
    rw [ids_eq_range dense]
    exact List.nodup_range
  have injective : Function.Injective (fun n : Nat => (some [.nat n] : Option Row)) := by
    intro left right same
    simpa using same
  have mapped := ids.map injective
  change ((source.rows.map row).map (project (table source) ["id"])).Nodup
  simpa only [List.map_map, Function.comp_def, project_id] using mapped

theorem name_unique {source : CounterTable} (dense : ExportCounterTables.Dense source) :
    KeyUnique (table source) ["name"] := by
  have names := (List.nodup_cons.mp dense.names).2
  have injective : Function.Injective (fun s : String => (some [.text s] : Option Row)) := by
    intro left right same
    simpa using same
  have mapped := names.map injective
  change ((source.rows.map row).map (project (table source) ["name"])).Nodup
  simpa only [List.map_map, Function.comp_def, project_name] using mapped

theorem spelling_unique {source : CounterTable} (dense : ExportCounterTables.Dense source) :
    KeyUnique (table source) ["spelling"] := by
  have injective : Function.Injective (fun s : String => (some [.text s] : Option Row)) := by
    intro left right same
    simpa using same
  have mapped := dense.spellings.map injective
  change ((source.rows.map row).map (project (table source) ["spelling"])).Nodup
  simpa only [List.map_map, Function.comp_def, project_spelling] using mapped

theorem row_typed (bundle : Bundle) (source : CounterTable) {r : CounterRow} (bound : r.id < uint64Bound) :
    RowTyped bundle (table source).columns (row r) := by
  simp [RowTyped, table, row, CellTyped, resolveType, ScalarCell, bound]

theorem dense_valid {source : CounterTable} (dense : ExportCounterTables.Dense source) :
    DenseValid (table source) := by
  refine ⟨rfl, ⟨⟨"id", .scalar .nat⟩, rfl, rfl⟩, ?_⟩
  intro i hi
  change i < (source.rows.map row).length at hi
  have sourceIndex : i < source.rows.length := by simpa [table] using hi
  have id := dense.ids i sourceIndex
  change cellAt (table source) ((source.rows.map row)[i]) "id" = some (.nat (0 + i))
  rw [List.getElem_map]
  change some (Cell.nat source.rows[i].id) = some (Cell.nat (0 + i))
  rw [id, Nat.zero_add]

theorem tableValid_of_dense (bundle : Bundle) {source : CounterTable}
    (dense : ExportCounterTables.Dense source) (bound : source.rows.length ≤ uint64Bound) :
    TableValid bundle (table source) := by
  refine ⟨by dsimp only [table]; decide, by dsimp only [table]; decide,
    by dsimp only [table]; decide, by dsimp only [table]; decide, ?_,
    by dsimp only [table, KeyValid]; decide, by dsimp only [table, KeyValid]; decide,
    primary_unique dense, ?_, dense_valid dense, ?_⟩
  · intro column member
    simp only [table, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [TypeValid, resolveType, ScalarValid]
  · intro key member
    simp only [table, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact name_unique dense
    · exact spelling_unique dense
  · intro cells member
    change cells ∈ source.rows.map row at member
    obtain ⟨r, hr, eq⟩ := List.mem_map.mp member
    subst cells
    exact row_typed bundle source (id_bound dense bound hr)

/-- Existing chunked Dense admission supplies shared-table admission without
rechecking quadratic string distinctness over the whole counter table. -/
theorem check_of_dense {source : CounterTable} (dense : ExportCounterTables.Dense source)
    (bound : source.rows.length ≤ uint64Bound) : check [table source] = true := by
  apply (check_iff _).mpr
  refine ⟨by change (["Counters"] : List String).Nodup; decide, ?_⟩
  intro target member
  simp only [List.mem_singleton] at member
  subst target
  exact tableValid_of_dense _ dense bound

end Mettapedia.GSLT.LanguageDef.DeclaredCounterTables
