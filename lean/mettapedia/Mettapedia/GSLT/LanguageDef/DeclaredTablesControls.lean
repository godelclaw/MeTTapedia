import Mettapedia.GSLT.LanguageDef.DeclaredTables
import Mettapedia.GSLT.LanguageDef.DeclaredCounterTables

/-! Positive and separating controls for typed-table admission and ordered views. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeclaredTables.Controls

open MacroExportPlan (Atom)

def profiles : Table :=
  ⟨"Profiles", [⟨"id", .scalar .nat⟩, ⟨"code", .scalar .identifier⟩, ⟨"label", .scalar .text⟩,
    ⟨"enabled", .scalar .boolean⟩, ⟨"kind", .scalar (.enumeration ["store", "scratch"])⟩],
    ["id"], [["code"]], none,
    [[.nat 41, .identifier "fast", .text "Fast profile", .boolean true, .identifier "store"],
     [.nat 7, .identifier "false", .text "Other profile", .boolean false, .identifier "scratch"]]⟩

def operations : Table :=
  ⟨"Operations", [⟨"profile", .reference "Profiles" "id"⟩, ⟨"opcode", .scalar .nat⟩,
      ⟨"name", .scalar .identifier⟩],
    ["profile", "opcode"], [["name"]], none,
    [[.nat 41, .nat 0, .identifier "alpha"], [.nat 7, .nat 0, .identifier "beta"],
      [.nat 41, .nat 2, .identifier "gamma"]]⟩

/-- A reference may precede its target table in the bundle. -/
def registry : Bundle := [operations, profiles]

theorem registry_checked : check registry = true := by decide
theorem registry_valid : BundleValid registry := (check_iff _).mp registry_checked
theorem registry_source_decodes : decodeBundle (quoteBundle registry) = some registry := by decide
theorem registry_source_admitted : checkSource (quoteBundle registry) = true := by decide

theorem supplied_ids_preserved :
    project profiles ["id"] profiles.rows[0] = some [.nat 41] ∧
      project profiles ["id"] profiles.rows[1] = some [.nat 7] := by decide

theorem composite_repeated_component_allowed :
    check [operations, profiles] = true ∧
      (operations.rows.map (project operations ["opcode"])).Nodup = False := by decide

theorem wrong_dense_refused : check [{profiles with dense := some "id"}] = false := by decide

theorem missing_reference_refused :
    check [{operations with rows := [[.nat 99, .nat 0, .identifier "alpha"]]}, profiles] = false := by decide

theorem missing_table_refused : check [operations] = false := by decide

theorem non_singleton_target_key_refused :
    check [operations, {profiles with primaryKey := ["id", "code"]}] = false := by decide

theorem row_arity_short_refused :
    check [{profiles with rows := [[.nat 41, .identifier "fast", .text "Fast profile", .boolean true]]}] =
      false := by decide

theorem row_arity_long_refused :
    check [{profiles with rows := profiles.rows.map (fun row => row ++ [.nat 9])}] = false := by decide

theorem text_is_not_identifier :
    check [{profiles with rows :=
      [[.nat 41, .text "fast", .text "Fast profile", .boolean true, .identifier "store"]]}] = false := by decide

theorem natural_is_not_boolean :
    check [{profiles with rows :=
      [[.nat 41, .identifier "fast", .text "Fast profile", .nat 1, .identifier "store"]]}] = false := by decide

theorem enum_nonmember_refused :
    check [{profiles with rows :=
      [[.nat 41, .identifier "fast", .text "Fast profile", .boolean true, .identifier "unknown"]]}] =
      false := by decide

theorem invalid_identifier_refused :
    check [{profiles with rows :=
      [[.nat 41, .identifier "bad-name", .text "Fast profile", .boolean true, .identifier "store"]]}] =
      false := by decide

theorem duplicate_primary_refused :
    check [{operations with rows := operations.rows ++ [[.nat 41, .nat 0, .identifier "delta"]]}, profiles] =
      false := by decide

theorem duplicate_additional_key_refused :
    check [{operations with rows := operations.rows ++ [[.nat 41, .nat 3, .identifier "alpha"]]}, profiles] =
      false := by decide

theorem duplicate_columns_refused :
    check [{profiles with columns := profiles.columns ++ [⟨"id", .scalar .nat⟩], rows := []}] = false := by decide

theorem duplicate_tables_refused : check [profiles, profiles] = false := by decide

theorem nonexistent_key_column_refused :
    check [{profiles with primaryKey := ["absent"]}] = false := by decide

theorem repeated_key_column_refused :
    check [{profiles with primaryKey := ["id", "id"]}] = false := by decide

def wordTable (n : Nat) : Table :=
  ⟨"Words", [⟨"id", .scalar .nat⟩], ["id"], [], none, [[.nat n]]⟩

theorem uint64_maximum_accepted : check [wordTable (uint64Bound - 1)] = true := by decide
theorem uint64_overflow_refused : check [wordTable uint64Bound] = false := by decide

def cycleA : Table :=
  ⟨"A", [⟨"id", .scalar .nat⟩, ⟨"next", .reference "B" "id"⟩], ["id"], [], none,
    [[.nat 1, .nat 2]]⟩
def cycleB : Table :=
  ⟨"B", [⟨"id", .scalar .nat⟩, ⟨"next", .reference "A" "id"⟩], ["id"], [], none,
    [[.nat 2, .nat 1]]⟩

theorem scalar_key_reference_cycle_allowed : check [cycleA, cycleB] = true := by decide

theorem reference_to_reference_key_refused :
    check [cycleA, {cycleB with columns :=
      [⟨"id", .reference "A" "id"⟩, ⟨"next", .reference "A" "id"⟩], rows := [[.nat 1, .nat 1]]}] =
      false := by decide

def keywords : Table :=
  ⟨"Keywords", [⟨"id", .scalar .identifier⟩, ⟨"kind", .scalar (.enumeration ["if", "false"])⟩,
      ⟨"yes", .scalar .boolean⟩], ["id"], [], none,
    [[.identifier "true", .identifier "if", .boolean true],
      [.identifier "false", .identifier "false", .boolean false]]⟩

theorem keyword_identifiers_allowed : check [keywords] = true := by decide
theorem type_directed_true_false : decodeBundle (quoteBundle [keywords]) = some [keywords] := by decide

theorem empty_enum_refused :
    check [{keywords with columns :=
      [⟨"id", .scalar .identifier⟩, ⟨"kind", .scalar (.enumeration [])⟩], rows := []}] = false := by decide

theorem duplicate_enum_member_refused :
    check [{keywords with columns :=
      [⟨"id", .scalar .identifier⟩, ⟨"kind", .scalar (.enumeration ["if", "if"])⟩], rows := []}] = false := by decide

theorem scalar_token_presentation_controls :
    decodeScalarCell .nat (.symbol "007") = none ∧
      decodeScalarCell .nat (.symbol "-1") = none ∧
      decodeScalarCell .boolean (.text "true") = none ∧
      decodeScalarCell .identifier (.symbol "true") = some (.identifier "true") ∧
      decodeScalarCell .boolean (.symbol "true") = some (.boolean true) := by decide

theorem field_order_refused :
    decodeTail [.list [.symbol "Rows"], .list [.symbol "Dense", .symbol "id"]] = none := by decide

theorem duplicate_dense_refused :
    decodeTail [.list [.symbol "Dense", .symbol "id"], .list [.symbol "Dense", .symbol "id"],
      .list [.symbol "Rows"]] = none := by decide

theorem unknown_column_type_refused :
    decodeColumnType (.symbol "Integer") = none := by decide

theorem missing_row_field_refused :
    decodeRow registry profiles.columns
      (.list [.symbol "Row", .symbol "41", .symbol "fast"]) = none := by decide

theorem lowering_length_hypothesis_necessary :
    lowerRow [⟨"id", .scalar .nat⟩] [.nat 7, .nat 8] = [("id", .nat 7)] ∧
      checkRow [] [⟨"id", .scalar .nat⟩] [.nat 7, .nat 8] = false := by decide

def counters : Table :=
  ⟨"Counters", [⟨"id", .scalar .nat⟩, ⟨"name", .scalar .text⟩, ⟨"spelling", .scalar .text⟩],
    ["id"], [["name"], ["spelling"]], some "id",
    [[.nat 0, .text "one", .text "first"], [.nat 1, .text "two", .text "second"],
      [.nat 2, .text "three", .text "third"]]⟩

theorem dense_counters_accepted : check [counters] = true := by decide

def nameCode : Option Row → Nat
  | some [.text name] => ExportCounterTables.encode name
  | _ => 0

def codeChunks : List (List Row × List Nat) :=
  [(counters.rows.take 1, [ExportCounterTables.encode "one"]),
   (counters.rows.drop 1, [ExportCounterTables.encode "two", ExportCounterTables.encode "three"])]

theorem chunked_key_admission : KeyUnique counters ["name"] := by
  apply keyUnique_of_code_chunks nameCode codeChunks
  · decide
  · decide
  · exact (ExportCounterTables.allDistinct_sound (t := .leaf) trivial (by decide)).1

theorem selected_order_and_ids :
    select operations [("profile", .nat 41)] =
      [[.nat 41, .nat 0, .identifier "alpha"], [.nat 41, .nat 2, .identifier "gamma"]] := by decide

theorem ordered_repeated_projection :
    view operations [("profile", .nat 41)] ["name", "opcode", "name"] =
      some [[.identifier "alpha", .nat 0, .identifier "alpha"],
        [.identifier "gamma", .nat 2, .identifier "gamma"]] := by decide

theorem conjunctive_filter :
    view operations [("profile", .nat 41), ("opcode", .nat 2)] ["name"] =
      some [[.identifier "gamma"]] := by decide

theorem unknown_projection_refused : view operations [] ["absent"] = none := by decide

theorem selected_view_not_implicitly_dense :
    check [{counters with rows := select counters [("id", .nat 1)]}] = false := by decide

theorem empty_selection_does_not_validate_manifest :
    view operations [("profile", .nat 99)] ["absent"] = some [] := by decide

theorem empty_selection_unknown_projection_refused :
    checkViewNames registry operations [("profile", .nat 99)] ["absent"] = false := by decide

theorem empty_selection_unknown_predicate_refused :
    checkViewNames registry operations [("absent", .nat 99)] ["name"] = false := by decide

theorem empty_selection_wrong_predicate_type_refused :
    checkViewNames registry operations [("profile", .text "99")] ["name"] = false := by decide

theorem typed_absent_reference_filter_allowed :
    checkViewPlan registry operations [("profile", .nat 99)] ["name"] [] [] = true := by decide

theorem ordered_view_plan_accepted :
    checkViewPlan registry operations [("profile", .nat 41)] ["name", "opcode"]
      [[.nat 41, .nat 0, .identifier "alpha"], [.nat 41, .nat 2, .identifier "gamma"]]
      [[.identifier "alpha", .nat 0], [.identifier "gamma", .nat 2]] = true := by decide

theorem wrong_view_order_refused :
    checkView operations [("profile", .nat 41)] ["name"]
      [[.nat 41, .nat 2, .identifier "gamma"], [.nat 41, .nat 0, .identifier "alpha"]]
      [[.identifier "gamma"], [.identifier "alpha"]] = false := by decide

def legacyCounter : ExportCounterTables.Table :=
  ⟨"LegacyCounter", "C_", "COUNT", "legacy_counter_names",
    [⟨0, "1", "first"⟩, ⟨1, "two", "second"⟩]⟩

theorem numeric_suffix_legacy_dense : ExportCounterTables.Dense legacyCounter :=
  ExportCounterTables.checkDense_sound (by decide)

theorem numeric_suffix_requires_text_column : identifier "1" = false := by decide

theorem legacy_counter_core_admitted : check [DeclaredCounterTables.table legacyCounter] = true :=
  DeclaredCounterTables.check_of_dense numeric_suffix_legacy_dense (by decide)

theorem legacy_counter_source_roundtrip :
    decodeBundle (quoteBundle [DeclaredCounterTables.table legacyCounter]) =
      some [DeclaredCounterTables.table legacyCounter] := by decide

#print axioms check_iff
#print axioms reference_resolves
#print axioms reference_row_unique
#print axioms lowerRows_reconstruct
#print axioms project_all_columns
#print axioms keyUnique_of_code_chunks
#print axioms checkView_sound
#print axioms checkViewNames_sound
#print axioms checkViewPlan_sound
#print axioms checkSource_iff
#print axioms registry_checked
#print axioms registry_source_decodes
#print axioms chunked_key_admission
#print axioms empty_selection_does_not_validate_manifest
#print axioms DeclaredCounterTables.tableValid_of_dense
#print axioms legacy_counter_core_admitted
#print axioms legacy_counter_source_roundtrip

end Mettapedia.GSLT.LanguageDef.DeclaredTables.Controls
