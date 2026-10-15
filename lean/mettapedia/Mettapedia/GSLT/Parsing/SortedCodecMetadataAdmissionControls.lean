import Mettapedia.GSLT.Parsing.SortedCodecMetadataAdmission

/-!
# Finite metadata admission controls

The fixtures use token spelling nodes, explicit precedence-category aliases,
ordered list flattening, and auxiliary profile events. They instantiate the
generic metadata boundary, not the native C parser or a byte importer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SortedCodecMetadataAdmissionControls

open SortedCodecMetadataAdmission
open SortedCanonicalSExprCodec
open CanonicalProjectionSExprAdapter
open CanonicalGrammar (CanonicalTerm Production Sym)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def fixtureProfile : Notation where
  safeSymbol spelling := spelling == "x" || spelling == "y"

def acceptsToken (sort spelling : String) : Bool :=
  match sort with
  | "Identifier" => spelling == "x" || spelling == "y" || spelling == "$x"
  | "UnsignedLiteral" => spelling == "1u" || spelling == "2U"
  | _ => false

def varRow : ProductionRow :=
  ⟨10, some "fixture:Expressions", "Expr1", [.argument "NAME"], .constructor "Var"⟩

def intRow : ProductionRow :=
  ⟨11, some "fixture:Expressions", "Expr2", [.argument "UINT"], .constructor "IntConst"⟩

def aliasRow : ProductionRow :=
  ⟨12, some "fixture:Expressions", "Expr1", [.argument "Expr2"], .transparent⟩

def repeatedRow : ProductionRow :=
  ⟨13, some "fixture:Expressions", "Expr1",
    [.argument "Expr1", .fixed "COMMA" (some ","), .argument "Expr2",
      .fixed "COMMA" (some ","), .argument "Expr1"], .constructor "Repeated"⟩

def listEmptyRow : ProductionRow :=
  ⟨20, some "fixture:List", "[Expr]", [], .listEmpty⟩

def listSingletonRow : ProductionRow :=
  ⟨21, some "fixture:List", "[Expr]", [.argument "Expr1"], .listSingleton⟩

def listConsRow : ProductionRow :=
  ⟨22, some "fixture:List", "[Expr]",
    [.argument "[Expr]", .fixed "COMMA" (some ","), .argument "Expr2"], .listCons true⟩

def programRow : ProductionRow :=
  ⟨30, some "fixture:Program", "Program", [.argument "[Expr]"], .constructor "Program"⟩

def fixture : Metadata where
  sorts :=
    [⟨"Identifier", .token .identifier "NAME"⟩,
      ⟨"UnsignedLiteral", .token .literal "UINT"⟩,
      ⟨"Expr", .constructors⟩, ⟨"ExprList", .list "Expr" "[Expr]"⟩,
      ⟨"Program", .constructors⟩]
  categories :=
    [⟨"NAME", some "Identifier", .token⟩,
      ⟨"UINT", some "UnsignedLiteral", .token⟩,
      ⟨"Expr1", some "Expr", .rule⟩, ⟨"Expr2", some "Expr", .rule⟩,
      ⟨"[Expr]", some "ExprList", .rule⟩, ⟨"Program", some "Program", .rule⟩,
      ⟨"ScopePush", none, .erased⟩]
  productions :=
    [varRow, intRow, aliasRow, repeatedRow, listEmptyRow, listSingletonRow,
      listConsRow, programRow, ⟨40, some "fixture:Profile", "ScopePush", [], .erased⟩]

theorem fixture_accepted : check fixture fixtureProfile = true := by decide +kernel

def admitted : AdmittedMetadata fixtureProfile :=
  ⟨fixture, (check_iff fixture fixtureProfile).mp fixture_accepted⟩

theorem fixture_valid : Valid fixture fixtureProfile := admitted.valid

def compiledSchema : Schema := admitted.schema acceptsToken
def compiledLayout : Layout := admitted.layout

theorem ordered_signature_preserved :
    constructorRow? fixture repeatedRow =
      some ⟨repeatedRow, "Expr", ⟨"Repeated", ["Expr", "Expr", "Expr"]⟩⟩ := by
  decide +kernel

theorem source_occurrences_and_origins_preserved :
    (constructorRows fixture).map (fun row => (row.source.occurrence, row.source.origin)) =
      [(10, some "fixture:Expressions"), (11, some "fixture:Expressions"),
        (13, some "fixture:Expressions"), (30, some "fixture:Program")] := by
  decide +kernel

theorem precedence_categories_remain_distinct :
    category? fixture "Expr1" = some ⟨"Expr1", some "Expr", .rule⟩ ∧
      category? fixture "Expr2" = some ⟨"Expr2", some "Expr", .rule⟩ := by
  decide +kernel

theorem explicit_transparent_alias_accepted : productionCheck fixture fixtureProfile aliasRow = true := by
  decide +kernel

def sourceTerm : CanonicalTerm :=
  .node "Program" [.node "[Expr]" [.seq
    [.node "Var" [.node "NAME" [.text "x"]],
      .node "IntConst" [.node "UINT" [.text "1u"]],
      .node "Var" [.node "NAME" [.text "x"]]]]]

def codecTerm : CanonicalTerm :=
  .node "Program" [.seq
    [.node "Var" [.text "x"], .node "IntConst" [.text "1u"], .node "Var" [.text "x"]]]

def wire : Atom :=
  .expression [.symbol "c:Program", .expression [.symbol "c:List",
    .expression [.symbol "c:Var", .symbol "x"],
    .expression [.symbol "c:IntConst", .grounded (.string "1u")],
    .expression [.symbol "c:Var", .symbol "x"]]]

theorem token_and_list_lowering :
    toCodec? compiledSchema fixtureProfile compiledLayout "Program" sourceTerm = some codecTerm := rfl

theorem token_and_list_reconstruction :
    fromCodec? compiledSchema fixtureProfile compiledLayout "Program" codecTerm = some sourceTerm := by
  exact fromCodec_of_toCodec _ _ _ token_and_list_lowering

theorem actual_wire_preserves_ordered_repeat :
    encode? compiledSchema fixtureProfile "Program" codecTerm = some wire := by decide +kernel

theorem actual_wire_decodes : decode? compiledSchema fixtureProfile "Program" wire = some codecTerm := by
  exact decode_encoded compiledSchema fixtureProfile _ _ _ actual_wire_preserves_ordered_repeat

def typedTerm : SortedTerm compiledSchema fixtureProfile "Program" :=
  ⟨codecTerm, decode_sorted compiledSchema fixtureProfile "Program" wire codecTerm actual_wire_decodes⟩

theorem actual_typed_admission :
    SortedCanonicalSExprCodec.admit? compiledSchema fixtureProfile "Program" wire = some typedTerm :=
  (admit_some_iff compiledSchema fixtureProfile "Program" wire typedTerm).mpr actual_wire_decodes

theorem actual_total_quote : quote typedTerm = wire :=
  quote_of_admit compiledSchema fixtureProfile "Program" wire typedTerm actual_typed_admission

theorem projection_wire_decodes :
    decodeProjection? compiledSchema fixtureProfile compiledLayout "Program" wire = some sourceTerm := by
  exact decodeProjection_encoded _ _ _ (by decide +kernel)

theorem unsafe_identifier_is_string_wrapped :
    encode? compiledSchema fixtureProfile "Identifier" (.text "$x") =
      some (.expression [.symbol "c:Symbol", .grounded (.string "$x")]) := by decide +kernel

theorem unsafe_identifier_cannot_be_bare :
    decode? compiledSchema fixtureProfile "Identifier" (.symbol "$x") = none := by decide +kernel

theorem wrong_token_spelling_refused :
    encode? compiledSchema fixtureProfile "UnsignedLiteral" (.text "1uBROKEN") = none := by decide +kernel

theorem wrong_wrapper_refused :
    toCodec? compiledSchema fixtureProfile compiledLayout "Identifier"
      (.node "UINT" [.text "x"]) = none := by decide +kernel

theorem constructor_as_list_refused :
    decode? compiledSchema fixtureProfile "ExprList"
      (.expression [.symbol "c:Program", .expression [.symbol "c:List"]]) = none := by
  decide +kernel

theorem unknown_constructor_refused :
    decode? compiledSchema fixtureProfile "Expr" (.expression [.symbol "c:Unknown"]) = none := by
  decide +kernel

def duplicateSort : Metadata := { fixture with sorts := fixture.sorts ++ [⟨"Expr", .constructors⟩] }
def duplicateCategory : Metadata :=
  { fixture with categories := fixture.categories ++ [⟨"Expr1", some "Expr", .rule⟩] }
def duplicateOccurrence : Metadata :=
  { fixture with productions := fixture.productions ++ [{ aliasRow with occurrence := 10 }] }
def duplicateHead : Metadata :=
  { fixture with productions := fixture.productions ++
      [⟨50, some "fixture:Duplicate", "Expr2", [.argument "NAME"], .constructor "Var"⟩] }
def reservedHead : Metadata :=
  { fixture with productions := fixture.productions ++
      [⟨50, some "fixture:Reserved", "Expr1", [], .constructor "List"⟩] }
def missingArgument : Metadata :=
  { fixture with productions := fixture.productions ++
      [⟨50, none, "Expr1", [.argument "Missing"], .constructor "MissingArgument"⟩] }
def erasedArgument : Metadata :=
  { fixture with productions := fixture.productions ++
      [⟨50, none, "Expr1", [.argument "ScopePush"], .constructor "ErasedArgument"⟩] }
def missingElementSort : Metadata :=
  { fixture with sorts := fixture.sorts ++ [⟨"BadList", .list "Missing" "[Missing]"⟩] }
def wrongTokenHead : Metadata :=
  { fixture with categories := fixture.categories ++ [⟨"OtherNAME", some "Identifier", .token⟩] }
def undeclaredSpine : Metadata :=
  { fixture with
    categories := fixture.categories ++ [⟨"[Expr]2", some "ExprList", .rule⟩]
    productions := fixture.productions ++ [⟨50, none, "[Expr]",
      [.argument "[Expr]2", .fixed "COMMA" (some ","), .argument "Expr1"], .listCons true⟩] }
def suffixSortsDistinct : Metadata :=
  { fixture with
    sorts := fixture.sorts ++ [⟨"Expr2", .constructors⟩]
    categories := fixture.categories.map fun row =>
      if row.name = "Expr2" then { row with logicalSort := some "Expr2" } else row }

theorem invalid_metadata_refused :
    [duplicateSort, duplicateCategory, duplicateOccurrence, duplicateHead, reservedHead,
      missingArgument, erasedArgument, missingElementSort, wrongTokenHead,
      undeclaredSpine, suffixSortsDistinct].all (fun data => !check data fixtureProfile) = true := by
  decide +kernel

theorem suffix_similarity_does_not_merge :
    productionCheck suffixSortsDistinct fixtureProfile aliasRow = false := by decide +kernel

theorem visible_rhs_lowering :
    surfaceProduction? fixture (fun id => "occ:" ++ toString id) repeatedRow =
      some ⟨"occ:13", "Expr1", [.rule "Expr1", .fixed ",", .rule "Expr2",
        .fixed ",", .rule "Expr1"]⟩ := by decide +kernel

def auxiliaryProgramRow : ProductionRow :=
  { programRow with rhs :=
    [.erased "ScopePush", .fixed "virtual:ordinary-name" none, .argument "[Expr]"] }

theorem auxiliary_slots_are_explicitly_checked :
    productionCheck fixture fixtureProfile auxiliaryProgramRow = true := by decide +kernel

theorem auxiliary_slots_do_not_become_surface_grammar :
    surfaceProduction? fixture (fun id => "occ:" ++ toString id) auxiliaryProgramRow = none := by
  decide +kernel

/-- Structural list admission intentionally does not prove that a physical
source category derives an empty list. That obligation stays at its grammar
fibre even when the finite codec metadata has passed. -/
def nonemptyOnly : Metadata :=
  { fixture with productions := fixture.productions.filter (fun row => row.occurrence != 20) }

theorem nonempty_metadata_accepted : check nonemptyOnly fixtureProfile = true := by decide +kernel

theorem structural_admission_ignores_source_nonemptiness :
    decode? (schema nonemptyOnly acceptsToken) fixtureProfile "ExprList"
      (.expression [.symbol "c:List"]) = some (.seq []) := rfl

#print axioms check_iff
#print axioms constructorRow_iff
#print axioms constructorRows_keys
#print axioms constructorRows_unique_occurrences
#print axioms surfaceProduction_iff
#print axioms fixture_accepted
#print axioms invalid_metadata_refused
#print axioms actual_wire_decodes
#print axioms actual_total_quote
#print axioms token_and_list_reconstruction

end Mettapedia.GSLT.Parsing.SortedCodecMetadataAdmissionControls
