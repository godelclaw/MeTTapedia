import Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodec
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation

/-!
# Sorted canonical codec and indexed admission controls

The finite expression signature is extracted from the existing modern Lean
theory quotation. It is an integration control, not the full C grammar, a C
lexer, or evidence that the historical byte `.module` format has been parsed.
Its lexical policy deliberately admits only the named test identifier and
integer spellings. Literal payload controls use all strings to test the
representation boundary independently of source-language lexical admission.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodecControls

open SortedCanonicalSExprCodec
open CanonicalGrammar (CanonicalTerm)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra
open UpstreamTheoryQuotation
open Mettapedia.GSLT.LanguageDef.Extension

def expressions : UpstreamTheoryQuotation.QuotedTheory :=
  moduleTheory! Theory CodecExpressions() {
    Types { IdentToken; IntToken; LiteralToken; Expr; ExprList; }
    Terms {
      Var . identifier:IdentToken |- identifier : Expr;
      IntConst . spelling:IntToken |- spelling : Expr;
      StringConst . spelling:LiteralToken |- spelling : Expr;
      Add . left:Expr, right:Expr |- "(" left "+" right ")" : Expr;
      Call . function:Expr, arguments:ExprList |- function "(" arguments ")" : Expr;
    }
  }

def tokenShape : String → Option TokenRepresentation
  | "IdentToken" => some .identifier
  | "IntToken" | "LiteralToken" => some .literal
  | _ => none

def listShape : String → Option String
  | "ExprList" => some "Expr"
  | _ => none

def lexicalControl : String → String → Bool
  | "IdentToken", spelling => spelling == "p" || spelling == "q" || spelling == "$x"
  | "IntToken", spelling => spelling == "1u" || spelling == "2u"
  | "LiteralToken", _ => true
  | _, _ => false

def profile : Notation where
  safeSymbol := fun spelling => spelling != "$x"

def schema : Schema :=
  (schemaOfLanguage? expressions.toLanguageDef tokenShape listShape lexicalControl).get (by rfl)

def context : Context := ⟨schema, profile, "Expr"⟩

def one : CanonicalTerm := .node "IntConst" [.text "1u"]
def two : CanonicalTerm := .node "IntConst" [.text "2u"]
def pointer : CanonicalTerm := .node "Var" [.text "p"]
def sum : CanonicalTerm := .node "Add" [one, two]

def oneWire : Atom := .expression [.symbol "c:IntConst", .grounded (.string "1u")]
def twoWire : Atom := .expression [.symbol "c:IntConst", .grounded (.string "2u")]
def pointerWire : Atom := .expression [.symbol "c:Var", .symbol "p"]
def sumWire : Atom := .expression [.symbol "c:Add", oneWire, twoWire]

theorem quotation_is_admitted : (UpstreamTheoryQuotation.admit? expressions).isSome = true := by
  decide +kernel

/-- Exact integer spelling is retained, including its suffix. -/
theorem integer_spelling_round_trip :
    encode? schema profile "Expr" one = some oneWire ∧
      decode? schema profile "Expr" oneWire = some one := ⟨rfl, rfl⟩

theorem identifier_is_a_bare_symbol :
    encode? schema profile "Expr" pointer = some pointerWire ∧
      decode? schema profile "Expr" pointerWire = some pointer := ⟨rfl, rfl⟩

theorem nested_constructors_round_trip :
    encode? schema profile "Expr" sum = some sumWire ∧
      decode? schema profile "Expr" sumWire = some sum := ⟨rfl, rfl⟩

theorem duplicate_children_and_order_are_retained :
    decode? schema profile "ExprList"
      (.expression [.symbol "c:List", twoWire, oneWire, twoWire]) =
        some (.seq [two, one, two]) := rfl

theorem empty_list_retained :
    decode? schema profile "ExprList" (.expression [.symbol "c:List"]) = some (.seq []) := rfl

theorem unsafe_identifier_is_wrapped :
    encode? schema profile "Expr" (.node "Var" [.text "$x"]) =
      some (.expression [.symbol "c:Var",
        .expression [.symbol "c:Symbol", .grounded (.string "$x")]]) ∧
    decode? schema profile "Expr"
      (.expression [.symbol "c:Var",
        .expression [.symbol "c:Symbol", .grounded (.string "$x")]]) =
      some (.node "Var" [.text "$x"]) := ⟨rfl, rfl⟩

theorem template_variable_is_not_identifier_data :
    decode? schema profile "Expr"
      (.expression [.symbol "c:Var", .var "x"]) = none := rfl

theorem unsafe_bare_symbol_rejected :
    decode? schema profile "IdentToken" (.symbol "$x") = none := rfl

theorem redundant_safe_symbol_escape_rejected :
    decode? schema profile "IdentToken"
      (.expression [.symbol "c:Symbol", .grounded (.string "p")]) = none := rfl

theorem wrong_child_sort_rejected :
    decode? schema profile "Expr"
      (.expression [.symbol "c:IntConst", .symbol "p"]) = none := rfl

theorem interpreted_number_rejected :
    decode? schema profile "Expr"
      (.expression [.symbol "c:IntConst", .grounded (.int 1)]) = none := rfl

theorem invalid_lexeme_rejected :
    decode? schema profile "Expr"
      (.expression [.symbol "c:IntConst", .grounded (.string "many")]) = none := rfl

theorem unknown_constructor_rejected :
    decode? schema profile "Expr"
      (.expression [.symbol "c:Unknown", oneWire]) = none := rfl

theorem wrong_namespace_rejected :
    decode? schema profile "Expr"
      (.expression [.symbol "other:IntConst", .grounded (.string "1u")]) = none := rfl

theorem missing_argument_rejected :
    decode? schema profile "Expr"
      (.expression [.symbol "c:Add", oneWire]) = none := rfl

theorem extra_argument_rejected :
    decode? schema profile "Expr"
      (.expression [.symbol "c:IntConst", .grounded (.string "1u"), oneWire]) = none := rfl

theorem list_at_expression_sort_rejected :
    decode? schema profile "Expr" (.expression [.symbol "c:List", oneWire]) = none := rfl

theorem expression_at_list_sort_rejected :
    decode? schema profile "ExprList" oneWire = none := rfl

theorem unknown_sort_rejected : decode? schema profile "UnknownSort" oneWire = none := rfl

def duplicateSchema : Schema where
  shape? := fun sort => if sort = "Expr" then
    some (.constructors [⟨"Duplicated", []⟩, ⟨"Duplicated", ["Expr"]⟩]) else none
  acceptsToken := fun _ _ => false

theorem duplicate_label_has_no_list_order_fallback :
    decode? duplicateSchema profile "Expr"
      (.expression [.symbol "c:Duplicated"]) = none := rfl

def reservedSchema : Schema where
  shape? := fun sort => if sort = "Expr" then
    some (.constructors [⟨"List", []⟩, ⟨"Symbol", []⟩]) else none
  acceptsToken := fun _ _ => false

theorem reserved_heads_are_not_grammar_constructors :
    decode? reservedSchema profile "Expr" (.expression [.symbol "c:List"]) = none ∧
      decode? reservedSchema profile "Expr" (.expression [.symbol "c:Symbol"]) = none :=
  ⟨rfl, rfl⟩

def withoutAddition : LanguageDef := { expressions.toLanguageDef with
  «terms» := expressions.terms.filter (fun row => row.label != "Add") }

def smallerSchema : Schema :=
  (schemaOfLanguage? withoutAddition tokenShape listShape lexicalControl).get (by rfl)

/-- The same data is admitted in the extended fibre and rejected in the old one. -/
theorem admission_depends_on_actual_schema :
    decode? schema profile "Expr" sumWire = some sum ∧
      decode? smallerSchema profile "Expr" sumWire = none := ⟨rfl, rfl⟩

def similarlyNamedSorts : UpstreamTheoryQuotation.QuotedTheory :=
  moduleTheory! Theory DistinctNumberedSorts() {
    Types { Expr1; Expr2; Wrapper; }
    Terms {
      Leaf1 . |- "one" : Expr1;
      Leaf2 . |- "two" : Expr2;
      First . child:Expr1 |- "first" child : Wrapper;
      Second . child:Expr2 |- "second" child : Wrapper;
      Swapped . first:Expr1, second:Expr2 |- second ":" first : Wrapper;
      Repeated . child:Expr1 |- child ":" child : Wrapper;
    }
  }

def numberedSchema : Schema :=
  (schemaOfLanguage? similarlyNamedSorts.toLanguageDef (fun _ => none)
    (fun _ => none) (fun _ _ => false)).get (by rfl)

/-- Numeric suffixes carry no implicit sort-equivalence policy. -/
theorem numeric_suffix_sorts_are_distinct :
    decode? numberedSchema profile "Wrapper"
      (.expression [.symbol "c:First", .expression [.symbol "c:Leaf1"]]) =
        some (.node "First" [.node "Leaf1" []]) ∧
    decode? numberedSchema profile "Wrapper"
      (.expression [.symbol "c:First", .expression [.symbol "c:Leaf2"]]) = none :=
  ⟨rfl, rfl⟩

theorem child_sorts_follow_syntax_occurrences :
    decode? numberedSchema profile "Wrapper"
      (.expression [.symbol "c:Swapped", .expression [.symbol "c:Leaf2"],
        .expression [.symbol "c:Leaf1"]]) =
      some (.node "Swapped" [.node "Leaf2" [], .node "Leaf1" []]) ∧
    decode? numberedSchema profile "Wrapper"
      (.expression [.symbol "c:Swapped", .expression [.symbol "c:Leaf1"],
        .expression [.symbol "c:Leaf2"]]) = none := ⟨rfl, rfl⟩

theorem repeated_nonterminal_occurrences_are_not_dropped :
    decode? numberedSchema profile "Wrapper"
      (.expression [.symbol "c:Repeated", .expression [.symbol "c:Leaf1"],
        .expression [.symbol "c:Leaf1"]]) =
      some (.node "Repeated" [.node "Leaf1" [], .node "Leaf1" []]) ∧
    decode? numberedSchema profile "Wrapper"
      (.expression [.symbol "c:Repeated", .expression [.symbol "c:Leaf1"]]) = none :=
  ⟨rfl, rfl⟩

def admittedSum : SortedTerm schema profile "Expr" :=
  ⟨sum, decode_sorted schema profile "Expr" sumWire sum rfl⟩

theorem document_quotes_actual_tree_twice :
    quoteDocument context [admittedSum, admittedSum] =
      .bundle [.declaration sumWire, .declaration sumWire] := by
  have exactWire : quote admittedSum = sumWire :=
    Option.some.inj ((encode_quote admittedSum).symm.trans (by rfl))
  change DeclarationDocument.bundle
    [.declaration (quote admittedSum), .declaration (quote admittedSum)] = _
  rw [exactWire]

theorem quoted_document_admitted_with_duplicate_occurrences :
    elaborateDocument? context (quoteDocument context [admittedSum, admittedSum]) =
      some [admittedSum, admittedSum] := elaborate_quoteDocument context _

theorem malformed_declaration_rejects_whole_document :
    elaborateDocument? context (.bundle [
      .declaration oneWire,
      .declaration (.expression [.symbol "c:Add", oneWire])]) = none := by
  apply append_rejected_right
  simp [elaborateDocument?, context, DeclarationDocument.values,
    SortedCanonicalSExprCodec.admit?, missing_argument_rejected]

/-- All host string payloads survive; source C lexical restrictions are separate. -/
theorem every_literal_payload_survives (spelling : String) :
    decode? schema profile "LiteralToken"
      (encodeToken profile .literal spelling) = some (.text spelling) := by
  rfl

theorem every_byte_payload_survives (byte : UInt8) :
    decode? schema profile "LiteralToken"
      (encodeToken profile .literal (String.singleton (Char.ofNat byte.toNat))) =
      some (.text (String.singleton (Char.ofNat byte.toNat))) :=
  every_literal_payload_survives _

def bindingRow : GrammarRule := {
  label := "Binding"
  category := "Expr"
  params := [.abstractionNamed (some "x") "body" (.base "Expr")]
  syntaxPattern := [.nonTerminal "body"] }

theorem extraction_rejects_binding_without_erasure :
    (schemaOfLanguage? { expressions.toLanguageDef with «terms» := [bindingRow] }
      tokenShape listShape lexicalControl).isSome = false := rfl

#print axioms quotation_is_admitted
#print axioms admission_depends_on_actual_schema
#print axioms every_literal_payload_survives
#print axioms every_byte_payload_survives

end Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodecControls
