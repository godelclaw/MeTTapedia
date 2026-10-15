import Mettapedia.GSLT.Parsing.CanonicalProjectionSExprAdapter
import Mettapedia.GSLT.Parsing.NonemptySeparatorRefactoringControls
import Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodecControls

/-!
# Canonical projection adapter controls

Real separated-list CSTs exercise token wrappers, keyed ordered lists and
source derivability. Nested constructor controls reuse the actual schema
extracted from the modern theory-quotation fixture. That fixture is not a byte
reader for historical metta-venus syntax. No native LR, compiler or byte-escape
claim is made here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.CanonicalProjectionSExprAdapter.Controls

open CanonicalGrammar
open SortedCanonicalSExprCodec
open NonemptySeparatorRefactoring.Controls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def itemSchema : Schema where
  shape?
    | "Items" => some (.list "Item")
    | "Item" => some (.token .identifier)
    | _ => none
  acceptsToken := fun sort spelling => sort == "Item" && (spelling == "x" || spelling == "y")

def itemProfile : Notation where
  safeSymbol := fun spelling => spelling == "x" || spelling == "y"

def itemLayout : Layout := ⟨id, fun _ => "items"⟩

def itemValues : CanonicalTerm := .seq [.text "x", .text "x", .text "y"]

def itemWire : Atom := .expression [.symbol "c:List", .symbol "x", .symbol "x", .symbol "y"]

theorem actual_token_wrapper_is_adapted :
    toCodec? itemSchema itemProfile itemLayout "Item" x = some (.text "x") ∧
      fromCodec? itemSchema itemProfile itemLayout "Item" (.text "x") = some x := ⟨rfl, rfl⟩

theorem actual_list_projection_is_adapted :
    toCodec? itemSchema itemProfile itemLayout "Items" repeatedCanonical = some itemValues ∧
      fromCodec? itemSchema itemProfile itemLayout "Items" itemValues = some repeatedCanonical := ⟨rfl, rfl⟩

theorem actual_projection_has_expected_wire :
    encodeProjection? itemSchema itemProfile itemLayout "Items" repeatedCanonical = some itemWire := rfl

theorem expected_wire_has_actual_projection :
    decodeProjection? itemSchema itemProfile itemLayout "Items" itemWire = some repeatedCanonical := rfl

theorem right_CST_encodes :
    (canon (grammar true [","]) (classification true) rightTree >>=
      encodeProjection? itemSchema itemProfile itemLayout "Items") = some itemWire := by
  rw [right_repeated_projection]
  exact actual_projection_has_expected_wire

theorem left_CST_encodes :
    (canon (grammar false [","]) (classification false) leftTree >>=
      encodeProjection? itemSchema itemProfile itemLayout "Items") = some itemWire := by
  rw [left_repeated_projection]
  exact actual_projection_has_expected_wire

theorem real_grammar_refactoring_preserves_wire (tokens : List Tok) (wire : Atom) :
    (∃ tree source, Derives (grammar true [","]) "H" tokens tree ∧
      canon (grammar true [","]) (classification true) tree = some source ∧
      encodeProjection? itemSchema itemProfile itemLayout "Items" source = some wire) ↔
    (∃ tree source, Derives (grammar false [","]) "H" tokens tree ∧
      canon (grammar false [","]) (classification false) tree = some source ∧
      encodeProjection? itemSchema itemProfile itemLayout "Items" source = some wire) :=
  encoded_derivation_refactoring (comma_wellFormed true) (comma_wellFormed false)
    (.token "Item") [","] rfl rfl (elements_agree true false [","] [","]) "Items" tokens wire

def repeatedProjection : ProjectionTerm itemSchema itemProfile itemLayout "Items" :=
  ⟨repeatedCanonical, itemValues,
    toCodec_adapts itemSchema itemProfile itemLayout "Items" repeatedCanonical itemValues rfl⟩

theorem projection_quote_has_expected_wire : quoteProjection repeatedProjection = itemWire :=
  Option.some.inj ((encodeProjection_quoteProjection repeatedProjection).symm.trans
    actual_projection_has_expected_wire)

theorem actual_wire_is_admitted :
    admitProjection? itemSchema itemProfile itemLayout "Items" itemWire = some repeatedProjection := by
  rw [← projection_quote_has_expected_wire]
  exact admitProjection_quoteProjection repeatedProjection

def repeatedGrammarProjection :
    GrammarProjectionTerm (grammar true [","]) (classification true) "H"
      itemSchema itemProfile itemLayout "Items" :=
  ⟨repeatedProjection, repeatedTokens, rightTree, right_repeated_derivation, right_repeated_projection⟩

theorem actual_grammar_projection_round_trip :
    fromGrammarSorted itemLayout (toGrammarSorted repeatedGrammarProjection) = repeatedGrammarProjection :=
  fromGrammarSorted_toGrammarSorted repeatedGrammarProjection

theorem actual_grammar_codec_fibre_retains_repeats :
    (toGrammarSorted repeatedGrammarProjection).val.val = itemValues := by
  exact Option.some.inj ((toCodec_toSorted repeatedProjection).symm.trans
    actual_list_projection_is_adapted.1)

theorem order_is_not_reversed :
    decodeProjection? itemSchema itemProfile itemLayout "Items" itemWire ≠
      some (.node "items" [.seq [y, x, x]]) := by
  rw [expected_wire_has_actual_projection]
  simp [repeatedCanonical, x, y]

theorem repetition_is_not_collapsed :
    decodeProjection? itemSchema itemProfile itemLayout "Items" itemWire ≠
      some (.node "items" [.seq [x, y]]) := by
  rw [expected_wire_has_actual_projection]
  simp [repeatedCanonical, x, y]

theorem wrong_list_key_rejected :
    toCodec? itemSchema itemProfile itemLayout "Items" (.node "wrong" [.seq [x]]) = none := rfl

theorem missing_list_key_rejected :
    toCodec? itemSchema itemProfile itemLayout "Items" (.seq [x]) = none := rfl

theorem source_wrapper_is_not_a_codec_list :
    fromCodec? itemSchema itemProfile itemLayout "Items" repeatedCanonical = none := rfl

theorem wrong_token_head_rejected :
    toCodec? itemSchema itemProfile itemLayout "Item" (.node "Other" [.text "x"]) = none := rfl

theorem missing_token_wrapper_rejected :
    toCodec? itemSchema itemProfile itemLayout "Item" (.text "x") = none := rfl

theorem wrong_token_wrapper_arity_rejected :
    toCodec? itemSchema itemProfile itemLayout "Item" (.node "Item" [.text "x", .text "y"]) = none := rfl

theorem wrong_list_wrapper_arity_rejected :
    toCodec? itemSchema itemProfile itemLayout "Items" (.node "items" [.seq [x], .seq [y]]) = none := rfl

theorem invalid_lexeme_rejected_both_directions :
    toCodec? itemSchema itemProfile itemLayout "Item" (.node "Item" [.text "z"]) = none ∧
      fromCodec? itemSchema itemProfile itemLayout "Item" (.text "z") = none := ⟨rfl, rfl⟩

theorem wrong_expected_sort_rejected :
    toCodec? itemSchema itemProfile itemLayout "Item" repeatedCanonical = none ∧
      fromCodec? itemSchema itemProfile itemLayout "Items" (.text "x") = none := ⟨rfl, rfl⟩

/-! Generic structural list admission does not entail source nonemptiness. -/

theorem generic_schema_admits_empty_projection :
    decodeProjection? itemSchema itemProfile itemLayout "Items"
      (.expression [.symbol "c:List"]) = some (.node "items" [.seq []]) := rfl

theorem source_nonempty_grammar_rejects_empty_projection :
    ¬ DerivableProjection (grammar true [","]) (classification true) "H" (.node "items" [.seq []]) := by
  rintro ⟨tokens, tree, derived, projected⟩
  have printed := (NonemptySeparatorRefactoring.projected_derivation_iff_printsList
    (comma_wellFormed true) rfl [] tokens).mp ⟨tree, derived, projected⟩
  exact (NonemptySeparatorRefactoring.printsList_to_right printed).nonempty rfl

theorem generic_empty_list_is_outside_grammar_codec_fibre :
    ¬ ∃ source, DerivableProjection (grammar true [","]) (classification true) "H" source ∧
      fromCodec? itemSchema itemProfile itemLayout "Items" (.seq []) = some source := by
  rintro ⟨source, derived, converted⟩
  have computed : fromCodec? itemSchema itemProfile itemLayout "Items" (.seq []) =
      some (.node "items" [.seq []]) := rfl
  have same : source = .node "items" [.seq []] := Option.some.inj (converted.symm.trans computed)
  rw [same] at derived
  exact source_nonempty_grammar_rejects_empty_projection derived

/-! Nested constructors reuse the actual extracted schema, without changing it. -/

abbrev expressionSchema := SortedCanonicalSExprCodecControls.schema
abbrev expressionProfile := SortedCanonicalSExprCodecControls.profile

def expressionLayout : Layout := ⟨id, fun sort => if sort = "ExprList" then "arguments" else sort⟩

def expressionDeclarations : List Constructor := [⟨"Var", ["IdentToken"]⟩, ⟨"IntConst", ["IntToken"]⟩,
  ⟨"StringConst", ["LiteralToken"]⟩, ⟨"Add", ["Expr", "Expr"]⟩, ⟨"Call", ["Expr", "ExprList"]⟩]

@[simp] theorem expression_shape : expressionSchema.shape? "Expr" =
    some (.constructors expressionDeclarations) := rfl

@[simp] theorem identifier_shape : expressionSchema.shape? "IdentToken" = some (.token .identifier) := rfl

@[simp] theorem integer_shape : expressionSchema.shape? "IntToken" = some (.token .literal) := rfl

@[simp] theorem expression_list_shape : expressionSchema.shape? "ExprList" = some (.list "Expr") := rfl

@[simp] theorem identifier_p_admitted : expressionSchema.acceptsToken "IdentToken" "p" = true := rfl
@[simp] theorem identifier_q_admitted : expressionSchema.acceptsToken "IdentToken" "q" = true := rfl
@[simp] theorem unsafe_identifier_admitted : expressionSchema.acceptsToken "IdentToken" "$x" = true := rfl
@[simp] theorem integer_suffix_admitted : expressionSchema.acceptsToken "IntToken" "2u" = true := rfl

@[simp] theorem var_constructor_found :
    constructor? expressionProfile expressionDeclarations "Var" = some ⟨"Var", ["IdentToken"]⟩ := rfl

@[simp] theorem int_constructor_found :
    constructor? expressionProfile expressionDeclarations "IntConst" = some ⟨"IntConst", ["IntToken"]⟩ := rfl

@[simp] theorem call_constructor_found :
    constructor? expressionProfile expressionDeclarations "Call" = some ⟨"Call", ["Expr", "ExprList"]⟩ := rfl

def sourceVariable (spelling : String) : CanonicalTerm := .node "Var" [.node "IdentToken" [.text spelling]]
def sourceInteger (spelling : String) : CanonicalTerm := .node "IntConst" [.node "IntToken" [.text spelling]]

theorem variable_adapts (spelling : String)
    (accepted : expressionSchema.acceptsToken "IdentToken" spelling = true) :
    Adapts expressionSchema expressionProfile expressionLayout "Expr" (sourceVariable spelling)
      (.node "Var" [.text spelling]) := by
  exact .node "Expr" "Var" expressionDeclarations ⟨"Var", ["IdentToken"]⟩ _ _ expression_shape
    var_constructor_found (.cons (.token "IdentToken" spelling .identifier identifier_shape accepted) .nil)

theorem integer_adapts (spelling : String)
    (accepted : expressionSchema.acceptsToken "IntToken" spelling = true) :
    Adapts expressionSchema expressionProfile expressionLayout "Expr" (sourceInteger spelling)
      (.node "IntConst" [.text spelling]) := by
  exact .node "Expr" "IntConst" expressionDeclarations ⟨"IntConst", ["IntToken"]⟩ _ _ expression_shape
    int_constructor_found (.cons (.token "IntToken" spelling .literal integer_shape accepted) .nil)

def sourceNestedCall : CanonicalTerm := .node "Call" [sourceVariable "p", .node "arguments" [.seq [
  sourceInteger "2u", .node "Call" [sourceVariable "q", .node "arguments" [.seq []]], sourceInteger "2u"]]]

def codecNestedCall : CanonicalTerm := .node "Call" [.node "Var" [.text "p"], .seq [
  .node "IntConst" [.text "2u"], .node "Call" [.node "Var" [.text "q"], .seq []],
  .node "IntConst" [.text "2u"]]]

def nestedCallWire : Atom := .expression [.symbol "c:Call", .expression [.symbol "c:Var", .symbol "p"],
  .expression [.symbol "c:List", .expression [.symbol "c:IntConst", .grounded (.string "2u")],
    .expression [.symbol "c:Call", .expression [.symbol "c:Var", .symbol "q"],
      .expression [.symbol "c:List"]], .expression [.symbol "c:IntConst", .grounded (.string "2u")]]]

theorem nested_projection_adapts :
    Adapts expressionSchema expressionProfile expressionLayout "Expr" sourceNestedCall codecNestedCall := by
  have emptyArgs : Adapts expressionSchema expressionProfile expressionLayout "ExprList"
      (.node "arguments" [.seq []]) (.seq []) :=
    .list "ExprList" "Expr" [] [] expression_list_shape (.nil "Expr")
  have inner : Adapts expressionSchema expressionProfile expressionLayout "Expr"
      (.node "Call" [sourceVariable "q", .node "arguments" [.seq []]])
      (.node "Call" [.node "Var" [.text "q"], .seq []]) :=
    .node "Expr" "Call" expressionDeclarations ⟨"Call", ["Expr", "ExprList"]⟩ _ _ expression_shape
      call_constructor_found (.cons (variable_adapts "q" identifier_q_admitted) (.cons emptyArgs .nil))
  exact .node "Expr" "Call" expressionDeclarations ⟨"Call", ["Expr", "ExprList"]⟩ _ _ expression_shape
    call_constructor_found (.cons (variable_adapts "p" identifier_p_admitted)
      (.cons (.list "ExprList" "Expr" _ _ expression_list_shape
        (.cons (integer_adapts "2u" integer_suffix_admitted)
          (.cons inner (.cons (integer_adapts "2u" integer_suffix_admitted) (.nil "Expr"))))) .nil))

theorem nested_projection_adapts_both_directions :
    toCodec? expressionSchema expressionProfile expressionLayout "Expr" sourceNestedCall = some codecNestedCall ∧
      fromCodec? expressionSchema expressionProfile expressionLayout "Expr" codecNestedCall = some sourceNestedCall :=
  ⟨nested_projection_adapts.toCodec, nested_projection_adapts.fromCodec⟩

theorem nested_codec_has_expected_wire :
    encode? expressionSchema expressionProfile "Expr" codecNestedCall = some nestedCallWire := by
  simp [codecNestedCall, nestedCallWire, encode?, encodeArguments?, encodeElements?, encodeToken,
    constructor?, expressionDeclarations, expressionProfile, SortedCanonicalSExprCodecControls.profile,
    Notation.listHead]

theorem nested_projection_wire_round_trip :
    encodeProjection? expressionSchema expressionProfile expressionLayout "Expr" sourceNestedCall =
      some nestedCallWire ∧
    decodeProjection? expressionSchema expressionProfile expressionLayout "Expr" nestedCallWire =
      some sourceNestedCall := by
  have encoded : encodeProjection? expressionSchema expressionProfile expressionLayout "Expr" sourceNestedCall =
      some nestedCallWire := by
    simpa [encodeProjection?, nested_projection_adapts.toCodec] using nested_codec_has_expected_wire
  exact ⟨encoded, decodeProjection_encoded "Expr" sourceNestedCall nestedCallWire encoded⟩

theorem ordinary_one_child_constructor_is_retained :
    toCodec? expressionSchema expressionProfile expressionLayout "Expr" (sourceVariable "p") =
      some (.node "Var" [.text "p"]) := rfl

theorem unknown_one_child_constructor_is_not_erased :
    toCodec? expressionSchema expressionProfile expressionLayout "Expr"
      (.node "Unknown" [.node "IdentToken" [.text "p"]]) = none := rfl

theorem wrong_nested_list_key_rejected :
    toCodec? expressionSchema expressionProfile expressionLayout "Expr"
      (.node "Call" [sourceVariable "p", .node "items" [.seq []]]) = none := rfl

theorem wrong_constructor_child_sort_rejected :
    toCodec? expressionSchema expressionProfile expressionLayout "Expr"
      (.node "IntConst" [.node "IdentToken" [.text "p"]]) = none := rfl

theorem safe_identifier_is_symbol_data :
    encodeProjection? expressionSchema expressionProfile expressionLayout "Expr" (sourceVariable "p") =
      some (.expression [.symbol "c:Var", .symbol "p"]) := rfl

theorem unsafe_identifier_still_uses_codec_escape :
    encodeProjection? expressionSchema expressionProfile expressionLayout "Expr" (sourceVariable "$x") =
      some (.expression [.symbol "c:Var", .expression [.symbol "c:Symbol", .grounded (.string "$x")]]) ∧
    decodeProjection? expressionSchema expressionProfile expressionLayout "Expr"
      (.expression [.symbol "c:Var", .expression [.symbol "c:Symbol", .grounded (.string "$x")]]) =
      some (sourceVariable "$x") := ⟨rfl, rfl⟩

theorem template_variable_is_rejected :
    decodeProjection? expressionSchema expressionProfile expressionLayout "Expr"
      (.expression [.symbol "c:Var", .var "x"]) = none := rfl

theorem constructor_arity_is_checked :
    toCodec? expressionSchema expressionProfile expressionLayout "Expr"
      (.node "Call" [sourceVariable "p"]) = none ∧
    fromCodec? expressionSchema expressionProfile expressionLayout "Expr"
      (.node "Call" [.node "Var" [.text "p"], .seq [], .seq []]) = none := ⟨rfl, rfl⟩

def alternativeLayout : Layout := ⟨fun _ => "DifferentToken", fun _ => "differentList"⟩

theorem admission_depends_on_declared_source_layout :
    toCodec? itemSchema itemProfile alternativeLayout "Items" repeatedCanonical = none ∧
      toCodec? itemSchema itemProfile itemLayout "Items" repeatedCanonical = some itemValues := ⟨rfl, rfl⟩

end Mettapedia.GSLT.Parsing.CanonicalProjectionSExprAdapter.Controls
