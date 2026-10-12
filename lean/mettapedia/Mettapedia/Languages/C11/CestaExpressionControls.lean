import Mettapedia.Languages.C11.CestaExpressionCorrespondence
import Mettapedia.Languages.C11.LocatedExpressionControls

/-!
# Cesta integer-expression elaboration controls

The canonical trees use the CExpr and CDecl constructor names. The controls
exercise independent numeral/type formation, nested source elaboration,
scope shadowing, update value selection, sequencing and alias conflicts.
They do not certify a native parser or instantiate an entire C11 grammar.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.CestaExpressionControls

open Mettapedia.GSLT.Parsing.CanonicalGrammar (CanonicalTerm)
open ObjectAccessMemory IntegerMemoryModel LocatedExpressions
open ExpressionEventExecution
open CestaExpressionElaboration CestaLocatedExpressions CestaExpressionCorrespondence
open IntegerMemoryControls

def environment : ScopedLvalues.Environment :=
  [[("x", integer), ("alias", integer), ("ch", character), ("b", boolean)]]

def variableTerm (name : String) : CanonicalTerm := .node "Var" [.text name]
def literalTerm (spelling : String) : CanonicalTerm := .node "IntConst" [.text spelling]

def typeSyntax (first : PrimitiveSpecifier) (rest : List PrimitiveSpecifier) : CanonicalTerm :=
  .node "TypeName" [.node "PrimitiveSpecifierQualifiers" [.node first.head [],
    .seq (rest.map (fun specifier => .node "PrimitiveQualifierTail" [.node specifier.head []]))],
    .node "NoAbstractDeclarator" []]

def boolSyntax : CanonicalTerm := .node "TypeName" [.node "UniqueSpecifierQualifiers"
  [.node "Bool" [], .node "NoTypeQualifiers" []], .node "NoAbstractDeclarator" []]

theorem decimal_digits_are_positional : decimal? "257" = some 257 := by cbv
theorem zero_is_a_decimal_token : decimal? "0" = some 0 := by cbv
theorem empty_literal_refused : decimal? "" = none := by cbv
theorem malformed_digit_refused : decimal? "12x" = none := by cbv
theorem negative_sign_is_not_literal_syntax : decimal? "-7" = none := by cbv
theorem octal_spelling_requires_another_profile : decimal? "077" = none := by cbv
theorem hexadecimal_spelling_requires_another_profile : decimal? "0x10" = none := by cbv
theorem suffix_requires_candidate_type_selection : decimal? "2u" = none := by cbv
theorem unicode_digit_is_not_c_decimal_digit : decimal? "٢" = none := by cbv

def maxInt : IntegerScalar.Value model.parameters := ⟨.int, ⟨2147483647, by decide⟩⟩
theorem maximal_fixture_int_literal : literal? model "2147483647" = some maxInt := by decide +kernel
theorem larger_decimal_requires_candidate_type_selection : literal? model "2147483648" = none := by decide +kernel

theorem unsigned_long_long_type : typeName? (typeSyntax .unsigned [.long, .long, .int]) =
    some (.unsigned (.standard .longLong)) := by cbv
theorem reordered_unsigned_long_long_type : typeName? (typeSyntax .long [.int, .unsigned, .long]) =
    some (.unsigned (.standard .longLong)) := by cbv
theorem signed_character_type : typeName? (typeSyntax .signed [.char]) = some characterType := by cbv
theorem unsigned_short_type : typeName? (typeSyntax .short [.unsigned, .int]) =
    some (.unsigned (.standard .short)) := by cbv
theorem bool_type : typeName? boolSyntax = some .boolean := by cbv
theorem signed_unsigned_combination_refused : typeName? (typeSyntax .signed [.unsigned, .int]) = none := by cbv
theorem duplicated_int_specifier_refused : typeName? (typeSyntax .int [.int]) = none := by cbv
theorem third_long_specifier_refused : typeName? (typeSyntax .long [.long, .long]) = none := by cbv
theorem plain_character_keeps_its_separate_type : typeName? (typeSyntax .char []) = none := by cbv
theorem floating_type_is_not_integer_type : typeName? (.node "TypeName"
    [.node "PrimitiveSpecifierQualifiers" [.node "Float" [], .seq []],
      .node "NoAbstractDeclarator" []]) = none := by cbv
theorem pointer_declarator_is_not_scalar_type : typeName? (.node "TypeName"
    [.node "PrimitiveSpecifierQualifiers" [.node "Int" [], .seq []],
      .node "SomeAbstractDeclarator" [.node "AbstractPointer"
        [.node "Pointer" [.node "NoTypeQualifiers" []]]]]) = none := by rfl

theorem identifier_load_is_typed : readTerm model environment (variableTerm "ch") =
    some (.load ⟨character, characterType, rfl⟩) := by cbv
theorem missing_identifier_refused : readTerm model environment (variableTerm "missing") = none := by cbv
theorem nearest_shadowed_integer_binding : readTerm model [[("x", character)], [("x", integer)]] (variableTerm "x") =
    some (.load ⟨character, characterType, rfl⟩) := by cbv
theorem empty_inner_scopes_preserve_lookup : readTerm model [[], [], [], [("x", integer)]]
    (variableTerm "x") = some (.load ⟨integer, .int, rfl⟩) := by cbv

def pointerLocation : Lvalue := integer.cast ⟨.scalar (.pointer 41), {}⟩
theorem noninteger_shadow_is_not_skipped : readTerm model [[("x", pointerLocation)], [("x", integer)]]
    (variableTerm "x") = none := by cbv

def assignmentTerm : CanonicalTerm := .node "Assign" [variableTerm "x",
  .node "Cast" [typeSyntax .signed [.char], .node "Add" [literalTerm "255", literalTerm "2"]]]
def postfixTerm : CanonicalTerm := .node "Comma" [assignmentTerm, .node "PostIncrement" [variableTerm "x"]]
def prefixTerm : CanonicalTerm := .node "Comma" [assignmentTerm, .node "PreIncrement" [variableTerm "x"]]

def intDestination : Destination := ⟨integer, .int, rfl⟩
def expectedAssignment : Expression model := .assignment intDestination
  (.cast characterType (.arithmetic .add (.value twoFiftyFive) (.value two)))
def expectedPostfix : Expression model := .comma expectedAssignment (.update intDestination true false)
def expectedPrefix : Expression model := .comma expectedAssignment (.update intDestination true true)

theorem nested_assignment_elaborates : readTerm model environment assignmentTerm = some expectedAssignment := by cbv
theorem nested_postfix_elaborates : readTerm model environment postfixTerm = some expectedPostfix := by cbv
theorem nested_prefix_elaborates : readTerm model environment prefixTerm = some expectedPrefix := by cbv
theorem postfix_has_independent_syntax_evidence : TermReading model environment postfixTerm expectedPostfix :=
  readTerm_sound _ _ _ _ nested_postfix_elaborates

def parsedProbe (term : CanonicalTerm) : Option LocatedExpressionControls.Probe := do
  let expression ← readTerm model environment term
  LocatedExpressionControls.probe intervalReductionPolicy
    ((compile expression).component.enumeration.items.length + 1) expression
    (compile expression).component.enumeration.items

theorem postfix_returns_old_value_and_keeps_new_memory :
    (parsedProbe postfixTerm).map (fun result => (result.result, result.integer, result.stores, result.finished)) =
      some (some 1, some 2, 2, true) := by decide +kernel
theorem prefix_returns_new_value_and_keeps_new_memory :
    (parsedProbe prefixTerm).map (fun result => (result.result, result.integer, result.stores, result.finished)) =
      some (some 2, some 2, 2, true) := by decide +kernel

def binaryTerm (operator : IntegerBinaryOperator) : CanonicalTerm :=
  .node (binaryHead operator) [literalTerm "17", literalTerm "2"]
def parsedResult (term : CanonicalTerm) : Option Int := (parsedProbe term).bind (fun result => result.result)

theorem all_five_arithmetic_heads_compute :
    [.add, .subtract, .multiply, .divide, .remainder].map (fun operator => parsedResult (binaryTerm operator)) =
      [some 19, some 15, some 34, some 8, some 1] := by cbv

theorem non_lvalue_assignment_refused : readTerm model environment
    (.node "Assign" [literalTerm "1", literalTerm "2"]) = none := by cbv
theorem non_lvalue_update_refused : readTerm model environment
    (.node "PostIncrement" [.node "Add" [variableTerm "x", literalTerm "1"]]) = none := by cbv
theorem invented_arithmetic_constructor_refused : readTerm model environment
    (.node "ArithmeticAdd" [literalTerm "1", literalTerm "2"]) = none := by cbv
theorem swapped_cast_arguments_refused : readTerm model environment
    (.node "Cast" [literalTerm "1", typeSyntax .int []]) = none := by cbv
theorem unsupported_call_is_not_fabricated : readTerm model environment
    (.node "Call" [variableTerm "x", .node "NoArguments" []]) = none := by cbv
theorem extra_argument_refused : readTerm model environment
    (.node "Add" [literalTerm "1", literalTerm "2", literalTerm "3"]) = none := by cbv

def aliasConflict : CanonicalTerm := .node "Add"
  [.node "PostIncrement" [variableTerm "x"], variableTerm "alias"]
theorem resolved_aliases_preserve_source_conflict :
    (readTerm model environment aliasConflict).map (fun expression => admissible (compile expression)) = some false := by cbv

def invalidDivision : CanonicalTerm := .node "Divide" [literalTerm "1", literalTerm "0"]
theorem undefined_arithmetic_keeps_a_distinct_outcome :
    (parsedProbe invalidDivision).map (fun result => (result.result, result.finished)) = some (none, true) := by cbv

end Mettapedia.Languages.C11.CestaExpressionControls
