import Mettapedia.GSLT.Parsing.CheckedTreePresentation

/-!
# Constructed controls for checked presentations

The examples use the existing C AST constructor vocabulary. Two
different rule tables abbreviate the same trees. They also demonstrate
recursive fallback, removal of statement wrappers, duplicate-rule refusal,
changed-tree refusal, exact literal spellings, normalization and versioned
document admission. These tables are structural controls, not complete
implementations of any foreign source language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.CheckedTreePresentationControls

open CanonicalGrammar (CanonicalTerm)
open CheckedTreePresentation
open ExactPresentation (convert normalize expandDocument viewDocument)

def unary (head constructor : String) : Rule :=
  ⟨head, 1, .node constructor [.slot 0]⟩

def binary (head constructor : String) : Rule :=
  ⟨head, 2, .node constructor [.slot 0, .slot 1]⟩

def operatorRules : List Rule :=
  [unary "v" "Var", unary "i" "IntConst", unary "*" "Indirection",
   binary "*" "Multiply", binary "+" "Add", binary "+=" "AddAssign",
   binary "-" "Subtract",
   ⟨"stmt", 1, .node "ExpressionStatement" [.node "SomeFullExpression" [.slot 0]]⟩]

def wordRules : List Rule :=
  [unary "variable" "Var", unary "integer" "IntConst", unary "indirect" "Indirection",
   binary "multiply" "Multiply", binary "add" "Add", binary "add-assign" "AddAssign"]

def operatorProposal : Proposer
  | .node "Var" [_], children => some (.form "v" children)
  | .node "IntConst" [_], children => some (.form "i" children)
  | .node "Indirection" [_], children => some (.form "*" children)
  | .node "Multiply" [_, _], children => some (.form "*" children)
  | .node "Add" [_, _], children => some (.form "+" children)
  | .node "AddAssign" [_, _], children => some (.form "+=" children)
  | .node "ExpressionStatement" [.node "SomeFullExpression" [_]],
      [.node "SomeFullExpression" [child]] => some (.form "stmt" [child])
  | _, _ => none

def wordProposal : Proposer
  | .node "Var" [_], children => some (.form "variable" children)
  | .node "IntConst" [_], children => some (.form "integer" children)
  | .node "Indirection" [_], children => some (.form "indirect" children)
  | .node "Multiply" [_, _], children => some (.form "multiply" children)
  | .node "Add" [_, _], children => some (.form "add" children)
  | .node "AddAssign" [_, _], children => some (.form "add-assign" children)
  | _, _ => none

def operatorPresentation := presentation ⟨"operator-tree", 1⟩ operatorRules operatorProposal
def wordPresentation := presentation ⟨"word-tree", 1⟩ wordRules wordProposal

def cVariable (name : String) : CanonicalTerm := .node "Var" [.text name]
def integer (spelling : String) : CanonicalTerm := .node "IntConst" [.text spelling]
def sum : CanonicalTerm := .node "Add" [cVariable "x", integer "001u"]
def store : CanonicalTerm :=
  .node "AddAssign" [.node "Indirection" [cVariable "p"], integer "1u"]
def statement : CanonicalTerm :=
  .node "ExpressionStatement" [.node "SomeFullExpression" [store]]

def compactStore : Surface :=
  .form "+=" [.form "*" [.form "v" [.text "p"]], .form "i" [.text "1u"]]

def wordStore : Surface :=
  .form "add-assign"
    [.form "indirect" [.form "variable" [.text "p"]], .form "integer" [.text "1u"]]

theorem unary_operator_has_exact_reading :
    expand operatorRules (.form "*" [.form "v" [.text "p"]]) =
      some (.node "Indirection" [cVariable "p"]) := rfl

theorem binary_operator_has_distinct_exact_reading :
    expand operatorRules (.form "*" [.form "v" [.text "x"], .form "v" [.text "y"]]) =
      some (.node "Multiply" [cVariable "x", cVariable "y"]) := rfl

theorem wrong_operator_arity_is_refused :
    expand operatorRules (.form "*" []) = none := rfl

theorem unknown_form_is_refused :
    expand operatorRules (.form "defer" [.form "v" [.text "x"]]) = none := rfl

theorem duplicate_dispatch_is_refused :
    interpret [binary "+" "Add", binary "+" "Subtract"] "+"
      [cVariable "x", integer "1u"] = none := rfl

theorem reversed_duplicate_dispatch_is_also_refused :
    interpret [binary "+" "Subtract", binary "+" "Add"] "+"
      [cVariable "x", integer "1u"] = none := rfl

theorem missing_template_slot_is_refused :
    interpret [⟨"bad-slot", 1, .node "Add" [.slot 0, .slot 1]⟩] "bad-slot"
      [cVariable "x"] = none := rfl

theorem operator_view_is_compact : view operatorRules operatorProposal store = compactStore := rfl

theorem word_view_is_different : view wordRules wordProposal store = wordStore := rfl

theorem compact_store_expands_exactly : expand operatorRules compactStore = some store := rfl

theorem word_store_expands_to_same_tree : expand wordRules wordStore = some store := rfl

theorem statement_wrappers_can_be_removed :
    view operatorRules operatorProposal statement = .form "stmt" [compactStore] := rfl

theorem statement_wrapper_expansion_is_exact :
    expand operatorRules (.form "stmt" [compactStore]) = some statement := rfl

def attributed : CanonicalTerm :=
  .node "AttributedDeclarator" [cVariable "p", .node "GNUAttribute" [store]]

theorem unfamiliar_parent_keeps_compact_children :
    view operatorRules operatorProposal attributed =
      .node "AttributedDeclarator"
        [.form "v" [.text "p"], .node "GNUAttribute" [compactStore]] := rfl

theorem unfamiliar_parent_round_trips :
    expand operatorRules (view operatorRules operatorProposal attributed) = some attributed :=
  expand_view operatorRules operatorProposal attributed

def changedProposal : Proposer
  | .node "Add" [_, _], children => some (.form "-" children)
  | tree, children => operatorProposal tree children

theorem changed_meaning_candidate_falls_back :
    view operatorRules changedProposal sum =
      .node "Add" [.form "v" [.text "x"], .form "i" [.text "001u"]] := rfl

theorem changed_meaning_never_reaches_tree :
    expand operatorRules (view operatorRules changedProposal sum) = some sum :=
  expand_view operatorRules changedProposal sum

def invalidProposal : Proposer := fun _ _ => some (.form "unknown" [])

theorem invalid_candidate_falls_back_recursively :
    view operatorRules invalidProposal sum =
      .node "Add" [.node "Var" [.text "x"], .node "IntConst" [.text "001u"]] := rfl

theorem literal_spelling_is_preserved :
    expand operatorRules (view operatorRules operatorProposal (integer "001u")) =
      some (integer "001u") := rfl

theorem ast_literal_zeroes_are_not_normalized :
    equalTree (integer "001u") (integer "1u") = false := rfl

theorem sequence_order_and_multiplicity_are_preserved :
    expand operatorRules
      (view operatorRules operatorProposal (.seq [store, sum, store])) =
        some (.seq [store, sum, store]) :=
  expand_view operatorRules operatorProposal _

theorem conversion_changes_view_preserving_tree :
    convert operatorPresentation wordPresentation (sort := ()) compactStore = some wordStore := rfl

theorem conversion_back_restores_preferred_form :
    (convert operatorPresentation wordPresentation (sort := ()) compactStore).bind
      (convert wordPresentation operatorPresentation (sort := ())) = some compactStore := rfl

def exactStore : Surface :=
  .node "AddAssign" [.node "Indirection" [.node "Var" [.text "p"]],
    .node "IntConst" [.text "1u"]]

theorem alternate_spelling_normalizes :
    normalize operatorPresentation (sort := ()) exactStore = some compactStore := rfl

theorem back_conversion_normalizes_instead_of_preserving_spelling :
    (convert operatorPresentation wordPresentation (sort := ()) exactStore).bind
      (convert wordPresentation operatorPresentation (sort := ())) = some compactStore := rfl

theorem invalid_input_stays_invalid_across_conversion :
    convert operatorPresentation wordPresentation (sort := ()) (.form "defer" []) = none := rfl

theorem versioned_document_has_exact_reading :
    expandDocument operatorPresentation
      (viewDocument operatorPresentation (sort := ()) store) = some store := rfl

theorem different_document_version_is_refused :
    expandDocument operatorPresentation (sort := ())
      ⟨⟨"operator-tree", 2⟩, compactStore⟩ = none := rfl

theorem different_document_presentation_is_refused :
    expandDocument operatorPresentation (sort := ())
      ⟨⟨"word-tree", 1⟩, wordStore⟩ = none := rfl

end Mettapedia.GSLT.Parsing.CheckedTreePresentationControls
