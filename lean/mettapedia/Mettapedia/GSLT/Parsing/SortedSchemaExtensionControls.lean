import Mettapedia.GSLT.Parsing.SortedSchemaExtension

/-! A genuine schema extension adds an integer sort and expression constructor.
Old nested trees keep their ordered fields and exact wire representation.
Mutants change argument order, arity, list/token shape, or unique dispatch. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SortedSchemaExtensionControls

open SortedSchemaExtension SortedCanonicalSExprCodec PreparedSortedCodecSchema
open CanonicalGrammar (CanonicalTerm)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def profile : Notation where
  safeSymbol := fun _ => true

def accepts : String → String → Bool
  | "Name", spelling => spelling == "x" || spelling == "y"
  | "Integer", spelling => spelling == "1u"
  | _, _ => false

def before : List Entry :=
  [⟨"Name", .token .identifier⟩,
   ⟨"Expr", .constructors [⟨"Var", ["Name"]⟩, ⟨"Put", ["Name", "Expr"]⟩]⟩,
   ⟨"ExprList", .list "Expr"⟩]

def after : List Entry :=
  [⟨"Name", .token .identifier⟩,
   ⟨"Expr", .constructors [⟨"Var", ["Name"]⟩, ⟨"Put", ["Name", "Expr"]⟩,
     ⟨"IntConst", ["Integer"]⟩]⟩,
   ⟨"ExprList", .list "Expr"⟩,
   ⟨"Integer", .token .literal⟩]

def schemaBefore : Schema := preparedSchema before accepts
def schemaAfter : Schema := preparedSchema after accepts

def specimen : CanonicalTerm := .seq
  [.node "Var" [.text "x"], .node "Put" [.text "y", .node "Var" [.text "x"]]]

def wire : Atom := .expression [.symbol "c:List",
  .expression [.symbol "c:Var", .symbol "x"],
  .expression [.symbol "c:Put", .symbol "y", .expression [.symbol "c:Var", .symbol "x"]]]

theorem genuine_extension_admitted : check profile before after = true := by decide

theorem old_nested_tree_decodes : decode? schemaBefore profile "ExprList" wire = some specimen := by rfl

theorem old_wire_keeps_same_tree : decode? schemaAfter profile "ExprList" wire = some specimen := by
  exact old_wire_preserved profile before after genuine_extension_admitted accepts
    "ExprList" wire specimen old_nested_tree_decodes

theorem old_encoding_keeps_exact_wire : encode? schemaAfter profile "ExprList" specimen = some wire := by
  have formed := decode_sorted schemaBefore profile "ExprList" wire specimen old_nested_tree_decodes
  have same := encode_preserved profile before after genuine_extension_admitted accepts "ExprList" specimen formed
  exact same.trans (by rfl)

def integerWire : Atom := .expression [.symbol "c:IntConst", .grounded (.string "1u")]

theorem added_constructor_really_adds_structure :
    decode? schemaBefore profile "Expr" integerWire = none ∧
      decode? schemaAfter profile "Expr" integerWire = some (.node "IntConst" [.text "1u"]) := by
  constructor <;> rfl

def withConstructors (rows : List Constructor) : List Entry :=
  [⟨"Name", .token .identifier⟩, ⟨"Expr", .constructors rows⟩, ⟨"ExprList", .list "Expr"⟩]

theorem changed_argument_order_refused : check profile before
    (withConstructors [⟨"Var", ["Name"]⟩, ⟨"Put", ["Expr", "Name"]⟩]) = false := by decide

theorem changed_arity_refused : check profile before
    (withConstructors [⟨"Var", ["Name", "Name"]⟩, ⟨"Put", ["Name", "Expr"]⟩]) = false := by decide

theorem duplicate_old_head_refused : check profile before
    (withConstructors [⟨"Var", ["Name"]⟩, ⟨"Var", ["Name"]⟩, ⟨"Put", ["Name", "Expr"]⟩]) = false := by decide

theorem duplicate_added_head_refused : check profile before
    (withConstructors [⟨"Var", ["Name"]⟩, ⟨"Put", ["Name", "Expr"]⟩,
      ⟨"Extra", []⟩, ⟨"Extra", []⟩]) = false := by decide

theorem dangling_added_sort_refused : check profile before
    (withConstructors [⟨"Var", ["Name"]⟩, ⟨"Put", ["Name", "Expr"]⟩,
      ⟨"Extra", ["Missing"]⟩]) = false := by decide

theorem changed_list_element_refused : check profile before
    [⟨"Name", .token .identifier⟩,
     ⟨"Expr", .constructors [⟨"Var", ["Name"]⟩, ⟨"Put", ["Name", "Expr"]⟩]⟩,
     ⟨"ExprList", .list "Name"⟩] = false := by decide

theorem changed_token_representation_refused : check profile before
    [⟨"Name", .token .literal⟩,
     ⟨"Expr", .constructors [⟨"Var", ["Name"]⟩, ⟨"Put", ["Name", "Expr"]⟩]⟩,
     ⟨"ExprList", .list "Expr"⟩] = false := by decide

theorem duplicate_sort_refused : check profile before (after ++ [⟨"Name", .token .literal⟩]) = false := by decide

theorem reserved_added_constructor_refused : check profile before
    (withConstructors [⟨"Var", ["Name"]⟩, ⟨"Put", ["Name", "Expr"]⟩, ⟨"List", []⟩]) = false := by decide

def putTemplate : CheckedTreePresentation.Template :=
  .node "Put" [.slot 0, .node "Var" [.slot 1]]

theorem old_template_checked :
    SortedTreePresentationTemplates.check schemaBefore profile ["Name", "Name"] "Expr" putTemplate = true := by rfl

theorem typed_template_certificate_transports :
    SortedTreePresentationTemplates.Typed schemaAfter profile ["Name", "Name"] "Expr" putTemplate := by
  exact template_transport profile before after genuine_extension_admitted accepts ["Name", "Name"] "Expr" putTemplate
    (SortedTreePresentationTemplates.check_sound _ _ _ _ _ old_template_checked)

theorem wrong_slot_sort_refused :
    SortedTreePresentationTemplates.check schemaAfter profile ["Expr", "Name"] "Expr" putTemplate = false := by rfl

end Mettapedia.GSLT.Parsing.SortedSchemaExtensionControls
