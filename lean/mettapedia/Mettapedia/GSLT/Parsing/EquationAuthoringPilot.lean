import Mettapedia.GSLT.Parsing.GrammarPresentationTransport
import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SemanticGluingControls

/-!
# Token-level English equation authoring

An authored `LanguageDef` recognizes declarations such as
`Declare that first equals zero .`. It uses the existing complete derivation
enumerator, retains every candidate tree, and explicitly rejects anything
other than one candidate. Constructor-directed lowering contributes an
equation body to the existing origin-sensitive module authoring algebra.

This finite-operator pilot begins at tokens. Source lexing, scannerless packed
parsing, arbitrary typed operators and binder lowering remain separate work.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.EquationAuthoringPilot

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SemanticGluingControls

def operatorRule (label token : String) : GrammarRule :=
  { label, category := "Operator", params := [], syntaxPattern := [.terminal token] }

def declarationRule : GrammarRule :=
  { label := "DeclareEquation", category := "Declaration"
    params := [.simple "left" (.base "Operator"), .simple "right" (.base "Operator")]
    syntaxPattern := [.terminal "Declare", .terminal "that", .nonTerminal "left",
      .terminal "equals", .nonTerminal "right", .terminal "."] }

def english : LanguageDef :=
  { name := "EquationAuthoringPilot"
    types := [TypeDecl.plain "Operator", TypeDecl.plain "Declaration"]
    equations := [], rewrites := []
    terms := [operatorRule "Zero" "zero", operatorRule "One" "one",
      operatorRule "First" "first", operatorRule "Second" "second", declarationRule] }

theorem english_consuming : ConsumingGrammar english :=
  consumingGrammarB_sound (by decide)

def syntaxBinding : LanguageDefSyntaxCompiler.Binding where
  literalRef := some
  lexicalSortRef := fun _ => none
  categoryRef := fun name => "category:" ++ name
  ruleRef := fun name => "rule:" ++ name

theorem english_uses_existing_syntax_compiler :
    (LanguageDefSyntaxCompiler.compileRules? syntaxBinding english).isSome = true := by decide

theorem english_compilation_retains_authored_rows :
    ∃ rules, LanguageDefSyntaxCompiler.compileRules? syntaxBinding english = some rules ∧
      rules.map (fun rule => rule.source) = english.terms := by
  cases compiled : LanguageDefSyntaxCompiler.compileRules? syntaxBinding english with
  | none =>
      have positive := english_uses_existing_syntax_compiler
      rw [compiled] at positive
      cases positive
  | some rules =>
      exact ⟨rules, rfl,
        LanguageDefSyntaxCompiler.compileRules_sourceRules syntaxBinding english rules compiled⟩

/-- All complete token parses, with no scheduling-based selection. -/
def candidates (lang : LanguageDef) (input : List String) : List Pattern :=
  enumDerives lang input.length "Declaration" input

theorem candidates_exact (lang : LanguageDef) (consuming : ConsumingGrammar lang)
    (input : List String) (tree : Pattern) :
    tree ∈ candidates lang input ↔ Derives lang "Declaration" input tree := by
  rw [candidates, mem_enumDerives_iff]
  exact ⟨And.left, fun derivation => ⟨derivation, derives_height_le consuming derivation⟩⟩

def decodeOperator : Pattern → Option Op
  | .apply "Zero" [] => some .zero
  | .apply "One" [] => some .one
  | .apply "First" [] => some .first
  | .apply "Second" [] => some .second
  | _ => none

def decodeDeclaration : Pattern → Option (Op × Op)
  | .apply "DeclareEquation" [left, right] => do
      let lhs ← decodeOperator left
      let rhs ← decodeOperator right
      pure (lhs, rhs)
  | _ => none

/-- The ambiguity policy is explicit and runs after complete enumeration. -/
def elaborate (lang : LanguageDef) (input : List String) : Option (Op × Op) :=
  match candidates lang input with
  | [tree] => decodeDeclaration tree
  | _ => none

theorem elaborate_sound (lang : LanguageDef) (consuming : ConsumingGrammar lang)
    (input : List String) (body : Op × Op) (success : elaborate lang input = some body) :
    ∃ tree, Derives lang "Declaration" input tree ∧ decodeDeclaration tree = some body := by
  unfold elaborate at success
  split at success
  · rename_i tree single
    exact ⟨tree, (candidates_exact lang consuming input tree).mp
      (by rw [single]; exact List.mem_singleton_self tree), success⟩
  · contradiction

/-- The source owner supplies the origin and label. Textual coincidence is
not used to manufacture shared declaration identity. -/
def authored (lang : LanguageDef) (input : List String) (origin : Nat) (label : String) :
    Option (Document Nat String (Op × Op)) :=
  (elaborate lang input).map (fun body => .declaration {⟨origin, label, body⟩})

def firstInput : List String := ["Declare", "that", "first", "equals", "zero", "."]
def secondInput : List String := ["Declare", "that", "second", "equals", "one", "."]
def firstTree : Pattern := .apply "DeclareEquation" [.apply "First" [], .apply "Zero" []]

theorem english_one_complete_parse : candidates english firstInput = [firstTree] := by decide

theorem english_lowering : elaborate english firstInput = some (.first, .zero) := by decide

def tokenChange : String ≃ String :=
  (Equiv.swap "Declare" "assert").trans ((Equiv.swap "equals" "=").trans
    ((Equiv.swap "zero" "0").trans (Equiv.swap "one" "1")))

def symbolic : LanguageDef := GrammarPresentationTransport.mapLanguage tokenChange english

theorem symbolic_one_complete_parse :
    candidates symbolic (firstInput.map tokenChange) = [firstTree] := by decide

theorem same_equation_from_both_interfaces :
    elaborate symbolic (firstInput.map tokenChange) = elaborate english firstInput := by decide

/-! ## The presentation-change program edits actual grammar data -/

open GrammarPresentationTransport

def editStart : NotationMachine.State :=
  ⟨english, [], [("equals", "="), ("zero", "0")]⟩

def editMiddle : NotationMachine.State :=
  ⟨mapLanguage (Equiv.swap "equals" "=") english, [("equals", "=")], [("zero", "0")]⟩

def editFinish : NotationMachine.State :=
  ⟨mapLanguage (Equiv.swap "zero" "0") editMiddle.presentation,
    [("equals", "="), ("zero", "0")], []⟩

def editPath : IndexedOperational.ExecutionPath NotationMachine.system editStart editFinish :=
  .cons ⟨.edit english [] ("equals", "=") [("zero", "0")]⟩
    (.cons ⟨.edit editMiddle.presentation [("equals", "=")] ("zero", "0") []⟩
      (.refl editFinish))

theorem edit_program_executes :
    NotationMachine.execute editStart = some editMiddle ∧
      NotationMachine.execute editMiddle = some editFinish ∧
      NotationMachine.execute editFinish = none := ⟨rfl, rfl, rfl⟩

theorem edit_program_changes_grammar :
    (editFinish.presentation.terms[4]?).map GrammarRule.syntaxPattern ≠
      (english.terms[4]?).map GrammarRule.syntaxPattern := by
  simp [editFinish, editMiddle, english, mapLanguage, mapRule, mapItem,
    declarationRule, operatorRule]
  decide

theorem edit_program_preserves_all_original_parses :
    NotationMachine.observe editStart = NotationMachine.observe editFinish :=
  NotationMachine.path_observe editPath

theorem edited_english_has_same_complete_tree :
    candidates editFinish.presentation ["Declare", "that", "first", "=", "0", "."] =
      [firstTree] := by decide

/-- Both independently parsed texts feed the existing checked module join. -/
theorem english_declarations_make_existing_join :
    (authored english firstInput 1 "First").bind (fun first =>
      (authored english secondInput 2 "Second").bind (fun second =>
        Mettapedia.GSLT.LanguageDef.ModuleAlgebra.elaborate
          (.bundle [.declaration {parameter}, first, second]))) =
      some whole := by
  have secondLowering : elaborate english secondInput = some (.second, .one) := by decide
  simp only [authored, english_lowering, secondLowering, Option.map_some, Option.bind_some]
  apply check_eq_some_iff.mpr
  simp [unionFragments, LanguageDef.Extension.DeclarationDocument.values,
    LanguageDef.Extension.DeclarationDocument.valuesList, whole, ownFirst, ownSecond]
  decide

theorem selected_equation_has_existing_binding_semantics (first second : Bool) :
    SemanticGluing.equationSat schema (pointAlgebra first second) (.first, .zero) ↔
      first = false := by
  simpa [constant] using point_satisfies_iff first second (.first, .zero)

theorem incomplete_sentence_has_no_parse :
    candidates english ["Declare", "that", "first", "equals", "."] = [] := by decide

theorem incomplete_sentence_is_not_derivable :
    ¬ ∃ tree, Derives english "Declaration" ["Declare", "that", "first", "equals", "."] tree := by
  rintro ⟨tree, derivation⟩
  have member := (candidates_exact english english_consuming _ tree).mpr derivation
  rw [incomplete_sentence_has_no_parse] at member
  exact List.not_mem_nil member

/-- An added grammar row can invent a second constructor on the same input. -/
def ambiguous : LanguageDef :=
  { english with terms := english.terms ++ [{ declarationRule with label := "OtherEquation" }] }

def otherTree : Pattern := .apply "OtherEquation" [.apply "First" [], .apply "Zero" []]

theorem ambiguity_is_retained : candidates ambiguous firstInput = [firstTree, otherTree] := by decide

theorem ambiguity_is_rejected : elaborate ambiguous firstInput = none := by decide

theorem forward_preservation_does_not_remove_extra_parse :
    Derives ambiguous "Declaration" firstInput firstTree ∧
      Derives ambiguous "Declaration" firstInput otherTree ∧ firstTree ≠ otherTree := by
  have consuming : ConsumingGrammar ambiguous := consumingGrammarB_sound (by decide)
  have first := (candidates_exact ambiguous consuming firstInput firstTree).mp
    (by rw [ambiguity_is_retained]; simp)
  have other := (candidates_exact ambiguous consuming firstInput otherTree).mp
    (by rw [ambiguity_is_retained]; simp)
  exact ⟨first, other, by decide⟩

end Mettapedia.GSLT.Parsing.EquationAuthoringPilot
