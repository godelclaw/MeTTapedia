import Mettapedia.GSLT.LanguageDef.BindingSignatureReification
import Mettapedia.GSLT.LanguageDef.BindingSignatureEquationPresentation
import Mettapedia.GSLT.LanguageDef.BindingSignatureNotation

/-!
# Controls for closed first-order reification

The codec consumes actual language declarations and computes two different
sorted constructor trees. Wrong sorts, argument order, arity, and undeclared
labels fail this restricted codec. An authored, validator-accepted rewrite
contains a mistyped closed left side, exposing the validator/typing boundary
without changing admission or firing semantics.
-/

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.Reification.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation

set_option autoImplicit false

private def truthRule : GrammarRule where
  label := "Truth"
  category := "Bool"
  params := []
  syntaxPattern := [.terminal "truth"]

private def countRule : GrammarRule where
  label := "Count"
  category := "Nat"
  params := []
  syntaxPattern := [.terminal "count"]

private def flagRule : GrammarRule where
  label := "Flag"
  category := "Result"
  params := [.simple "value" (.base "Bool")]
  syntaxPattern := [.nonTerminal "value"]

private def boxRule : GrammarRule where
  label := "Box"
  category := "Result"
  params := [.simple "value" (.base "Nat")]
  syntaxPattern := [.nonTerminal "value"]

private def pairRule : GrammarRule where
  label := "Pair"
  category := "Result"
  params := [.simple "first" (.base "Bool"), .simple "second" (.base "Nat")]
  syntaxPattern := [.nonTerminal "first", .nonTerminal "second"]

def truth : Pattern := .apply "Truth" []
def count : Pattern := .apply "Count" []
def flag : Pattern := .apply "Flag" [truth]
def box : Pattern := .apply "Box" [count]
def pair : Pattern := .apply "Pair" [truth, count]
def wrongInput : Pattern := .apply "Box" [truth]

private def mistypedRewrite : RewriteRule where
  name := "MistypedClosedInput"
  typeContext := []
  premises := []
  left := wrongInput
  right := truth

/-- The deliberately mistyped row is authored in this validator-accepted
language, rather than supplied as an unrelated malformed query. -/
def language : LanguageDef := LanguageDef.ofCore "ReificationControls"
  ["Bool", "Nat", "Result"]
  [truthRule, countRule, flagRule, boxRule, pairRule] [] [mistypedRewrite]

theorem language_valid : language.validate = [] := by cbv

theorem two_different_constructor_trees_are_computed :
    (reify? language flag (.base "Result")).map erase = some flag ∧
    (reify? language box (.base "Result")).map erase = some box ∧ flag ≠ box := by
  decide +kernel

theorem mixed_argument_sorts_are_computed :
    (reify? language pair (.base "Result")).map erase = some pair := by
  decide +kernel

theorem computed_flags_have_the_original_type :
    HasType language FreeTypeContext.empty [] flag (.base "Result") ∧
    HasType language FreeTypeContext.empty [] box (.base "Result") := by
  have flagSome : (reify? language flag (.base "Result")).isSome = true := by
    decide +kernel
  have boxSome : (reify? language box (.base "Result")).isSome = true := by
    decide +kernel
  constructor
  · cases result : reify? language flag (.base "Result") with
    | none => simp [result] at flagSome
    | some term => exact reify?_typed result
  · cases result : reify? language box (.base "Result") with
    | none => simp [result] at boxSome
    | some term => exact reify?_typed result

theorem wrong_requested_sort_is_not_reified :
    reify? language flag (.base "Nat") = none := by decide +kernel

theorem wrong_argument_sort_is_not_reified :
    reify? language wrongInput (.base "Result") = none := by decide +kernel

theorem swapped_sorted_arguments_are_not_reified :
    reify? language (.apply "Pair" [count, truth]) (.base "Result") = none := by
  decide +kernel

theorem wrong_arity_is_not_reified :
    reify? language (.apply "Pair" [truth]) (.base "Result") = none := by
  decide +kernel

theorem undeclared_label_is_not_reified :
    reify? language (.apply "Invented" []) (.base "Result") = none := by
  decide +kernel

theorem authored_mistyped_input_is_firstOrder :
    compilePattern? mistypedRewrite.left ≠ none := by decide +kernel

theorem authored_mistyped_input_is_not_typed :
    ¬ HasType language FreeTypeContext.empty [] mistypedRewrite.left (.base "Result") := by
  intro typed
  have found := reify?_complete typed authored_mistyped_input_is_firstOrder
  change (reify? language wrongInput (.base "Result")).isSome = true at found
  rw [wrong_argument_sort_is_not_reified] at found
  cases found

theorem validation_does_not_supply_typed_reification :
    language.validate = [] ∧ mistypedRewrite ∈ language.rewrites ∧
    compilePattern? mistypedRewrite.left ≠ none ∧
    ¬ HasType language FreeTypeContext.empty [] mistypedRewrite.left (.base "Result") := by
  exact ⟨language_valid, by simp [language, LanguageDef.ofCore],
    authored_mistyped_input_is_firstOrder, authored_mistyped_input_is_not_typed⟩

/-- This binder-containing term is typed by the original judgment but is not
first-order; codec nonacceptance here is not a language typing rejection. -/
theorem typed_lambda_is_outside_the_codec :
    HasType language FreeTypeContext.empty [] (.lambda none (.bvar 0))
        (.arrow (.base "Bool") (.base "Bool")) ∧
    compilePattern? (.lambda none (.bvar 0)) = none ∧
    reify? language (.lambda none (.bvar 0))
        (.arrow (.base "Bool") (.base "Bool")) = none := by
  exact ⟨.lambda (.bvar rfl), rfl, by simp [reify?]⟩

/-! ## A compiled authored equation reaches its actual context category -/

open Mettapedia.GSLT.LanguageDef.BindingSyntax.EquationPresentation
open Mettapedia.GSLT.LanguageDef.BindingSyntax.OpenReification
open Mettapedia.GSLT.LanguageDef.NamedFreeContext

def boxEquation : Equation where
  name := "BoxCount"
  typeContext := [("x", .base "Nat")]
  premises := []
  left := .apply "Box" [.fvar "x"]
  right := box

/-- Reuse the declared constructors, with the equation authored in the
language itself and no deliberately mistyped rewrite in this fixture. -/
def equationLanguage : LanguageDef :=
  { language with rewrites := [], equations := [boxEquation] }

def compiledBox : CompiledRow equationLanguage boxEquation (.base "Result") :=
  (compile? equationLanguage boxEquation (.base "Result")).get (by decide +kernel)

theorem compiled_equation_is_authored : boxEquation ∈ equationLanguage.equations := by
  simp [equationLanguage]

theorem compiled_terms_distinct : compiledBox.left ≠ compiledBox.right := by
  intro same
  have named := congrArg
    (namedFirstOrderErase? (names boxEquation.typeContext)) same
  rw [compiledBox.left_named, compiledBox.right_named] at named
  cases named

theorem raw_arrows_distinct : compiledBox.leftArrow ≠ compiledBox.rightArrow := by
  intro same
  exact compiled_terms_distinct (congrFun same (0 : Fin 1))

/-- A substantive equation identifies two distinct generated arrows. -/
theorem actual_quotient_identifies_authored_equation :
    compiledBox.leftArrow ≠ compiledBox.rightArrow ∧
    compiledBox.contextPresentation.map compiledBox.leftArrow =
      compiledBox.contextPresentation.map compiledBox.rightArrow :=
  ⟨raw_arrows_distinct, compiledBox.equation_arrows_equal⟩

theorem equation_wrong_sort_rejected :
    compile? equationLanguage boxEquation (.base "Nat") = none := by decide +kernel

theorem erased_schema_context_rejected :
    (compile? equationLanguage {boxEquation with typeContext := []}
      (.base "Result")).isSome = false := by decide +kernel

theorem side_condition_not_silently_erased :
    (compile? equationLanguage
      {boxEquation with premises := [.congruence count count]}
      (.base "Result")).isSome = false := by decide +kernel

theorem binding_metadata_not_silently_erased :
    (compile? equationLanguage
      {boxEquation with bindings := some ⟨[("x", [.base "Nat"])], []⟩}
      (.base "Result")).isSome = false := by decide +kernel

def proseTokens : String ≃ String := Equiv.swap "count" "number"

theorem concrete_notation_really_changes :
    (Mettapedia.GSLT.Parsing.GrammarPresentationTransport.mapLanguage
      proseTokens equationLanguage).terms ≠ equationLanguage.terms := by decide +kernel

/-- This body came from the authored, sorted open equation. The enclosing
lambda introduces its declared input, rather than erasing its binding. -/
def boundBox : Term (signatureOf equationLanguage) []
    (.arrow (.base "Nat") (.base "Result")) :=
  .op (.lambda (.base "Nat") (.base "Result")) (.cons compiledBox.left .nil)

theorem binding_and_free_schema_survive_notation :
    Notation.untransport proseTokens (Notation.transport proseTokens boundBox) = boundBox ∧
    Notation.untransport proseTokens (Notation.transport proseTokens compiledBox.left) =
      compiledBox.left :=
  ⟨Notation.untransport_transport proseTokens boundBox,
    Notation.untransport_transport proseTokens compiledBox.left⟩

private def illShapedBinderRule : GrammarRule where
  label := "IllShapedBinder"
  category := "Bool"
  params := [.abstractionNamed none "body" (.collection .vec (.base "Bool"))]
  syntaxPattern := [.nonTerminal "body"]

private def illShapedBinderLanguage : LanguageDef :=
  LanguageDef.ofCore "IllShapedBinderControl" ["Bool"] [illShapedBinderRule] [] []

theorem validation_does_not_supply_parameter_shape :
    illShapedBinderLanguage.validate = [] ∧
    parameterType? (illShapedBinderRule.params.get ⟨0, by decide⟩) = none := by cbv

end Mettapedia.GSLT.LanguageDef.BindingSyntax.Reification.Controls
