import Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTyping

/-! # Actual module replacement typing and representation controls -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTypingControls

open Mettapedia.OSLF.MeTTaIL.Syntax WellSorted

def a : TypeExpr := .base "A"
def b : TypeExpr := .base "B"

def atom (name sort : String) : GrammarRule :=
  { label := name, category := sort, params := [], syntaxPattern := [] }

def original : GrammarRule :=
  { label := "K", category := "A", params := [.simple "x" a, .simple "y" b], syntaxPattern := [] }

def reordered : GrammarRule :=
  { original with label := "L", params := [.simple "y" b, .simple "x" a] }

def value : Value :=
  { entries := [newItem 0 .sort "A" (.sort "A"), newItem 0 .sort "B" (.sort "B"),
      newItem 0 .term "A0" (.term (atom "A0" "A")),
      newItem 0 .term "B0" (.term (atom "B0" "B")),
      newItem 0 .term "K" (.term original)] }

def after := replaceRow value ⟨"K", reordered⟩
def language := flattenRaw "Reordered" (after.toOption.getD value)
def arguments : List Pattern := [.apply "A0" [], .apply "B0" []]

theorem reordering_accepted : after.isOk = true := by decide +kernel

theorem result_sort_change_refused :
    replaceRow value ⟨"K", { reordered with category := "B" }⟩ =
      .error (.replaceTyping "K" "L") := by rfl

theorem argument_type_change_refused :
    replaceRow value ⟨"K", { reordered with params := [.simple "y" a, .simple "x" a] }⟩ =
      .error (.replaceTyping "K" "L") := by rfl

def functional : GrammarRule :=
  { original with params := [.simple "body" (.arrow a a)] }

def binding : GrammarRule :=
  { functional with label := "Binder", params := [.abstractionNamed none "body" a] }

theorem equal_arrow_type_does_not_authorize_binder_change :
    functional.params.head?.bind parameterType? = some (.arrow a a) ∧
      binding.params.head?.bind parameterType? = some (.arrow a a) ∧
      checkReplacementTyping functional binding = false := by decide +kernel

def shorthandBinder : GrammarRule :=
  { binding with params := [.abstractionNamed (some "x") "body" a] }

def explicitBinder : GrammarRule :=
  { binding with params := [.abstractionNamed (some "renamed") "body" (.arrow a a)] }

theorem binder_display_and_type_shorthand_preserved :
    checkReplacementTyping shorthandBinder explicitBinder = true := by decide +kernel

def homogeneous : GrammarRule :=
  { original with params := [.simple "x" a, .simple "y" a] }

def packed : GrammarRule :=
  { label := "Bag", category := "A", params := [.simple "items" (.collection .hashBag a)],
    syntaxPattern := [] }

theorem homogeneous_collection_profile : checkReplacementTyping homogeneous packed = true := by decide +kernel

theorem heterogeneous_collection_profile_refused :
    checkReplacementTyping original packed = false := by decide +kernel

theorem changed_collection_result_refused :
    checkReplacementTyping homogeneous { packed with category := "B" } = false := by decide +kernel

/-- Explicit sort export still renames the declaration and its parameter
sorts together. It does not pass through constructor replacement. -/
theorem explicit_sort_export_remains_available :
    (exportRow value ⟨"A", some "RenamedA"⟩).toOption.map
      (fun changed => ((flattenRaw "Renamed" changed).terms.find? (·.label == "K")).map
        (fun rule => (rule.category, rule.params))) =
      some (some ("RenamedA", [.simple "x" (.base "RenamedA"), .simple "y" b])) := by decide +kernel

theorem source_argument_spine_typed :
    ArgumentsHaveTypes language (fun _ => none) [] arguments original.params := by
  apply checkArgumentsHaveTypes_sound_of
    (fun _ _ _ checked => checkHasType_sound checked)
  decide +kernel

theorem actual_reordered_spine_typed :
    ArgumentsHaveTypes language (fun _ => none) []
      [.apply "B0" [], .apply "A0" []] reordered.params := by
  have actual : argumentMap original reordered = some
      (fun args => [args[1]?.getD (.fvar "y"), args[0]?.getD (.fvar "x")]) := by
    rfl
  exact argumentMap_named_typed (by decide +kernel) (by decide +kernel)
    source_argument_spine_typed actual

theorem actual_reordering_retains_occurrences :
    [.apply "B0" [], .apply "A0" []].Perm arguments := by
  have actual : argumentMap original reordered = some
      (fun args => [args[1]?.getD (.fvar "y"), args[0]?.getD (.fvar "x")]) := by rfl
  exact argumentMap_named_occurrences (arguments := arguments) (by decide +kernel) rfl actual

theorem equal_payload_packing_is_typed :
    ArgumentsHaveTypes language (fun _ => none) []
      [.collection .hashBag [.apply "A0" [], .apply "A0" []] none] packed.params := by
  have sourceTyped : ArgumentsHaveTypes language (fun _ => none) []
      [.apply "A0" [], .apply "A0" []] homogeneous.params := by
    apply checkArgumentsHaveTypes_sound_of (fun _ _ _ checked => checkHasType_sound checked)
    decide +kernel
  have actual : argumentMap homogeneous packed = some (fun args => [.collection .hashBag args none]) := by rfl
  exact argumentMap_typed (by decide +kernel) sourceTyped actual

theorem reordered_constructor_checks :
    checkHasType language (fun _ => none) []
      (.apply "L" [.apply "B0" [], .apply "A0" []]) a = true ∧
      checkHasType language (fun _ => none) []
        (.apply "L" [.apply "A0" [], .apply "B0" []]) a = false := by decide +kernel

def unitDeclaration : GrammarRule := atom "One" "A"

def foldDeclaration : GrammarRule :=
  { label := "Fold", category := "A", params := [.simple "items" (.collection .vec a)],
    syntaxPattern := [.terminal "One", .nonTerminal "items"],
    algebra? := some { flatten := true, unit := some "One" } }

def otherDeclaration : GrammarRule :=
  { label := "OtherFold", category := "A", params := [.simple "items" (.collection .hashBag a)],
    syntaxPattern := [], algebra? := some { flatten := false, unit := some "OneMore" } }

def unitValue : Value :=
  { entries := [newItem 0 .sort "A" (.sort "A"),
      newItem 0 .term "One" (.term unitDeclaration),
      newItem 0 .term "OneMore" (.term (atom "OneMore" "A")),
      newItem 0 .term "Fold" (.term foldDeclaration),
      newItem 0 .term "OtherFold" (.term otherDeclaration)] }

def unitReplacement : Replacement := ⟨"One", { unitDeclaration with label := "Zero" }⟩
def unitResult? := replaceRow unitValue unitReplacement
def unitResult := unitResult?.toOption.getD unitValue
def unitLanguage := flattenRaw "RenamedUnit" unitResult

def algebraReadout (value : Value) : List (String × Bool × Option String) :=
  (flattenRaw "" value).terms.filterMap fun rule =>
    rule.algebra?.map fun algebra => (rule.label, algebra.flatten, algebra.unit)

theorem actual_unit_replacement_succeeds : unitResult?.isOk = true := by decide +kernel

theorem renamed_unit_and_unrelated_reference :
    algebraReadout unitResult = [("Fold", true, some "Zero"), ("OtherFold", false, some "OneMore")] := by
  decide +kernel

theorem unit_replacement_keeps_origins :
    unitResult.entries.map (·.origin) = unitValue.entries.map (·.origin) := by decide +kernel

theorem literal_syntax_is_not_a_unit_reference :
    (unitLanguage.terms.find? (·.label == "Fold")).map (·.syntaxPattern) =
      some [.terminal "One", .nonTerminal "items"] := by decide +kernel

theorem renamed_unit_checks_and_old_unit_does_not :
    checkHasType unitLanguage (fun _ => none) [] (.apply "Zero" []) a = true ∧
      checkHasType unitLanguage (fun _ => none) [] (.apply "One" []) a = false := by decide +kernel

theorem normalization_uses_renamed_unit :
    Mettapedia.OSLF.MeTTaIL.CollectionLaws.standardForm
      (Mettapedia.OSLF.MeTTaIL.CollectionLaws.declared unitLanguage) []
      (.collection .vec [.apply "Zero" [], .apply "OneMore" []] none) =
        .collection .vec [.apply "OneMore" []] none := by cbv

def unitRenamedTwice? := replaceRow unitResult ⟨"Zero", { unitDeclaration with label := "Nil" }⟩

theorem sequential_unit_replacement_follows_identity :
    unitRenamedTwice?.isOk = true ∧
      unitRenamedTwice?.toOption.map algebraReadout =
        some [("Fold", true, some "Nil"), ("OtherFold", false, some "OneMore")] := by decide +kernel

theorem colliding_unit_rename_refused :
    (replaceRow unitValue ⟨"One", atom "OneMore" "A"⟩).isOk = false := by decide +kernel

end Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTypingControls
