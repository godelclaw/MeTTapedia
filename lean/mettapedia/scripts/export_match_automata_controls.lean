import Mettapedia.GSLT.LanguageDef.MatchAutomataControls
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderContextualExecution
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleTraceExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ContextualRuleExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution

/-! Export one shared semantic corpus and its exact Lean results to MeTTa. -/

open Mettapedia.GSLT.LanguageDef
open MatchAutomataControls MeTTaILSubtermMatchAutomata
open MeTTaILFirstOrderRuleCompilation
open CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataDerivativeExecution
  (obligationTerm goalTerm locationTerm finishedTerm)
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataExecution
  (matchRunTerm)

namespace RuleControls

open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.Controls

def renderTextObservationFor (family name query : String) (expected : String) : String :=
  "!(let $actual " ++ query ++ "\n" ++
    "  (println! (" ++ family ++ " " ++ (Term.string name).render ++
    " (== $actual (quote " ++ expected ++ ")))))\n"

def renderTextObservation (name query : String) (expected : Term) : String :=
  renderTextObservationFor "RuleExecutionControl" name query expected.render

def renderObservation (name : String) (query expected : Term) : String :=
  renderTextObservation name query.render expected

def render (fixture : Fixture) : String :=
  renderObservation fixture.name fixture.queryTerm fixture.expectedTerm

def renderWrongObservationFor (family name : String) (query incorrect : Term) : String :=
  "!(let $actual " ++ query.render ++ "\n" ++
    "  (println! (" ++ family ++ " " ++ (Term.string name).render ++
    " (== (== $actual (quote " ++ incorrect.render ++ ")) False))))\n"

def renderWrongObservation (name : String) (query incorrect : Term) : String :=
  renderWrongObservationFor "RuleExecutionControl" name query incorrect

def renderRefusal (control : Fixture × Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) : String :=
  renderWrongObservation ("refuse-" ++ control.1.name) control.1.queryTerm
    (InferenceCettaWire.encodePattern control.2)

def renderGeneralRefusal (control : ObservationFixture × Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) : String :=
  renderWrongObservation ("refuse-" ++ control.1.name) control.1.queryTerm
    (InferenceCettaWire.encodePattern control.2)

def renderWrongListObservation (name : String) (query : Term)
    (incorrect : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) : String :=
  renderWrongObservation name query (InferenceCettaWire.encodePatterns incorrect)

def rowLookupControls : List String :=
  let values := [Term.symbol "first", .symbol "second", .symbol "second"]
  [0, 2, 3].map fun index =>
    let selected := match values[index]? with
      | none => Term.symbol "None"
      | some value => .application "Some" [value]
    renderObservation ("physical-row-lookup-" ++ toString index)
      (.application "gslt:rule:row-at" [.natural index, encodeList id values]) selected

def payloadLookupControls : List String :=
  let fixtures : List (String × String × List (String × Term)) :=
    [("opaque-call-payload", "payload", [("payload", .application "+" [.natural 2, .natural 3])]),
     ("duplicate-name-keeps-first-payload", "payload",
       [("payload", .symbol "first"), ("payload", .symbol "later")]),
     ("missing-payload-is-none", "missing", [("payload", .symbol "present")])]
  fixtures.map fun (label, name, bindings) =>
    let expected :=
      Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataBindingExecution.payloadOptionTerm
        (Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataBindingExecution.payloadLookup bindings name)
    renderObservation ("payload-lookup-" ++ label)
      (.application "gslt:automata:binding" [.string name,
        Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataBindingExecution.payloadBindingsTerm bindings])
      expected

def traceBatchControls : List String := Id.run do
  let fixture := Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleTraceExecution.Controls.fixture
  let state := Mettapedia.Languages.MeTTa.PeTTa.Effects.empty
  let route := Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleTraceExecution.Controls.path state
  let queries := Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleTraceExecution.queryTerms
    state fixture.language (.symbol "LNil") (.symbol "LNil") (fun _ => .symbol "LNil")
    fixture.compiled fixture.rows route
  let expected := Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleTraceExecution.Controls.expectedFrontiers
  let renderAnswers := fun (answers : List Term) => "(" ++ String.intercalate " " (answers.map Term.render) ++ ")"
  let query := "(collapse (superpose " ++ renderAnswers queries ++ "))"
  let positive := "!(let $actual " ++ query ++ "\n" ++
    "  (println! (RuleExecutionControl \"finite-path-ordered-batch\" (== $actual " ++ renderAnswers expected ++ "))))\n"
  let negative := "!(let $actual " ++ query ++ "\n" ++
    "  (println! (RuleExecutionControl \"refuse-reversed-finite-path-observations\" (== (== $actual " ++
      renderAnswers expected.reverse ++ ") False))))\n"
  let empty := "!(let $actual (collapse (superpose ()))\n" ++
    "  (println! (RuleExecutionControl \"finite-empty-path-batch\" (== $actual ()))))\n"
  return [positive, negative, empty]

/-- Both strategies consume the same authored contexts and canonical results.
The ordinary wire renderer retains premises instead of compiling child matches
into unconditional rewrites. -/
def contextualControls : IO (List String) := do
  let source := MeTTaILFirstOrderContextualExecution.Controls.language
  let subject := MeTTaILFirstOrderContextualExecution.Controls.subject
  let rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow :=
    [⟨"allow", [MeTTaILFirstOrderContextualExecution.Controls.start]⟩,
     ⟨"allow", [MeTTaILFirstOrderContextualExecution.Controls.start]⟩]
  let fixtures :=
    [("recursive-witnesses", source, [], 2, subject),
     ("zero-depth", source, [], 0, subject),
     ("exhausted-depth", source, [], 1, subject),
     ("extra-depth", source, [], 4, subject),
     ("unauthorized-child", MeTTaILFirstOrderContextualExecution.Controls.childOnlyLanguage,
       [], 4, subject),
     ("conflicting-target-seed", MeTTaILFirstOrderContextualExecution.Controls.conflictingLanguage,
       [], 2, subject),
     ("missing-guard", MeTTaILFirstOrderContextualExecution.Controls.guardedLanguage,
       [], 2, subject),
     ("guard-times-recursive-witnesses", MeTTaILFirstOrderContextualExecution.Controls.guardedLanguage,
       rows, 2, subject),
     ("nested-exhausted-depth", source, [], 2, PatternPlan.application "Box" [subject]),
     ("nested-authorized-context", source, [], 3, PatternPlan.application "Box" [subject]),
     ("root-ordered-occurrences", source, [], 1, PatternPlan.application "Start" []),
     ("freshness-duplicate-rules", MeTTaILFirstOrderContextualExecution.Controls.freshnessLanguage,
       [], 1, .application "Fresh" [.application "Pair" [.metavariable "other", .metavariable "other"]]),
     ("freshness-nonfresh", MeTTaILFirstOrderContextualExecution.Controls.freshnessLanguage,
       [], 1, .application "Fresh" [.application "Pair" [.metavariable "other", .metavariable "atom"]]),
     ("freshness-captured-name", MeTTaILFirstOrderContextualExecution.Controls.resolvedFreshnessLanguage,
       [], 1, .application "FreshName" [.metavariable "actual", .metavariable "other"]),
     ("freshness-captured-nonfresh", MeTTaILFirstOrderContextualExecution.Controls.resolvedFreshnessLanguage,
       [], 1, .application "FreshName" [.metavariable "actual", .metavariable "actual"]),
     ("freshness-nonname", MeTTaILFirstOrderContextualExecution.Controls.resolvedFreshnessLanguage,
       [], 1, .application "FreshName" [.application "NotAName" [], .metavariable "other"]),
     ("query-before-freshness", MeTTaILFirstOrderContextualExecution.Controls.nameGuardLanguage true,
       Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ContextualRuleExecution.Controls.nameGuardRows,
       1, .application "Fresh" [.metavariable "actual"]),
     ("freshness-before-query", MeTTaILFirstOrderContextualExecution.Controls.nameGuardLanguage false,
       Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ContextualRuleExecution.Controls.nameGuardRows,
       1, .application "Fresh" [.metavariable "actual"])]
  let mut controls := []
  for strategy in [MeTTaILMatchAutomataExecution.Strategy.bottomUp, .topDown] do
    let label := match strategy with | .bottomUp => "bottom-" | .topDown => "top-"
    let head := "gslt:rule:language-contextual-" ++ label ++ "reducts"
    for (name, language, providers, depth, input) in fixtures do
      let some wire := CanonicalWire.renderLanguage? language
        | throw (IO.userError s!"contextual fixture {name} is outside the canonical wire profile")
      let query := "(" ++ head ++ " " ++ wire ++ " " ++
        (Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution.providerRowsTerm providers).render ++
        " " ++ toString depth ++ " " ++ Term.render (InferenceCettaWire.encodePattern input.erase) ++ ")"
      let expected := MeTTaILMatchAutomataExecution.runAt strategy
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
          (Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution.providerEnv providers))
        language depth input
      controls := controls ++ [renderTextObservation ("contextual-" ++ label ++ name)
        query (InferenceCettaWire.encodePatterns expected)]
  return controls

def write (output : String) : IO Unit := do
  let contexts ← contextualControls
  let observations := observationFixtures.map fun fixture =>
    renderObservation fixture.name fixture.queryTerm fixture.expectedTerm
  let general := generalFixtures.map fun fixture =>
    renderObservation fixture.name fixture.queryTerm fixture.expectedTerm
  let wrongGeneral := incorrectGeneralResults.map renderGeneralRefusal
  let scopeObservations :=
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.ScopedCapture.Controls.fixtures.map
      fun fixture => renderObservation ("scoped-" ++ fixture.name) fixture.queryTerm fixture.expectedTerm
  let wrongScoped :=
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.ScopedCapture.Controls.incorrectResults.map
      fun (fixture, incorrect) =>
        renderWrongObservation ("refuse-scoped-" ++ fixture.name) fixture.queryTerm incorrect
  let relationFixtures :=
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution.Controls.fixtures ++
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution.Controls.preparationFixtures ++
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution.Controls.premiseFixtures
  let relations := relationFixtures.map
      fun fixture => renderObservation ("relation-" ++ fixture.name) fixture.queryTerm fixture.expectedTerm
  let roots :=
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution.Controls.fixtures.map
      fun fixture => renderObservation fixture.name fixture.queryTerm fixture.expectedTerm
  let wrongRoots :=
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution.Controls.incorrectResults.zipIdx.map
      fun (control, index) =>
        renderWrongListObservation ("refuse-root-observation-" ++ toString index)
          control.1.queryTerm control.2
  let conditional :=
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution.Conditional.Controls.fixtures.map
      fun fixture => renderObservation fixture.name fixture.queryTerm fixture.expectedTerm
  let wrongConditional :=
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution.Conditional.Controls.incorrectResults.zipIdx.map
      fun (control, index) =>
        renderWrongListObservation ("refuse-conditional-observation-" ++ toString index)
          control.1.queryTerm control.2
  let matched := [MeTTaILMatchAutomataExecution.Strategy.bottomUp, .topDown].flatMap fun strategy =>
    let label := match strategy with | .bottomUp => "bottom-" | .topDown => "top-"
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution.Conditional.Controls.fixtures.map
      fun fixture => renderObservation (label ++ fixture.name)
        (Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution.Matched.Controls.queryTerm strategy fixture)
        fixture.expectedTerm
  let wrongMatched := [MeTTaILMatchAutomataExecution.Strategy.bottomUp, .topDown].flatMap fun strategy =>
    let label := match strategy with | .bottomUp => "bottom-" | .topDown => "top-"
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution.Conditional.Controls.incorrectResults.zipIdx.map
      fun (control, index) => renderWrongListObservation ("refuse-" ++ label ++ "matched-observation-" ++ toString index)
        (Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution.Matched.Controls.queryTerm strategy control.1) control.2
  let rawRefusals :=
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution.Controls.refusalFixtures.map
      fun fixture =>
        "!(let $actual (collapse " ++ fixture.queryTerm.render ++ ")\n" ++
        "  (println! (RuleExecutionControl " ++ (Term.string fixture.name).render ++
        " (== $actual ()))))\n"
  let drives :=
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleTraceExecution.Controls.driveFixtures.map
      fun control => renderObservation ("drive-" ++ control.1)
        (Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleTraceExecution.Controls.driveQuery
          control.2.1 control.2.2.1) control.2.2.2
  let wrongDrives :=
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleTraceExecution.Controls.driveRefusals.map
      fun control => renderWrongObservation ("refuse-drive-" ++ control.1) control.2.1 control.2.2
  let scopedMetadata :=
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.ScopedMetadata.Controls.fixtures.map
      fun fixture => renderTextObservationFor "ScopedMetadataControl" fixture.name
        fixture.queryTerm.render fixture.expectedTerm.render
  let wrongMetadata :=
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.ScopedMetadata.Controls.incorrectResults.zipIdx.map
      fun (control, index) => renderWrongObservationFor "ScopedMetadataControl"
        ("refuse-metadata-observation-" ++ toString index) control.1.queryTerm control.2
  let text := "; Generated from the proved rule-operation fixtures and their canonical results.\n" ++
    String.join (fixtures.map render) ++ String.join (incorrectResults.map renderRefusal) ++
    String.join observations ++ String.join general ++ String.join wrongGeneral ++
    String.join scopeObservations ++ String.join wrongScoped ++
    String.join relations ++ String.join roots ++
    String.join wrongRoots ++ String.join rawRefusals ++ String.join conditional ++ String.join wrongConditional ++
    String.join matched ++ String.join wrongMatched ++ String.join rowLookupControls ++
    String.join payloadLookupControls ++ String.join traceBatchControls ++
    String.join drives ++ String.join wrongDrives ++ String.join contexts ++
    String.join scopedMetadata ++ String.join wrongMetadata
  IO.FS.writeFile output text
  IO.println s!"Exported {fixtures.length + incorrectResults.length + observations.length + general.length + wrongGeneral.length + scopeObservations.length + wrongScoped.length + relations.length + roots.length + wrongRoots.length + rawRefusals.length + conditional.length + wrongConditional.length + matched.length + wrongMatched.length + rowLookupControls.length + payloadLookupControls.length + traceBatchControls.length + drives.length + wrongDrives.length + contexts.length + scopedMetadata.length + wrongMetadata.length} exact rule and scoped metadata controls ({text.utf8ByteSize} bytes)."

end RuleControls

namespace ModuleControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open ModuleAlgebra.NativeAuthoring

private def renderList (rows : List String) : String :=
  rows.foldr (fun row rest => "(LCons " ++ row ++ " " ++ rest ++ ")") "LNil"

private def languageText (language : LanguageDef) : IO String := do
  let some rendered := CanonicalWire.renderLanguage? language
    | throw (IO.userError s!"module fixture {language.name} is outside the canonical wire profile")
  return rendered

private def fragmentText (fragments : List LanguageDef) : IO String := do
  return renderList (← fragments.mapM languageText)

private def observe (name query expected : String) : String :=
  RuleControls.renderTextObservationFor "ModuleExecutionControl" name query expected

private def assemblyControls : IO (List String) := do
  let source := MeTTaILFirstOrderContextualExecution.Controls.language
  let empty := LanguageDef.empty "Empty"
  let first : LanguageDef := { empty with name := "First", rewrites := source.rewrites.take 2 }
  let last : LanguageDef := { empty with name := "Last", rewrites := source.rewrites.drop 2 }
  let syntaxFragment : LanguageDef :=
    { empty with
      name := "Syntax"
      types := [⟨"Term", .ast⟩]
      terms := [{ label := "Start", category := "Term", params := [], syntaxPattern := [.terminal "start"] }] }
  let fixtures :=
    [("empty", []), ("split-core", splitCore source),
     ("empty-between-fragments", [empty, first, empty, last, empty]),
     ("duplicate-physical-rows", [first, empty, first]),
     ("staged-assembly", [assembleRaw "Left" [first, empty], assembleRaw "Right" [last]]),
     ("signature-retained", syntaxFragment :: splitCore source),
     ("local-names-do-not-override", [{ first with name := "Other" }, { last with name := "Other" }]),
     ("all-empty", [empty, empty, empty])]
  fixtures.mapM fun (name, fragments) => do
    let inputs ← fragmentText fragments
    let expected ← languageText (assembleRaw "Assembled" fragments)
    return observe ("assemble-" ++ name) ("(gslt:module:assemble \"Assembled\" " ++ inputs ++ ")")
      ("(Some " ++ expected ++ ")")

private def executionControls : IO (List String) := do
  let source := MeTTaILFirstOrderContextualExecution.Controls.language
  let guarded := MeTTaILFirstOrderContextualExecution.Controls.guardedLanguage
  let subject := MeTTaILFirstOrderContextualExecution.Controls.subject
  let empty := LanguageDef.empty "Empty"
  let children : LanguageDef := { empty with rewrites := source.rewrites.take 3 }
  let wrapper : LanguageDef := { empty with rewrites := source.rewrites.drop 3 }
  let guardedWrapper : LanguageDef := { empty with rewrites := guarded.rewrites.drop 3 }
  let rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow :=
    [⟨"allow", [MeTTaILFirstOrderContextualExecution.Controls.start]⟩,
     ⟨"allow", [MeTTaILFirstOrderContextualExecution.Controls.start]⟩]
  let fresh := MeTTaILFirstOrderContextualExecution.Controls.freshnessLanguage
  let freshSubject := PatternPlan.application "Box"
    [.application "Fresh" [.application "Pair" [.metavariable "other", .metavariable "other"]]]
  let nonfreshSubject := PatternPlan.application "Box"
    [.application "Fresh" [.application "Pair" [.metavariable "other", .metavariable "atom"]]]
  let nameSubject := PatternPlan.application "Box" [.application "Fresh" [.metavariable "actual"]]
  let nameRows :=
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ContextualRuleExecution.Controls.nameGuardRows
  let fixtures :=
    [("recursive-witness-crosses-fragments", [children, wrapper], [], 2, subject),
     ("duplicate-wrapper-occurrences", [children, wrapper, empty, wrapper], [], 2, subject),
     ("missing-recursive-witness", [wrapper], [], 3, subject),
     ("missing-context-permission", [children], [], 3, subject),
     ("guard-and-recursion-cross-fragments", [children, empty, guardedWrapper], rows, 2, subject),
     ("exhausted-recursive-depth", [children, wrapper], [], 1, subject),
     ("freshness-witness-crosses-fragments", [fresh, wrapper], [], 2, freshSubject),
     ("freshness-retains-duplicate-wrapper-occurrences", [fresh, wrapper, wrapper], [], 2, freshSubject),
     ("nonfresh-recursive-witness-refused", [fresh, wrapper], [], 2, nonfreshSubject),
     ("freshness-does-not-authorize-context", [fresh], [], 3, freshSubject),
     ("freshness-before-query-crosses-fragments",
       [MeTTaILFirstOrderContextualExecution.Controls.nameGuardLanguage false, wrapper],
       nameRows, 2, nameSubject),
     ("query-before-freshness-refuses-recursive-witness",
       [MeTTaILFirstOrderContextualExecution.Controls.nameGuardLanguage true, wrapper],
       nameRows, 2, nameSubject)]
  let mut result := []
  for strategy in [MeTTaILMatchAutomataExecution.Strategy.bottomUp, .topDown] do
    let strategyName := match strategy with | .bottomUp => "MatchBottomUp" | .topDown => "MatchTopDown"
    for (name, fragments, providers, depth, inputSubject) in fixtures do
      let input ← fragmentText fragments
      let query := "(gslt:module:reducts \"Assembled\" " ++ input ++ " " ++ strategyName ++ " " ++
        (Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution.providerRowsTerm providers).render ++
        " " ++ toString depth ++ " " ++ Term.render (InferenceCettaWire.encodePattern inputSubject.erase) ++ ")"
      let expected := MeTTaILMatchAutomataExecution.runAt strategy
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
          (Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution.providerEnv providers))
        (assembleRaw "Assembled" fragments) depth inputSubject
      result := result ++ [observe (strategyName ++ "-" ++ name) query
        (Term.render (InferenceCettaWire.encodePatterns expected))]
  return result

private def refusalControls : IO (List String) := do
  let empty ← languageText (LanguageDef.empty "Empty")
  let bad := ["(LCons BrokenFragment LNil)", "BrokenTail",
    "(LCons (GSLTLanguageDefWireV1 \"MissingField\" LNil LNil LNil) LNil)",
    "(LCons " ++ empty ++ " (LCons BrokenFragment LNil))"]
  return bad.zipIdx.map fun (fragments, index) =>
    observe ("malformed-fragment-" ++ toString index)
      ("(gslt:module:assemble \"Assembled\" " ++ fragments ++ ")") "None"

/-- Assembly treats supplied payloads as data; these controls retain equation
rows without claiming that an equation wire has operational admission. -/
private def payloadControls : List String :=
  let first : List Term := [.symbol "first-type", .symbol "first-syntax", .symbol "same-equation", .symbol "first-rewrite"]
  let second : List Term := [.symbol "second-type", .symbol "second-syntax", .symbol "same-equation", .symbol "second-rewrite"]
  let wire := fun (name : String) (rows : List Term) =>
    Term.application "GSLTLanguageDefWireV1" (.string name :: rows.map (fun row => encodeList id [row]))
  let all := [wire "Left" first, wire "Right" second]
  let assembled := Term.application "GSLTLanguageDefWireV1"
    (.string "Assembled" :: (first.zip second).map (fun (left, right) => encodeList id [left, right]))
  [observe "opaque-all-row-families"
    (.application "gslt:module:assemble" [.string "Assembled", encodeList id all] : Term).render
    (.application "Some" [assembled] : Term).render,
   observe "opaque-duplicate-equation-occurrences"
    (.application "gslt:module:assemble" [.string "Assembled", encodeList id [wire "Left" first, wire "Left" first]] : Term).render
    (.application "Some" [.application "GSLTLanguageDefWireV1"
      (.string "Assembled" :: first.map (fun row => encodeList id [row, row]))] : Term).render]

private def importControls : List String := Id.run do
  let entry := fun (origin label body : String) =>
    (⟨.string origin, .string label, .symbol body⟩ : ModuleAlgebra.Entry Term Term Term)
  let shared := entry "Shared" "shared" "SharedBody"
  let left := entry "Left" "left" "LeftBody"
  let right := entry "Right" "right" "RightBody"
  let renamed := entry "Shared" "renamed" "SharedBody"
  let changed := entry "Shared" "shared" "ChangedBody"
  let collision := entry "Other" "shared" "SharedBody"
  let fixtures :=
    [("empty", [], []), ("diamond", [shared, left], [shared, right]),
     ("same-fragment-twice", [shared, left], [shared, left]),
     ("first-seen-order", [left, shared], [right, shared, left]),
     ("duplicate-within-fragment", [shared, shared, left], [right, right]),
     ("label-collision", [shared], [collision]),
     ("shared-body-conflict", [shared], [changed]),
     ("distinct-view-at-shared-origin", [shared], [renamed]),
     ("late-conflict", [shared, left], [right, shared, changed])]
  let mut result := []
  for contract in [ImportContract.coherentOrigin, .structuralView] do
    let mode := contract.wireTerm
    for (name, first, second) in fixtures do
      let query := Term.application "gslt:module:join"
        [mode, encodeList importEntryTerm first, encodeList importEntryTerm second]
      let expected := match contract.join? first second with
        | none => Term.symbol "None"
        | some entries => .application "Some" [encodeList importEntryTerm entries]
      result := result ++ [observe (mode.render ++ "-" ++ name) query.render expected.render]
  let malformed :=
    [("unknown-contract", "OtherContract", "LNil", "LNil"),
     ("malformed-entry", "CoherentOriginV1", "(LCons BrokenEntry LNil)", "LNil"),
     ("malformed-tail", "CoherentOriginV1", "LNil", "BrokenTail"),
     ("malformed-late-entry", "StructuralOriginViewV1",
       (encodeList importEntryTerm [shared]).render, "(LCons BrokenEntry LNil)")]
  result := result ++ malformed.map fun (name, mode, first, second) =>
    observe name ("(gslt:module:join " ++ mode ++ " " ++ first ++ " " ++ second ++ ")") "None"
  return result

private def checkedExecutionControls : IO (List String) := do
  let source := MeTTaILFirstOrderContextualExecution.Controls.language
  let subject := MeTTaILFirstOrderContextualExecution.Controls.subject
  let empty := LanguageDef.empty "Empty"
  let children : LanguageDef := { empty with name := "Children", rewrites := source.rewrites.take 3 }
  let wrapper : LanguageDef := { empty with name := "Wrapper", rewrites := source.rewrites.drop 3 }
  let changed : LanguageDef := { children with rewrites := [] }
  let body := fun (language : LanguageDef) =>
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataExecution.matchingProjectionTerm
      language (.symbol "LNil") (.symbol "LNil") (.symbol "LNil") (fun _ => .symbol "LNil")
      (fun rule => (Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ContextualRuleExecution.premisesTerm?
        rule.premises).getD (.symbol "LNil"))
  let catalogue := [children, wrapper, empty, changed]
  let entry := fun (origin label : String) (language : LanguageDef) =>
    (⟨.string origin, .string label, body language⟩ : ModuleAlgebra.Entry Term Term Term)
  let shared := entry "Shared" "children" children
  let left := entry "Left" "wrapper" wrapper
  let right := entry "Right" "empty" empty
  let duplicate := entry "OtherWrapper" "second-wrapper" wrapper
  let renamed := entry "Shared" "renamed-children" children
  let conflict := entry "Shared" "children" changed
  let collision := entry "OtherOrigin" "children" children
  let fixtures :=
    [("diamond-execution", [shared, left], [shared, right]),
     ("repeated-import-execution", [shared, left], [shared, left]),
     ("distinct-identities-retain-body-rules", [shared, left], [shared, duplicate]),
     ("missing-context-permission-after-join", [shared], [shared]),
     ("missing-child-witness-after-join", [left], [left]),
     ("late-conflict-refuses-execution", [shared, left], [right, shared, conflict]),
     ("label-collision-refuses-execution", [shared, left], [collision]),
     ("shared-origin-view-execution", [shared, left], [renamed])]
  let mut result := []
  for contract in [ImportContract.coherentOrigin, .structuralView] do
    for strategy in [MeTTaILMatchAutomataExecution.Strategy.bottomUp, .topDown] do
      for (name, first, second) in fixtures do
        let query := Term.application "gslt:module:import-reducts"
          [contract.wireTerm, .string "Assembled", encodeList importEntryTerm first,
           encodeList importEntryTerm second,
           Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ContextualRuleExecution.strategyTerm strategy,
           .symbol "LNil", .natural 2, InferenceCettaWire.encodePattern subject.erase]
        let expected ← match contract.join? first second with
          | none => pure (Term.symbol "None")
          | some kept => do
              let fragments ← kept.mapM fun retained => do
                let some language := catalogue.find? (fun language => body language == retained.body)
                  | throw (IO.userError "checked module control has an unregistered complete body")
                pure language
              pure (InferenceCettaWire.encodePatterns (MeTTaILMatchAutomataExecution.runAt strategy
                (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
                  (Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution.providerEnv []))
                (assembleRaw "Assembled" fragments) 2 subject))
        result := result ++ [observe (contract.wireTerm.render ++ "-" ++
          (Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ContextualRuleExecution.strategyTerm strategy).render ++
          "-" ++ name) query.render expected.render]
  let payloadCall := Term.application "+" [.natural 2, .natural 3]
  let opaqueEntry : ModuleAlgebra.Entry Term Term Term := ⟨.string "Opaque", .string "opaque", payloadCall⟩
  result := result ++ [observe "import-body-remains-opaque"
    (Term.application "gslt:module:bodies" [encodeList importEntryTerm [opaqueEntry]]).render
    (encodeList id [payloadCall]).render,
    observe "import-conflict-does-not-evaluate-strategy-or-subject"
      (Term.application "gslt:module:import-reducts"
        [ImportContract.coherentOrigin.wireTerm, .string "Assembled",
         encodeList importEntryTerm [shared], encodeList importEntryTerm [conflict],
         payloadCall, payloadCall, payloadCall, payloadCall]).render "None"]
  return result

def write (output : String) : IO Unit := do
  let controls := (← assemblyControls) ++ (← executionControls) ++ (← refusalControls) ++
    payloadControls ++ importControls ++ (← checkedExecutionControls)
  let text := "; Generated from complete-row module assembly and canonical contextual execution.\n" ++ String.join controls
  IO.FS.writeFile output text
  IO.println s!"Exported {controls.length} exact module controls ({text.utf8ByteSize} bytes)."

end ModuleControls

namespace PremiseControls

open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.Controls

def write (output : String) : IO Unit := do
  let exact := fixtures.map fun fixture =>
    RuleControls.renderTextObservationFor "PremiseOperationControl" fixture.name
      fixture.queryTerm.render fixture.expectedTerm.render
  let refused := incorrectResults.map fun test =>
    RuleControls.renderWrongObservationFor "PremiseOperationControl"
      ("refuse-" ++ test.1.name) test.1.queryTerm test.2
  let controls := exact ++ refused
  let text := "; Generated from canonical free-variable, freshness and lexical quantifier operations.\n" ++
    String.join controls
  IO.FS.writeFile output text
  IO.println s!"Exported {controls.length} exact premise-operation controls ({text.utf8ByteSize} bytes)."

end PremiseControls

def renderControl (control : Control) : String :=
  let patterns := encodeList InferenceCettaWire.encodePattern control.patterns |>.render
  let subject := Term.render (InferenceCettaWire.encodePattern control.subject.erase)
  let expected := reference control.patterns control.subject
  let bottom := matchRunTerm expected (bottomCounts control).1 (bottomCounts control).2 |>.render
  let top := matchRunTerm expected (topCounts control).1 (topCounts control).2 |>.render
  "!(let $bottom (gslt:automata:bottom " ++ patterns ++ " " ++ subject ++ ")\n" ++
    "  (let $top (gslt:automata:top " ++ patterns ++ " " ++ subject ++ ")\n" ++
    "    (println! (AutomataControl " ++ (Term.string control.name).render ++
    " (== $bottom " ++ bottom ++ ") (== $top " ++ top ++ ")))))\n"

def generatedSubject (seed : Nat) : Nat → PatternPlan
  | 0 => atom (if seed % 2 = 0 then "a" else "b")
  | depth + 1 =>
      if seed % 3 = 0 then app "pair" [generatedSubject (seed / 2) depth,
        generatedSubject (seed / 2) depth]
      else if seed % 3 = 1 then app "pair" [generatedSubject (seed + 1) depth,
        generatedSubject (seed + 2) depth]
      else app "g" [generatedSubject (seed / 2) depth]

def generatedControls : List Control :=
  (List.range 30).map fun seed =>
    ⟨"generated-" ++ toString seed,
      [repeated, pat "g" [.fvar "x"], pat "a" [], repeated, .fvar "whole"],
      generatedSubject seed 3⟩

def sharedControl : Control :=
  ⟨"shared-prefix-32", List.replicate 32 overlapA ++ [overlapB],
    app "f" [app "g" [atom "z"], atom "a"]⟩

def renderLanguageControl : Option String := do
  let source : Control := ⟨"language-wire", [overlapA, overlapB, overlapA],
    app "f" [app "g" [atom "z"], atom "a"]⟩
  let rules := source.patterns.zipIdx.map fun row =>
    Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule.mk
      ("rule-" ++ toString row.2) [] [] row.1 (.apply "done" []) none
  let language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef :=
    { name := "AutomataControl", types := [], terms := [], equations := [], rewrites := rules }
  let rendered ← CanonicalWire.renderLanguage? language
  let subject := Term.render (InferenceCettaWire.encodePattern source.subject.erase)
  let results := reference source.patterns source.subject
  pure ("!(let $bottom (gslt:automata:language-bottom " ++ rendered ++ " " ++ subject ++ ")\n" ++
    "  (let $top (gslt:automata:language-top " ++ rendered ++ " " ++ subject ++ ")\n" ++
    "    (println! (AutomataControl \"language-wire\" (== $bottom " ++
    (matchRunTerm results (bottomCounts source).1 (bottomCounts source).2).render ++ ") (== $top " ++
    (matchRunTerm results (topCounts source).1 (topCounts source).2).render ++ ")))))\n")

def renderStreamControl (control : Derivative.StreamControl) : String :=
  let executed := TopDownMatchDerivatives.executeCounted control.observations control.goals
  let locations := TopDownMatchDerivatives.completed executed.1
  let observations := (encodeList obligationTerm control.observations).render
  let goals := (encodeList goalTerm control.goals).render
  let expectedRun := (finishedTerm executed.1 (control.dispatches + executed.2)).render
  let expectedLocations := (encodeList locationTerm locations).render
  "!(let $run (gslt:automata:execute " ++ observations ++ " " ++ goals ++ " " ++
    toString control.dispatches ++ ")\n" ++
    "  (case $run (((MFinished $remaining $dispatches)\n" ++
    "    (println! (AutomataControl " ++ (Term.string control.name).render ++
    " (== $run " ++ expectedRun ++ ")\n" ++
    "      (== (gslt:automata:completed $remaining) " ++ expectedLocations ++ ")))))))\n"

def exportMatchControls (output : String) : IO Unit := do
  let all := controls ++ generatedControls ++ [sharedControl]
  let some languageControl := renderLanguageControl
    | throw (IO.userError "canonical LanguageDef fixture is not renderable")
  let text := "; Generated from MatchAutomataControls and the canonical Lean binding matcher.\n" ++
    String.join (all.map renderControl) ++ languageControl ++
    String.join (Derivative.streamControls.map renderStreamControl)
  IO.FS.writeFile output text
  IO.println s!"Exported {all.length + 1 + Derivative.streamControls.length} exact controls ({text.utf8ByteSize} bytes)."
  for control in (controls.drop 3).take 1 ++ [sharedControl] do
    IO.println s!"{control.name}: bottom={bottomCounts control}, top={topCounts control}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [output] => exportMatchControls output; pure 0
  | [output, ruleOutput] =>
      exportMatchControls output
      RuleControls.write ruleOutput
      pure 0
  | [output, ruleOutput, moduleOutput] =>
      exportMatchControls output
      RuleControls.write ruleOutput
      ModuleControls.write moduleOutput
      pure 0
  | [output, ruleOutput, moduleOutput, premiseOutput] =>
      exportMatchControls output
      RuleControls.write ruleOutput
      ModuleControls.write moduleOutput
      PremiseControls.write premiseOutput
      pure 0
  | _ =>
      IO.eprintln "usage: export_match_automata_controls.lean MATCH_OUTPUT.metta [RULE_OUTPUT.metta [MODULE_OUTPUT.metta [PREMISE_OUTPUT.metta]]]"
      pure 2
