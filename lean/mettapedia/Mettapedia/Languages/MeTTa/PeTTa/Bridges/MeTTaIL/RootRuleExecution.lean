import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution
import Mettapedia.GSLT.LanguageDef.MeTTaILMatchAutomataExecution
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Ordered root execution of admitted first-order language rows

The retained MeTTa helpers apply every authored row at the root, evaluate its
admitted relation queries in the preceding bindings and append all surviving
observations in source order. A compiled `RuleProgram`
provides exact source erasure, including absence of binding annotations.
The five-field language wire retains opaque administrative fields; it is a
projection of an admitted language, not a validator of arbitrary languages.

The completed PeTTa observation is exactly the canonical ordered root
frontier. Preservation and reflection of GSLT steps additionally require
`LanguageDef.isEquationFree`, which excludes generated equations too.
The `Conditional` namespace composes literal finite provider rows and the
canonical builtin tuples. The earlier premise-free entry is retained as a
separately checked executor. Scoped provider authority and recursive context
premises require their own execution joins.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution

open Mettapedia.GSLT.LanguageDef
open CettaWire MeTTaILFirstOrderRuleCompilation
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval RuleExecutionProgram
open MatchAutomataExecution (rewriteRowTerm rewriteRowsTerm matchingProjectionTerm)

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (value : Term) : Atom := CettaWireAtom.encode value
private abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
private abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)
private abbrev noPremises (_ : RewriteRule) : Term := .symbol "LNil"
private abbrev rowsValue (contexts : RewriteRule → Term) (plans : List RulePlan) : Atom :=
  encoded (rewriteRowsTerm contexts noPremises (eraseRulePlans plans))

attribute [local simp] a v encoded patternValue patternsValue rowsValue noPremises

private theorem patterns_as_list (patterns : List Pattern) :
    patternsValue patterns =
      MatchAutomataSourceExecution.listValue (patterns.map InferenceCettaWire.encodePattern) := by
  rw [patternsValue, InferenceCettaWire.encodePatterns_eq_encodeList]
  simp only [MatchAutomataSourceExecution.listValue, encodeList_map, Function.comp_def, id_eq]

private theorem append_captured_returns (caller : Subst) (state : State) (left right : List Pattern)
    (captured : [v "head", v "tail"].map (applySubst caller) =
      [patternsValue left, patternsValue right]) :
    PureReturns program caller state (a "gslt:automata:append" [v "head", v "tail"]) state
      (patternsValue (left ++ right)) := by
  apply automata_captured_returns (by decide +kernel)
  simpa only [patterns_as_list, List.map_append] using
    MatchAutomataSourceExecution.append_captured_returns caller state
      (left.map InferenceCettaWire.encodePattern) (right.map InferenceCettaWire.encodePattern)
      (v "head") (v "tail") (by simpa only [patterns_as_list] using captured)

private def rootEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:root-reducts")[0]'(by decide +kernel)

private def rootEnvironment (contexts : RewriteRule → Term) (plans : List RulePlan)
    (subject : PatternPlan) : Subst :=
  [("subject", patternValue subject.erase), ("rewrites", rowsValue contexts plans)]

private def rootConsBody : Atom :=
  a "let*" [.expression
    [.expression [v "head", a "gslt:rule:apply-root" [v "left", v "right", v "subject"]],
     .expression [v "tail", a "gslt:rule:root-reducts" [v "rest", v "subject"]]],
    a "gslt:automata:append" [v "head", v "tail"]]

private def rootCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "RewriteRule" [v "name", v "context", .symbol "LNil", v "left", v "right"],
      v "rest"], rootConsBody)]

private theorem root_shape : rootEquation.body =
    a "case" [v "rewrites", .expression (rootCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem root_clause (contexts : RewriteRule → Term) (plans : List RulePlan) (subject : PatternPlan) :
    clauses program "gslt:rule:root-reducts" [rowsValue contexts plans, patternValue subject.erase] =
      [.evaluate (rootEnvironment contexts plans subject) rootEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:root-reducts").filterMap _ = _
  rw [show equations "gslt:rule:root-reducts" = [rootEquation] from rfl]
  have formals : rootEquation.arguments = [v "rewrites", v "subject"] := by decide +kernel
  simp [formals, rootEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem root_call (caller : Subst) (state : State) (contexts : RewriteRule → Term)
    (plans : List RulePlan) (subject : PatternPlan) (one two answer : Atom)
    (captured : [one, two].map (applySubst caller) = [rowsValue contexts plans, patternValue subject.erase])
    (returned : PureReturns program (rootEnvironment contexts plans subject) state rootEquation.body state answer) :
    PureReturns program caller state (a "gslt:rule:root-reducts" [one, two]) state answer := by
  apply PureData.raw_authored_call_return program caller (rootEnvironment contexts plans subject) state state
    "gslt:rule:root-reducts" [one, two] rootEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl <;> decide +kernel
  · rw [captured]
    exact root_clause contexts plans subject

private theorem root_body_returns (state : State) (relations : RelationEnv) (language : LanguageDef)
    (contexts : RewriteRule → Term) (plans : List RulePlan) (subject : PatternPlan)
    (premiseFree : ∀ plan ∈ plans, plan.premises = []) :
    PureReturns program (rootEnvironment contexts plans subject) state rootEquation.body state
      (patternsValue (plans.flatMap (fun plan => plan.run relations language subject.erase))) := by
  induction plans with
  | nil =>
      let caller := rootEnvironment contexts [] subject
      rw [root_shape]
      simp only [List.flatMap_nil, patternsValue, encoded, InferenceCettaWire.encodePatterns,
        CettaWireAtom.encode]
      apply case_returns program caller caller state state state (v "rewrites") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ rootCases (read_cases_encoded _) _ _ _
      · simpa [caller, rootEnvironment, eraseRulePlans, rewriteRowsTerm, encodeList,
          CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program caller state "rewrites"
      · simp [rootCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons plan plans ih =>
      let caller := rootEnvironment contexts (plan :: plans) subject
      let selected := ("rest", rowsValue contexts plans) ::
        ("right", patternValue plan.right.erase) :: ("left", patternValue plan.left.erase) ::
        ("context", encoded (contexts plan.erase)) :: ("name", encoded (.string plan.name)) :: caller
      let headResults := plan.run relations language subject.erase
      let tailResults := plans.flatMap (fun row => row.run relations language subject.erase)
      let headValue := patternsValue headResults
      let headBound := ("head", headValue) :: selected
      let tailValue := patternsValue tailResults
      let tailBound := ("tail", tailValue) :: headBound
      have firstFree := premiseFree plan (by simp)
      have restFree : ∀ row ∈ plans, row.premises = [] := by
        intro row member
        exact premiseFree row (by simp [member])
      rw [root_shape]
      apply case_returns program caller selected state state state (v "rewrites")
        (rowsValue contexts (plan :: plans)) rootConsBody _ _ rootCases (read_cases_encoded _) _ _ _
      · simpa [caller, rootEnvironment, applySubst, Subst.lookup] using
          variable_returns program caller state "rewrites"
      · simp [rootCases, eraseRulePlans, rewriteRowsTerm, rewriteRowTerm, RulePlan.erase,
          encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, rootEnvironment]
      · have headReturned : PureReturns program selected state
            (a "gslt:rule:apply-root" [v "left", v "right", v "subject"]) state headValue := by
          simpa only [headValue, headResults, RulePlan.run, firstFree, runPremisePlans,
              List.map_cons, List.map_nil, ← List.map_eq_flatMap, run_eq_matchPattern] using
            RuleInstantiationExecution.apply_root_captured_returns selected state
              plan.left plan.right subject (v "left") (v "right") (v "subject")
              (by simp [selected, caller, rootEnvironment, applySubst, Subst.lookup])
        have headMatched : SpaceSemantics.matchBinding selected (v "head") headValue = some headBound := by
          simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, headBound,
            selected, caller, rootEnvironment]
        have tailReturned := root_call headBound state contexts plans subject (v "rest") (v "subject")
          tailValue (by simp [headBound, selected, caller, rootEnvironment, applySubst, Subst.lookup])
          (ih restFree)
        have tailMatched : SpaceSemantics.matchBinding headBound (v "tail") tailValue = some tailBound := by
          simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound,
            headBound, selected, caller, rootEnvironment]
        have appended : PureReturns program tailBound state
            (a "gslt:automata:append" [v "head", v "tail"]) state
            (patternsValue (headResults ++ tailResults)) :=
          append_captured_returns tailBound state headResults tailResults
            (by simp [tailBound, tailValue, headBound, headValue, applySubst, Subst.lookup])
        have computed := PureData.let_bindings_return
          (PureData.BindingsReturn.cons headReturned headMatched
            (PureData.BindingsReturn.cons tailReturned tailMatched (.nil tailBound state))) state
          (a "gslt:automata:append" [v "head", v "tail"]) _ appended
        simpa only [rootConsBody, List.map_cons, List.map_nil, List.flatMap_cons,
          headResults, tailResults] using computed

/-- Every admitted row is executed once; failed matches contribute no reducts.
Observation order and duplicate occurrences are retained by actual append. -/
theorem root_reducts_captured_returns (caller : Subst) (state : State)
    (relations : RelationEnv) (language : LanguageDef) (contexts : RewriteRule → Term)
    (plans : List RulePlan) (subject : PatternPlan)
    (premiseFree : ∀ plan ∈ plans, plan.premises = []) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [rowsValue contexts plans, patternValue subject.erase]) :
    PureReturns program caller state (a "gslt:rule:root-reducts" [one, two]) state
      (patternsValue (plans.flatMap (fun plan => plan.run relations language subject.erase))) :=
  root_call caller state contexts plans subject one two _ captured
    (root_body_returns state relations language contexts plans subject premiseFree)

theorem root_reducts_returns (state : State) (relations : RelationEnv) (language : LanguageDef)
    (contexts : RewriteRule → Term) (plans : List RulePlan) (subject : PatternPlan)
    (premiseFree : ∀ plan ∈ plans, plan.premises = []) :
    PureReturns program [] state
      (a "gslt:rule:root-reducts" [rowsValue contexts plans, patternValue subject.erase]) state
      (patternsValue (plans.flatMap (fun plan => plan.run relations language subject.erase))) :=
  root_reducts_captured_returns [] state relations language contexts plans subject premiseFree _ _ (by simp)

private def languageEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:language-root-reducts")[0]'(by decide +kernel)

private abbrev languageValue (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) : Atom :=
  encoded (matchingProjectionTerm language types terms (.symbol "LNil") contexts noPremises)

private def languageEnvironment (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (subject : PatternPlan) : Subst :=
  [("subject", patternValue subject.erase), ("language", languageValue language types terms contexts)]

private def languageBody : Atom :=
  a "gslt:rule:root-reducts" [v "rewrites", v "subject"]

private def languageCases : SpaceSemantics.Cases :=
  [(a "GSLTLanguageDefWireV1" [v "name", v "types", v "terms", .symbol "LNil", v "rewrites"],
    languageBody)]

private theorem language_shape : languageEquation.body =
    a "case" [v "language", .expression (languageCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem language_clause (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (subject : PatternPlan) :
    clauses program "gslt:rule:language-root-reducts"
      [languageValue language types terms contexts, patternValue subject.erase] =
      [.evaluate (languageEnvironment language types terms contexts subject) languageEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:language-root-reducts").filterMap _ = _
  rw [show equations "gslt:rule:language-root-reducts" = [languageEquation] from rfl]
  have formals : languageEquation.arguments = [v "language", v "subject"] := by decide +kernel
  simp [formals, languageEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem language_body_returns (state : State) (relations : RelationEnv) (language : LanguageDef)
    (types terms : Term) (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites)
    (subject : PatternPlan) (premiseFree : ∀ row ∈ language.rewrites, row.premises = []) :
    PureReturns program (languageEnvironment language types terms contexts subject) state
      languageEquation.body state
      (patternsValue (rewriteStepWithPremisesUsing relations language subject.erase)) := by
  let caller := languageEnvironment language types terms contexts subject
  let selected := ("rewrites", encoded (rewriteRowsTerm contexts noPremises language.rewrites)) ::
    ("terms", encoded terms) :: ("types", encoded types) :: ("name", encoded (.string language.name)) :: caller
  rw [language_shape]
  apply case_returns program caller selected state state state (v "language")
    (languageValue language types terms contexts) languageBody _ _ languageCases (read_cases_encoded _) _ _ _
  · simpa [caller, languageEnvironment, applySubst, Subst.lookup] using
      variable_returns program caller state "language"
  · simp [languageCases, languageValue, matchingProjectionTerm, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
      selected, caller, languageEnvironment]
  · have executed := root_reducts_captured_returns selected state relations language contexts compiled.plans
        subject (compiled.premiseFree_plans premiseFree) (v "rewrites") (v "subject")
        (by simp [selected, caller, languageEnvironment, applySubst, Subst.lookup,
          compiled.erase_eq_source])
    rw [compiled.run_eq_rootFrontier_of_premiseFree relations language subject.erase premiseFree] at executed
    exact executed

/-- The target input keeps the existing five-field language projection. Source
admission is supplied separately, rather than inferred from omitted metadata. -/
def languageRootQuery (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (subject : PatternPlan) : Atom :=
  a "gslt:rule:language-root-reducts"
    [languageValue language types terms contexts, patternValue subject.erase]

/-- The actual language helper produces exactly the canonical ordered root
frontier. The `RuleProgram` witnesses that no source binding metadata vanished. -/
theorem language_root_reducts_captured_returns (caller : Subst) (state : State)
    (relations : RelationEnv) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites)
    (subject : PatternPlan) (premiseFree : ∀ row ∈ language.rewrites, row.premises = [])
    (one two : Atom) (captured : [one, two].map (applySubst caller) =
      [languageValue language types terms contexts, patternValue subject.erase]) :
    PureReturns program caller state (a "gslt:rule:language-root-reducts" [one, two]) state
      (patternsValue (rewriteStepWithPremisesUsing relations language subject.erase)) := by
  apply PureData.raw_authored_call_return program caller
    (languageEnvironment language types terms contexts subject) state state
    "gslt:rule:language-root-reducts" [one, two] languageEquation.body _
    (by decide) (by decide) (by decide) (by decide +kernel) _ _
    (language_body_returns state relations language types terms contexts compiled subject premiseFree)
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl <;> decide +kernel
  · rw [captured]
    exact language_clause language types terms contexts subject

theorem language_root_reducts_returns (state : State) (relations : RelationEnv)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : RuleProgram language.rewrites) (subject : PatternPlan)
    (premiseFree : ∀ row ∈ language.rewrites, row.premises = []) :
    PureReturns program [] state (languageRootQuery language types terms contexts subject) state
      (patternsValue (rewriteStepWithPremisesUsing relations language subject.erase)) :=
  language_root_reducts_captured_returns [] state relations language types terms contexts compiled subject
    premiseFree _ _ (by simp)

theorem language_root_completed_iff (state : State) (relations : RelationEnv)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : RuleProgram language.rewrites) (subject : PatternPlan)
    (premiseFree : ∀ row ∈ language.rewrites, row.premises = [])
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate [] (languageRootQuery language types terms contexts subject) } =
        .complete after answers input output) ↔
      after = state ∧ answers = [patternsValue (rewriteStepWithPremisesUsing relations language subject.erase)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (language_root_reducts_returns state relations language types terms contexts compiled subject premiseFree)
    after answers input output

theorem language_root_derivation_iff (state : State) (relations : RelationEnv)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : RuleProgram language.rewrites) (subject : PatternPlan)
    (premiseFree : ∀ row ∈ language.rewrites, row.premises = [])
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (languageRootQuery language types terms contexts subject) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [patternsValue (rewriteStepWithPremisesUsing relations language subject.erase)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (language_root_reducts_returns state relations language types terms contexts compiled subject premiseFree)
    after answers input output

/-- A target observation is a completed run and a member of its returned list;
the result list is not defined by reference to source reduction. -/
def ObservesRootReduct (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (subject : PatternPlan) (target : Pattern) : Prop :=
  ∃ reducts : List Pattern,
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (languageRootQuery language types terms contexts subject) }
      (.complete state [patternsValue reducts] [] []) ∧ target ∈ reducts

/-- Completed retained-source observations preserve and reflect the canonical
GSLT step on the admitted equation-free profile. No child rewrite permission
is inferred from structural matches. -/
theorem observes_root_iff_gslt_step (state : State) (relations : RelationEnv)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : RuleProgram language.rewrites) (subject : PatternPlan)
    (premiseFree : ∀ row ∈ language.rewrites, row.premises = [])
    (equationFree : language.isEquationFree = true) (target : Pattern) :
    ObservesRootReduct state language types terms contexts subject target ↔
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing relations language).Step subject.erase target := by
  have exactRun := language_root_derivation_iff state relations language types terms contexts compiled subject
    premiseFree state
  have nonrecursive : ∀ row ∈ language.rewrites,
      Mettapedia.OSLF.MeTTaIL.ContextualStep.NoncontextualPremises row.premises := by
    intro row member
    rw [premiseFree row member]
    exact .nil
  rw [← Mettapedia.OSLF.Framework.TypeSynthesis.mem_rootFrontier_iff_langGSLTUsing_step
    relations language equationFree nonrecursive subject.erase target]
  constructor
  · rintro ⟨reducts, executed, member⟩
    have observation := (exactRun [patternsValue reducts] [] []).mp executed
    have sameAtom := List.cons.inj observation.2.1 |>.1
    have sameWire := CettaWireAtom.encode_injective _ _ sameAtom
    have same := InferenceCettaWire.encodePatterns_injective sameWire
    simpa [same] using member
  · intro member
    exact ⟨_, (exactRun _ [] []).mpr ⟨rfl, rfl, rfl, rfl⟩, member⟩

#print axioms root_reducts_returns
#print axioms language_root_reducts_returns
#print axioms language_root_completed_iff
#print axioms language_root_derivation_iff
#print axioms observes_root_iff_gslt_step

namespace Controls

private def atom (name : String) : PatternPlan := .application name []
private def row (name : String) (left right : PatternPlan) : RulePlan :=
  { name, typeContext := [], premises := [], left, right }

/-- Finite source controls include their explicit premise-free admission. -/
structure Fixture where
  name : String
  plans : List RulePlan
  subject : PatternPlan
  premiseFree : plans.all (fun plan => plan.premises.isEmpty) = true

def duplicateFixture : Fixture :=
  ⟨"language-root-duplicate-occurrences",
    [row "first" (atom "a") (atom "b"), row "miss" (atom "unmatched") (atom "omitted"),
     row "second" (atom "a") (atom "c"), row "first" (atom "a") (atom "b")], atom "a", by decide⟩

def childFixture : Fixture :=
  ⟨"language-root-child-match-grants-no-permission",
    [row "leaf" (atom "a") (atom "b")], .application "wrap" [atom "a"], by decide⟩

def fixtures : List Fixture :=
  [⟨"language-root-no-rows", [], atom "a", by decide⟩,
   duplicateFixture, childFixture,
   ⟨"language-root-wildcard-before-specific",
     [row "any" (.metavariable "whole") (.application "seen" [.metavariable "whole"]),
      row "specific" (atom "a") (atom "last")], atom "a", by decide⟩,
   ⟨"language-root-repeated-variable-hit",
     [row "same" (.application "pair" [.metavariable "x", .metavariable "x"])
       (.application "out" [.metavariable "x"])], .application "pair" [atom "a", atom "a"], by decide⟩,
   ⟨"language-root-repeated-variable-conflict",
     [row "same" (.application "pair" [.metavariable "x", .metavariable "x"])
       (.application "out" [.metavariable "x"])], .application "pair" [atom "a", atom "b"], by decide⟩,
   ⟨"language-root-arity-mismatch",
     [row "one" (.application "wrap" [.metavariable "x"]) (atom "out")],
     .application "wrap" [atom "a", atom "b"], by decide⟩,
   ⟨"language-root-opaque-variable-payload",
     [row "extract" (.application "wrap" [.metavariable "x"]) (.metavariable "x")],
     .application "wrap" [.metavariable "inside"], by decide⟩,
   ⟨"language-root-rigid-bound-occurrence",
     [row "bound" (.bound 2) (atom "out")], .bound 2, by decide⟩,
   ⟨"language-root-unbound-rhs-retained",
     [row "introduce" (atom "a") (.metavariable "unbound")], atom "a", by decide⟩]

def Fixture.language (fixture : Fixture) : LanguageDef :=
  { name := fixture.name, types := [], terms := [], equations := [], rewrites := eraseRulePlans fixture.plans }

def Fixture.compiled (fixture : Fixture) : RuleProgram fixture.language.rewrites :=
  { plans := fixture.plans, erase_eq_source := rfl }

private theorem Fixture.source_premiseFree (fixture : Fixture) :
    ∀ source ∈ fixture.language.rewrites, source.premises = [] := by
  intro source member
  change source ∈ fixture.plans.map RulePlan.erase at member
  obtain ⟨plan, planMember, same⟩ := (List.mem_map (f := RulePlan.erase)).mp member
  subst source
  have empty := List.all_eq_true.mp fixture.premiseFree plan planMember
  have premiseFree : plan.premises = [] := by simpa using empty
  simp [RulePlan.erase, erasePremisePlans, premiseFree]

def Fixture.queryTerm (fixture : Fixture) : Term :=
  .application "gslt:rule:language-root-reducts"
    [matchingProjectionTerm fixture.language (.symbol "LNil") (.symbol "LNil") (.symbol "LNil")
      (fun _ => .symbol "LNil") noPremises, InferenceCettaWire.encodePattern fixture.subject.erase]

def Fixture.expectedTerm (fixture : Fixture) : Term :=
  InferenceCettaWire.encodePatterns
    (rewriteStepWithPremisesUsing RelationEnv.empty fixture.language fixture.subject.erase)

theorem Fixture.returns (fixture : Fixture) (state : State) :
    PureReturns program [] state (encoded fixture.queryTerm) state (encoded fixture.expectedTerm) := by
  simpa [Fixture.queryTerm, Fixture.expectedTerm, languageRootQuery, languageValue,
      CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    language_root_reducts_returns state RelationEnv.empty fixture.language (.symbol "LNil") (.symbol "LNil")
      (fun _ => .symbol "LNil") fixture.compiled fixture.subject fixture.source_premiseFree

/-- Wrong ordered observations include collapsed occurrences, reordered rows,
and an unauthorized child reduct. -/
def incorrectResults : List (Fixture × List Pattern) :=
  [(duplicateFixture, [.apply "b" [], .apply "c" []]),
   (duplicateFixture, [.apply "c" [], .apply "b" [], .apply "b" []]),
   (childFixture, [.apply "wrap" [.apply "b" []]])]

theorem Fixture.refuses_incorrect (fixture : Fixture) (state : State) (incorrect : List Pattern)
    (different : incorrect ≠ rewriteStepWithPremisesUsing RelationEnv.empty fixture.language fixture.subject.erase) :
    ¬ DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded fixture.queryTerm) }
      (.complete state [patternsValue incorrect] [] []) := by
  intro accepted
  have observed := (pure_returns_derivation_iff program [] state state _ _ (fixture.returns state)
    state [patternsValue incorrect] [] []).mp accepted
  have sameAtom := List.cons.inj observed.2.1 |>.1
  exact different (InferenceCettaWire.encodePatterns_injective (CettaWireAtom.encode_injective _ _ sameAtom))

theorem incorrect_observations_refused (state : State) :
    ∀ control ∈ incorrectResults,
      ¬ DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded control.1.queryTerm) }
        (.complete state [patternsValue control.2] [] []) := by
  intro control member
  simp only [incorrectResults, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    apply Fixture.refuses_incorrect
    decide +kernel

/-- These raw wires contain unsupported fields visibly; no admission proof
or silently erased annotation stands in for their refusal. -/
structure RefusalFixture where
  name : String
  queryTerm : Term

private def conditionalWireRow : Term :=
  rewriteRowTerm (fun _ => .symbol "LNil")
    (fun _ => encodeList id [.application "RelationQuery" [.string "pending", .symbol "LNil"]])
    (row "conditional" (atom "a") (atom "b")).erase

def refusalFixtures : List RefusalFixture :=
  [⟨"language-root-nonempty-premise-wire",
     .application "gslt:rule:root-reducts"
       [encodeList id [conditionalWireRow], InferenceCettaWire.encodePattern (atom "a").erase]⟩,
   ⟨"language-root-nonempty-equation-wire",
     .application "gslt:rule:language-root-reducts"
       [.application "GSLTLanguageDefWireV1" [.string "equations", .symbol "LNil", .symbol "LNil",
         encodeList id [.symbol "AnEquation"], .symbol "LNil"],
        InferenceCettaWire.encodePattern (atom "a").erase]⟩]

theorem raw_refusals_finish_without_answers :
    ∀ fixture ∈ refusalFixtures,
      (match run program 100 { state := Effects.empty, control := .evaluate [] (encoded fixture.queryTerm) } with
      | .complete _ answers _ _ => answers.isEmpty
      | _ => false) = true := by
  intro fixture member
  simp only [refusalFixtures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide +kernel

theorem raw_refusals_no_positive_result (fixture : RefusalFixture) (member : fixture ∈ refusalFixtures)
    (value : Atom) :
    ¬ DeclarativeSpec.Runs program
      { state := Effects.empty, control := .evaluate [] (encoded fixture.queryTerm) }
      (.complete Effects.empty [value] [] []) := by
  intro accepted
  obtain ⟨fuel, computed⟩ := derivation_has_run accepted
  have finished := raw_refusals_finish_without_answers fixture member
  cases observed : run program 100
      { state := Effects.empty, control := .evaluate [] (encoded fixture.queryTerm) } with
  | exhausted _ => simp [observed] at finished
  | fault _ _ => simp [observed] at finished
  | complete after answers input output =>
      have noAnswers : answers = [] := by simpa [observed] using finished
      subst answers
      have empty := completed_result_unique program 100 fuel _ after Effects.empty [] input output [value] [] []
        observed computed
      have impossible := empty.2.1
      cases impossible

def annotatedRow : RewriteRule :=
  { (row "annotated" (atom "a") (atom "b")).erase with bindings := some { dependencies := [] } }

theorem binding_annotation_not_admitted : compileRule? annotatedRow = none :=
  compileRule?_annotated_none annotatedRow { dependencies := [] } rfl

end Controls

#print axioms Controls.Fixture.returns
#print axioms Controls.incorrect_observations_refused
#print axioms Controls.raw_refusals_finish_without_answers
#print axioms Controls.raw_refusals_no_positive_result
#print axioms Controls.binding_annotation_not_admitted


namespace Conditional

open RelationPremiseExecution (premiseTerm premisesTerm providerRowsTerm providerEnv
  VariableRuleView VariableSourceProgram variableRuleView)
open MatchAutomataBindingExecution (bindingsTerm bindingsOptionTerm)

private abbrev bindingsValue (bindings : Bindings) : Atom := encoded (bindingsTerm bindings)
private abbrev premisesValue (plans : List PremisePlan) : Atom := encoded (premisesTerm plans)
private abbrev providerRowsValue
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) : Atom :=
  encoded (providerRowsTerm rows)
private abbrev resultsValue (results : List Bindings) : Atom :=
  encoded (RelationPremiseExecution.bindingResultsTerm results)

/-- A compiled row retains all five source fields; the compiler's erasure
proof separately earns absence of annotations unsupported by this carrier. -/
def ruleTerm (contexts : RewriteRule → Term) (plan : RulePlan) : Term :=
  .application "RewriteRule" [.string plan.name, contexts plan.erase, premisesTerm plan.premises,
    InferenceCettaWire.encodePattern plan.left.erase, InferenceCettaWire.encodePattern plan.right.erase]

def rulesTerm (contexts : RewriteRule → Term) (plans : List RulePlan) : Term :=
  encodeList (ruleTerm contexts) plans

/-- The target language projection is derived from every compiled authored
row. Equation-free admission also checks the source's generated equations. -/
def languageTerm (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites) : Term :=
  .application "GSLTLanguageDefWireV1" [.string language.name, types, terms,
    .symbol "LNil", rulesTerm contexts compiled.plans]

private def applyEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:apply-conditional")[0]'(by decide +kernel)

private def applyEnvironment
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : RulePlan) (subject : PatternPlan) : Subst :=
  [("subject", patternValue subject.erase), ("rows", providerRowsValue rows),
   ("premises", premisesValue plan.premises), ("right", patternValue plan.right.erase),
   ("left", patternValue plan.left.erase)]

private def applySomeBody : Atom :=
  a "let" [v "results", a "gslt:rule:premises" [v "premises", v "rows", v "seed"],
    a "gslt:rule:instantiate-results" [v "right", v "results"]]

private def applyCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "LNil"), (a "Some" [v "seed"], applySomeBody)]

private theorem apply_shape : applyEquation.body =
    a "case" [a "gslt:automata:bind" [v "left", v "subject"],
      .expression (applyCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem apply_clause
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : RulePlan) (subject : PatternPlan) :
    clauses program "gslt:rule:apply-conditional"
      [patternValue plan.left.erase, patternValue plan.right.erase, premisesValue plan.premises,
       providerRowsValue rows, patternValue subject.erase] =
      [.evaluate (applyEnvironment rows plan subject) applyEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:apply-conditional").filterMap _ = _
  rw [show equations "gslt:rule:apply-conditional" = [applyEquation] from rfl]
  have formals : applyEquation.arguments = [v "left", v "right", v "premises", v "rows", v "subject"] := by
    decide +kernel
  simp [formals, applyEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem apply_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : RulePlan) (view : VariableRuleView plan) (subject : PatternPlan) :
    PureReturns program (applyEnvironment rows plan subject) state applyEquation.body state
      (patternsValue (plan.run (providerEnv rows) language subject.erase)) := by
  let caller := applyEnvironment rows plan subject
  have matched := automata_captured_returns (by decide +kernel)
    (MatchAutomataBindingExecution.bind_captured_returns caller state plan.left subject [v "left", v "subject"]
      (by simp [caller, applyEnvironment, applySubst, Subst.lookup]))
  simp only [RulePlan.run, run_eq_matchPattern]
  rw [← MatchAutomataBindingExecution.bind_matches_singleton plan.left subject]
  rw [apply_shape]
  cases found : (matchPattern plan.left.erase subject.erase).head? with
  | none =>
      simp only [Option.toList_none, List.flatMap_nil, patternsValue, encoded,
        InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
      apply case_returns program caller caller state state state
        (a "gslt:automata:bind" [v "left", v "subject"]) (.symbol "None")
        (.symbol "LNil") (.symbol "LNil") _ applyCases (read_cases_encoded _) _ _ _
      · simpa [found, bindingsOptionTerm, CettaWireAtom.encode] using matched
      · simp [applyCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | some seed =>
      let selected := ("seed", bindingsValue seed) :: caller
      let choices := runPremisePlans (providerEnv rows) language plan.premises seed
      let bound := ("results", resultsValue choices) :: selected
      simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      apply case_returns program caller selected state state state
        (a "gslt:automata:bind" [v "left", v "subject"])
        (a "Some" [bindingsValue seed]) applySomeBody _ _ applyCases (read_cases_encoded _) _ _ _
      · simpa [found, bindingsOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using matched
      · simp [applyCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, applyEnvironment]
      · have executed := RelationPremiseExecution.checked_premises_captured_returns selected state language rows
            plan.premises view seed (v "premises") (v "rows") (v "seed")
            (by simp [selected, caller, applyEnvironment, applySubst, Subst.lookup])
        apply let_returns program selected bound state state state (v "results") _ _ _ _ executed _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, selected, caller, applyEnvironment, choices]
        · simpa only [choices] using RuleInstantiationExecution.instantiate_results_captured_returns
            bound state plan.right choices (v "right") (v "results")
            (by simp [bound, selected, caller, applyEnvironment, applySubst, Subst.lookup,
              RelationPremiseExecution.bindingResultsTerm])

/-- The actual row call composes canonical matching, the complete ordered
relation-premise fold and RHS construction. No premise verdict is assumed. -/
theorem apply_rule_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : RulePlan) (view : VariableRuleView plan) (subject : PatternPlan) (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) =
      [patternValue plan.left.erase, patternValue plan.right.erase, premisesValue plan.premises,
       providerRowsValue rows, patternValue subject.erase]) :
    PureReturns program caller state (a "gslt:rule:apply-conditional" [one, two, three, four, five]) state
      (patternsValue (plan.run (providerEnv rows) language subject.erase)) := by
  apply PureData.raw_authored_call_return program caller (applyEnvironment rows plan subject) state state
    "gslt:rule:apply-conditional" [one, two, three, four, five] applyEquation.body _
    (by decide) (by decide) (by decide) (by decide +kernel) _ _
    (apply_body_returns state language rows plan view subject)
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · rw [captured]
    exact apply_clause rows plan subject

def applyRuleTerm
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : RulePlan) (subject : PatternPlan) : Term :=
  .application "gslt:rule:apply-conditional"
    [InferenceCettaWire.encodePattern plan.left.erase, InferenceCettaWire.encodePattern plan.right.erase,
     premisesTerm plan.premises, providerRowsTerm rows, InferenceCettaWire.encodePattern subject.erase]

theorem apply_rule_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : RulePlan) (view : VariableRuleView plan) (subject : PatternPlan) :
    PureReturns program [] state (encoded (applyRuleTerm rows plan subject)) state
      (patternsValue (plan.run (providerEnv rows) language subject.erase)) :=
  apply_rule_captured_returns [] state language rows plan view subject _ _ _ _ _ (by simp)


private abbrev ruleRowsValue (contexts : RewriteRule → Term) (plans : List RulePlan) : Atom :=
  encoded (rulesTerm contexts plans)

private def rootEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:conditional-root-reducts")[0]'(by decide +kernel)

private def rootEnvironment (contexts : RewriteRule → Term)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plans : List RulePlan) (subject : PatternPlan) : Subst :=
  [("subject", patternValue subject.erase), ("rows", providerRowsValue rows),
   ("rewrites", ruleRowsValue contexts plans)]

private def rootPairs : List (Atom × Atom) :=
  [(v "head", a "gslt:rule:apply-conditional" [v "left", v "right", v "premises", v "rows", v "subject"]),
   (v "tail", a "gslt:rule:conditional-root-reducts" [v "rest", v "rows", v "subject"])]

private def rootResult : Atom := a "gslt:automata:append" [v "head", v "tail"]
private def rootConsBody : Atom :=
  a "let*" [.expression (rootPairs.map fun pair => .expression [pair.1, pair.2]), rootResult]

private def rootCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "RewriteRule" [v "name", v "context", v "premises", v "left", v "right"],
      v "rest"], rootConsBody)]

private theorem root_shape : rootEquation.body =
    a "case" [v "rewrites", .expression (rootCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem root_clause (contexts : RewriteRule → Term)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plans : List RulePlan) (subject : PatternPlan) :
    clauses program "gslt:rule:conditional-root-reducts"
      [ruleRowsValue contexts plans, providerRowsValue rows, patternValue subject.erase] =
      [.evaluate (rootEnvironment contexts rows plans subject) rootEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:conditional-root-reducts").filterMap _ = _
  rw [show equations "gslt:rule:conditional-root-reducts" = [rootEquation] from rfl]
  have formals : rootEquation.arguments = [v "rewrites", v "rows", v "subject"] := by decide +kernel
  simp [formals, rootEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem root_call (caller : Subst) (state : State) (contexts : RewriteRule → Term)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plans : List RulePlan) (subject : PatternPlan) (one two three answer : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [ruleRowsValue contexts plans, providerRowsValue rows, patternValue subject.erase])
    (returned : PureReturns program (rootEnvironment contexts rows plans subject) state
      rootEquation.body state answer) :
    PureReturns program caller state (a "gslt:rule:conditional-root-reducts" [one, two, three]) state answer := by
  apply PureData.raw_authored_call_return program caller (rootEnvironment contexts rows plans subject) state state
    "gslt:rule:conditional-root-reducts" [one, two, three] rootEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl <;> decide +kernel
  · rw [captured]
    exact root_clause contexts rows plans subject

private theorem root_body_returns (state : State) (language : LanguageDef)
    (contexts : RewriteRule → Term) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true) (subject : PatternPlan) :
    PureReturns program (rootEnvironment contexts rows plans subject) state rootEquation.body state
      (patternsValue (plans.flatMap (fun plan => plan.run (providerEnv rows) language subject.erase))) := by
  induction plans with
  | nil =>
      let caller := rootEnvironment contexts rows [] subject
      rw [root_shape]
      simp only [List.flatMap_nil, patternsValue, encoded, InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
      apply case_returns program caller caller state state state (v "rewrites") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ rootCases (read_cases_encoded _) _ _ _
      · simpa [caller, rootEnvironment, ruleRowsValue, rulesTerm, encodeList,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program caller state "rewrites"
      · simp [rootCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons plan plans ih =>
      have tailViews : ∀ row ∈ plans, row.variablePremises?.isSome = true := by
        intro row member
        exact sourceViews row (by simp [member])
      have firstView := variableRuleView plan (sourceViews plan (by simp))
      let caller := rootEnvironment contexts rows (plan :: plans) subject
      let selected := ("rest", ruleRowsValue contexts plans) ::
        ("right", patternValue plan.right.erase) :: ("left", patternValue plan.left.erase) ::
        ("premises", premisesValue plan.premises) :: ("context", encoded (contexts plan.erase)) ::
        ("name", encoded (.string plan.name)) :: caller
      let headResults := plan.run (providerEnv rows) language subject.erase
      let tailResults := plans.flatMap (fun next => next.run (providerEnv rows) language subject.erase)
      let headBound := ("head", patternsValue headResults) :: selected
      let tailBound := ("tail", patternsValue tailResults) :: headBound
      have headReturned := apply_rule_captured_returns selected state language rows plan firstView subject
        (v "left") (v "right") (v "premises") (v "rows") (v "subject")
        (by simp [selected, caller, rootEnvironment, applySubst, Subst.lookup])
      have tailReturned := root_call headBound state contexts rows plans subject
        (v "rest") (v "rows") (v "subject") (patternsValue tailResults)
        (by simp [headBound, selected, caller, rootEnvironment, applySubst, Subst.lookup]) (ih tailViews)
      rw [root_shape]
      apply case_returns program caller selected state state state (v "rewrites")
        (ruleRowsValue contexts (plan :: plans)) rootConsBody _ _ rootCases (read_cases_encoded _) _ _ _
      · simpa [caller, rootEnvironment, applySubst, Subst.lookup] using variable_returns program caller state "rewrites"
      · simp [rootCases, ruleRowsValue, rulesTerm, ruleTerm, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, rootEnvironment]
      · have bound : PureData.BindingsReturn program selected state rootPairs tailBound state := by
          apply PureData.BindingsReturn.cons (bound := headBound) headReturned
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, headBound, headResults,
              selected, caller, rootEnvironment]
          apply PureData.BindingsReturn.cons (bound := tailBound) tailReturned
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound,
              headBound, selected, caller, rootEnvironment]
          exact .nil _ _
        change PureReturns program selected state
          (a "let*" [.expression (rootPairs.map fun pair => .expression [pair.1, pair.2]), rootResult]) state _
        apply PureData.let_bindings_return bound
        simp only [List.flatMap_cons]
        exact append_captured_returns tailBound state headResults tailResults
          (by simp [tailBound, headBound, applySubst, Subst.lookup])

/-- Conditional root dispatch walks every admitted row in authored order,
including each duplicate row and every surviving premise witness. -/
theorem root_reducts_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (contexts : RewriteRule → Term) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true) (subject : PatternPlan) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [ruleRowsValue contexts plans, providerRowsValue rows, patternValue subject.erase]) :
    PureReturns program caller state (a "gslt:rule:conditional-root-reducts" [one, two, three]) state
      (patternsValue (plans.flatMap (fun plan => plan.run (providerEnv rows) language subject.erase))) :=
  root_call caller state contexts rows plans subject one two three _ captured
    (root_body_returns state language contexts rows plans sourceViews subject)

def rootQueryTerm (contexts : RewriteRule → Term)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plans : List RulePlan) (subject : PatternPlan) : Term :=
  .application "gslt:rule:conditional-root-reducts"
    [rulesTerm contexts plans, providerRowsTerm rows, InferenceCettaWire.encodePattern subject.erase]

theorem root_reducts_returns (state : State) (language : LanguageDef)
    (contexts : RewriteRule → Term) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true) (subject : PatternPlan) :
    PureReturns program [] state (encoded (rootQueryTerm contexts rows plans subject)) state
      (patternsValue (plans.flatMap (fun plan => plan.run (providerEnv rows) language subject.erase))) :=
  root_reducts_captured_returns [] state language contexts rows plans sourceViews subject _ _ _ (by simp)

private def languageEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:language-conditional-root-reducts")[0]'(by decide +kernel)

private def languageEnvironment (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (subject : PatternPlan) : Subst :=
  [("subject", patternValue subject.erase), ("rows", providerRowsValue rows),
   ("language", encoded (languageTerm language types terms contexts compiled))]

private def languageCases : SpaceSemantics.Cases :=
  [(a "GSLTLanguageDefWireV1" [v "name", v "types", v "terms", .symbol "LNil", v "rewrites"],
    a "gslt:rule:conditional-root-reducts" [v "rewrites", v "rows", v "subject"])]

private theorem language_shape : languageEquation.body =
    a "case" [v "language", .expression (languageCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem language_clause (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) :
    clauses program "gslt:rule:language-conditional-root-reducts"
      [encoded (languageTerm language types terms contexts compiled), providerRowsValue rows,
       patternValue subject.erase] =
      [.evaluate (languageEnvironment language types terms contexts compiled rows subject) languageEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:language-conditional-root-reducts").filterMap _ = _
  rw [show equations "gslt:rule:language-conditional-root-reducts" = [languageEquation] from rfl]
  have formals : languageEquation.arguments = [v "language", v "rows", v "subject"] := by decide +kernel
  simp [formals, languageEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem language_body_returns (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) :
    PureReturns program (languageEnvironment language types terms contexts compiled rows subject) state
      languageEquation.body state
      (patternsValue (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)) := by
  let caller := languageEnvironment language types terms contexts compiled rows subject
  let selected := ("rewrites", ruleRowsValue contexts compiled.plans) :: ("terms", encoded terms) ::
    ("types", encoded types) :: ("name", encoded (.string language.name)) :: caller
  rw [language_shape]
  apply case_returns program caller selected state state state (v "language")
    (encoded (languageTerm language types terms contexts compiled.val))
    (a "gslt:rule:conditional-root-reducts" [v "rewrites", v "rows", v "subject"]) _ _
    languageCases (read_cases_encoded _) _ _ _
  · simpa [caller, languageEnvironment, applySubst, Subst.lookup] using variable_returns program caller state "language"
  · simp [languageCases, languageTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, selected, caller, languageEnvironment, ruleRowsValue, VariableSourceProgram.plans]
  · rw [← compiled.run_eq_rootFrontier (providerEnv rows) language subject.erase]
    exact root_reducts_captured_returns selected state language contexts rows compiled.plans compiled.property subject
      (v "rewrites") (v "rows") (v "subject")
      (by simp [selected, caller, languageEnvironment, applySubst, Subst.lookup])

def languageQueryTerm (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) : Term :=
  .application "gslt:rule:language-conditional-root-reducts"
    [languageTerm language types terms contexts compiled, providerRowsTerm rows,
     InferenceCettaWire.encodePattern subject.erase]

theorem language_root_captured_returns (caller : Subst) (state : State)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (subject : PatternPlan) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [encoded (languageTerm language types terms contexts compiled.val), providerRowsValue rows,
       patternValue subject.erase]) :
    PureReturns program caller state (a "gslt:rule:language-conditional-root-reducts" [one, two, three]) state
      (patternsValue (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)) := by
  apply PureData.raw_authored_call_return program caller
    (languageEnvironment language types terms contexts compiled rows subject) state state
    "gslt:rule:language-conditional-root-reducts" [one, two, three] languageEquation.body _
    (by decide) (by decide) (by decide) (by decide +kernel) _ _
    (language_body_returns state language types terms contexts compiled rows subject)
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl <;> decide +kernel
  · rw [captured]
    exact language_clause language types terms contexts compiled rows subject

theorem language_root_returns (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) :
    PureReturns program [] state (encoded (languageQueryTerm language types terms contexts compiled rows subject)) state
      (patternsValue (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)) :=
  language_root_captured_returns [] state language types terms contexts compiled rows subject _ _ _ (by simp)

theorem language_root_completed_iff (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate [] (encoded (languageQueryTerm language types terms contexts compiled rows subject)) } =
        .complete after answers input output) ↔
      after = state ∧ answers = [patternsValue (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (language_root_returns state language types terms contexts compiled rows subject) after answers input output

theorem language_root_derivation_iff (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (languageQueryTerm language types terms contexts compiled rows subject)) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [patternsValue (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (language_root_returns state language types terms contexts compiled rows subject) after answers input output

/-- Only an actual completed retained-source execution can supply this
observation; the source frontier is not its defining result list. -/
def ObservesRootReduct (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (subject : PatternPlan) (target : Pattern) : Prop :=
  ∃ reducts : List Pattern,
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (languageQueryTerm language types terms contexts compiled rows subject)) }
      (.complete state [patternsValue reducts] [] []) ∧ target ∈ reducts

/-- Retained conditional execution preserves and reflects equation-free
GSLT steps with a finite literal provider. Nonrecursive premise support is
earned from complete compilation, including the actual preceding bindings. -/
theorem observes_root_iff_gslt_step (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (equationFree : language.isEquationFree = true) (target : Pattern) :
    ObservesRootReduct state language types terms contexts compiled rows subject target ↔
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing (providerEnv rows) language).Step subject.erase target := by
  have exactRun := language_root_derivation_iff state language types terms contexts compiled rows subject state
  rw [← Mettapedia.OSLF.Framework.TypeSynthesis.mem_rootFrontier_iff_langGSLTUsing_step
    (providerEnv rows) language equationFree compiled.noncontextual_premises subject.erase target]
  constructor
  · rintro ⟨reducts, executed, member⟩
    have observation := (exactRun [patternsValue reducts] [] []).mp executed
    have sameAtom := List.cons.inj observation.2.1 |>.1
    have sameWire := CettaWireAtom.encode_injective _ _ sameAtom
    have same := InferenceCettaWire.encodePatterns_injective sameWire
    simpa [same] using member
  · intro member
    exact ⟨_, (exactRun _ [] []).mpr ⟨rfl, rfl, rfl, rfl⟩, member⟩

#print axioms apply_rule_returns
#print axioms root_reducts_returns
#print axioms language_root_returns
#print axioms language_root_completed_iff
#print axioms language_root_derivation_iff
#print axioms observes_root_iff_gslt_step


namespace Controls

private def atom (name : String) : PatternPlan := .application name []
private def row (name : String) (left right : PatternPlan) (premises : List VariablePremisePlan) : RulePlan :=
  { name, typeContext := [], premises := premises.map VariablePremisePlan.toPlan, left, right }

structure Fixture where
  name : String
  plans : List RulePlan
  rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow
  subject : PatternPlan

private def guard : RulePlan := row "guard" (atom "start") (atom "done") [⟨"ready", []⟩]

def duplicateGuardFixture : Fixture :=
  ⟨"conditional-duplicate-guard-witnesses", [guard],
    [⟨"ready", []⟩, ⟨"ignored", []⟩, ⟨"ready", []⟩, ⟨"ready", []⟩], atom "start"⟩

def chainFixture : Fixture :=
  ⟨"conditional-ordered-dependent-branches",
    [row "chain" (atom "start") (.application "out" [.metavariable "y"])
      [⟨"first", ["x"]⟩, ⟨"next", ["x", "y"]⟩]],
    [⟨"first", [.apply "b" []]⟩, ⟨"first", [.apply "a" []]⟩,
     ⟨"next", [.apply "a" [], .apply "c" []]⟩,
     ⟨"next", [.apply "b" [], .apply "d" []]⟩,
     ⟨"next", [.apply "b" [], .apply "d" []]⟩], atom "start"⟩

def childFixture : Fixture :=
  ⟨"conditional-child-match-grants-no-permission", [guard], [⟨"ready", []⟩],
    .application "wrap" [atom "start"]⟩

def fixtures : List Fixture :=
  [⟨"conditional-missing-guard", [guard], [], atom "start"⟩,
   duplicateGuardFixture, chainFixture,
   ⟨"conditional-failed-suffix-removes-branches",
     [row "suffix" (atom "start") (atom "done") [⟨"ready", []⟩, ⟨"missing", []⟩]],
     [⟨"ready", []⟩, ⟨"ready", []⟩], atom "start"⟩,
   ⟨"conditional-repeated-query-variable-conflict",
     [row "same" (atom "start") (atom "done") [⟨"pair", ["x", "x"]⟩]],
     [⟨"pair", [.apply "a" [], .apply "b" []]⟩], atom "start"⟩,
   ⟨"conditional-opaque-prebound-variable",
     [row "literal" (.application "wrap" [.metavariable "x"]) (.metavariable "y")
       [⟨"payload", ["x", "y"]⟩]],
     [⟨"payload", [.fvar "inside", .apply "kept" []]⟩,
      ⟨"payload", [.apply "inside" [], .apply "discarded" []]⟩],
     .application "wrap" [.metavariable "inside"]⟩,
   ⟨"conditional-two-equal-builtin-witnesses",
     [row "equal" (.application "pair" [.metavariable "x", .metavariable "y"])
       (atom "done") [⟨"eq", ["x", "y"]⟩]], [],
     .application "pair" [atom "a", atom "a"]⟩,
   ⟨"conditional-builtins-before-provider-witness",
     [row "witness" (atom "start") (.application "out" [.metavariable "x", .metavariable "y"])
       [⟨"eq", ["x", "y"]⟩]], [⟨"eq", [.apply "p" [], .apply "q" []]⟩], atom "start"⟩,
   ⟨"conditional-duplicate-rules-times-guard-witnesses", [guard, guard],
     [⟨"ready", []⟩, ⟨"ready", []⟩], atom "start"⟩,
   ⟨"conditional-provider-arity-refusal",
     [row "arity" (atom "start") (atom "done") [⟨"one", ["x"]⟩]],
     [⟨"one", []⟩, ⟨"one", [.apply "a" [], .apply "b" []]⟩], atom "start"⟩,
   childFixture,
   ⟨"conditional-premise-free-parity",
     [row "first" (atom "start") (atom "a") [], row "second" (atom "start") (atom "b") []],
     [⟨"irrelevant", [.apply "anything" []]⟩], atom "start"⟩]

def Fixture.language (fixture : Fixture) : LanguageDef :=
  { name := fixture.name, types := [], terms := [], equations := [], rewrites := eraseRulePlans fixture.plans }

def Fixture.compiled (fixture : Fixture) : RuleProgram fixture.language.rewrites :=
  { plans := fixture.plans, erase_eq_source := rfl }

def Fixture.queryTerm (fixture : Fixture) : Term :=
  languageQueryTerm fixture.language (.symbol "LNil") (.symbol "LNil") (fun _ => .symbol "LNil")
    fixture.compiled fixture.rows fixture.subject

def Fixture.results (fixture : Fixture) : List Pattern :=
  rewriteStepWithPremisesUsing (providerEnv fixture.rows) fixture.language fixture.subject.erase

def Fixture.expectedTerm (fixture : Fixture) : Term :=
  InferenceCettaWire.encodePatterns fixture.results

def Fixture.sourceCompiled (fixture : Fixture)
    (admitted : fixture.plans.all (fun plan => plan.variablePremises?.isSome) = true) :
    VariableSourceProgram fixture.language.rewrites :=
  ⟨fixture.compiled, List.all_eq_true.mp admitted⟩

theorem Fixture.returns (fixture : Fixture)
    (admitted : fixture.plans.all (fun plan => plan.variablePremises?.isSome) = true) (state : State) :
    PureReturns program [] state (encoded fixture.queryTerm) state (encoded fixture.expectedTerm) := by
  exact language_root_returns state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled admitted) fixture.rows fixture.subject

/-- The dependent second premise is checked in each preceding branch's
bindings, and duplicate rows remain two distinct successful observations. -/
theorem ordered_branch_observations :
    chainFixture.results =
      [.apply "out" [.apply "d" []], .apply "out" [.apply "d" []], .apply "out" [.apply "c" []]] := by
  decide +kernel

def incorrectResults : List (Fixture × List Pattern) :=
  [(duplicateGuardFixture, [.apply "done" []]),
   (chainFixture, [.apply "out" [.apply "c" []], .apply "out" [.apply "d" []], .apply "out" [.apply "d" []]]),
   (childFixture, [.apply "wrap" [.apply "done" []]])]

theorem Fixture.refuses_incorrect (fixture : Fixture)
    (admitted : fixture.plans.all (fun plan => plan.variablePremises?.isSome) = true) (state : State) (incorrect : List Pattern)
    (different : incorrect ≠ fixture.results) :
    ¬ DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded fixture.queryTerm) }
      (.complete state [patternsValue incorrect] [] []) := by
  intro accepted
  have observed := (pure_returns_derivation_iff program [] state state _ _ (fixture.returns admitted state)
    state [patternsValue incorrect] [] []).mp accepted
  have sameAtom := List.cons.inj observed.2.1 |>.1
  exact different (InferenceCettaWire.encodePatterns_injective (CettaWireAtom.encode_injective _ _ sameAtom))

theorem incorrect_observations_refused (state : State) :
    ∀ control ∈ incorrectResults,
      ¬ DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded control.1.queryTerm) }
        (.complete state [patternsValue control.2] [] []) := by
  intro control member
  simp only [incorrectResults, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    apply Fixture.refuses_incorrect
    · decide +kernel
    · decide +kernel

/-- A recursive context premise is outside this relation-only plan profile. -/
theorem congruence_not_admitted :
    compileRule? { guard.erase with premises := [.congruence (.fvar "x") (.fvar "y")] } = none := by
  decide +kernel

end Controls

#print axioms Controls.Fixture.returns
#print axioms Controls.ordered_branch_observations
#print axioms Controls.incorrect_observations_refused
#print axioms Controls.congruence_not_admitted

end Conditional

namespace Matched

open MeTTaILSubtermMatchAutomata (BoundMatch)
open MatchAutomataBindingExecution (bindingsTerm boundMatchTerm matchesTerm)
open RelationPremiseExecution (premisesTerm providerRowsTerm providerEnv
  VariableRuleView VariableSourceProgram variableRuleView)

/-- The lowered row continuation uses the matcher-supplied bindings directly.
It evaluates every guard before constructing the right-hand side. -/
def runForBindings (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (language : LanguageDef) (plan : RulePlan) (bindings : Bindings) : List Pattern :=
  (runPremisePlans (providerEnv rows) language plan.premises bindings).map plan.right.instantiate

/-- Resolve a physical authored occurrence and retain only authorized root
observations. This does not grant reduction authority to a subterm match. -/
def runMatch (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (language : LanguageDef) (compiled : RuleProgram language.rewrites) (matched : BoundMatch) : List Pattern :=
  if matched.location.position.isEmpty then
    match compiled.plans[matched.location.occurrence]? with
    | none => []
    | some plan => runForBindings rows language plan matched.bindings
  else []

def runMatches (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (language : LanguageDef) (compiled : RuleProgram language.rewrites)
    (observations : List BoundMatch) : List Pattern :=
  observations.flatMap (runMatch rows language compiled)

theorem runMatch_eq_dispatch (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (language : LanguageDef) (compiled : RuleProgram language.rewrites) (matched : BoundMatch) :
    runMatch rows language compiled matched =
      if matched.location.position.isEmpty then
        MeTTaILMatchAutomataExecution.dispatchMatch
          (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises (providerEnv rows))
          language (fun _ => []) matched
      else [] := by
  have sourceLookup := congrArg (fun rules => rules[matched.location.occurrence]?) compiled.erase_eq_source
  rw [eraseRulePlans, List.getElem?_map] at sourceLookup
  unfold runMatch
  split
  · unfold MeTTaILMatchAutomataExecution.dispatchMatch
    rw [← sourceLookup]
    cases found : compiled.plans[matched.location.occurrence]? with
    | none => simp
    | some plan =>
        simp only [Option.map_some]
        unfold runForBindings
        rw [runPremisePlans_eq_premisesUsing (providerEnv rows) language (fun _ => [])
          plan.premises matched.bindings]
        simp [RulePlan.erase, Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.RuleInterpretation.syntactic,
          Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings, instantiate_eq_applyBindings,
          applyBindingsScoped_zero_of_binderFree _ _ _ (binderFree_erase plan.right)]
  · rfl

theorem runMatches_eq_dispatch (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (language : LanguageDef) (compiled : RuleProgram language.rewrites)
    (observations : List BoundMatch) :
    runMatches rows language compiled observations =
      MeTTaILMatchAutomataExecution.dispatchRoot
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises (providerEnv rows))
        language (fun _ => []) observations := by
  unfold runMatches MeTTaILMatchAutomataExecution.dispatchRoot MeTTaILMatchAutomataExecution.atRoot
  induction observations with
  | nil => rfl
  | cons matched observations ih =>
      cases root : matched.location.position.isEmpty <;> simp [root, ih, runMatch_eq_dispatch]

private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev listValue (values : List Term) : Atom := encoded (encodeList id values)
private def optionTerm : Option Term → Term
  | none => .symbol "None"
  | some value => .application "Some" [value]
private abbrev optionValue (value : Option Term) : Atom := encoded (optionTerm value)

/-- Row selection is shared with RHS and scoped-payload execution. -/
theorem row_at_captured_returns (caller : Subst) (state : State) (index : Nat) (values : List Term)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [number index, listValue values]) :
    PureReturns program caller state (a "gslt:rule:row-at" [one, two]) state (optionValue values[index]?) := by
  have returned := RuleInstantiationExecution.RowLookup.row_at_captured_returns caller state index values
    one two captured
  cases found : values[index]? <;>
    simpa [found, optionValue, optionTerm, MatchAutomataBindingExecution.payloadOptionTerm] using returned

theorem row_at_returns (state : State) (index : Nat) (values : List Term) :
    PureReturns program [] state (a "gslt:rule:row-at" [number index, listValue values]) state
      (optionValue values[index]?) :=
  row_at_captured_returns [] state index values _ _ (by simp)

private abbrev compiledRows {language : LanguageDef} (contexts : RewriteRule → Term)
    (compiled : RuleProgram language.rewrites) : Atom :=
  encoded (Conditional.rulesTerm contexts compiled.plans)

private abbrev seedValue (seed : Bindings) : Atom := encoded (bindingsTerm seed)
private abbrev choiceValue (choices : List Bindings) : Atom :=
  encoded (RelationPremiseExecution.bindingResultsTerm choices)

private theorem compiledRows_as_list {language : LanguageDef} (contexts : RewriteRule → Term)
    (compiled : RuleProgram language.rewrites) :
    compiledRows contexts compiled = listValue (compiled.plans.map (Conditional.ruleTerm contexts)) := by
  simp only [compiledRows, Conditional.rulesTerm, listValue, encodeList_map, Function.comp_def, id_eq]

private def applyMatchEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:apply-root-match")[0]'(by decide +kernel)

private def applyMatchEnvironment {language : LanguageDef} (contexts : RewriteRule → Term)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (compiled : RuleProgram language.rewrites) (matched : BoundMatch) : Subst :=
  [("matched", encoded (boundMatchTerm matched)), ("rows", encoded (providerRowsTerm rows)),
   ("rewrites", compiledRows contexts compiled)]

private def applyMatchSomeBody : Atom :=
  a "let" [v "choices", a "gslt:rule:premises" [v "premises", v "rows", v "seed"],
    a "gslt:rule:instantiate-results" [v "right", v "choices"]]

private def applyMatchRowCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "LNil"),
   (a "Some" [a "RewriteRule" [v "name", v "context", v "premises", v "left", v "right"]],
    applyMatchSomeBody)]

private def applyMatchRootBody : Atom :=
  a "let" [v "selected", a "gslt:rule:row-at" [v "index", v "rewrites"],
    a "case" [v "selected", .expression (applyMatchRowCases.map fun row => .expression [row.1, row.2])]]

private def applyMatchCases : SpaceSemantics.Cases :=
  [(a "Found" [.symbol "LNil", v "index", v "seed"], applyMatchRootBody),
   (a "Found" [a "LCons" [v "child", v "path"], v "index", v "seed"], .symbol "LNil")]

private theorem applyMatch_shape : applyMatchEquation.body =
    a "case" [v "matched", .expression (applyMatchCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem applyMatch_clause {language : LanguageDef} (contexts : RewriteRule → Term)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (compiled : RuleProgram language.rewrites) (matched : BoundMatch) :
    clauses program "gslt:rule:apply-root-match"
      [compiledRows contexts compiled, encoded (providerRowsTerm rows), encoded (boundMatchTerm matched)] =
      [.evaluate (applyMatchEnvironment contexts rows compiled matched) applyMatchEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:apply-root-match").filterMap _ = _
  rw [show equations "gslt:rule:apply-root-match" = [applyMatchEquation] from rfl]
  have formals : applyMatchEquation.arguments = [v "rewrites", v "rows", v "matched"] := by
    decide +kernel
  simp [formals, applyMatchEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem applyMatch_body_returns (state : State) (language : LanguageDef)
    (contexts : RewriteRule → Term)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (compiled : VariableSourceProgram language.rewrites) (matched : BoundMatch) :
    PureReturns program (applyMatchEnvironment contexts rows compiled.val matched) state
      applyMatchEquation.body state (patternsValue (runMatch rows language compiled.val matched)) := by
  rcases matched with ⟨⟨position, index⟩, seed⟩
  rw [applyMatch_shape]
  cases position with
  | nil =>
      let caller := applyMatchEnvironment contexts rows compiled.val ⟨⟨[], index⟩, seed⟩
      let selected := ("seed", seedValue seed) :: ("index", number index) :: caller
      let rowTerms := compiled.plans.map (Conditional.ruleTerm contexts)
      let looked := ("selected", optionValue rowTerms[index]?) :: selected
      have lookup := row_at_captured_returns selected state index rowTerms (v "index") (v "rewrites")
        (by simp [selected, caller, applyMatchEnvironment, applySubst, Subst.lookup,
          compiledRows_as_list, rowTerms, VariableSourceProgram.plans])
      simp only [runMatch, List.isEmpty_nil, ↓reduceIte]
      apply case_returns program caller selected state state state (v "matched")
        (encoded (boundMatchTerm ⟨⟨[], index⟩, seed⟩)) applyMatchRootBody _ _
        applyMatchCases (read_cases_encoded _) _ _ _
      · simpa [caller, applyMatchEnvironment, applySubst, Subst.lookup] using
          variable_returns program caller state "matched"
      · simp [applyMatchCases, boundMatchTerm, MatchAutomataDerivativeExecution.positionTerm,
          encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, applyMatchEnvironment, seedValue, number]
      · unfold applyMatchRootBody
        apply let_returns program selected looked state state state (v "selected") _ _ _ _ lookup _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, looked, selected,
            caller, applyMatchEnvironment]
        · cases found : compiled.val.plans[index]? with
          | none =>
              have emptyRow : rowTerms[index]? = none := by simp [rowTerms, VariableSourceProgram.plans, List.getElem?_map, found]
              simp only [patternsValue, InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
              apply case_returns program looked looked state state state (v "selected") (.symbol "None")
                (.symbol "LNil") (.symbol "LNil") _ applyMatchRowCases (read_cases_encoded _) _ _ _
              · simpa [looked, emptyRow, optionValue, optionTerm, CettaWireAtom.encode, applySubst, Subst.lookup] using
                  variable_returns program looked state "selected"
              · simp [applyMatchRowCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · exact symbol_returns program looked state "LNil"
          | some plan =>
              have chosenRow : rowTerms[index]? = some (Conditional.ruleTerm contexts plan) := by
                simp [rowTerms, VariableSourceProgram.plans, List.getElem?_map, found]
              let rowBound := ("right", patternValue plan.right.erase) ::
                ("left", patternValue plan.left.erase) ::
                ("premises", encoded (premisesTerm plan.premises)) ::
                ("context", encoded (contexts plan.erase)) :: ("name", encoded (.string plan.name)) :: looked
              let choices := runPremisePlans (providerEnv rows) language plan.premises seed
              let choicesBound := ("choices", choiceValue choices) :: rowBound
              apply case_returns program looked rowBound state state state (v "selected")
                (encoded (.application "Some" [Conditional.ruleTerm contexts plan]))
                applyMatchSomeBody _ _ applyMatchRowCases (read_cases_encoded _) _ _ _
              · simpa [looked, chosenRow, optionValue, optionTerm, applySubst, Subst.lookup] using
                  variable_returns program looked state "selected"
              · simp [applyMatchRowCases, Conditional.ruleTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, Subst.lookup, rowBound, looked, selected, caller, applyMatchEnvironment]
              · have guarded := RelationPremiseExecution.checked_premises_captured_returns rowBound state language rows
                    plan.premises (compiled.ruleView plan (List.mem_of_getElem? found)) seed (v "premises") (v "rows") (v "seed")
                    (by simp [rowBound, looked, selected, caller, applyMatchEnvironment,
                      seedValue, applySubst, Subst.lookup])
                unfold applyMatchSomeBody
                apply let_returns program rowBound choicesBound state state state (v "choices")
                  _ _ _ _ guarded _ _
                · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, choicesBound, choiceValue,
                    RelationPremiseExecution.bindingResultsTerm,
                    choices, rowBound, looked, selected, caller, applyMatchEnvironment]
                · simpa only [runForBindings, choices] using
                    RuleInstantiationExecution.instantiate_results_captured_returns choicesBound state
                      plan.right choices (v "right") (v "choices")
                      (by simp [choicesBound, rowBound, looked, selected, caller, applyMatchEnvironment,
                        choiceValue, RelationPremiseExecution.bindingResultsTerm, applySubst, Subst.lookup])
  | cons child path =>
      let caller := applyMatchEnvironment contexts rows compiled.val ⟨⟨child :: path, index⟩, seed⟩
      let selected := ("seed", seedValue seed) :: ("index", number index) ::
        ("path", encoded (MatchAutomataDerivativeExecution.positionTerm path)) :: ("child", number child) :: caller
      simp only [runMatch, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        patternsValue, InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
      apply case_returns program caller selected state state state (v "matched")
        (encoded (boundMatchTerm ⟨⟨child :: path, index⟩, seed⟩)) (.symbol "LNil") (.symbol "LNil") _
        applyMatchCases (read_cases_encoded _) _ _ _
      · simpa [caller, applyMatchEnvironment, applySubst, Subst.lookup] using
          variable_returns program caller state "matched"
      · simp [applyMatchCases, boundMatchTerm, MatchAutomataDerivativeExecution.positionTerm,
          encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
          selected, caller, applyMatchEnvironment, seedValue, number]
      · exact symbol_returns program selected state "LNil"

/-- The continuation resolves the matcher's physical row and evaluates its
guards using the supplied bindings, without matching the LHS a second time. -/
theorem apply_match_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (contexts : RewriteRule → Term)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (compiled : VariableSourceProgram language.rewrites) (matched : BoundMatch) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [compiledRows contexts compiled.val, encoded (providerRowsTerm rows), encoded (boundMatchTerm matched)]) :
    PureReturns program caller state (a "gslt:rule:apply-root-match" [one, two, three]) state
      (patternsValue (runMatch rows language compiled.val matched)) := by
  apply PureData.raw_authored_call_return program caller
    (applyMatchEnvironment contexts rows compiled.val matched) state state "gslt:rule:apply-root-match"
    [one, two, three] applyMatchEquation.body _
    (by decide) (by decide) (by decide) (by decide +kernel) _ _
    (applyMatch_body_returns state language contexts rows compiled matched)
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl <;> decide +kernel
  · rw [captured]
    exact applyMatch_clause contexts rows compiled.val matched

private def matchedRootEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:matched-root-reducts")[0]'(by decide +kernel)

private def matchedRootEnvironment {language : LanguageDef} (contexts : RewriteRule → Term)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (compiled : RuleProgram language.rewrites) (observations : List BoundMatch) : Subst :=
  [("matches", encoded (matchesTerm observations)), ("rows", encoded (providerRowsTerm rows)),
   ("rewrites", compiledRows contexts compiled)]

private def matchedRootPairs : List (Atom × Atom) :=
  [(v "head", a "gslt:rule:apply-root-match" [v "rewrites", v "rows", v "matched"]),
   (v "tail", a "gslt:rule:matched-root-reducts" [v "rewrites", v "rows", v "rest"])]

private def matchedRootResult : Atom := a "gslt:automata:append" [v "head", v "tail"]
private def matchedRootConsBody : Atom :=
  a "let*" [.expression (matchedRootPairs.map fun pair => .expression [pair.1, pair.2]), matchedRootResult]

private def matchedRootCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [v "matched", v "rest"], matchedRootConsBody)]

private theorem matchedRoot_shape : matchedRootEquation.body =
    a "case" [v "matches", .expression (matchedRootCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem matchedRoot_clause {language : LanguageDef} (contexts : RewriteRule → Term)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (compiled : RuleProgram language.rewrites) (observations : List BoundMatch) :
    clauses program "gslt:rule:matched-root-reducts"
      [compiledRows contexts compiled, encoded (providerRowsTerm rows), encoded (matchesTerm observations)] =
      [.evaluate (matchedRootEnvironment contexts rows compiled observations) matchedRootEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:matched-root-reducts").filterMap _ = _
  rw [show equations "gslt:rule:matched-root-reducts" = [matchedRootEquation] from rfl]
  have formals : matchedRootEquation.arguments = [v "rewrites", v "rows", v "matches"] := by
    decide +kernel
  simp [formals, matchedRootEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem matchedRoot_call (caller : Subst) (state : State) (language : LanguageDef)
    (contexts : RewriteRule → Term)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (compiled : RuleProgram language.rewrites) (observations : List BoundMatch) (one two three answer : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [compiledRows contexts compiled, encoded (providerRowsTerm rows), encoded (matchesTerm observations)])
    (returned : PureReturns program (matchedRootEnvironment contexts rows compiled observations) state
      matchedRootEquation.body state answer) :
    PureReturns program caller state (a "gslt:rule:matched-root-reducts" [one, two, three]) state answer := by
  apply PureData.raw_authored_call_return program caller
    (matchedRootEnvironment contexts rows compiled observations) state state "gslt:rule:matched-root-reducts"
    [one, two, three] matchedRootEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl <;> decide +kernel
  · rw [captured]
    exact matchedRoot_clause contexts rows compiled observations

private theorem matchedRoot_body_returns (state : State) (language : LanguageDef)
    (contexts : RewriteRule → Term)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (compiled : VariableSourceProgram language.rewrites) (observations : List BoundMatch) :
    PureReturns program (matchedRootEnvironment contexts rows compiled.val observations) state
      matchedRootEquation.body state (patternsValue (runMatches rows language compiled.val observations)) := by
  induction observations with
  | nil =>
      let caller := matchedRootEnvironment contexts rows compiled.val []
      rw [matchedRoot_shape]
      simp only [runMatches, List.flatMap_nil, patternsValue, InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
      apply case_returns program caller caller state state state (v "matches") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ matchedRootCases (read_cases_encoded _) _ _ _
      · simpa [caller, matchedRootEnvironment, matchesTerm, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "matches"
      · simp [matchedRootCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons matched observations ih =>
      let caller := matchedRootEnvironment contexts rows compiled.val (matched :: observations)
      let selected := ("rest", encoded (matchesTerm observations)) :: ("matched", encoded (boundMatchTerm matched)) :: caller
      let headResults := runMatch rows language compiled.val matched
      let tailResults := runMatches rows language compiled.val observations
      let headBound := ("head", patternsValue headResults) :: selected
      let tailBound := ("tail", patternsValue tailResults) :: headBound
      have headReturned := apply_match_captured_returns selected state language contexts rows compiled matched
        (v "rewrites") (v "rows") (v "matched")
        (by simp [selected, caller, matchedRootEnvironment, applySubst, Subst.lookup])
      have tailReturned := matchedRoot_call headBound state language contexts rows compiled observations
        (v "rewrites") (v "rows") (v "rest") (patternsValue tailResults)
        (by simp [headBound, selected, caller, matchedRootEnvironment, applySubst, Subst.lookup]) ih
      rw [matchedRoot_shape]
      apply case_returns program caller selected state state state (v "matches")
        (encoded (matchesTerm (matched :: observations))) matchedRootConsBody _ _
        matchedRootCases (read_cases_encoded _) _ _ _
      · simpa [caller, matchedRootEnvironment, applySubst, Subst.lookup] using variable_returns program caller state "matches"
      · simp [matchedRootCases, matchesTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, matchedRootEnvironment]
      · have bound : PureData.BindingsReturn program selected state matchedRootPairs tailBound state := by
          apply PureData.BindingsReturn.cons (bound := headBound) headReturned
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, headBound, headResults,
              selected, caller, matchedRootEnvironment]
          apply PureData.BindingsReturn.cons (bound := tailBound) tailReturned
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound,
              headBound, selected, caller, matchedRootEnvironment]
          exact .nil _ _
        change PureReturns program selected state
          (a "let*" [.expression (matchedRootPairs.map fun pair => .expression [pair.1, pair.2]), matchedRootResult]) state _
        apply PureData.let_bindings_return bound
        simp only [runMatches, List.flatMap_cons]
        exact append_captured_returns tailBound state headResults tailResults
          (by simp [tailBound, headBound, applySubst, Subst.lookup])

/-- Ordered dispatch consumes both real matcher observations and all surviving
premise witnesses. It neither sorts nor removes repeated occurrences. -/
theorem matched_root_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (contexts : RewriteRule → Term)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (compiled : VariableSourceProgram language.rewrites) (observations : List BoundMatch) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [compiledRows contexts compiled.val, encoded (providerRowsTerm rows), encoded (matchesTerm observations)]) :
    PureReturns program caller state (a "gslt:rule:matched-root-reducts" [one, two, three]) state
      (patternsValue (runMatches rows language compiled.val observations)) :=
  matchedRoot_call caller state language contexts rows compiled observations one two three _ captured
    (matchedRoot_body_returns state language contexts rows compiled observations)

private def premiseFields (rule : RewriteRule) : Term :=
  match compilePremises? rule.premises with
  | none => .symbol "LNil"
  | some plans => premisesTerm plans

/-- The matcher and dispatcher receive the identical source-derived language
wire, including its authored premise occurrences and administrative fields. -/
theorem language_wire_eq_projection (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites) :
    Conditional.languageTerm language types terms contexts compiled =
      matchingProjectionTerm language types terms (.symbol "LNil") contexts premiseFields := by
  have each (plan : RulePlan) : Conditional.ruleTerm contexts plan =
      rewriteRowTerm contexts premiseFields plan.erase := by
    simp [Conditional.ruleTerm, rewriteRowTerm, premiseFields, RulePlan.erase,
      compilePremises?_erase]
  have rows : Conditional.rulesTerm contexts compiled.plans =
      rewriteRowsTerm contexts premiseFields language.rewrites := by
    calc
      _ = rewriteRowsTerm contexts premiseFields (eraseRulePlans compiled.plans) := by
        simp only [Conditional.rulesTerm, rewriteRowsTerm, eraseRulePlans, encodeList_map]
        congr 1
        funext plan
        exact each plan
      _ = _ := congrArg (rewriteRowsTerm contexts premiseFields) compiled.erase_eq_source
  simp only [Conditional.languageTerm, matchingProjectionTerm, rows]

private theorem compiled_patterns (language : LanguageDef) (compiled : RuleProgram language.rewrites) :
    erasePatterns (compiled.plans.map (·.left)) = MeTTaILSubtermMatchAutomata.languagePatterns language := by
  have same := congrArg (List.map RewriteRule.left) compiled.erase_eq_source
  simpa only [MeTTaILSubtermMatchAutomata.languagePatterns, erasePatterns_eq_map, eraseRulePlans,
    List.map_map, Function.comp_def, RulePlan.erase] using same

theorem run_reference_eq_frontier (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (language : LanguageDef) (compiled : RuleProgram language.rewrites) (subject : PatternPlan) :
    runMatches rows language compiled
      (MeTTaILSubtermMatchAutomata.reference (MeTTaILSubtermMatchAutomata.languagePatterns language) subject) =
      rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase := by
  rw [runMatches_eq_dispatch, MeTTaILMatchAutomataExecution.dispatch_reference]
  rw [← compiled.run_eq_rootFrontier (providerEnv rows) language subject.erase]
  conv_lhs => arg 2; rw [← compiled.erase_eq_source]
  simp only [eraseRulePlans, List.flatMap_map]
  apply List.flatMap_congr
  intro plan member
  rw [run_eq_syntactic (providerEnv rows) language (fun _ => []) plan subject.erase]
  simp [Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing,
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.RuleInterpretation.syntactic,
    RulePlan.erase, Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings,
    applyBindingsScoped_zero_of_binderFree _ _ _ (binderFree_erase plan.right)]

open MeTTaILMatchAutomataExecution (Strategy)

private def matcherHead : Strategy → String
  | .bottomUp => "gslt:automata:language-bottom"
  | .topDown => "gslt:automata:language-top"

private def executorHead : Strategy → String
  | .bottomUp => "gslt:rule:language-bottom-reducts"
  | .topDown => "gslt:rule:language-top-reducts"

private def matcherResult (strategy : Strategy) (patterns : List PatternPlan) (subject : PatternPlan) : Term :=
  match strategy with
  | .bottomUp => MatchAutomataExecution.bottomRunTerm patterns subject
  | .topDown => MatchAutomataExecution.topRunTerm patterns subject

private theorem matcher_result_shape (strategy : Strategy) (patterns : List PatternPlan) (subject : PatternPlan) :
    ∃ reads tests, matcherResult strategy patterns subject =
      MatchAutomataExecution.matchRunTerm
        (MeTTaILSubtermMatchAutomata.reference (erasePatterns patterns) subject) reads tests := by
  cases strategy <;> exact ⟨_, _, rfl⟩

private def languageEquation (strategy : Strategy) : SpaceSemantics.Equation :=
  (equations (executorHead strategy))[0]'(by cases strategy <;> decide +kernel)

private def languageEnvironment (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) : Subst :=
  [("subject", patternValue subject.erase), ("rows", encoded (providerRowsTerm rows)),
   ("language", encoded (Conditional.languageTerm language types terms contexts compiled))]

private def languageResultCases : SpaceSemantics.Cases :=
  [(a "MatchRun" [v "matches", v "reads", v "tests"],
    a "gslt:rule:matched-root-reducts" [v "rewrites", v "rows", v "matches"])]

private def languageMatchBody (strategy : Strategy) : Atom :=
  a "let" [v "matched", a (matcherHead strategy) [v "language", v "subject"],
    a "case" [v "matched", .expression (languageResultCases.map fun row => .expression [row.1, row.2])]]

private def languageCases (strategy : Strategy) : SpaceSemantics.Cases :=
  [(a "GSLTLanguageDefWireV1" [v "name", v "types", v "terms", .symbol "LNil", v "rewrites"],
    languageMatchBody strategy)]

private theorem language_shape (strategy : Strategy) : (languageEquation strategy).body =
    a "case" [v "language", .expression ((languageCases strategy).map fun row => .expression [row.1, row.2])] := by
  cases strategy <;> decide +kernel

private theorem language_clause (strategy : Strategy) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) :
    clauses program (executorHead strategy)
      [encoded (Conditional.languageTerm language types terms contexts compiled), encoded (providerRowsTerm rows),
       patternValue subject.erase] =
      [.evaluate (languageEnvironment language types terms contexts compiled rows subject) (languageEquation strategy).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations (executorHead strategy)).filterMap _ = _
  rw [show equations (executorHead strategy) = [languageEquation strategy] from by cases strategy <;> rfl]
  have formals : (languageEquation strategy).arguments = [v "language", v "rows", v "subject"] := by
    cases strategy <;> decide +kernel
  simp [formals, languageEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem language_body_returns (strategy : Strategy) (state : State)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) :
    PureReturns program (languageEnvironment language types terms contexts compiled rows subject) state
      (languageEquation strategy).body state
      (patternsValue (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)) := by
  let caller := languageEnvironment language types terms contexts compiled rows subject
  let selected := ("rewrites", compiledRows contexts compiled.val) :: ("terms", encoded terms) ::
    ("types", encoded types) :: ("name", encoded (.string language.name)) :: caller
  let patterns := compiled.plans.map (·.left)
  have admitted := compiled_patterns language compiled.val
  have closed : PureReturns MatchAutomataProgram.program [] state
      (a (matcherHead strategy) [encoded (Conditional.languageTerm language types terms contexts compiled.val), patternValue subject.erase])
      state (encoded (matcherResult strategy patterns subject)) := by
    cases strategy with
    | bottomUp =>
        simpa only [matcherHead, matcherResult, language_wire_eq_projection] using
          MatchAutomataExecution.language_bottom_returns state language types terms (.symbol "LNil")
            contexts premiseFields patterns subject admitted
    | topDown =>
        simpa only [matcherHead, matcherResult, language_wire_eq_projection] using
          MatchAutomataExecution.language_top_returns state language types terms (.symbol "LNil")
            contexts premiseFields patterns subject admitted
  have captured : PureReturns MatchAutomataProgram.program selected state
      (a (matcherHead strategy) [v "language", v "subject"]) state
      (encoded (matcherResult strategy patterns subject)) := by
    apply PureData.raw_capture_returns MatchAutomataProgram.program [] selected state state
      (matcherHead strategy)
      [encoded (Conditional.languageTerm language types terms contexts compiled.val), patternValue subject.erase]
      [v "language", v "subject"] _ _ _ _ _ closed
    · cases strategy <;> decide +kernel
    · intro index bounded
      have small : index = 0 ∨ index = 1 := by
        simp only [List.length_cons, List.length_nil] at bounded
        omega
      rcases small with rfl | rfl <;> cases strategy <;> decide +kernel
    · cases strategy <;> decide
    · simp [selected, caller, languageEnvironment, applySubst, Subst.lookup]
  have matched := automata_captured_returns
    (show codeWithin RuleExecutionProgram.matcherHead
      (a (matcherHead strategy) [v "language", v "subject"]) = true from by cases strategy <;> decide +kernel)
    captured
  obtain ⟨reads, tests, shape⟩ := matcher_result_shape strategy patterns subject
  rw [shape] at matched
  have sourcePatterns : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language := admitted
  rw [sourcePatterns] at matched
  let observations := MeTTaILSubtermMatchAutomata.reference
    (MeTTaILSubtermMatchAutomata.languagePatterns language) subject
  let matchValue := encoded (MatchAutomataExecution.matchRunTerm observations reads tests)
  let bound := ("matched", matchValue) :: selected
  let matchBound := ("tests", number tests) :: ("reads", number reads) ::
    ("matches", encoded (matchesTerm observations)) :: bound
  rw [language_shape]
  apply case_returns program caller selected state state state (v "language")
    (encoded (Conditional.languageTerm language types terms contexts compiled.val)) (languageMatchBody strategy) _ _
    (languageCases strategy) (read_cases_encoded _) _ _ _
  · simpa [caller, languageEnvironment, applySubst, Subst.lookup] using variable_returns program caller state "language"
  · simp [languageCases, Conditional.languageTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, selected, caller, languageEnvironment, compiledRows]
  · unfold languageMatchBody
    apply let_returns program selected bound state state state (v "matched") _ _ _ _ matched _ _
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, matchValue,
        selected, caller, languageEnvironment, observations]
    · apply case_returns program bound matchBound state state state (v "matched") matchValue
        (a "gslt:rule:matched-root-reducts" [v "rewrites", v "rows", v "matches"]) _ _
        languageResultCases (read_cases_encoded _) _ _ _
      · simpa [bound, matchValue, applySubst, Subst.lookup] using variable_returns program bound state "matched"
      · simp [languageResultCases, matchValue, MatchAutomataExecution.matchRunTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, matchBound, bound, number, selected, caller, languageEnvironment]
      · rw [← run_reference_eq_frontier rows language compiled.val subject]
        exact matched_root_captured_returns matchBound state language contexts rows compiled observations
          (v "rewrites") (v "rows") (v "matches")
          (by simp [matchBound, bound, selected, caller, languageEnvironment, applySubst, Subst.lookup])

def languageQueryTerm (strategy : Strategy) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) : Term :=
  .application (executorHead strategy)
    [Conditional.languageTerm language types terms contexts compiled, providerRowsTerm rows,
     InferenceCettaWire.encodePattern subject.erase]

/-- Both complete native entries execute their shared matcher and its retained
bindings before the canonical guarded row continuations. -/
theorem language_captured_returns (strategy : Strategy) (caller : Subst) (state : State)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [encoded (Conditional.languageTerm language types terms contexts compiled.val), encoded (providerRowsTerm rows),
       patternValue subject.erase]) :
    PureReturns program caller state (a (executorHead strategy) [one, two, three]) state
      (patternsValue (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)) := by
  apply PureData.raw_authored_call_return program caller
    (languageEnvironment language types terms contexts compiled rows subject) state state (executorHead strategy)
    [one, two, three] (languageEquation strategy).body _
    (by cases strategy <;> decide) (by cases strategy <;> decide)
    (by cases strategy <;> decide) (by cases strategy <;> decide +kernel) _ _
    (language_body_returns strategy state language types terms contexts compiled rows subject)
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl <;> cases strategy <;> decide +kernel
  · rw [captured]
    exact language_clause strategy language types terms contexts compiled rows subject

theorem language_returns (strategy : Strategy) (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) :
    PureReturns program [] state (encoded (languageQueryTerm strategy language types terms contexts compiled rows subject)) state
      (patternsValue (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)) :=
  language_captured_returns strategy [] state language types terms contexts compiled rows subject _ _ _ (by simp)

theorem language_completed_iff (strategy : Strategy) (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate [] (encoded (languageQueryTerm strategy language types terms contexts compiled rows subject)) } =
        .complete after answers input output) ↔
      after = state ∧ answers = [patternsValue (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (language_returns strategy state language types terms contexts compiled rows subject) after answers input output

theorem language_derivation_iff (strategy : Strategy) (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (languageQueryTerm strategy language types terms contexts compiled rows subject)) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [patternsValue (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (language_returns strategy state language types terms contexts compiled rows subject) after answers input output

def ObservesRootReduct (strategy : Strategy) (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) (target : Pattern) : Prop :=
  ∃ reducts : List Pattern,
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (languageQueryTerm strategy language types terms contexts compiled rows subject)) }
      (.complete state [patternsValue reducts] [] []) ∧ target ∈ reducts

theorem observes_root_iff_gslt_step (strategy : Strategy) (state : State)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (equationFree : language.isEquationFree = true) (target : Pattern) :
    ObservesRootReduct strategy state language types terms contexts compiled rows subject target ↔
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing (providerEnv rows) language).Step subject.erase target := by
  rw [← Conditional.observes_root_iff_gslt_step state language types terms contexts compiled rows subject equationFree target]
  unfold ObservesRootReduct Conditional.ObservesRootReduct
  simp only [language_derivation_iff, Conditional.language_root_derivation_iff]

namespace Controls

/-- Both automata use the existing guarded-rule corpus, rather than a second
set of example semantics. -/
def queryTerm (strategy : Strategy) (fixture : Conditional.Controls.Fixture) : Term :=
  languageQueryTerm strategy fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") fixture.compiled fixture.rows fixture.subject

theorem fixture_returns (strategy : Strategy) (fixture : Conditional.Controls.Fixture)
    (admitted : fixture.plans.all (fun plan => plan.variablePremises?.isSome) = true) (state : State) :
    PureReturns program [] state (encoded (queryTerm strategy fixture)) state
      (encoded fixture.expectedTerm) :=
  language_returns strategy state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled admitted) fixture.rows fixture.subject

theorem incorrect_observation_refused (strategy : Strategy) (fixture : Conditional.Controls.Fixture)
    (admitted : fixture.plans.all (fun plan => plan.variablePremises?.isSome) = true)
    (incorrect : List Pattern) (state : State) (different : incorrect ≠ fixture.results) :
    ¬ DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (queryTerm strategy fixture)) }
      (.complete state [patternsValue incorrect] [] []) := by
  intro executed
  apply Conditional.Controls.Fixture.refuses_incorrect fixture admitted state incorrect different
  apply (Conditional.language_root_derivation_iff state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled admitted) fixture.rows fixture.subject state _ [] []).mpr
  exact (language_derivation_iff strategy state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled admitted) fixture.rows fixture.subject state _ [] []).mp executed

/-- A future row occurrence is rejected even if the supplied bindings would
otherwise satisfy a row's guards. Only a real authored occurrence can run. -/
theorem future_occurrence_returns_nil (state : State) (language : LanguageDef)
    (contexts : RewriteRule → Term) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (compiled : VariableSourceProgram language.rewrites) (seed : Bindings) :
    PureReturns program [] state
      (a "gslt:rule:apply-root-match"
        [compiledRows contexts compiled.val, encoded (providerRowsTerm rows),
         encoded (boundMatchTerm ⟨⟨[], compiled.plans.length⟩, seed⟩)]) state (.symbol "LNil") := by
  simpa [runMatch, VariableSourceProgram.plans, List.getElem?_eq_none, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
    apply_match_captured_returns [] state language contexts rows compiled
      ⟨⟨[], compiled.plans.length⟩, seed⟩
      (compiledRows contexts compiled.val) (encoded (providerRowsTerm rows))
      (encoded (boundMatchTerm ⟨⟨[], compiled.plans.length⟩, seed⟩)) (by simp)

end Controls

#print axioms runMatch_eq_dispatch
#print axioms runMatches_eq_dispatch
#print axioms row_at_returns
#print axioms apply_match_captured_returns
#print axioms matched_root_captured_returns
#print axioms language_wire_eq_projection
#print axioms run_reference_eq_frontier
#print axioms language_returns
#print axioms language_completed_iff
#print axioms language_derivation_iff
#print axioms observes_root_iff_gslt_step
#print axioms Controls.fixture_returns
#print axioms Controls.incorrect_observation_refused
#print axioms Controls.future_occurrence_returns_nil

end Matched

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution.ScopedObservation

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire.ContextObservation
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Eval RuleExecutionProgram

open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.ScopedPermissions
open Mettapedia.GSLT.LanguageDef.BindingSyntax

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (value : CettaTerm) : Atom := CettaWireAtom.encode value
private abbrev patternValue (value : Pattern) : Atom := encoded (encodePattern value)
private abbrev contextValue (context : OneHoleContext) : Atom := encoded (contextTerm context)
private abbrev permissionValue (permissions : OperationalPermissions) : Atom := encoded (permissionsTerm permissions)

private inductive Helper where | focus
private def Helper.head : Helper → String
  | .focus => "gslt:rule:scope-focus-observation"
private def Helper.names : Helper → List String
  | .focus => ["ordinal", "original", "rule", "permissions", "address", "context", "source", "target"]
private def equation (helper : Helper) : SpaceSemantics.Equation :=
  (program.equations.filter fun row => row.head == helper.head)[0]'(by cases helper; decide +kernel)
private def environment (helper : Helper) (values : List Atom) : Subst := (helper.names.zip values).reverse

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses program helper.head values = [.evaluate (environment helper values) (equation helper).body] :=
  PureData.named_equation_clause program helper.head (equation helper) helper.names values
    (by cases helper; rfl) (by cases helper; decide +kernel) (by cases helper; decide) length

private theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw program helper.head index = true := by
  cases helper; simp only [Helper.names, List.length_cons, List.length_nil] at bounded
  all_goals interval_cases index <;> decide +kernel

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (environment helper values) state (equation helper).body state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (environment helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper; decide) (by cases helper; decide) (by cases helper; decide)
    (by cases helper; decide +kernel)
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

private theorem named_let_returns (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom) (fresh : Subst.lookup caller name = none)
    (computed : PureReturns program caller state expression state value)
    (continued : PureReturns program ((name, value) :: caller) state body state answer) :
    PureReturns program caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns program caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed _ continued
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

private theorem bool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns program caller state condition state (Effects.boolean value))
    (returned : PureReturns program caller state (if value then yes else no) state answer) :
    PureReturns program caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns program caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

private inductive Constructor where | observation
private def Constructor.head : Constructor → String
  | .observation => "ScopedFocusObservation"

private theorem constructor_template (constructor : Constructor) (names : List String) :
    PureData.Template program (a constructor.head (names.map v)) := by
  apply PureData.Template.constructor constructor.head _
    (by cases constructor; decide +kernel) (by cases constructor; decide)
  intro argument member
  obtain ⟨name, _, same⟩ := List.mem_map.mp member
  subst argument
  exact .captured name
def focusQueryTerm (ordinal declarationIndex : Nat) (rule : RewriteRule)
    (permissions : OperationalPermissions) (address : List Nat)
    (context : OneHoleContext) (source target : Pattern) : CettaTerm :=
  .application "gslt:rule:scope-focus-observation"
    [.natural ordinal, .natural declarationIndex, AuthoredRule.rewriteTerm rule,
      permissionsTerm permissions, encodeList CettaTerm.natural address, contextTerm context,
      encodePattern source, encodePattern target]

private def focusBody : Atom :=
  a "if" [a "gslt:rule:scope-permitted" [v "permissions", v "context"],
    a "let" [v "whole-source", a "gslt:rule:scope-fill" [v "context", v "source"],
      a "let" [v "whole-target", a "gslt:rule:scope-fill" [v "context", v "target"],
        a "Some" [a "ScopedFocusObservation"
          (["ordinal", "original", "rule", "permissions", "address", "context", "source", "target",
            "whole-source", "whole-target"].map v)]]], .symbol "None"]

private theorem focus_shape : (equation .focus).body = focusBody := by decide +kernel

private theorem focus_template : PureData.Template program
    (a "Some" [a "ScopedFocusObservation"
      (["ordinal", "original", "rule", "permissions", "address", "context", "source", "target",
        "whole-source", "whole-target"].map v)]) := by
  apply PureData.Template.constructor "Some" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst argument
  exact constructor_template .observation _

/-- The actual source returns both filled endpoints only when the supplied
capability permits this same original context. The full authored row and all
physical positions are captured data throughout the computation. -/
theorem focus_returns (state : State) (ordinal declarationIndex : Nat) (rule : RewriteRule)
    (permissions : OperationalPermissions) (address : List Nat)
    (context : OneHoleContext) (source target : Pattern) :
    PureReturns program [] state (encoded (focusQueryTerm ordinal declarationIndex rule permissions address context source target))
      state (encoded (focusObservationOptionTerm ordinal declarationIndex rule permissions address context source target)) := by
  let values := [encoded (.natural ordinal), encoded (.natural declarationIndex), encoded (AuthoredRule.rewriteTerm rule),
    permissionValue permissions, encoded (encodeList CettaTerm.natural address), contextValue context,
    patternValue source, patternValue target]
  let caller := environment .focus values
  let sourceBound := ("whole-source", patternValue (context.fill source)) :: caller
  let targetBound := ("whole-target", patternValue (context.fill target)) :: sourceBound
  apply helper_call .focus [] state _ values _ rfl
    (by simp [values, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst])
  rw [focus_shape]
  apply bool_if_returns caller state _ (permissions.permitsContext context)
  · exact Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.ContextObservation.permitted_captured_returns caller state permissions context (v "permissions") (v "context")
      (by simp [caller, values, environment, Helper.names, applySubst, Subst.lookup])
  · cases allowed : permissions.permitsContext context with
    | false =>
        simpa only [allowed, Bool.false_eq_true, ite_false, focusObservationOptionTerm,
          encoded, CettaWireAtom.encode] using symbol_returns program caller state "None"
    | true =>
        simp only [allowed, ite_true, focusObservationOptionTerm]
        apply named_let_returns caller state "whole-source" _ (patternValue (context.fill source)) _ _
        · simp [caller, values, environment, Helper.names, Subst.lookup]
        · exact Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.ContextObservation.fill_captured_returns caller state context source (v "context") (v "source")
            (by simp [caller, values, environment, Helper.names, applySubst, Subst.lookup])
        · apply named_let_returns sourceBound state "whole-target" _ (patternValue (context.fill target)) _ _
          · simp [sourceBound, caller, values, environment, Helper.names, Subst.lookup]
          · exact Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.ContextObservation.fill_captured_returns sourceBound state context target (v "context") (v "target")
              (by simp [sourceBound, caller, values, environment, Helper.names, applySubst, Subst.lookup])
          · simpa [targetBound, sourceBound, caller, values, environment, Helper.names,
              applySubst, applySubst.applySubstList, Subst.lookup, focusObservationTerm, encoded,
              CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return program targetBound state _ focus_template

theorem focus_completed_iff (state after : State) (ordinal declarationIndex : Nat) (rule : RewriteRule)
    (permissions : OperationalPermissions) (address : List Nat)
    (context : OneHoleContext) (source target : Pattern) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state := state, control := .evaluate [] (encoded
        (focusQueryTerm ordinal declarationIndex rule permissions address context source target)) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded
        (focusObservationOptionTerm ordinal declarationIndex rule permissions address context source target)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (focus_returns state ordinal declarationIndex rule permissions address context source target)
    after answers input output

theorem focus_derivation_iff (state after : State) (ordinal declarationIndex : Nat) (rule : RewriteRule)
    (permissions : OperationalPermissions) (address : List Nat)
    (context : OneHoleContext) (source target : Pattern) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state := state, control := .evaluate [] (encoded
        (focusQueryTerm ordinal declarationIndex rule permissions address context source target)) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded
        (focusObservationOptionTerm ordinal declarationIndex rule permissions address context source target)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (focus_returns state ordinal declarationIndex rule permissions address context source target)
    after answers input output

theorem focus_success_iff (state : State) (ordinal declarationIndex : Nat) (rule : RewriteRule)
    (permissions : OperationalPermissions) (address : List Nat)
    (context : OneHoleContext) (source target : Pattern) :
    (∃ fuel, run program fuel { state := state, control := .evaluate [] (encoded
        (focusQueryTerm ordinal declarationIndex rule permissions address context source target)) } =
      .complete state [encoded (.application "Some"
        [focusObservationTerm ordinal declarationIndex rule permissions address context source target])] [] []) ↔
      permissions.permitsContext context = true := by
  rw [focus_completed_iff]
  cases allowed : permissions.permitsContext context <;>
    simp [focusObservationOptionTerm, allowed, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]

theorem focus_refusal_iff (state : State) (ordinal declarationIndex : Nat) (rule : RewriteRule)
    (permissions : OperationalPermissions) (address : List Nat)
    (context : OneHoleContext) (source target : Pattern) :
    (∃ fuel, run program fuel { state := state, control := .evaluate [] (encoded
        (focusQueryTerm ordinal declarationIndex rule permissions address context source target)) } =
      .complete state [encoded (.symbol "None")] [] []) ↔
      permissions.permitsContext context = false := by
  rw [focus_completed_iff]
  cases allowed : permissions.permitsContext context <;>
    simp [focusObservationOptionTerm, allowed, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]

def receiptQueryTerm (permissions : OperationalPermissions) (receipt : Receipt) : CettaTerm :=
  focusQueryTerm receipt.job.ordinal receipt.job.declaration.declarationIndex receipt.job.declaration.authored
    permissions receipt.job.site.address receipt.job.site.context receipt.job.site.focus receipt.localTarget

def receiptObservationTerm (permissions : OperationalPermissions) (receipt : Receipt) : CettaTerm :=
  focusObservationTerm receipt.job.ordinal receipt.job.declaration.declarationIndex receipt.job.declaration.authored
    permissions receipt.job.site.address receipt.job.site.context receipt.job.site.focus receipt.localTarget

/-- A receipt from the original guarded execution earns the source permission
observation and both actual fill endpoints. The supplied plan remains the
capability authority, and the root certificate retains the full ordered guard
history, captures and physical selected rule occurrence. -/
theorem guarded_receipt_source_observation
    {plan : Plan} {bound : List TypeExpr} {sort : TypeExpr} {source : Pattern}
    (state : State) (receipt : Receipt) (valid : receipt.Valid plan bound sort source) :
    PureReturns program [] state (CettaWireAtom.encode (receiptQueryTerm plan.permissions.sites receipt)) state
      (CettaWireAtom.encode (.application "Some" [receiptObservationTerm plan.permissions.sites receipt])) ∧
    GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan)
      receipt.job.site.focusBound receipt.job.site.focusType receipt.job.site.focus receipt.job.ordinal
      receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory receipt.localTarget ∧
    receipt.job.site.address = contextAddress receipt.job.site.context ∧
    receipt.job.site.context.fill receipt.job.site.focus = source ∧
    receipt.job.site.context.fill receipt.localTarget = receipt.target := by
  have allowed := valid.1.2.permitted
  have returned := focus_returns state receipt.job.ordinal receipt.job.declaration.declarationIndex
    receipt.job.declaration.authored plan.permissions.sites receipt.job.site.address receipt.job.site.context
    receipt.job.site.focus receipt.localTarget
  refine ⟨?_, valid.2.1, valid.1.2.address_eq, valid.1.2.source_eq, valid.2.2.2.1.symm⟩
  simpa only [focusObservationOptionTerm, allowed, ite_true, receiptQueryTerm, receiptObservationTerm] using returned



/-- Read the actual outer execution cursor. Every answer emitted by its
existing `finishRoot` branch is observed by the source at the same licensed
site, retaining both rule positions and the original guarded-firing evidence.
This adapter does not execute the native premise dispatcher. -/
theorem expanded_guarded_source_observation
    (request : GeneralRuleJobExecution.Request) (frame : GeneralRuleJobExecution.Frame request)
    (state : State) (answer : GeneralRuleJobExecution.Answer request)
    (emitted : answer ∈ (GeneralRuleJobExecution.expand request (.root frame)).answers) :
    answer.val.job = request.job ∧
      PureReturns program [] state (CettaWireAtom.encode (receiptQueryTerm request.plan.permissions.sites answer.val)) state
        (CettaWireAtom.encode (.application "Some" [receiptObservationTerm request.plan.permissions.sites answer.val])) ∧
      GeneralPremise.RootFiring request.environment
        answer.val.job.site.focusBound answer.val.job.site.focusType answer.val.job.site.focus answer.val.job.ordinal
        answer.val.matcherTrace answer.val.captured answer.val.completed answer.val.premiseHistory answer.val.localTarget ∧
      answer.val.job.site.address = contextAddress answer.val.job.site.context ∧
      answer.val.job.site.context.fill answer.val.job.site.focus = request.source ∧
      answer.val.job.site.context.fill answer.val.localTarget = answer.val.target := by
  refine ⟨?_, guarded_receipt_source_observation state answer.val answer.property⟩
  unfold GeneralRuleJobExecution.expand at emitted
  cases found : frame.state.answers[frame.cursor]? with
  | none => simp only [found] at emitted; split at emitted <;> simp at emitted
  | some result =>
      simp only [found] at emitted
      cases result with
      | root trace captured completed history target firing =>
          have finished : GeneralRuleJobExecution.finishRoot request frame.licensed trace captured completed
              history target firing = some answer := by
            cases computed : GeneralRuleJobExecution.finishRoot request frame.licensed trace captured completed
                history target firing with
            | none => simp [computed] at emitted
            | some value =>
                have same : answer = value := by simpa [computed] using emitted
                simp only [← same]
          unfold GeneralRuleJobExecution.finishRoot GeneralRuleJobExecution.finishRootIn at finished
          split at finished
          next represented =>
            split at finished
            next typed =>
              exact (congrArg (fun value : GeneralRuleJobExecution.Answer request => value.val.job)
                (Option.some.inj finished)).symm
            next => simp at finished
          next => simp at finished



/-- The original finite-work cursor retains every guarded answer with the
same job and source observation. Its completion budget is the existing work
forest, rather than an externally supplied bound or answer oracle. -/
theorem finished_guarded_source_observation
    (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (state : State) (answer : GeneralRuleJobExecution.Answer request)
    (emitted : answer ∈ (GeneralRuleJobExecution.finishState request licensed).answers) :
    answer.val.job = request.job ∧
      PureReturns program [] state (CettaWireAtom.encode (receiptQueryTerm request.plan.permissions.sites answer.val)) state
        (CettaWireAtom.encode (.application "Some" [receiptObservationTerm request.plan.permissions.sites answer.val])) ∧
      GeneralPremise.RootFiring request.environment
        answer.val.job.site.focusBound answer.val.job.site.focusType answer.val.job.site.focus answer.val.job.ordinal
        answer.val.matcherTrace answer.val.captured answer.val.completed answer.val.premiseHistory answer.val.localTarget ∧
      answer.val.job.site.address = contextAddress answer.val.job.site.context ∧
      answer.val.job.site.context.fill answer.val.job.site.focus = request.source ∧
      answer.val.job.site.context.fill answer.val.localTarget = answer.val.target := by
  obtain ⟨result, _, projected⟩ := (GeneralRuleJobExecution.finishState_exact_roots request licensed answer).mp emitted
  exact ⟨GeneralRuleJobExecution.projection_job projected,
    guarded_receipt_source_observation state answer.val answer.property⟩

/-- Exact guarded receipt coverage is retained when its source permission
and fill observation is attached. Source permission alone does not replace
membership in the original guarded execution. -/
theorem finished_receipt_and_source_iff
    (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (stratified : GeneralPremise.checkStepStratification request.environment.language = true)
    (state : State) (receipt : Receipt) :
    (receipt ∈ (GeneralRuleJobExecution.finishState request licensed).answers.map Subtype.val ∧
      PureReturns program [] state (CettaWireAtom.encode (receiptQueryTerm request.plan.permissions.sites receipt)) state
        (CettaWireAtom.encode (.application "Some" [receiptObservationTerm request.plan.permissions.sites receipt]))) ↔
      receipt.Valid request.plan request.bound request.expected request.source ∧ receipt.job = request.job := by
  constructor
  · intro emitted
    exact (GeneralRuleJobExecution.finishState_receipt_iff request licensed stratified receipt).mp emitted.1
  · rintro ⟨valid, same⟩
    exact ⟨(GeneralRuleJobExecution.finishState_receipt_iff request licensed stratified receipt).mpr ⟨valid, same⟩,
      (guarded_receipt_source_observation state receipt valid).1⟩

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ScopedEncoding
open Mettapedia.CategoryTheory.GroundPath
open _root_.CategoryTheory

variable {language : LanguageDef}
local instance : Quiver (Scope (signatureOf language)) := bindingFrameQuiver (signatureOf language)

/-- Source success at an intrinsic context is equivalent to independently
enabled execution and the existing permitted path, including binder frames
compressed into authored constructor parameters. -/
theorem source_path_permission_iff (state : State) (language : LanguageDef)
    (ordinal declarationIndex : Nat) (rule : RewriteRule) (permissions : OperationalPermissions) (address : List Nat)
    {sourceScope targetScope : Scope (signatureOf language)}
    (context : BindingContext (signatureOf language) sourceScope targetScope) (source target : Pattern) :
    (∃ fuel, run program fuel
      {state := state, control := .evaluate [] (CettaWireAtom.encode
        (focusQueryTerm ordinal declarationIndex rule permissions address (contextZipper context) source target))} =
      .complete state [CettaWireAtom.encode (.application "Some"
        [focusObservationTerm ordinal declarationIndex rule permissions address (contextZipper context) source target])] [] []) ↔
      permissions.enabled = true ∧
        FramePermission.PermittedPath (framePermission (signatureOf language) (slotPermission permissions)) context := by
  rw [focus_success_iff, contextZipper_permitted, pathAllowed_iff]

namespace Controls

open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.Controls
open ScopedPermissionControls AmbientControls RawInstantiationControls InputControls

theorem full_authored_metadata_is_retained :
    focusObservationTerm 0 0 outputRule boxCapabilities openSite.address boxBodyContext openSourceTarget openSourceResult ≠
      focusObservationTerm 0 0 {outputRule with bindings := none} boxCapabilities openSite.address
        boxBodyContext openSourceTarget openSourceResult := by
  intro same
  have authored := (focusObservation_retains_origins same).2.2.1
  have attached := congrArg RewriteRule.bindings authored
  cases attached

theorem physical_selected_and_original_positions_remain_distinct :
    focusObservationTerm 0 1 outputRule boxCapabilities openSite.address boxBodyContext openSourceTarget openSourceResult ≠
      focusObservationTerm 1 0 outputRule boxCapabilities openSite.address boxBodyContext openSourceTarget openSourceResult := by
  intro same
  have positions := focusObservation_retains_origins same
  cases positions.1

theorem actual_source_accepts_open_binder (state : State) :
    ∃ fuel, run program fuel
      {state := state, control := .evaluate [] (CettaWireAtom.encode
        (focusQueryTerm 0 0 outputRule boxCapabilities openSite.address boxBodyContext openSourceTarget openSourceResult))} =
      .complete state [CettaWireAtom.encode (.application "Some"
        [focusObservationTerm 0 0 outputRule boxCapabilities openSite.address boxBodyContext openSourceTarget openSourceResult])] [] [] :=
  (focus_success_iff state 0 0 outputRule boxCapabilities openSite.address boxBodyContext
    openSourceTarget openSourceResult).mpr (by decide +kernel)

theorem actual_source_refuses_blocked_binder (state : State) :
    ∃ fuel, run program fuel
      {state := state, control := .evaluate [] (CettaWireAtom.encode
        (focusQueryTerm 0 0 outputRule blockedBinderCapabilities openSite.address boxBodyContext
          openSourceTarget openSourceResult))} =
      .complete state [CettaWireAtom.encode (.symbol "None")] [] [] :=
  (focus_refusal_iff state 0 0 outputRule blockedBinderCapabilities openSite.address boxBodyContext
    openSourceTarget openSourceResult).mpr (by decide +kernel)

theorem actual_source_refuses_blocked_constructor (state : State) :
    ∃ fuel, run program fuel
      {state := state, control := .evaluate [] (CettaWireAtom.encode
        (focusQueryTerm 0 0 outputRule blockedConstructorCapabilities openSite.address boxBodyContext
          openSourceTarget openSourceResult))} =
      .complete state [CettaWireAtom.encode (.symbol "None")] [] [] :=
  (focus_refusal_iff state 0 0 outputRule blockedConstructorCapabilities openSite.address boxBodyContext
    openSourceTarget openSourceResult).mpr (by decide +kernel)

theorem actual_source_stopped_root_refused (state : State) :
    ∃ fuel, run program fuel
      {state := state, control := .evaluate [] (CettaWireAtom.encode
        (focusQueryTerm 0 0 outputRule .stopped [] .hole openSourceTarget openSourceResult))} =
      .complete state [CettaWireAtom.encode (.symbol "None")] [] [] :=
  (focus_refusal_iff state 0 0 outputRule .stopped [] .hole openSourceTarget openSourceResult).mpr rfl

theorem actual_source_substitution_permission_refused (state : State) :
    ∃ fuel, run program fuel
      {state := state, control := .evaluate [] (CettaWireAtom.encode
        (focusQueryTerm 0 0 outputRule .all [0] (.substBody .hole (.bvar 0)) openSourceTarget openSourceResult))} =
      .complete state [CettaWireAtom.encode (.symbol "None")] [] [] :=
  (focus_refusal_iff state 0 0 outputRule .all [0] (.substBody .hole (.bvar 0))
    openSourceTarget openSourceResult).mpr rfl

theorem actual_source_unresolved_rest_refused (state : State) :
    ∃ fuel, run program fuel
      {state := state, control := .evaluate [] (CettaWireAtom.encode
        (focusQueryTerm 0 0 outputRule .all [0]
          (.collection .vec [] .hole [] (some "tail")) openSourceTarget openSourceResult))} =
      .complete state [CettaWireAtom.encode (.symbol "None")] [] [] :=
  (focus_refusal_iff state 0 0 outputRule .all [0] (.collection .vec [] .hole [] (some "tail"))
    openSourceTarget openSourceResult).mpr rfl

theorem blocked_context_keeps_structural_match (state : State) :
    ScopedRuleMatching.matchRuleAt outputRule outputSpec 1 openSourceTarget = [[("P", openCapture)]] ∧
      ∃ fuel, run program fuel
        {state := state, control := .evaluate [] (CettaWireAtom.encode
          (focusQueryTerm 0 0 outputRule blockedBinderCapabilities openSite.address boxBodyContext
            openSourceTarget openSourceResult))} =
        .complete state [CettaWireAtom.encode (.symbol "None")] [] [] :=
  ⟨whole_actual_match_keeps_ambient_dependency.1, actual_source_refuses_blocked_binder state⟩

def openRequest : GeneralRuleJobExecution.Request :=
  ⟨guardedScopedPlan, [], t, openWholeSource, admittedOpenJob⟩

def openMachine : GeneralRuleJobExecution.State openRequest :=
  GeneralRuleJobExecution.finishState openRequest complete_plan_has_original_licensed_open_job

theorem original_open_job_machine_drains :
    GeneralRuleJobExecution.settled openMachine = true :=
  List.isEmpty_iff.mpr (GeneralRuleJobExecution.finishState_settled
    openRequest complete_plan_has_original_licensed_open_job)

/-- The general admission plan accepts this scoped rule; the older universal
resolution checker has a separate zero-dependency restriction. -/
theorem original_static_resolution_gate_refuses_scoped_dependencies :
    guardedScopedPlan.complete = true ∧
      GeneralPremise.Static.checkLanguage openRequest.environment = false := by
  exact ⟨actual_admission_keeps_guarded_scoped_parent_and_child.2.2, by cbv⟩

/-- Observe a result produced by the original machine, without supplying a
root-firing premise to the source endpoint. -/
theorem original_open_job_machine_emits_source_observation (state : State) :
    ∃ answer ∈ openMachine.answers,
      answer.val.target = openWholeTarget ∧
      PureReturns program [] state (CettaWireAtom.encode
        (receiptQueryTerm openRequest.plan.permissions.sites answer.val)) state
        (CettaWireAtom.encode (.application "Some"
          [receiptObservationTerm openRequest.plan.permissions.sites answer.val])) ∧
      GeneralPremise.RootFiring openRequest.environment
        answer.val.job.site.focusBound answer.val.job.site.focusType answer.val.job.site.focus answer.val.job.ordinal
        answer.val.matcherTrace answer.val.captured answer.val.completed answer.val.premiseHistory answer.val.localTarget := by
  obtain ⟨trace, valid⟩ := complete_plan_emits_actual_guarded_open_receipt.2
  obtain ⟨answer, emitted, same⟩ := GeneralRuleJobExecution.finishState_receipt_complete
    (request := openRequest) complete_plan_has_original_licensed_open_job (by cbv) valid rfl
  have observation := guarded_receipt_source_observation state answer.val answer.property
  refine ⟨answer, emitted, ?_, observation.1, observation.2.1⟩
  rw [same]
  rfl

/-- Permission and fill observations cannot discharge an earlier guard. -/
theorem allowed_observation_keeps_missing_guard_blocked (state : State) :
    (∃ fuel, run program fuel
      {state := state, control := .evaluate [] (CettaWireAtom.encode
        (focusQueryTerm 1 1 guardedScopedRule boxCapabilities [] .hole openWholeSource openWholeTarget))} =
      .complete state [CettaWireAtom.encode (.application "Some"
        [focusObservationTerm 1 1 guardedScopedRule boxCapabilities [] .hole openWholeSource openWholeTarget])] [] []) ∧
      ∀ (trace : List GeneralScopedMatchMachine.BagChoice) (initial final : ScopedRuleMatching.Assignment)
        (history : List GeneralPremise.Event),
        ¬ GeneralPremise.RootFiring emptyScopedProviderEnvironment [] t openWholeSource 1 trace initial final
          history openWholeTarget := by
  refine ⟨(focus_success_iff state 1 1 guardedScopedRule boxCapabilities [] .hole
    openWholeSource openWholeTarget).mpr rfl, ?_⟩
  intro trace initial final history firing
  cases firing with
  | fire declared specified admitted sourceTyped matched captureTyped premises converted targetTyped =>
      have sameRule : guardedScopedRule = _ := Option.some.inj declared
      subst sameRule
      have specRead : GeneralPremise.specification? emptyScopedProviderEnvironment 1 = some guardedScopedSpec := by
        decide +kernel
      have sameSpec := Option.some.inj (specRead.symm.trans specified)
      subst sameSpec
      exact empty_declared_guard_blocks_actual_scoped_parent.2.2.2 initial final history premises

/-- An allowed zipper observation retains an out-of-scope target as data;
the original guarded execution independently refuses its typing. -/
theorem allowed_observation_keeps_target_typing_separate (state : State) :
    (∃ fuel, run program fuel
      {state := state, control := .evaluate [] (CettaWireAtom.encode
        (focusQueryTerm 0 0 outputRule boxCapabilities openSite.address boxBodyContext openSourceTarget (.bvar 42)))} =
      .complete state [CettaWireAtom.encode (.application "Some"
        [focusObservationTerm 0 0 outputRule boxCapabilities openSite.address boxBodyContext openSourceTarget (.bvar 42)])] [] []) ∧
      ∀ (trace : List GeneralScopedMatchMachine.BagChoice) (initial final : ScopedRuleMatching.Assignment)
        (history : List GeneralPremise.Event),
        ¬ GeneralPremise.RootFiring guardedScopedEnvironment [u] t openSourceTarget 0 trace initial final history (.bvar 42) := by
  refine ⟨(focus_success_iff state 0 0 outputRule boxCapabilities openSite.address boxBodyContext
    openSourceTarget (.bvar 42)).mpr (by decide +kernel), ?_⟩
  intro trace initial final history firing
  cases firing with
  | fire declared specified admitted sourceTyped matched captureTyped premises converted targetTyped =>
      have checked := checkOpenPatternWellSorted_complete targetTyped
      have refused : checkOpenPatternWellSorted guardedScopedEnvironment.language guardedScopedEnvironment.free
          [u] t (.bvar 42) = false := by decide +kernel
      rw [refused] at checked
      cases checked

def unselectedRule : RewriteRule := {outputRule with name := "unselected-scoped-output"}

def filteredLanguage : LanguageDef :=
  {guardedScopedLanguage with rewrites := unselectedRule :: guardedScopedLanguage.rewrites}

def filteredPermissions : Permissions := {permissionData with ruleIndices := some [1, 2]}

def filteredPlan : Plan := compile ⟨filteredLanguage, [], scopedProvider⟩ filteredPermissions

def filteredOpenJob : Job := ⟨0, ⟨1, outputRule, ⟨outputSpec, .authored⟩⟩, openSite⟩

theorem actual_selection_preserves_distinct_physical_indices :
    filteredPlan.complete = true ∧
      filteredPlan.rules = [⟨1, outputRule, ⟨outputSpec, .authored⟩⟩,
        ⟨2, guardedScopedRule, ⟨guardedScopedSpec, .authored⟩⟩] ∧
      filteredOpenJob.Valid filteredPlan [] t openWholeSource := by
  have read : filteredPlan.rules = [⟨1, outputRule, ⟨outputSpec, .authored⟩⟩,
      ⟨2, guardedScopedRule, ⟨guardedScopedSpec, .authored⟩⟩] := by cbv
  refine ⟨by cbv, read, ?_⟩
  constructor
  · rw [read]
    exact List.mem_cons_self
  · apply (generate_spec _ _ _ _ _ _ _).mp
    decide +kernel

def filteredOpenReceipt (trace : List GeneralScopedMatchMachine.BagChoice) : Receipt :=
  ⟨filteredOpenJob, trace, [("P", openCapture)], [("P", openCapture)], [], openSourceResult, openWholeTarget⟩

theorem filtered_guarded_receipt_keeps_both_source_positions (state : State) :
    ∃ trace, (filteredOpenReceipt trace).Valid filteredPlan [] t openWholeSource ∧
      filteredLanguage.rewrites[1]? = some (filteredOpenReceipt trace).job.declaration.authored ∧
      (GeneralPlanEnvironment.environment filteredPlan).language.rewrites[0]? =
        some (filteredOpenReceipt trace).job.declaration.rule ∧
      PureReturns program [] state (CettaWireAtom.encode
        (receiptQueryTerm filteredPlan.permissions.sites (filteredOpenReceipt trace))) state
        (CettaWireAtom.encode (.application "Some"
          [receiptObservationTerm filteredPlan.permissions.sites (filteredOpenReceipt trace)])) := by
  have matched : [("P", openCapture)] ∈ ScopedRuleMatching.matchAt outputRule outputSpec 1 .left [] 0 []
      outputRule.left openSourceTarget := by decide +kernel
  obtain ⟨trace, traced⟩ := GeneralScopedMatchMachine.traced_iff_matchAt.mpr matched
  have valid : (filteredOpenReceipt trace).Valid filteredPlan [] t openWholeSource := by
    apply finish_sound actual_selection_preserves_distinct_physical_indices.2.2 traced .nil
    cbv
  have origin := GeneralRuleJobExecution.guarded_receipt_authored_origin (permissions := filteredPermissions) (receipt := filteredOpenReceipt trace) valid
  exact ⟨trace, valid, origin.1, origin.2.2,
    (guarded_receipt_source_observation state (filteredOpenReceipt trace) valid).1⟩

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution.ScopedObservation
