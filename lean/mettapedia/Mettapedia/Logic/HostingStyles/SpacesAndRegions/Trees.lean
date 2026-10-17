import Mettapedia.Logic.HostingStyles.SpacesAndRegions.Candidate
import Mettapedia.Logic.HostingStyles.AmbientRegions.TwoSpaces

/-!
# Trees of runs, and a run in a run, on patterns and on terms

In the candidate of spaces and regions a run is an atom, so runs stand in an
application, and a tree of applications may have a run in a different space
at every leaf.  This module states how such a tree steps, with no guard and
at every ambient space.

* **The steps of an application** (`spacesAndRegions_app_step_iff`): beta, a
  step of the function, a step of the argument, or an answer of the ambient
  space for the application.
* **A tree of any finite number of runs** (`spacesAndRegions_tree_step_iff`):
  its steps are those that `TreeStep` generates.  A leaf steps in the member
  at its own space; an application steps in its function and in its
  argument; and the ambient space is asked for an application as a whole,
  since an application of two runs is an atom outside every run.  Positive
  `threeRuns_step`, `rootOfRuns_step`; negative `twoStillRuns_normal`.
* **A run in a run, on terms** (`spacesAndRegions_nested_termStep_iff`): its
  transitions are the runs of the runs of the transitions of the inner atom
  in the member at the inner space.
* **A tree of runs, on terms** (`spacesAndRegions_tree_termStep_iff`): its
  transitions are those that `TermTreeStep` generates, up to the static
  equivalence.

On terms a transition is a step up to the static equivalence, so the theorems
on terms carry a transition along a change of spelling: a term equal to an
application is an application of equal parts (`eq_appTerm_of_related`), and a
term equal to a run is a run of an equal space and an equal subject.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti
  (Theory withChoice chooseLeft chooseRight normal_of_normalTest)
open Mettapedia.GSLT.Dedukti.Language
  (betaRule betaLeft appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule
    lamBodyRule appLeft piLeft lamLeft fixedRules)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.AmbientRegions

variable {admits : Pattern → Bool}

/-! ## The steps of an application -/

/-- **The steps of an application**, under every guard and at every ambient
space: beta, when the function is an abstraction; a step of the function; a
step of the argument; or an answer of the ambient space for the
application. -/
theorem spacesAndRegions_app_step_iff {ambientSpace function argument target : Pattern} :
    Step (regionEvaluator admits ambientSpace) spacesAndRegions
        (.apply "App" [function, argument]) target ↔
      (∃ domain binder body, function = .apply "Lam" [domain, .lambda binder body] ∧
        target = instantiateBVar argument body) ∨
      (∃ next, Step (regionEvaluator admits ambientSpace) spacesAndRegions function next ∧
        target = .apply "App" [next, argument]) ∨
      (∃ next, Step (regionEvaluator admits ambientSpace) spacesAndRegions argument next ∧
        target = .apply "App" [function, next]) ∨
      target ∈ admittedAnswers admits ambientSpace (.apply "App" [function, argument]) := by
  rw [spacesAndRegions_eq_allHeaded]
  constructor
  · rintro ⟨fuel, step⟩
    cases fuel with
    | zero => cases step
    | succ fuel =>
        obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
        rcases mem_allHeaded_rewrites.mp member with plain | root | spatial | runRoot | beneath
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
          rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · obtain ⟨domain, binder, body, value, shape, applied⟩ := beta_inv matched premises
            simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
            obtain ⟨rfl, rfl⟩ := shape
            exact .inl ⟨domain, binder, body, rfl, applied⟩
          · obtain ⟨functionPattern, argumentPattern, moved, shape, inner, applied⟩ :=
              appFunction_inv matched premises
            simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
            obtain ⟨rfl, rfl⟩ := shape
            exact .inr (.inl ⟨moved, ⟨fuel, inner⟩, applied⟩)
          · obtain ⟨functionPattern, argumentPattern, moved, shape, inner, applied⟩ :=
              appArgument_inv matched premises
            simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
            obtain ⟨rfl, rfl⟩ := shape
            exact .inr (.inr (.inl ⟨moved, ⟨fuel, inner⟩, applied⟩))
          · exact absurd matched (apply_not_matched (label := "Pi") (other := "App") (by decide))
          · exact absurd matched (apply_not_matched (label := "Pi") (other := "App") (by decide))
          · exact absurd matched (apply_not_matched (label := "Lam") (other := "App") (by decide))
          · exact absurd matched (apply_not_matched (label := "Lam") (other := "App") (by decide))
          · exact absurd matched
              (apply_not_matched (label := "prime-drop") (other := "App") (by decide))
        · obtain ⟨name, label, parameters, rfl, exact, -⟩ := headedRoots_shape rule root
          obtain ⟨answer, found, applied⟩ := headedRoot_inv exact matched premises
          exact .inr (.inr (.inr (applied ▸ found)))
        · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inl spatial)
          rw [shape] at matched
          exact absurd matched
            (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inr (.inl runRoot))
          rw [shape] at matched
          exact absurd matched
            (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inr (.inr beneath))
          rw [shape] at matched
          exact absurd matched
            (apply_not_matched (label := "prime-run") (other := "App") (by decide))
  · rintro (⟨domain, binder, body, rfl, rfl⟩ | ⟨next, ⟨fuel, step⟩, rfl⟩ |
      ⟨next, ⟨fuel, step⟩, rfl⟩ | found)
    · exact ⟨1, step_beta (allHeaded_mem_plain (by simp)) domain body argument binder⟩
    · exact ⟨fuel + 1, step_appFunction (allHeaded_mem_plain (by simp)) argument step⟩
    · exact ⟨fuel + 1, step_appArgument (allHeaded_mem_plain (by simp)) function step⟩
    · exact ⟨1, step_headedRoot (name := "RootApp") (left := .apply "App" [.fvar "F", .fvar "X"])
        (allHeaded_mem_root (by simp [headedRoots]))
        (initial := [("X", argument), ("F", function)])
        (by simp [matchPattern, matchArgs, mergeBindings]) (by simp [applyBindings]) found⟩

/-! ## A tree of any finite number of runs, on patterns -/

/-- **One step of a tree of applications whose leaves are runs**, at an
ambient space.  A leaf steps in the member at its space; an application steps
in its function and in its argument; and at its root an application steps to
every answer of the ambient space for it. -/
inductive TreeStep (admits : Pattern → Bool) (ambientSpace : Pattern) : RunTree → Pattern → Prop
  | run {space subject next : Pattern} :
      Step (regionEvaluator admits space) spacesAndRegions subject next →
        TreeStep admits ambientSpace (.run space subject) (runPattern space next)
  | function {function : RunTree} {next : Pattern} (argument : RunTree) :
      TreeStep admits ambientSpace function next →
        TreeStep admits ambientSpace (.app function argument)
          (.apply "App" [next, argument.pattern])
  | argument (function : RunTree) {argument : RunTree} {next : Pattern} :
      TreeStep admits ambientSpace argument next →
        TreeStep admits ambientSpace (.app function argument)
          (.apply "App" [function.pattern, next])
  | root {function argument : RunTree} {answer : Pattern} :
      answer ∈ admittedAnswers admits ambientSpace
          (.apply "App" [function.pattern, argument.pattern]) →
        TreeStep admits ambientSpace (.app function argument) answer

/-- **A tree of applications whose leaves are runs steps as `TreeStep`
says**: under every guard, at every ambient space, for every tree. -/
theorem spacesAndRegions_tree_step_iff {ambientSpace : Pattern} :
    ∀ (tree : RunTree) {target : Pattern},
      Step (regionEvaluator admits ambientSpace) spacesAndRegions tree.pattern target ↔
        TreeStep admits ambientSpace tree target := by
  intro tree
  induction tree with
  | run space subject =>
      intro target
      rw [RunTree.pattern, spacesAndRegions_run_step_iff]
      constructor
      · rintro ⟨next, rfl, step⟩
        exact .run step
      · intro treeStep
        cases treeStep with
        | run step => exact ⟨_, rfl, step⟩
  | app function argument ihFunction ihArgument =>
      intro target
      rw [RunTree.pattern, spacesAndRegions_app_step_iff]
      constructor
      · rintro (⟨domain, binder, body, shape, -⟩ | ⟨next, step, rfl⟩ | ⟨next, step, rfl⟩ | found)
        · exact absurd shape (RunTree.pattern_ne_lam function _)
        · exact .function argument (ihFunction.mp step)
        · exact .argument function (ihArgument.mp step)
        · exact .root found
      · intro treeStep
        cases treeStep with
        | function _ inner => exact .inr (.inl ⟨_, ihFunction.mpr inner, rfl⟩)
        | argument _ inner => exact .inr (.inr (.inl ⟨_, ihArgument.mpr inner, rfl⟩))
        | root found => exact .inr (.inr (.inr found))

/-- **Positive**: a tree of three runs in three spaces, at the ambient space
of the two rules of choice and without a guard.  The middle run, in the space
of the two rules of choice, steps. -/
theorem threeRuns_step :
    Step (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) spacesAndRegions
      (RunTree.app (.app (.run emptySpace (atomAt 0 coin))
        (.run (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 coin)))
        (.run (ruleSpace [chooseLeft]) (atomAt 0 coin))).pattern
      (RunTree.app (.app (.run emptySpace (atomAt 0 coin))
        (.run (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 (.con "tails"))))
        (.run (ruleSpace [chooseLeft]) (atomAt 0 coin))).pattern :=
  (spacesAndRegions_tree_step_iff _).mpr
    (.function _ (.argument _ (.run
      ((spacesAndRegions_atom_step_iff anySubject_admitsAtoms choiceRules_admitted.1
        choiceRules_admitted.2 choiceRules_headed withChoice_rules (fun _ => rfl)).mpr
        ⟨_, rfl, Dedukti.step_choose_right Theory.empty _ _⟩))))

/-- The atom of `choose heads tails` has no step in the member at the empty
space. -/
theorem coin_normal_at_empty (target : Pattern) :
    ¬ Step (regionEvaluator anySubject (ruleSpace [])) spacesAndRegions (atomAt 0 coin) target := by
  intro step
  obtain ⟨next, -, sourceStep⟩ := (spacesAndRegions_atom_step_iff anySubject_admitsAtoms
    (rules := []) noRules_admitted.1 noRules_admitted.2
    (fun _ member => absurd member List.not_mem_nil) (theory := Theory.empty)
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl)).mp step
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

/-- **Negative**: at the ambient space of the two rules of choice, the
application of two runs of `choose heads tails` in the empty space has no
step: neither leaf steps in its own space, and the ambient space answers
nothing for the application. -/
theorem twoStillRuns_normal (target : Pattern) :
    ¬ Step (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) spacesAndRegions
      (RunTree.app (.run (ruleSpace []) (atomAt 0 coin))
        (.run (ruleSpace []) (atomAt 0 coin))).pattern target := by
  intro step
  have treeStep := (spacesAndRegions_tree_step_iff _).mp step
  cases treeStep with
  | function _ inner =>
      cases inner with
      | run leaf => exact coin_normal_at_empty _ leaf
  | argument _ inner =>
      cases inner with
      | run leaf => exact coin_normal_at_empty _ leaf
  | root found =>
      have listed : target ∈ admittedAnswers anySubject (ruleSpace [chooseLeft, chooseRight])
          (.apply "App" [runPattern (ruleSpace []) (atomAt 0 coin),
            runPattern (ruleSpace []) (atomAt 0 coin)]) := found
      rw [choiceSpace_quiet_on_pair anySubject] at listed
      cases listed

/-- The application of two runs of the unit atom in the empty space. -/
def unitRuns : RunTree := .app (.run emptySpace unitAtom) (.run emptySpace unitAtom)

/-- The space that stores one rule: that application is the unit atom. -/
def unitRunsSpace : Pattern := spaceOfAtoms [.apply "=" [unitRuns.pattern, unitAtom]]

/-- **Positive, the root**: an ambient space that stores a rule for an
application of two runs rewrites the application as a whole.  The application
is an atom outside every run, so the ambient space is asked for it. -/
theorem rootOfRuns_step :
    Step (regionEvaluator anySubject unitRunsSpace) spacesAndRegions unitRuns.pattern unitAtom := by
  refine (spacesAndRegions_tree_step_iff unitRuns).mpr (.root ?_)
  refine mem_admittedAnswers.mpr ⟨rfl, ?_⟩
  rw [show contract unitRunsSpace = unitRunsSpace by decide,
    show contract (Pattern.apply "App"
      [(RunTree.run emptySpace unitAtom).pattern, (RunTree.run emptySpace unitAtom).pattern]) =
      unitRuns.pattern by decide]
  refine mem_matchResults_spaceOfAtoms.mpr ⟨_, List.mem_singleton.mpr rfl, ?_⟩
  rw [atomResults_equation _ (by decide) (by decide)]
  simp [unitRuns, RunTree.pattern, runPattern, emptySpace, unitAtom, asRule, asRuleList,
    matchPattern, matchArgs, mergeBindings, applyBindings]

/-- **Negative, the root**: at the empty ambient space the same application
has no step. -/
theorem rootOfRuns_normal_at_empty (target : Pattern) :
    ¬ Step (regionEvaluator anySubject emptySpace) spacesAndRegions unitRuns.pattern target := by
  intro step
  have treeStep := (spacesAndRegions_tree_step_iff unitRuns).mp step
  have unitNormal : ∀ next, ¬ Step (regionEvaluator anySubject emptySpace) spacesAndRegions
      unitAtom next := by
    intro next unitStep
    obtain ⟨fuel, bounded⟩ := unitStep
    cases fuel with
    | zero => cases bounded
    | succ fuel =>
        rw [spacesAndRegions_eq_allHeaded] at bounded
        obtain ⟨rule, member, initial, final, matched, premises, -⟩ := exists_rule_of_stepAt bounded
        rcases mem_allHeaded_rewrites.mp member with plain | root | rest
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
          rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact absurd matched (apply_not_matched (by decide))
        · obtain ⟨name, label, parameters, rfl, exact, -⟩ := headedRoots_shape rule root
          obtain ⟨answer, found, -⟩ := headedRoot_inv exact matched premises
          rw [admittedAnswers_emptySpace] at found
          cases found
        · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left rest
          rw [shape] at matched
          exact absurd matched (apply_not_matched (label := "prime-run") (other := "prime-unit")
            (by decide))
  cases treeStep with
  | function _ inner =>
      cases inner with
      | run leaf => exact unitNormal _ leaf
  | argument _ inner =>
      cases inner with
      | run leaf => exact unitNormal _ leaf
  | root found =>
      rw [admittedAnswers_emptySpace] at found
      cases found

/-! ## Runs and applications as terms of the candidate -/

/-- The run of an atom of the candidate in a space, as an atom. -/
def runTerm {stage : List TypeExpr}
    (space : Contexts.Term spacesAndRegions ⟨.base "Space", stage⟩)
    (atom : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩) :
    Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩ :=
  runTermIn spacesAndRegions_declaresRun space atom

@[simp] theorem runTerm_val {stage : List TypeExpr}
    (space : Contexts.Term spacesAndRegions ⟨.base "Space", stage⟩)
    (atom : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩) :
    (runTerm space atom).1 = runPattern space.1 atom.1 :=
  rfl

/-- The application of an atom of the candidate to an atom. -/
def appTerm {stage : List TypeExpr}
    (function argument : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩) :
    Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩ :=
  appTermIn (presentation := spacesAndRegionsPresentation) spacesAndRegions_carriesAtoms function
    argument

@[simp] theorem appTerm_val {stage : List TypeExpr}
    (function argument : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩) :
    (appTerm function argument).1 = .apply "App" [function.1, argument.1] :=
  rfl

/-- The application constructor of the candidate takes two atoms. -/
theorem spacesAndRegions_application_params : ∀ rule ∈ spacesAndRegions.terms,
    rule.label = "App" →
      rule.params = [.simple "f" (.base "Atom"), .simple "a" (.base "Atom")] := by
  decide

/-- **The function and the argument of an application that is a term are
terms.** -/
theorem app_parts_wellSorted {function argument : Pattern} {bound : List TypeExpr}
    (sorted : OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty bound (.base "Atom")
      (.apply "App" [function, argument])) :
    OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty bound (.base "Atom") function ∧
      OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty bound (.base "Atom")
        argument := by
  obtain ⟨typed, canonical, object, scope⟩ := sorted
  obtain ⟨rule, member, label, arguments⟩ := hasType_apply_inv typed
  rw [spacesAndRegions_application_params rule member label] at arguments
  obtain ⟨functionTyped, rest⟩ := arguments.simple_cons_inv
  obtain ⟨argumentTyped, -⟩ := rest.simple_cons_inv
  have canonicalParts : function.hasCanonicalBinderMetadata = true ∧
      argument.hasCanonicalBinderMetadata = true := by
    simpa [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
      using canonical
  have objectParts : isObjectPattern function = true ∧ isObjectPattern argument = true := by
    simpa [isObjectPattern, isObjectPatternList] using object
  have scopeParts : function.isWellScopedAt bound.length = true ∧
      argument.isWellScopedAt bound.length = true := by
    have whole : (Pattern.apply "App" [function, argument]).isWellScopedAt bound.length = true :=
      scope
    simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using whole
  exact ⟨⟨functionTyped, canonicalParts.1, objectParts.1, scopeParts.1⟩,
    ⟨argumentTyped, canonicalParts.2, objectParts.2, scopeParts.2⟩⟩

/-- A term that is written as an application is the application of two
terms. -/
theorem eq_appTerm_of_val {stage : List TypeExpr}
    (term : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩) {function argument : Pattern}
    (shape : term.1 = .apply "App" [function, argument]) :
    ∃ functionTerm argumentTerm : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩,
      term = appTerm functionTerm argumentTerm ∧ functionTerm.1 = function ∧
        argumentTerm.1 = argument := by
  have parts := app_parts_wellSorted (shape ▸ term.2)
  exact ⟨⟨function, parts.1⟩, ⟨argument, parts.2⟩, Subtype.ext shape, rfl, rfl⟩

/-- **A term whose contraction is an application is an application** of
patterns with those contractions. -/
theorem eq_app_of_contract {stage : List TypeExpr}
    (term : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩) {function argument : Pattern}
    (same : contract term.1 = .apply "App" [function, argument]) :
    ∃ otherFunction otherArgument, term.1 = .apply "App" [otherFunction, otherArgument] ∧
      contract otherFunction = function ∧ contract otherArgument = argument := by
  obtain ⟨pattern, wellSorted⟩ := term
  cases pattern with
  | bvar index => simp [contract] at same
  | fvar name => simp [contract] at same
  | apply label arguments =>
      have notQuote : label ≠ "prime-quote" := by
        intro isQuote
        obtain ⟨rule, member, sameLabel, type⟩ := declared_constructor_of_hasType_apply wellSorted.1
        have category := (spacesAndRegions_quoteDropSorted.quote rule member
          (sameLabel.trans isQuote)).1
        rw [category] at type
        exact absurd (TypeExpr.base.inj type) (by decide)
      have unfolded : contract (Pattern.apply label arguments) =
          .apply "App" [function, argument] := same
      rw [contract_apply_of_ne notQuote] at unfolded
      simp only [Pattern.apply.injEq] at unfolded
      obtain ⟨rfl, parts⟩ := unfolded
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, more⟩⟩⟩
      · simp at parts
      · simp at parts
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at parts
        exact ⟨first, second, rfl, parts.1, parts.2⟩
      · simp at parts
  | lambda binder body => simp [contract] at same
  | multiLambda arity binders body => simp [contract] at same
  | subst body replacement => simp [contract] at same
  | collection kind elements rest => simp [contract] at same

/-- **Two applications are equal exactly when their functions are equal and
their arguments are equal.** -/
theorem appTerm_related_iff {base : BasePremiseEvaluator} {stage : List TypeExpr}
    {function argument otherFunction otherArgument :
      Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩} :
    (termSetoid base spacesAndRegions ⟨.base "Atom", stage⟩).r (appTerm function argument)
        (appTerm otherFunction otherArgument) ↔
      contract function.1 = contract otherFunction.1 ∧
        contract argument.1 = contract otherArgument.1 := by
  rw [spacesAndRegions_quoteDropOnly.termSetoid_iff spacesAndRegions_quoteDropSorted]
  show contract (.apply "App" [function.1, argument.1]) =
    contract (.apply "App" [otherFunction.1, otherArgument.1]) ↔ _
  rw [contract_apply_of_ne (by decide), contract_apply_of_ne (by decide)]
  simp

/-- **A term equal to an application is an application, of an equal function
and an equal argument.** -/
theorem eq_appTerm_of_related {base : BasePremiseEvaluator} {stage : List TypeExpr}
    {function argument other : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩}
    (related : (termSetoid base spacesAndRegions ⟨.base "Atom", stage⟩).r
      (appTerm function argument) other) :
    ∃ otherFunction otherArgument : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩,
      other = appTerm otherFunction otherArgument ∧
        contract otherFunction.1 = contract function.1 ∧
          contract otherArgument.1 = contract argument.1 := by
  have same : contract other.1 = .apply "App" [contract function.1, contract argument.1] := by
    rw [← spacesAndRegions_quoteDropOnly.contract_eq related]
    show contract (.apply "App" [function.1, argument.1]) = _
    rw [contract_apply_of_ne (by decide)]
    rfl
  obtain ⟨functionPattern, argumentPattern, shape, functionSame, argumentSame⟩ :=
    eq_app_of_contract other same
  obtain ⟨otherFunction, otherArgument, rfl, rfl, rfl⟩ := eq_appTerm_of_val other shape
  exact ⟨otherFunction, otherArgument, rfl, functionSame, argumentSame⟩

/-- A transition of the function is a transition of the application. -/
theorem termStep_appFunction {base : BasePremiseEvaluator} {stage : List TypeExpr}
    {function next : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩}
    (argument : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩)
    (step : TermStep base spacesAndRegions function next) :
    TermStep base spacesAndRegions (appTerm function argument) (appTerm next argument) := by
  obtain ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩ := step
  exact ⟨appTerm redex argument, appTerm contractum argument,
    appTerm_related_iff.mpr ⟨spacesAndRegions_quoteDropOnly.contract_eq before, rfl⟩,
    ⟨fuel + 1, step_appFunction
      (spacesAndRegions_rewrites ▸ allHeaded_mem_plain (by simp)) argument.1 fired⟩,
    appTerm_related_iff.mpr ⟨spacesAndRegions_quoteDropOnly.contract_eq after, rfl⟩⟩

/-- A transition of the argument is a transition of the application. -/
theorem termStep_appArgument {base : BasePremiseEvaluator} {stage : List TypeExpr}
    (function : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩)
    {argument next : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩}
    (step : TermStep base spacesAndRegions argument next) :
    TermStep base spacesAndRegions (appTerm function argument) (appTerm function next) := by
  obtain ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩ := step
  exact ⟨appTerm function redex, appTerm function contractum,
    appTerm_related_iff.mpr ⟨rfl, spacesAndRegions_quoteDropOnly.contract_eq before⟩,
    ⟨fuel + 1, step_appArgument
      (spacesAndRegions_rewrites ▸ allHeaded_mem_plain (by simp)) function.1 fired⟩,
    appTerm_related_iff.mpr ⟨rfl, spacesAndRegions_quoteDropOnly.contract_eq after⟩⟩

/-! ## A run in a run, on terms -/

/-- **On terms: the transitions of a run in a run are the runs of the runs of
the transitions of the inner atom in the member at the inner space**, under
every guard and at every ambient space.  Neither the outer space nor the
ambient space answers anything. -/
theorem spacesAndRegions_nested_termStep_iff {ambientSpace : Pattern} {stage : List TypeExpr}
    (outer inner : Contexts.Term spacesAndRegions ⟨.base "Space", stage⟩)
    (atom target : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩) :
    TermStep (regionEvaluator admits ambientSpace) spacesAndRegions
        (runTerm outer (runTerm inner atom)) target ↔
      ∃ next : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩,
        TermStep (regionEvaluator admits inner.1) spacesAndRegions atom next ∧
          (termSetoid (regionEvaluator admits ambientSpace) spacesAndRegions
            ⟨.base "Atom", stage⟩).r target (runTerm outer (runTerm inner next)) := by
  constructor
  · intro step
    obtain ⟨middle, innerStep, related⟩ :=
      (spacesAndRegions_run_termStep_iff outer (runTerm inner atom) target).mp step
    obtain ⟨next, atomStep, middleRelated⟩ :=
      (spacesAndRegions_run_termStep_iff (ambientSpace := outer.1) inner atom middle).mp innerStep
    refine ⟨next, atomStep, ?_⟩
    refine (termSetoid (regionEvaluator admits ambientSpace) spacesAndRegions _).iseqv.trans
      related ?_
    exact (runTermIn_related_iff spacesAndRegions_quoteDropOnly spacesAndRegions_quoteDropSorted
      spacesAndRegions_declaresRun).mpr
      ⟨rfl, spacesAndRegions_quoteDropOnly.contract_eq middleRelated⟩
  · rintro ⟨next, atomStep, related⟩
    exact (spacesAndRegions_run_termStep_iff outer (runTerm inner atom) target).mpr
      ⟨runTerm inner next,
        (spacesAndRegions_run_termStep_iff (ambientSpace := outer.1) inner atom _).mpr
          ⟨next, atomStep, Relation.EqvGen.refl _⟩, related⟩

/-! ## A tree of runs, on terms -/

/-- **A tree of applications whose leaves are runs, of terms of one stage.** -/
inductive TermTree (stage : List TypeExpr) where
  | run (space : Contexts.Term spacesAndRegions ⟨.base "Space", stage⟩)
      (atom : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩)
  | app (function argument : TermTree stage)

namespace TermTree

variable {stage : List TypeExpr}

/-- The term of a tree. -/
def term : TermTree stage → Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩
  | .run space atom => runTerm space atom
  | .app function argument => appTerm function.term argument.term

/-- The tree of patterns of a tree of terms. -/
def tree : TermTree stage → RunTree
  | .run space atom => .run space.1 atom.1
  | .app function argument => .app function.tree argument.tree

/-- The term of a tree is written as the pattern of its tree of patterns. -/
theorem term_val : ∀ tree : TermTree stage, tree.term.1 = tree.tree.pattern
  | .run _ _ => rfl
  | .app function argument => by
      show Pattern.apply "App" [function.term.1, argument.term.1] = _
      rw [term_val function, term_val argument]
      rfl

/-- The contraction of the term of a tree is no abstraction. -/
theorem contract_term_ne_lam (tree : TermTree stage) (arguments : List Pattern) :
    contract tree.term.1 ≠ .apply "Lam" arguments := by
  cases tree with
  | run space atom =>
      show contract (runPattern space.1 atom.1) ≠ _
      rw [contract_runPattern']
      simp [runPattern]
  | app function argument =>
      show contract (.apply "App" [function.term.1, argument.term.1]) ≠ _
      rw [contract_apply_of_ne (by decide)]
      simp

end TermTree

/-- **One transition of a tree of runs of terms**, at an ambient space.  A
leaf steps by a transition of its atom in the member at its space; an
application steps in its function and in its argument; and at its root an
application steps to every term that is an answer of the ambient space for
it. -/
inductive TermTreeStep (admits : Pattern → Bool) (ambientSpace : Pattern) {stage : List TypeExpr} :
    TermTree stage → Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩ → Prop
  | run {space : Contexts.Term spacesAndRegions ⟨.base "Space", stage⟩}
      {atom next : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩} :
      TermStep (regionEvaluator admits space.1) spacesAndRegions atom next →
        TermTreeStep admits ambientSpace (.run space atom) (runTerm space next)
  | function {function : TermTree stage}
      {next : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩} (argument : TermTree stage) :
      TermTreeStep admits ambientSpace function next →
        TermTreeStep admits ambientSpace (.app function argument) (appTerm next argument.term)
  | argument (function : TermTree stage) {argument : TermTree stage}
      {next : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩} :
      TermTreeStep admits ambientSpace argument next →
        TermTreeStep admits ambientSpace (.app function argument) (appTerm function.term next)
  | root {function argument : TermTree stage}
      {answer : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩} :
      answer.1 ∈ admittedAnswers admits ambientSpace
          (.apply "App" [function.term.1, argument.term.1]) →
        TermTreeStep admits ambientSpace (.app function argument) answer

/-- **On terms: a tree of applications whose leaves are runs has the
transitions that `TermTreeStep` generates, up to the static equivalence**,
under every guard and at every ambient space. -/
theorem spacesAndRegions_tree_termStep_iff {ambientSpace : Pattern} {stage : List TypeExpr} :
    ∀ (tree : TermTree stage) {target : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩},
      TermStep (regionEvaluator admits ambientSpace) spacesAndRegions tree.term target ↔
        ∃ next : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩,
          TermTreeStep admits ambientSpace tree next ∧
            (termSetoid (regionEvaluator admits ambientSpace) spacesAndRegions
              ⟨.base "Atom", stage⟩).r target next := by
  intro tree
  induction tree with
  | run space atom =>
      intro target
      constructor
      · intro step
        obtain ⟨next, atomStep, related⟩ :=
          (spacesAndRegions_run_termStep_iff space atom target).mp step
        exact ⟨runTerm space next, .run atomStep, related⟩
      · rintro ⟨reached, treeStep, related⟩
        cases treeStep with
        | run atomStep =>
            exact (spacesAndRegions_run_termStep_iff space atom target).mpr ⟨_, atomStep, related⟩
  | app function argument ihFunction ihArgument =>
      intro target
      have setoid := (termSetoid (regionEvaluator admits ambientSpace) spacesAndRegions
        ⟨.base "Atom", stage⟩).iseqv
      constructor
      · rintro ⟨redex, contractum, before, fired, after⟩
        obtain ⟨functionTerm, argumentTerm, rfl, functionSame, argumentSame⟩ :=
          eq_appTerm_of_related before
        have functionRelated : (termSetoid (regionEvaluator admits ambientSpace) spacesAndRegions
            ⟨.base "Atom", stage⟩).r function.term functionTerm :=
          (spacesAndRegions_quoteDropOnly.termSetoid_iff spacesAndRegions_quoteDropSorted).mpr
            functionSame.symm
        have argumentRelated : (termSetoid (regionEvaluator admits ambientSpace) spacesAndRegions
            ⟨.base "Atom", stage⟩).r argument.term argumentTerm :=
          (spacesAndRegions_quoteDropOnly.termSetoid_iff spacesAndRegions_quoteDropSorted).mpr
            argumentSame.symm
        rcases spacesAndRegions_app_step_iff.mp fired with
          ⟨domain, binder, body, shape, -⟩ | ⟨next, step, shape⟩ | ⟨next, step, shape⟩ | found
        · refine absurd ?_ (function.contract_term_ne_lam [contract domain,
            contract (.lambda binder body)])
          rw [← functionSame]
          show contract functionTerm.1 = _
          rw [shape, contract_apply_of_ne (by decide)]
          rfl
        · obtain ⟨nextTerm, otherArgument, rfl, rfl, argumentVal⟩ :=
            eq_appTerm_of_val contractum shape
          have same : otherArgument = argumentTerm := Subtype.ext argumentVal
          subst same
          obtain ⟨reached, treeStep, related⟩ := ihFunction.mp
            ⟨functionTerm, nextTerm, functionRelated, step, Relation.EqvGen.refl _⟩
          refine ⟨appTerm reached argument.term, .function argument treeStep, ?_⟩
          refine setoid.trans (setoid.symm after) ?_
          exact appTerm_related_iff.mpr
            ⟨spacesAndRegions_quoteDropOnly.contract_eq related, argumentSame⟩
        · obtain ⟨otherFunction, nextTerm, rfl, functionVal, rfl⟩ :=
            eq_appTerm_of_val contractum shape
          have same : otherFunction = functionTerm := Subtype.ext functionVal
          subst same
          obtain ⟨reached, treeStep, related⟩ := ihArgument.mp
            ⟨argumentTerm, nextTerm, argumentRelated, step, Relation.EqvGen.refl _⟩
          refine ⟨appTerm function.term reached, .argument function treeStep, ?_⟩
          refine setoid.trans (setoid.symm after) ?_
          exact appTerm_related_iff.mpr
            ⟨functionSame, spacesAndRegions_quoteDropOnly.contract_eq related⟩
        · refine ⟨contractum, .root ?_, setoid.symm after⟩
          have subjects : contract (Pattern.apply "App" [functionTerm.1, argumentTerm.1]) =
              contract (.apply "App" [function.term.1, argument.term.1]) := by
            rw [contract_apply_of_ne (by decide), contract_apply_of_ne (by decide)]
            simp [functionSame, argumentSame]
          rw [← admittedAnswers_congr admits rfl subjects]
          exact found
      · rintro ⟨reached, treeStep, related⟩
        cases treeStep with
        | function _ inner =>
            exact Contexts.termStep_resp_right _ _
              (termStep_appFunction argument.term
                (ihFunction.mpr ⟨_, inner, Relation.EqvGen.refl _⟩)) (setoid.symm related)
        | argument _ inner =>
            exact Contexts.termStep_resp_right _ _
              (termStep_appArgument function.term
                (ihArgument.mpr ⟨_, inner, Relation.EqvGen.refl _⟩)) (setoid.symm related)
        | root found =>
            exact ⟨appTerm function.term argument.term, reached, Relation.EqvGen.refl _,
              spacesAndRegions_app_step_iff.mpr (.inr (.inr (.inr found))), setoid.symm related⟩

#print axioms spacesAndRegions_app_step_iff
#print axioms spacesAndRegions_tree_step_iff
#print axioms threeRuns_step
#print axioms coin_normal_at_empty
#print axioms twoStillRuns_normal
#print axioms rootOfRuns_step
#print axioms rootOfRuns_normal_at_empty
#print axioms spacesAndRegions_application_params
#print axioms app_parts_wellSorted
#print axioms eq_appTerm_of_val
#print axioms eq_app_of_contract
#print axioms appTerm_related_iff
#print axioms eq_appTerm_of_related
#print axioms termStep_appFunction
#print axioms termStep_appArgument
#print axioms spacesAndRegions_nested_termStep_iff
#print axioms TermTree.term_val
#print axioms TermTree.contract_term_ne_lam
#print axioms spacesAndRegions_tree_termStep_iff

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
