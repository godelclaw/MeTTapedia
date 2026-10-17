import Mettapedia.Logic.HostingStyles.AmbientRegions.Scoping

/-!
# Two spaces in one term, without an equation

A run is an atom and may stand anywhere, so the contained presentation has
terms whose parts are in different spaces, and no equation is needed to write
them: `App(run(first, f), run(second, x))` is a term.

* **Each part steps by the rules of its own space, and by no other**
  (`contained_pair_step_iff`): the steps of the application are a step of the
  function in the member at the first space, a step of the argument in the
  member at the second, and an answer of the ambient space for the whole
  application.  The function is a run and no abstraction, so the application
  is no beta redex; the two spaces need not differ.
* For the atoms of two λΠ terms in the spaces of two lists of rules
  (`contained_pairAtoms_step_iff`, `contained_pairAtoms_termStep_iff`): at an
  ambient space that answers nothing for the application, the transitions are
  exactly a step of the function by the first rules, the argument unchanged,
  and a step of the argument by the second rules, the function unchanged.
  This is the statement that `pair_termStep_inv` makes for located atoms, in
  both directions, under the plain matching evaluator among others.
* **Instance** (`mixedCoins_function_steps`, `mixedCoins_argument_still`,
  `mixedCoins_argument_not_by_function_rules`): `choose heads tails` in the
  space of the two rules of choice applied to `choose heads tails` in the
  empty space, at the ambient space of the two rules of choice.  The function
  steps; the argument never moves, although the ambient space and the space
  of the function both store the rules of choice.
* **Negative** (`scoped_mixedCoins_argument_steps`): in the scoped
  presentation the argument steps, by the ambient rules.
* **Any finite number of runs** (`RunTree`, `contained_tree_step_iff`): a tree
  of applications whose leaves are runs steps by a step of one leaf in the
  member at the space of that leaf.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti
  (Theory patternVars usesOnly withChoice chooseLeft chooseRight normal_of_normalTest)
open Mettapedia.GSLT.Dedukti.Language
  (betaRule appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule lamBodyRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

variable {admits : Pattern → Bool}

/-! ## An application of two runs, on patterns -/

/-- **The steps of an application of two runs**, in the contained
presentation and at an ambient space that answers nothing for a run: a step of
the function in the member at its space, a step of the argument in the member
at its space, or an answer of the ambient space for the application. -/
theorem contained_pair_step_iff {ambientSpace first second function argument target : Pattern}
    (silent : RunSilent admits ambientSpace)
    (functionSide : tokens runLabel function = 0 ∨ RunSilent admits first)
    (argumentSide : tokens runLabel argument = 0 ∨ RunSilent admits second) :
    Step (regionEvaluator admits ambientSpace) containedRun
        (.apply "App" [runPattern first function, runPattern second argument]) target ↔
      (∃ next, target = .apply "App" [runPattern first next, runPattern second argument] ∧
        Step (regionEvaluator admits first) containedRun function next) ∨
      (∃ next, target = .apply "App" [runPattern first function, runPattern second next] ∧
        Step (regionEvaluator admits second) containedRun argument next) ∨
      target ∈ admittedAnswers admits ambientSpace
        (.apply "App" [runPattern first function, runPattern second argument]) := by
  constructor
  · rintro ⟨fuel, step⟩
    cases fuel with
    | zero => cases step
    | succ fuel =>
        obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
        rw [contained_rewrites] at member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨domain, binder, body, value, shape, -⟩ := beta_inv matched premises
          simp [runPattern] at shape
        · obtain ⟨functionPattern, argumentPattern, moved, shape, inner, applied⟩ :=
            appFunction_inv matched premises
          simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
          obtain ⟨rfl, rfl⟩ := shape
          obtain ⟨next, rfl, movedStep⟩ := contained_run_stepAt_inv silent fuel inner
          exact .inl ⟨next, applied, movedStep⟩
        · obtain ⟨functionPattern, argumentPattern, moved, shape, inner, applied⟩ :=
            appArgument_inv matched premises
          simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
          obtain ⟨rfl, rfl⟩ := shape
          obtain ⟨next, rfl, movedStep⟩ := contained_run_stepAt_inv silent fuel inner
          exact .inr (.inl ⟨next, applied, movedStep⟩)
        · exact absurd matched (apply_not_matched (label := "Pi") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "Pi") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "Lam") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "Lam") (other := "App") (by decide))
        · exact absurd matched
            (apply_not_matched (label := "prime-drop") (other := "App") (by decide))
        · obtain ⟨answer, found, applied⟩ := ambientRoot_inv matched premises
          exact .inr (.inr (applied ▸ found))
        · exact absurd matched (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "prime-run") (other := "App") (by decide))
  · rintro (⟨next, rfl, step⟩ | ⟨next, rfl, step⟩ | found)
    · obtain ⟨count, lifted⟩ := contained_run_of_step ambientSpace functionSide step
      exact ⟨count + 1, step_appFunction (by simp [contained_rewrites]) _ lifted⟩
    · obtain ⟨count, lifted⟩ := contained_run_of_step ambientSpace argumentSide step
      exact ⟨count + 1, step_appArgument (by simp [contained_rewrites]) _ lifted⟩
    · exact ⟨1, step_ambientRoot (by simp [contained_rewrites]) found⟩

/-! ## The atoms of two terms in the spaces of two lists of rules -/

/-- The empty space answers nothing, under every guard. -/
theorem admittedAnswers_emptySpace (admits : Pattern → Bool) (subject : Pattern) :
    admittedAnswers admits emptySpace subject = [] := by
  unfold admittedAnswers
  split_ifs
  · rw [show contract emptySpace = emptySpace by decide]
    exact matchResults_emptySpace _
  · rfl

/-- **The space of the two rules of choice answers nothing for an application
of two runs**, under every guard: the function of the left side of each rule
is an application. -/
theorem choiceSpace_quiet_on_pair (admits : Pattern → Bool)
    (first function second argument : Pattern) :
    admittedAnswers admits (ruleSpace [chooseLeft, chooseRight])
      (.apply "App" [runPattern first function, runPattern second argument]) = [] := by
  unfold admittedAnswers
  split_ifs
  · rw [contract_ruleSpace, contract_apply_of_ne (by decide)]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro answer found
    obtain ⟨rule, member, bindings, matched, -⟩ :=
      (mem_matchResults_ruleSpace choiceRules_admitted.1).mp found
    have left : rule.lhs = .app (.app (.con Dedukti.chooseName) (.var 1)) (.var 0) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl
    rw [left, ruleSide_app, ruleSide_app] at matched
    obtain ⟨functionPart, argumentPart, functionBindings, argumentBindings, shape, inFunction, -,
      -⟩ := matched_apply_two (label := "App") matched
    simp only [List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq, and_true,
      true_and] at shape
    obtain ⟨rfl, -⟩ := shape
    rw [contract_runPattern'] at inFunction
    exact apply_not_matched (label := "App") (other := "prime-run") (by decide) inFunction
  · rfl

/-- **Each part steps by the rules of its own space only**, on patterns.  For
two lists of first-order rules with bound right sides and the atoms of two
terms, at an ambient space that answers nothing for a run and nothing for the
application: the steps of the application of the run of the function in the
space of the first list to the run of the argument in the space of the second
are a step of the function by the first rules, the argument unchanged, and a
step of the argument by the second rules, the function unchanged. -/
theorem contained_pairAtoms_step_iff (admitsAtoms : AdmitsAtoms admits) {ambientSpace : Pattern}
    (silent : RunSilent admits ambientSpace)
    {functionRules argumentRules : List Dedukti.RewriteRule}
    (functionFirstOrder : ∀ rule ∈ functionRules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (functionBound : ∀ rule ∈ functionRules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (argumentFirstOrder : ∀ rule ∈ argumentRules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (argumentBound : ∀ rule ∈ argumentRules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {functionTheory argumentTheory : Theory}
    (functionIff : ∀ rule, functionTheory.rule rule ↔ rule ∈ functionRules)
    (argumentIff : ∀ rule, argumentTheory.rule rule ↔ rule ∈ argumentRules)
    (functionUndefined : ∀ name, functionTheory.body name = none)
    (argumentUndefined : ∀ name, argumentTheory.body name = none) {depth : Nat}
    {function argument : LF.Term}
    (quiet : admittedAnswers admits ambientSpace
      (.apply "App" [runPattern (ruleSpace functionRules) (atomAt depth function),
        runPattern (ruleSpace argumentRules) (atomAt depth argument)]) = [])
    {target : Pattern} :
    Step (regionEvaluator admits ambientSpace) containedRun
        (.apply "App" [runPattern (ruleSpace functionRules) (atomAt depth function),
          runPattern (ruleSpace argumentRules) (atomAt depth argument)]) target ↔
      (∃ next, Dedukti.Step functionTheory function next ∧
        target = .apply "App" [runPattern (ruleSpace functionRules) (atomAt depth next),
          runPattern (ruleSpace argumentRules) (atomAt depth argument)]) ∨
      (∃ next, Dedukti.Step argumentTheory argument next ∧
        target = .apply "App" [runPattern (ruleSpace functionRules) (atomAt depth function),
          runPattern (ruleSpace argumentRules) (atomAt depth next)]) := by
  rw [contained_pair_step_iff silent (.inl (tokens_run_atomAt function depth))
    (.inl (tokens_run_atomAt argument depth)), quiet]
  constructor
  · rintro (⟨reached, rfl, step⟩ | ⟨reached, rfl, step⟩ | found)
    · obtain ⟨next, rfl, sourceStep⟩ := (contained_atom_step_iff admitsAtoms functionFirstOrder
        functionBound functionIff functionUndefined).mp step
      exact .inl ⟨next, sourceStep, rfl⟩
    · obtain ⟨next, rfl, sourceStep⟩ := (contained_atom_step_iff admitsAtoms argumentFirstOrder
        argumentBound argumentIff argumentUndefined).mp step
      exact .inr ⟨next, sourceStep, rfl⟩
    · cases found
  · rintro (⟨next, sourceStep, rfl⟩ | ⟨next, sourceStep, rfl⟩)
    · exact .inl ⟨atomAt depth next, rfl, (contained_atom_step_iff admitsAtoms functionFirstOrder
        functionBound functionIff functionUndefined).mpr ⟨next, rfl, sourceStep⟩⟩
    · exact .inr (.inl ⟨atomAt depth next, rfl, (contained_atom_step_iff admitsAtoms
        argumentFirstOrder argumentBound argumentIff argumentUndefined).mpr
        ⟨next, rfl, sourceStep⟩⟩)

/-! ## On terms -/

section Terms

variable {presentation : ValidatedLanguageDef}

/-- **The application of the run of the atom of a function in the space of
one list of rules to the run of the atom of an argument in the space of
another.** -/
def pairAtomsIn (declares : DeclaresRun presentation.language)
    (carries : CarriesAtoms presentation.language)
    (functionRules argumentRules : List Dedukti.RewriteRule) (depth : Nat)
    (function argument : LF.Term) : Contexts.Term presentation.language (atomInterface depth) :=
  appTermIn carries (runAtomIn declares carries functionRules depth function)
    (runAtomIn declares carries argumentRules depth argument)

@[simp] theorem pairAtomsIn_val (declares : DeclaresRun presentation.language)
    (carries : CarriesAtoms presentation.language)
    (functionRules argumentRules : List Dedukti.RewriteRule) (depth : Nat)
    (function argument : LF.Term) :
    (pairAtomsIn declares carries functionRules argumentRules depth function argument).1 =
      .apply "App" [runPattern (ruleSpace functionRules) (atomAt depth function),
        runPattern (ruleSpace argumentRules) (atomAt depth argument)] :=
  rfl

/-- **Such an application is the only term of its class.** -/
theorem eq_pairAtomsIn_of_related (declares : DeclaresRun presentation.language)
    (carries : CarriesAtoms presentation.language) (only : QuoteDropOnly presentation.language)
    (sorted : QuoteDropSorted presentation.language)
    (names : NamesOnlyDropped presentation.language unquotedSorts) {base : BasePremiseEvaluator}
    {functionRules argumentRules : List Dedukti.RewriteRule} {depth : Nat}
    {function argument : LF.Term}
    {other : Contexts.Term presentation.language (atomInterface depth)}
    (related : (termSetoid base presentation.language (atomInterface depth)).r
      (pairAtomsIn declares carries functionRules argumentRules depth function argument) other) :
    other = pairAtomsIn declares carries functionRules argumentRules depth function argument := by
  refine eq_of_related_of_dropFree_in only sorted names
    (show resultIn unquotedSorts (.base "Atom") = true by decide) ?_ ?_ related
  · show contract (.apply "App" [runPattern (ruleSpace functionRules) (atomAt depth function),
      runPattern (ruleSpace argumentRules) (atomAt depth argument)]) =
        .apply "App" [runPattern (ruleSpace functionRules) (atomAt depth function),
          runPattern (ruleSpace argumentRules) (atomAt depth argument)]
    rw [contract_apply_of_ne (by decide)]
    simp only [List.map_cons, List.map_nil, contract_runAtom]
  · show tokens dropLabel (.apply "App" [runPattern (ruleSpace functionRules) (atomAt depth function),
      runPattern (ruleSpace argumentRules) (atomAt depth argument)]) = 0
    refine tokens_apply_eq_zero_iff.mpr ⟨by decide, fun part member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact tokens_drop_runAtom functionRules depth function
    · exact tokens_drop_runAtom argumentRules depth argument

theorem pairAtomsIn_injective (declares : DeclaresRun presentation.language)
    (carries : CarriesAtoms presentation.language)
    (functionRules argumentRules : List Dedukti.RewriteRule) (depth : Nat)
    {function argument otherFunction otherArgument : LF.Term}
    (same : pairAtomsIn declares carries functionRules argumentRules depth function argument =
      pairAtomsIn declares carries functionRules argumentRules depth otherFunction
        otherArgument) : function = otherFunction ∧ argument = otherArgument := by
  have patterns := congrArg Subtype.val same
  simp only [pairAtomsIn_val, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at patterns
  exact ⟨atomAt_injective depth (runPattern_injective patterns.1).2,
    atomAt_injective depth (runPattern_injective patterns.2).2⟩

end Terms

/-- **Each part steps by the rules of its own space only**, on terms.  For
every two lists of first-order rules with bound right sides, at every depth,
and at every ambient space that answers nothing for a run and nothing for the
application: the transitions of the application of the run of a function in
the space of the first list to the run of an argument in the space of the
second are exactly a step of the function by the first rules, the argument
unchanged, and a step of the argument by the second rules, the function
unchanged. -/
theorem contained_pairAtoms_termStep_iff (admitsAtoms : AdmitsAtoms admits)
    {ambientSpace : Pattern} (silent : RunSilent admits ambientSpace)
    {functionRules argumentRules : List Dedukti.RewriteRule}
    (functionFirstOrder : ∀ rule ∈ functionRules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (functionBound : ∀ rule ∈ functionRules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (argumentFirstOrder : ∀ rule ∈ argumentRules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (argumentBound : ∀ rule ∈ argumentRules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {functionTheory argumentTheory : Theory}
    (functionIff : ∀ rule, functionTheory.rule rule ↔ rule ∈ functionRules)
    (argumentIff : ∀ rule, argumentTheory.rule rule ↔ rule ∈ argumentRules)
    (functionUndefined : ∀ name, functionTheory.body name = none)
    (argumentUndefined : ∀ name, argumentTheory.body name = none) {depth : Nat}
    {function argument : LF.Term}
    (quiet : admittedAnswers admits ambientSpace
      (.apply "App" [runPattern (ruleSpace functionRules) (atomAt depth function),
        runPattern (ruleSpace argumentRules) (atomAt depth argument)]) = [])
    {target : Contexts.Term containedRun (atomInterface depth)} :
    TermStep (regionEvaluator admits ambientSpace) containedRun
        (pairAtomsIn (presentation := containedPresentation) contained_declaresRun
          region_carriesAtoms.1 functionRules argumentRules depth function argument) target ↔
      (∃ next, Dedukti.Step functionTheory function next ∧
        target = pairAtomsIn (presentation := containedPresentation) contained_declaresRun
          region_carriesAtoms.1 functionRules argumentRules depth next argument) ∨
      (∃ next, Dedukti.Step argumentTheory argument next ∧
        target = pairAtomsIn (presentation := containedPresentation) contained_declaresRun
          region_carriesAtoms.1 functionRules argumentRules depth function next) := by
  have alone := fun {function argument : LF.Term}
      {other : Contexts.Term containedRun (atomInterface depth)} =>
    eq_pairAtomsIn_of_related (presentation := containedPresentation) contained_declaresRun
      region_carriesAtoms.1 contained_quoteDropOnly contained_quoteDropSorted
      contained_namesOnlyDropped (base := regionEvaluator admits ambientSpace)
      (functionRules := functionRules) (argumentRules := argumentRules) (depth := depth)
      (function := function) (argument := argument) (other := other)
  have steps := fun {target : Pattern} =>
    contained_pairAtoms_step_iff admitsAtoms silent functionFirstOrder functionBound
      argumentFirstOrder argumentBound functionIff argumentIff functionUndefined argumentUndefined
      quiet (target := target)
  constructor
  · rintro ⟨redex, contractum, before, fired, after⟩
    obtain rfl := alone before
    rcases steps.mp fired with ⟨next, sourceStep, shape⟩ | ⟨next, sourceStep, shape⟩
    · have same : contractum = pairAtomsIn (presentation := containedPresentation)
          contained_declaresRun region_carriesAtoms.1 functionRules argumentRules depth next
          argument := Subtype.ext shape
      rw [same] at after
      exact .inl ⟨next, sourceStep, alone after⟩
    · have same : contractum = pairAtomsIn (presentation := containedPresentation)
          contained_declaresRun region_carriesAtoms.1 functionRules argumentRules depth function
          next := Subtype.ext shape
      rw [same] at after
      exact .inr ⟨next, sourceStep, alone after⟩
  · rintro (⟨next, sourceStep, rfl⟩ | ⟨next, sourceStep, rfl⟩)
    · exact ⟨_, _, Relation.EqvGen.refl _, steps.mpr (.inl ⟨next, sourceStep, rfl⟩),
        Relation.EqvGen.refl _⟩
    · exact ⟨_, _, Relation.EqvGen.refl _, steps.mpr (.inr ⟨next, sourceStep, rfl⟩),
        Relation.EqvGen.refl _⟩

/-! ## The instance: choice in one space, none in the other -/

/-- `choose heads tails` in the space of the two rules of choice, applied to
`choose heads tails` in the empty space. -/
def mixedCoins : Contexts.Term containedRun AtomsReduce.closedAtom :=
  pairAtomsIn (presentation := containedPresentation) contained_declaresRun region_carriesAtoms.1
    [chooseLeft, chooseRight] [] 0 coin coin

/-- The same application with other terms in the two runs. -/
def mixedPair (function argument : LF.Term) : Contexts.Term containedRun AtomsReduce.closedAtom :=
  pairAtomsIn (presentation := containedPresentation) contained_declaresRun region_carriesAtoms.1
    [chooseLeft, chooseRight] [] 0 function argument

theorem mixedCoins_eq : mixedCoins = mixedPair coin coin := rfl

/-- The transitions of such an application, at the ambient space of the two
rules of choice. -/
theorem mixedPair_termStep_iff (admitsAtoms : AdmitsAtoms admits) {function argument : LF.Term}
    {target : Contexts.Term containedRun AtomsReduce.closedAtom} :
    TermStep (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) containedRun
        (mixedPair function argument) target ↔
      (∃ next, Dedukti.Step (withChoice Theory.empty) function next ∧
        target = mixedPair next argument) ∨
      (∃ next, Dedukti.Step Theory.empty argument next ∧ target = mixedPair function next) :=
  contained_pairAtoms_termStep_iff admitsAtoms (choiceSpace_runSilent admits)
    (functionTheory := withChoice Theory.empty) (argumentTheory := Theory.empty)
    choiceRules_admitted.1 choiceRules_admitted.2 noRules_admitted.1 noRules_admitted.2
    withChoice_rules
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl) (fun _ => rfl) (choiceSpace_quiet_on_pair admits _ _ _ _)

/-- **Positive instance**: the function, in the space of the rules of choice,
steps to `heads`. -/
theorem mixedCoins_function_steps (admitsAtoms : AdmitsAtoms admits) :
    TermStep (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) containedRun mixedCoins
      (mixedPair (.con "heads") coin) :=
  (mixedPair_termStep_iff admitsAtoms).mpr
    (.inl ⟨_, Dedukti.step_choose_left Theory.empty _ _, rfl⟩)

/-- **Negative instance**: every transition of the application is a step of
its function by the calculus with choice.  Its argument, in the empty space,
does not move, although the ambient space and the space of the function both
store the rules of choice. -/
theorem mixedCoins_argument_still (admitsAtoms : AdmitsAtoms admits)
    {target : Contexts.Term containedRun AtomsReduce.closedAtom}
    (step : TermStep (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) containedRun
      mixedCoins target) :
    ∃ next, Dedukti.Step (withChoice Theory.empty) coin next ∧ target = mixedPair next coin := by
  rcases (mixedPair_termStep_iff admitsAtoms).mp step with found | ⟨next, sourceStep, -⟩
  · exact found
  · exact absurd sourceStep (normal_of_normalTest pureCover _ (by decide) _)

/-- **The argument does not step by the rules of the space of the function,
nor by those of the ambient space**: the application has no transition to the
application in which the argument is `heads`. -/
theorem mixedCoins_argument_not_by_function_rules (admitsAtoms : AdmitsAtoms admits) :
    ¬ TermStep (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) containedRun
      mixedCoins (mixedPair coin (.con "heads")) := by
  intro step
  obtain ⟨next, -, same⟩ := mixedCoins_argument_still admitsAtoms step
  have parts := pairAtomsIn_injective (presentation := containedPresentation)
    contained_declaresRun region_carriesAtoms.1 [chooseLeft, chooseRight] [] 0 same
  exact absurd parts.2 (by decide)

/-- **Under the plain matching evaluator**: without a guard, the three
statements hold. -/
theorem matching_mixedCoins :
    TermStep (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) containedRun
        mixedCoins (mixedPair (.con "heads") coin) ∧
      (∀ target : Contexts.Term containedRun AtomsReduce.closedAtom,
        TermStep (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) containedRun
            mixedCoins target →
          ∃ next, Dedukti.Step (withChoice Theory.empty) coin next ∧
            target = mixedPair next coin) ∧
        ¬ TermStep (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) containedRun
          mixedCoins (mixedPair coin (.con "heads")) :=
  ⟨mixedCoins_function_steps anySubject_admitsAtoms,
    fun _ step => mixedCoins_argument_still anySubject_admitsAtoms step,
    mixedCoins_argument_not_by_function_rules anySubject_admitsAtoms⟩

/-- **Negative, for the scoped presentation**: there the argument, in the
empty space, steps by the rules of the ambient space. -/
theorem scoped_mixedCoins_argument_steps (admitsAtoms : AdmitsAtoms admits) :
    Step (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) scopedRun
      (.apply "App" [runPattern (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 coin),
        runPattern (ruleSpace []) (atomAt 0 coin)])
      (.apply "App" [runPattern (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 coin),
        runPattern (ruleSpace []) (atomAt 0 (.con "heads"))]) := by
  obtain ⟨count, lifted⟩ := scoped_runCoin_steps admitsAtoms
  exact ⟨count + 1, step_appArgument (by simp [scoped_rewrites]) _ lifted⟩

/-! ## Any finite number of runs -/

/-- **A tree of applications whose leaves are runs.** -/
inductive RunTree where
  | run (space subject : Pattern)
  | app (function argument : RunTree)

namespace RunTree

/-- The pattern of a tree. -/
def pattern : RunTree → Pattern
  | .run space subject => runPattern space subject
  | .app function argument => .apply "App" [function.pattern, argument.pattern]

/-- **One leaf steps, in the member at the space of that leaf.** -/
inductive LeafStep (admits : Pattern → Bool) : RunTree → RunTree → Prop
  | run {space subject next : Pattern} :
      Step (regionEvaluator admits space) containedRun subject next →
        LeafStep admits (.run space subject) (.run space next)
  | function {function next : RunTree} (argument : RunTree) :
      LeafStep admits function next → LeafStep admits (.app function argument) (.app next argument)
  | argument (function : RunTree) {argument next : RunTree} :
      LeafStep admits argument next → LeafStep admits (.app function argument) (.app function next)

/-- No tree is an abstraction. -/
theorem pattern_ne_lam (tree : RunTree) (arguments : List Pattern) :
    tree.pattern ≠ .apply "Lam" arguments := by
  cases tree <;> simp [pattern, runPattern]

end RunTree

/-- **A tree of applications whose leaves are runs steps by a step of one
leaf in the member at the space of that leaf**, in the contained
presentation, under a guard that admits no run and at an ambient space that
answers nothing for an application. -/
theorem contained_tree_step_iff
    (refuses : ∀ space subject : Pattern, admits (runPattern space subject) = false)
    {ambientSpace : Pattern}
    (quiet : ∀ function argument : Pattern,
      admittedAnswers admits ambientSpace (.apply "App" [function, argument]) = []) :
    ∀ (tree : RunTree) {target : Pattern},
      Step (regionEvaluator admits ambientSpace) containedRun tree.pattern target ↔
        ∃ next : RunTree, target = next.pattern ∧ tree.LeafStep admits next := by
  intro tree
  induction tree with
  | run space subject =>
      intro target
      rw [RunTree.pattern, contained_run_step_iff_of_refuses refuses]
      constructor
      · rintro ⟨next, rfl, step⟩
        exact ⟨.run space next, rfl, .run step⟩
      · rintro ⟨next, rfl, leaf⟩
        cases leaf with
        | run step => exact ⟨_, rfl, step⟩
  | app function argument ihFunction ihArgument =>
      intro target
      constructor
      · rintro ⟨fuel, step⟩
        cases fuel with
        | zero => cases step
        | succ fuel =>
            obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ :=
              exists_rule_of_stepAt step
            rw [contained_rewrites] at member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · obtain ⟨domain, binder, body, value, shape, -⟩ := beta_inv matched premises
              simp only [RunTree.pattern, Pattern.apply.injEq, List.cons.injEq, and_true,
                true_and] at shape
              exact absurd shape.1 (RunTree.pattern_ne_lam function _)
            · obtain ⟨functionPattern, argumentPattern, moved, shape, inner, applied⟩ :=
                appFunction_inv matched premises
              simp only [RunTree.pattern, Pattern.apply.injEq, List.cons.injEq, and_true,
                true_and] at shape
              obtain ⟨rfl, rfl⟩ := shape
              obtain ⟨next, rfl, leaf⟩ := ihFunction.mp ⟨fuel, inner⟩
              exact ⟨.app next argument, applied, .function argument leaf⟩
            · obtain ⟨functionPattern, argumentPattern, moved, shape, inner, applied⟩ :=
                appArgument_inv matched premises
              simp only [RunTree.pattern, Pattern.apply.injEq, List.cons.injEq, and_true,
                true_and] at shape
              obtain ⟨rfl, rfl⟩ := shape
              obtain ⟨next, rfl, leaf⟩ := ihArgument.mp ⟨fuel, inner⟩
              exact ⟨.app function next, applied, .argument function leaf⟩
            · exact absurd matched (apply_not_matched (label := "Pi") (other := "App") (by decide))
            · exact absurd matched (apply_not_matched (label := "Pi") (other := "App") (by decide))
            · exact absurd matched (apply_not_matched (label := "Lam") (other := "App") (by decide))
            · exact absurd matched (apply_not_matched (label := "Lam") (other := "App") (by decide))
            · exact absurd matched
                (apply_not_matched (label := "prime-drop") (other := "App") (by decide))
            · obtain ⟨answer, found, -⟩ := ambientRoot_inv matched premises
              rw [RunTree.pattern, quiet] at found
              cases found
            · exact absurd matched
                (apply_not_matched (label := "prime-run") (other := "App") (by decide))
            · exact absurd matched
                (apply_not_matched (label := "prime-run") (other := "App") (by decide))
            · exact absurd matched
                (apply_not_matched (label := "prime-run") (other := "App") (by decide))
            · exact absurd matched
                (apply_not_matched (label := "prime-run") (other := "App") (by decide))
            · exact absurd matched
                (apply_not_matched (label := "prime-run") (other := "App") (by decide))
            · exact absurd matched
                (apply_not_matched (label := "prime-run") (other := "App") (by decide))
            · exact absurd matched
                (apply_not_matched (label := "prime-run") (other := "App") (by decide))
            · exact absurd matched
                (apply_not_matched (label := "prime-run") (other := "App") (by decide))
            · exact absurd matched
                (apply_not_matched (label := "prime-run") (other := "App") (by decide))
            · exact absurd matched
                (apply_not_matched (label := "prime-run") (other := "App") (by decide))
      · rintro ⟨next, rfl, leaf⟩
        cases leaf with
        | function _ inner =>
            obtain ⟨count, lifted⟩ := ihFunction.mpr ⟨_, rfl, inner⟩
            exact ⟨count + 1, step_appFunction (by simp [contained_rewrites]) _ lifted⟩
        | argument _ inner =>
            obtain ⟨count, lifted⟩ := ihArgument.mpr ⟨_, rfl, inner⟩
            exact ⟨count + 1, step_appArgument (by simp [contained_rewrites]) _ lifted⟩

/-- **Positive**: a tree of three runs in three spaces.  The middle run, in
the space of the two rules of choice, steps; the tree is at the empty ambient
space, under the guard that admits what is no run. -/
theorem threeRuns_step :
    Step (regionEvaluator notRun emptySpace) containedRun
      (RunTree.app (.app (.run emptySpace (atomAt 0 coin))
        (.run (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 coin)))
        (.run (ruleSpace [chooseLeft]) (atomAt 0 coin))).pattern
      (RunTree.app (.app (.run emptySpace (atomAt 0 coin))
        (.run (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 (.con "tails"))))
        (.run (ruleSpace [chooseLeft]) (atomAt 0 coin))).pattern :=
  (contained_tree_step_iff notRun_run (fun _ _ => admittedAnswers_emptySpace notRun _) _).mpr
    ⟨_, rfl, .function _ (.argument _ (.run
      ((contained_atom_step_iff notRun_admitsAtoms choiceRules_admitted.1 choiceRules_admitted.2
        withChoice_rules (fun _ => rfl)).mpr
        ⟨_, rfl, Dedukti.step_choose_right Theory.empty _ _⟩)))⟩

/-- **Negative**: a leaf whose subject has no step in the member at its space
gives the tree no step.  The run of `choose heads tails` in the empty space,
as a tree of one leaf. -/
theorem oneLeaf_normal (target : Pattern) :
    ¬ Step (regionEvaluator notRun emptySpace) containedRun
      (RunTree.run emptySpace (atomAt 0 coin)).pattern target := by
  intro step
  obtain ⟨next, -, leaf⟩ :=
    (contained_tree_step_iff notRun_run (fun _ _ => admittedAnswers_emptySpace notRun _) _).mp step
  cases leaf with
  | run inner => exact contained_normal_at_empty notRun coin (by decide) 0 _ inner

#print axioms contained_pair_step_iff
#print axioms choiceSpace_quiet_on_pair
#print axioms contained_pairAtoms_step_iff
#print axioms eq_pairAtomsIn_of_related
#print axioms contained_pairAtoms_termStep_iff
#print axioms mixedCoins_function_steps
#print axioms mixedCoins_argument_still
#print axioms mixedCoins_argument_not_by_function_rules
#print axioms matching_mixedCoins
#print axioms scoped_mixedCoins_argument_steps
#print axioms contained_tree_step_iff
#print axioms threeRuns_step
#print axioms oneLeaf_normal
#print axioms admittedAnswers_emptySpace
#print axioms pairAtomsIn_injective
#print axioms mixedCoins_eq
#print axioms mixedPair_termStep_iff
#print axioms RunTree.pattern_ne_lam

end Mettapedia.Logic.HostingStyles.AmbientRegions
