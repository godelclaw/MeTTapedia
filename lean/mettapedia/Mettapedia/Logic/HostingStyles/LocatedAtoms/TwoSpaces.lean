import Mettapedia.Logic.HostingStyles.LocatedAtoms.Contexts

/-!
# An application whose function and argument are runs in two different spaces

With the equations of a run a term may have its parts in different spaces:
`App(run(first, f), run(second, x))` is a term, and it is the run of no atom
in one space.  This module shows that each part steps by the rules of its own
space, and by no other.

* **Positive** (`pair_termStep_function`, `pair_termStep_argument`): a step
  of the function in the theory of the first space, and a step of the
  argument in the theory of the second, are transitions of the application.
  Instance (`mixedCoins_function_steps`): `choose heads tails` in the space
  of the two rules of choice, applied to `choose heads tails` in the empty
  space, has a transition to `heads` in its function.
* **Each part by the rules of its own space only** (`pair_termStep_inv`): for
  two different spaces of rules, every transition of the application is a
  step of the function in the theory of the first space or a step of the
  argument in the theory of the second, the other part unchanged.  The
  function is no abstraction, so that the application is no beta redex.
  The proof reads every spelling of the application: a step of a part read
  beneath an outer run (`spelled_under_stepAt`), and no root step of a run
  around the whole, whose leaves are in two spaces (`located?_app_apart`).
* **Negative** (`mixedCoins_argument_still`,
  `mixedCoins_argument_not_by_function_rules`): in the instance the argument
  never moves.  It is `choose heads tails` in the empty space, and the rules
  of choice are in the space of the function.
* **Negative, for the matching evaluator** (`matching_foreign_step`): under
  the evaluator that reads up to quotation and dropping only, the atom of
  `choose heads tails` in the empty space has a transition, by a rule of
  another space.  A run of a run is the inner run, so any space may be
  written around the atom, and the matching evaluator reads the outer one.
  Under the evaluator of located atoms it has none
  (`emptySpace_coin_normal`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.LocatedAtoms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti
  (Theory inst patternVars usesOnly withChoice chooseLeft chooseRight normal_of_normalTest)
open Mettapedia.GSLT.Dedukti.Language (metaName)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)
open Mettapedia.Logic.HostingStyles.AmbientSpace
  (coin choiceRules_admitted withChoice_rules noRules_admitted pureCover)

variable {base : BasePremiseEvaluator}

/-! ## The leaves of an application in two spaces -/

/-- **An application whose two parts are pushed in two different spaces is
located in no one space.** -/
theorem located?_app_apart {first second left right : Pattern} (apart : first ≠ second)
    (cleanLeft : tokens runLabel left = 0) (cleanRight : tokens runLabel right = 0) :
    located? (.apply "App" [push first left, push second right]) = none := by
  have head : headSpace? (.apply "App" [push first left, push second right]) = some first := by
    simp [headSpace?, headSpaceList?, headSpace?_push first left cleanLeft]
  have plain : unlocate (.apply "App" [push first left, push second right]) =
      .apply "App" [left, right] := by
    rw [unlocate_apply_of_ne (by decide)]
    simp [unlocate_push _ _ cleanLeft, unlocate_push _ _ cleanRight]
  unfold located?
  rw [head]
  simp only [plain, push_app]
  split_ifs with same
  · exfalso
    simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
    have heads := congrArg headSpace? same
    rw [headSpace?_push first right cleanRight, headSpace?_push second right cleanRight] at heads
    exact apart (Option.some.inj heads)
  · rfl

/-- **Positive**: with one space the application is located in it. -/
theorem located?_app_same (space : Pattern) {left right : Pattern}
    (cleanLeft : tokens runLabel left = 0) (cleanRight : tokens runLabel right = 0) :
    located? (.apply "App" [push space left, push space right]) =
      some (space, .apply "App" [left, right]) := by
  rw [← push_app]
  exact located?_push (by simp [tokens, tokensList, runLabel, cleanLeft, cleanRight]) space

/-! ## A step of a part, read beneath an outer run -/

/-- **A step of a term that, read beneath an outer space, is the atom of a
term pushed in a plain space, is a step of the term**, and the result is read
the same way. -/
theorem spelled_under_stepAt {space : Pattern} (plain : PlainSpace space) {theory : Theory}
    (answers : ∀ {depth : Nat} {term : LF.Term} {answer : Pattern},
      answer ∈ matchResults space (atomAt depth term) →
        ∃ next, answer = atomAt depth next ∧ Dedukti.Step theory term next)
    {fuel : Nat} {stage : List TypeExpr} {outer pattern target : Pattern} {depth : Nat}
    {term : LF.Term}
    (sorted : OpenPatternWellSorted located FreeTypeContext.empty stage (.base "Atom") pattern)
    (pushed : push outer (settle pattern) = push space (atomAt depth term))
    (step : StepAt locatedEvaluator located fuel pattern target) :
    ∃ next, Dedukti.Step theory term next ∧
      push outer (settle target) = push space (atomAt depth next) := by
  have wrapped := (spelled_run_of_settle plain pattern).1 sorted pushed
  rcases wrapped.run_inv with ⟨rfl, _, live⟩ | dead
  · obtain ⟨next, sNext, sourceStep⟩ := spelled_stepAt plain answers fuel live step
    exact ⟨next, sourceStep, sNext.settle_partial plain⟩
  · obtain ⟨next, sNext, sourceStep⟩ := spelled_stepAt plain answers fuel dead step
    exact ⟨next, sourceStep, by rw [sNext.settle_whole plain, push_push]⟩

/-! ## Every step of every spelling of the application -/

/-- **A step of a term that, read beneath an outer space, is an application
of an atom pushed in one plain space to an atom pushed in another, is a step
of the function in the theory of the first space or a step of the argument in
the theory of the second.**  The function is no abstraction. -/
theorem pair_stepAt {first second : Pattern} (plainFirst : PlainSpace first)
    (plainSecond : PlainSpace second) (apart : first ≠ second)
    {functionTheory argumentTheory : Theory}
    (functionAnswers : ∀ {depth : Nat} {term : LF.Term} {answer : Pattern},
      answer ∈ matchResults first (atomAt depth term) →
        ∃ next, answer = atomAt depth next ∧ Dedukti.Step functionTheory term next)
    (argumentAnswers : ∀ {depth : Nat} {term : LF.Term} {answer : Pattern},
      answer ∈ matchResults second (atomAt depth term) →
        ∃ next, answer = atomAt depth next ∧ Dedukti.Step argumentTheory term next) :
    ∀ (fuel : Nat) {stage : List TypeExpr} {outer pattern target : Pattern} {depth : Nat}
      {function argument : LF.Term},
      OpenPatternWellSorted located FreeTypeContext.empty stage (.base "Atom") pattern →
      (∀ domain body, function ≠ .lam domain body) →
      push outer (settle pattern) =
        .apply "App" [push first (atomAt depth function), push second (atomAt depth argument)] →
      StepAt locatedEvaluator located fuel pattern target →
        (∃ next, Dedukti.Step functionTheory function next ∧
          push outer (settle target) =
            .apply "App" [push first (atomAt depth next), push second (atomAt depth argument)]) ∨
        (∃ next, Dedukti.Step argumentTheory argument next ∧
          push outer (settle target) =
            .apply "App" [push first (atomAt depth function), push second (atomAt depth next)]) := by
  intro fuel
  induction fuel with
  | zero => intro stage outer pattern target depth function argument _ _ _ step; cases step
  | succ fuel ih =>
      intro stage outer pattern target depth function argument sorted notLam pushed step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [located_rewrites, atomsReduce_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      · obtain ⟨domain, binder, body, value, rfl, -⟩ := beta_inv matched premises
        rw [settle_app, settle_binder (label := "Lam") (.inl rfl), push_app,
          push_binder (label := "Lam") (.inl rfl)] at pushed
        simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at pushed
        rcases push_atomAt_cases first depth function with ⟨_, located⟩ | ⟨_, _, _, located⟩ |
          ⟨domainTerm, bodyTerm, rfl, _⟩ | ⟨_, _, _, located⟩
        · rw [located] at pushed
          simp [runPattern] at pushed
        · rw [located] at pushed
          simp at pushed
        · exact absurd rfl (notLam domainTerm bodyTerm)
        · rw [located] at pushed
          simp at pushed
      · obtain ⟨functionPattern, argumentPattern, next, rfl, inner, applied⟩ :=
          appFunction_inv matched premises
        obtain ⟨sortedFunction, -⟩ := wellSorted_app_inv sorted
        rw [settle_app, push_app] at pushed
        simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at pushed
        obtain ⟨nextTerm, sourceStep, moved⟩ :=
          spelled_under_stepAt plainFirst functionAnswers sortedFunction pushed.1 inner
        exact .inl ⟨nextTerm, sourceStep, by
          rw [applied, settle_app, push_app, moved, pushed.2]⟩
      · obtain ⟨functionPattern, argumentPattern, next, rfl, inner, applied⟩ :=
          appArgument_inv matched premises
        obtain ⟨-, sortedArgument⟩ := wellSorted_app_inv sorted
        rw [settle_app, push_app] at pushed
        simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at pushed
        obtain ⟨nextTerm, sourceStep, moved⟩ :=
          spelled_under_stepAt plainSecond argumentAnswers sortedArgument pushed.2 inner
        exact .inr ⟨nextTerm, sourceStep, by
          rw [applied, settle_app, push_app, moved, pushed.1]⟩
      · obtain ⟨domain, binder, body, next, rfl, -, -⟩ := piDomain_inv matched premises
        rw [settle_binder (label := "Pi") (.inr rfl), push_binder (label := "Pi") (.inr rfl)]
          at pushed
        simp at pushed
      · obtain ⟨domain, binder, body, next, rfl, -, -⟩ := piBody_inv matched premises
        rw [settle_binder (label := "Pi") (.inr rfl), push_binder (label := "Pi") (.inr rfl)]
          at pushed
        simp at pushed
      · obtain ⟨domain, binder, body, next, rfl, -, -⟩ := lamDomain_inv matched premises
        rw [settle_binder (label := "Lam") (.inl rfl), push_binder (label := "Lam") (.inl rfl)]
          at pushed
        simp at pushed
      · obtain ⟨domain, binder, body, next, rfl, -, -⟩ := lamBody_inv matched premises
        rw [settle_binder (label := "Lam") (.inl rfl), push_binder (label := "Lam") (.inl rfl)]
          at pushed
        simp at pushed
      · obtain ⟨atom, rfl, -⟩ := release_inv matched premises
        rw [dropped, settle_apply_of_ne (label := "prime-drop") (by decide) (by decide),
          push_wraps (distributes_eq_false (by decide) (by decide) (by decide) _)
            (fun both => absurd both.1 (by decide))] at pushed
        simp [runPattern] at pushed
      · obtain ⟨space, subject, next, rfl, inner, applied⟩ := runSubject_inv matched premises
        obtain ⟨-, sortedSubject⟩ := wellSorted_run_inv sorted
        rw [settle_runPattern, push_push] at pushed
        rcases ih sortedSubject notLam pushed inner with ⟨nextTerm, sourceStep, moved⟩ |
          ⟨nextTerm, sourceStep, moved⟩
        · exact .inl ⟨nextTerm, sourceStep, by
            rw [applied, settle_runPattern, push_push, moved]⟩
        · exact .inr ⟨nextTerm, sourceStep, by
            rw [applied, settle_runPattern, push_push, moved]⟩
      · obtain ⟨space, subject, answer, rfl, found, -⟩ := locatedRoot_inv matched premises
        rw [settle_runPattern, push_push] at pushed
        have silent : locatedAnswers space subject = [] := by
          unfold locatedAnswers
          rw [settle_runPattern, pushed, located?_app_apart apart
            (tokens_atomAt (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) function depth)
            (tokens_atomAt (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) argument depth)]
        rw [silent] at found
        cases found
      · obtain ⟨space, functionPattern, argumentPattern, next, rfl, inner, applied⟩ :=
          runAppFunction_inv matched premises
        obtain ⟨sortedSpace, sortedSubject⟩ := wellSorted_run_inv sorted
        obtain ⟨sortedFunction, -⟩ := wellSorted_app_inv sortedSubject
        rw [settle_runPattern, push_push, settle_app, push_app] at pushed
        simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at pushed
        obtain ⟨nextTerm, sourceStep, moved⟩ :=
          spelled_under_stepAt (outer := settle space) plainFirst functionAnswers
            (runTerm ⟨space, sortedSpace⟩ ⟨functionPattern, sortedFunction⟩).2
            ((congrArg (push (settle space)) (settle_runPattern space functionPattern)).trans
              ((push_push _ _ _).trans pushed.1)) inner
        rw [settle_runPattern, push_push] at moved
        exact .inl ⟨nextTerm, sourceStep, by
          rw [applied, settle_runPattern, push_push, settle_app, push_app, moved, pushed.2]⟩
      · obtain ⟨space, functionPattern, argumentPattern, next, rfl, inner, applied⟩ :=
          runAppArgument_inv matched premises
        obtain ⟨sortedSpace, sortedSubject⟩ := wellSorted_run_inv sorted
        obtain ⟨-, sortedArgument⟩ := wellSorted_app_inv sortedSubject
        rw [settle_runPattern, push_push, settle_app, push_app] at pushed
        simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at pushed
        obtain ⟨nextTerm, sourceStep, moved⟩ :=
          spelled_under_stepAt (outer := settle space) plainSecond argumentAnswers
            (runTerm ⟨space, sortedSpace⟩ ⟨argumentPattern, sortedArgument⟩).2
            ((congrArg (push (settle space)) (settle_runPattern space argumentPattern)).trans
              ((push_push _ _ _).trans pushed.2)) inner
        rw [settle_runPattern, push_push] at moved
        exact .inr ⟨nextTerm, sourceStep, by
          rw [applied, settle_runPattern, push_push, settle_app, push_app, moved, pushed.1]⟩
      · obtain ⟨space, domain, binder, body, next, rfl, -, -⟩ := runPiDomain_inv matched premises
        rw [settle_runPattern, push_push, settle_binder (label := "Pi") (.inr rfl),
          push_binder (label := "Pi") (.inr rfl)] at pushed
        simp at pushed
      · obtain ⟨space, domain, binder, body, next, rfl, -, -⟩ := runPiBody_inv matched premises
        rw [settle_runPattern, push_push, settle_binder (label := "Pi") (.inr rfl),
          push_binder (label := "Pi") (.inr rfl)] at pushed
        simp at pushed
      · obtain ⟨space, domain, binder, body, next, rfl, -, -⟩ := runLamDomain_inv matched premises
        rw [settle_runPattern, push_push, settle_binder (label := "Lam") (.inl rfl),
          push_binder (label := "Lam") (.inl rfl)] at pushed
        simp at pushed
      · obtain ⟨space, domain, binder, body, next, rfl, -, -⟩ := runLamBody_inv matched premises
        rw [settle_runPattern, push_push, settle_binder (label := "Lam") (.inl rfl),
          push_binder (label := "Lam") (.inl rfl)] at pushed
        simp at pushed

/-! ## A spelling of the application is equal to it -/

/-- **A term that, read beneath a pattern variable, is the application of an
atom pushed in the space of one list of rules to an atom pushed in the space
of another, is equal to the application of the two runs.** -/
theorem pair_related {functionRules argumentRules : List Dedukti.RewriteRule} {depth : Nat}
    {function argument : LF.Term} (pattern : Pattern) :
    ∀ (sorted : OpenPatternWellSorted located FreeTypeContext.empty
        (List.replicate depth (.base "Atom")) (.base "Atom") pattern),
      push (.fvar "outside") (settle pattern) =
        .apply "App" [push (ruleSpace functionRules) (atomAt depth function),
          push (ruleSpace argumentRules) (atomAt depth argument)] →
      (termSetoid base located (atomInterface depth)).r
        (⟨pattern, sorted⟩ : Contexts.Term located (atomInterface depth))
        (appTerm (runAtom functionRules depth function) (runAtom argumentRules depth argument)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro sorted pushed
      rw [settle, push] at pushed
      simp [runPattern] at pushed
  | hfvar name =>
      intro sorted pushed
      rw [settle, push] at pushed
      simp [runPattern] at pushed
  | happly label arguments ih =>
      intro sorted pushed
      rcases atom_cases sorted with ⟨_, shape⟩ | ⟨other, others, shape, listed⟩ |
        ⟨functionPattern, argumentPattern, shape, sortedFunction, sortedArgument⟩ |
        ⟨binderLabel, domain, body, binding, shape, _, _⟩ |
        ⟨space, subject, shape, sortedSpace, sortedSubject⟩
      · cases shape
      · simp only [Pattern.apply.injEq] at shape
        obtain ⟨rfl, rfl⟩ := shape
        have noRun : label ≠ "prime-run" := by rintro rfl; exact absurd listed (by decide)
        have noQuote : label ≠ "prime-quote" := by rintro rfl; exact absurd listed (by decide)
        have noApp : label ≠ "App" := by rintro rfl; exact absurd listed (by decide)
        have noLam : label ≠ "Lam" := by rintro rfl; exact absurd listed (by decide)
        have noPi : label ≠ "Pi" := by rintro rfl; exact absurd listed (by decide)
        rw [settle_apply_of_ne noRun noQuote, push_wraps (distributes_eq_false noApp noLam noPi _)
          (fun both => noRun both.1)] at pushed
        simp [runPattern] at pushed
      · simp only [Pattern.apply.injEq] at shape
        obtain ⟨rfl, rfl⟩ := shape
        rw [settle_app, push_app] at pushed
        simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at pushed
        have spelledFunction :=
          (spelled_run_of_settle (ruleSpace_plain functionRules) functionPattern).1
            sortedFunction pushed.1
        have spelledArgument :=
          (spelled_run_of_settle (ruleSpace_plain argumentRules) argumentPattern).1
            sortedArgument pushed.2
        rcases spelledFunction.run_inv with ⟨same, -, -⟩ | wholeFunction
        · exact absurd same ((ruleSpace_plain functionRules).node _)
        rcases spelledArgument.run_inv with ⟨same, -, -⟩ | wholeArgument
        · exact absurd same ((ruleSpace_plain argumentRules).node _)
        exact appTerm_related
          ((spelled_related (ruleSpaceTerm functionRules) wholeFunction sortedFunction
            (locatedAtom depth function).2).1 rfl)
          ((spelled_related (ruleSpaceTerm argumentRules) wholeArgument sortedArgument
            (locatedAtom depth argument).2).1 rfl)
      · simp only [Pattern.apply.injEq] at shape
        obtain ⟨rfl, rfl⟩ := shape
        rw [settle_binder binding, push_binder binding] at pushed
        simp only [Pattern.apply.injEq] at pushed
        rcases binding with rfl | rfl <;> exact absurd pushed.1 (by decide)
      · simp only [runPattern, Pattern.apply.injEq] at shape
        obtain ⟨rfl, rfl⟩ := shape
        have normal : settle (Pattern.apply "prime-run" [space, subject]) =
            push (settle space) (settle subject) := settle_runPattern space subject
        rw [normal, push_push] at pushed
        rcases atom_cases sortedSubject with ⟨index, rfl⟩ | ⟨other, others, rfl, listed⟩ |
          ⟨functionPattern, argumentPattern, rfl, sortedFunction, sortedArgument⟩ |
          ⟨binderLabel, domain, body, binding, rfl, _, _⟩ |
          ⟨inner, innerSubject, rfl, sortedInner, sortedInnerSubject⟩
        · rw [settle, push] at pushed
          simp [runPattern] at pushed
        · have noRun : other ≠ "prime-run" := by rintro rfl; exact absurd listed (by decide)
          have noQuote : other ≠ "prime-quote" := by rintro rfl; exact absurd listed (by decide)
          have noApp : other ≠ "App" := by rintro rfl; exact absurd listed (by decide)
          have noLam : other ≠ "Lam" := by rintro rfl; exact absurd listed (by decide)
          have noPi : other ≠ "Pi" := by rintro rfl; exact absurd listed (by decide)
          rw [settle_apply_of_ne noRun noQuote,
            push_wraps (distributes_eq_false noApp noLam noPi _) (fun both => noRun both.1)]
            at pushed
          simp [runPattern] at pushed
        · rw [settle_app, push_app] at pushed
          simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at pushed
          have spelledFunction := spells_of_settle (ruleSpace_plain functionRules)
            (runTerm ⟨space, sortedSpace⟩ ⟨functionPattern, sortedFunction⟩).2
            ((settle_runPattern space functionPattern).trans pushed.1)
          have spelledArgument := spells_of_settle (ruleSpace_plain argumentRules)
            (runTerm ⟨space, sortedSpace⟩ ⟨argumentPattern, sortedArgument⟩).2
            ((settle_runPattern space argumentPattern).trans pushed.2)
          exact .trans _ _ _
            (runTerm_app ⟨space, sortedSpace⟩ ⟨functionPattern, sortedFunction⟩
              ⟨argumentPattern, sortedArgument⟩)
            (appTerm_related
              ((spelled_related (ruleSpaceTerm functionRules) spelledFunction
                (runTerm ⟨space, sortedSpace⟩ ⟨functionPattern, sortedFunction⟩).2
                (locatedAtom depth function).2).1 rfl)
              ((spelled_related (ruleSpaceTerm argumentRules) spelledArgument
                (runTerm ⟨space, sortedSpace⟩ ⟨argumentPattern, sortedArgument⟩).2
                (locatedAtom depth argument).2).1 rfl))
        · rw [settle_binder binding, push_binder binding] at pushed
          simp only [Pattern.apply.injEq] at pushed
          rcases binding with rfl | rfl <;> exact absurd pushed.1 (by decide)
        · have whole := ih (runPattern inner innerSubject) (by simp) sortedSubject
            (by
              rw [settle_runPattern, push_push]
              rw [settle_runPattern, push_push] at pushed
              exact pushed)
          exact .trans _ _ _ (runTerm_related ⟨space, sortedSpace⟩ whole)
            (.trans _ _ _
              (runTerm_app ⟨space, sortedSpace⟩ (runAtom functionRules depth function)
                (runAtom argumentRules depth argument))
              (appTerm_related
                (runTerm_run ⟨space, sortedSpace⟩ (spaceAt (ruleSpaceTerm functionRules) _)
                  (locatedAtom depth function))
                (runTerm_run ⟨space, sortedSpace⟩ (spaceAt (ruleSpaceTerm argumentRules) _)
                  (locatedAtom depth argument))))
  | hlambda binder body _ =>
      intro sorted pushed
      rw [settle, push] at pushed
      cases pushed
  | hmultiLambda arity binders body _ =>
      intro sorted pushed
      rw [settle, push] at pushed
      simp [runPattern] at pushed
  | hsubst body replacement _ _ =>
      intro sorted pushed
      rw [settle, push] at pushed
      simp [runPattern] at pushed
  | hcollection kind elements rest _ =>
      intro sorted pushed
      rw [settle, push] at pushed
      simp [runPattern] at pushed

/-! ## The transitions of the application -/

/-- **Positive**: a step of the function, in a theory whose rules are those
of the first list, is a transition of the application. -/
theorem pair_termStep_function {functionRules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ functionRules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ functionRules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (listed : ∀ rule, theory.rule rule → rule ∈ functionRules)
    (undefined : ∀ name, theory.body name = none) (argumentRules : List Dedukti.RewriteRule)
    (depth : Nat) {function next : LF.Term} (argument : LF.Term)
    (step : Dedukti.Step theory function next) :
    TermStep locatedEvaluator located
      (appTerm (runAtom functionRules depth function) (runAtom argumentRules depth argument))
      (appTerm (runAtom functionRules depth next) (runAtom argumentRules depth argument)) :=
  termStep_appFunction _ (runAtom_termStep firstOrder bound listed undefined step depth)

/-- **Positive**: a step of the argument, in a theory whose rules are those
of the second list, is a transition of the application. -/
theorem pair_termStep_argument {argumentRules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ argumentRules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ argumentRules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (listed : ∀ rule, theory.rule rule → rule ∈ argumentRules)
    (undefined : ∀ name, theory.body name = none) (functionRules : List Dedukti.RewriteRule)
    (depth : Nat) (function : LF.Term) {argument next : LF.Term}
    (step : Dedukti.Step theory argument next) :
    TermStep locatedEvaluator located
      (appTerm (runAtom functionRules depth function) (runAtom argumentRules depth argument))
      (appTerm (runAtom functionRules depth function) (runAtom argumentRules depth next)) :=
  termStep_appArgument _ (runAtom_termStep firstOrder bound listed undefined step depth)

/-- The normal form of the application of two runs of atoms. -/
theorem settle_pair (functionRules argumentRules : List Dedukti.RewriteRule) (depth : Nat)
    (function argument : LF.Term) :
    settle (appTerm (runAtom functionRules depth function)
      (runAtom argumentRules depth argument)).1 =
      .apply "App" [push (ruleSpace functionRules) (atomAt depth function),
        push (ruleSpace argumentRules) (atomAt depth argument)] := by
  show settle (.apply "App" [runPattern (ruleSpace functionRules) (atomAt depth function),
    runPattern (ruleSpace argumentRules) (atomAt depth argument)]) = _
  rw [settle_app, settle_run_atomAt, settle_run_atomAt]

/-- **Each part steps by the rules of its own space only.**  For two
different lists of first-order rules with bound right sides, every transition
of the application of the run of a function in the space of the first to the
run of an argument in the space of the second is a step of the function in a
theory that declares the first rules, the argument unchanged, or a step of
the argument in a theory that declares the second, the function unchanged.
The function is no abstraction. -/
theorem pair_termStep_inv {functionRules argumentRules : List Dedukti.RewriteRule}
    (functionFirstOrder : ∀ rule ∈ functionRules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (functionBound : ∀ rule ∈ functionRules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (argumentFirstOrder : ∀ rule ∈ argumentRules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (argumentBound : ∀ rule ∈ argumentRules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (apart : functionRules ≠ argumentRules) {functionTheory argumentTheory : Theory}
    (functionDeclared : ∀ rule ∈ functionRules, functionTheory.rule rule)
    (argumentDeclared : ∀ rule ∈ argumentRules, argumentTheory.rule rule) {depth : Nat}
    {function argument : LF.Term} (notLam : ∀ domain body, function ≠ .lam domain body)
    {target : Contexts.Term located (atomInterface depth)}
    (step : TermStep locatedEvaluator located
      (appTerm (runAtom functionRules depth function) (runAtom argumentRules depth argument))
      target) :
    (∃ next, Dedukti.Step functionTheory function next ∧
      (termSetoid locatedEvaluator located (atomInterface depth)).r target
        (appTerm (runAtom functionRules depth next) (runAtom argumentRules depth argument))) ∨
    (∃ next, Dedukti.Step argumentTheory argument next ∧
      (termSetoid locatedEvaluator located (atomInterface depth)).r target
        (appTerm (runAtom functionRules depth function) (runAtom argumentRules depth next))) := by
  obtain ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩ := step
  have normal : push (.fvar "outside") (settle redex.1) =
      .apply "App" [push (ruleSpace functionRules) (atomAt depth function),
        push (ruleSpace argumentRules) (atomAt depth argument)] := by
    rw [← settle_eq_of_related before, settle_pair, push_app, push_push, push_push]
  rcases pair_stepAt (ruleSpace_plain functionRules) (ruleSpace_plain argumentRules)
      (fun same => apart (ruleSpace_injective same))
      (functionTheory := functionTheory) (argumentTheory := argumentTheory)
      (fun found => by
        obtain ⟨rule, inRules, assignment, rfl, rfl⟩ :=
          AtomsReduce.exists_instance_of_mem_matchResults functionFirstOrder functionBound found
        exact ⟨_, rfl, Dedukti.Step.root (.rule assignment (functionDeclared rule inRules))⟩)
      (fun found => by
        obtain ⟨rule, inRules, assignment, rfl, rfl⟩ :=
          AtomsReduce.exists_instance_of_mem_matchResults argumentFirstOrder argumentBound found
        exact ⟨_, rfl, Dedukti.Step.root (.rule assignment (argumentDeclared rule inRules))⟩)
      fuel redex.2 notLam normal fired with ⟨next, sourceStep, moved⟩ | ⟨next, sourceStep, moved⟩
  · exact .inl ⟨next, sourceStep,
      .trans _ _ _ (.symm _ _ after) (pair_related contractum.1 contractum.2 moved)⟩
  · exact .inr ⟨next, sourceStep,
      .trans _ _ _ (.symm _ _ after) (pair_related contractum.1 contractum.2 moved)⟩

/-! ## The instance: choice in one space, none in the other -/

/-- `choose heads tails` in the space of the two rules of choice, applied to
`choose heads tails` in the empty space. -/
def mixedCoins : Contexts.Term located AtomsReduce.closedAtom :=
  appTerm (runAtom [chooseLeft, chooseRight] 0 coin) (runAtom [] 0 coin)

/-- **Positive instance**: the function, in the space of the rules of choice,
steps to `heads`. -/
theorem mixedCoins_function_steps :
    TermStep locatedEvaluator located mixedCoins
      (appTerm (runAtom [chooseLeft, chooseRight] 0 (.con "heads")) (runAtom [] 0 coin)) :=
  pair_termStep_function choiceRules_admitted.1 choiceRules_admitted.2
    (theory := withChoice Theory.empty) (fun rule member => (withChoice_rules rule).mp member)
    (fun _ => rfl) [] 0 coin (Dedukti.step_choose_left Theory.empty _ _)

/-- **Negative instance**: every transition of the application is a step of
its function by the calculus with choice; its argument, in the empty space,
does not move. -/
theorem mixedCoins_argument_still {target : Contexts.Term located AtomsReduce.closedAtom}
    (step : TermStep locatedEvaluator located mixedCoins target) :
    ∃ next, Dedukti.Step (withChoice Theory.empty) coin next ∧
      (termSetoid locatedEvaluator located AtomsReduce.closedAtom).r target
        (appTerm (runAtom [chooseLeft, chooseRight] 0 next) (runAtom [] 0 coin)) := by
  rcases pair_termStep_inv (functionRules := [chooseLeft, chooseRight]) (argumentRules := [])
      choiceRules_admitted.1 choiceRules_admitted.2 noRules_admitted.1 noRules_admitted.2
      (by decide) (functionTheory := withChoice Theory.empty) (argumentTheory := Theory.empty)
      (fun rule member => (withChoice_rules rule).mpr member)
      (fun _ member => absurd member List.not_mem_nil) (depth := 0) (function := coin)
      (argument := coin)
      (fun _ _ wrong => by simp [coin, Mettapedia.GSLT.Dedukti.choose] at wrong) step with
      ⟨next, sourceStep, related⟩ |
      ⟨next, sourceStep, -⟩
  · exact ⟨next, sourceStep, related⟩
  · exact absurd sourceStep (normal_of_normalTest pureCover _ (by decide) _)

/-- **The argument does not step by the rules of the space of the
function**: the application has no transition to the application in which the
argument is `heads`. -/
theorem mixedCoins_argument_not_by_function_rules :
    ¬ TermStep locatedEvaluator located mixedCoins
      (appTerm (runAtom [chooseLeft, chooseRight] 0 coin) (runAtom [] 0 (.con "heads"))) := by
  intro step
  obtain ⟨next, -, related⟩ := mixedCoins_argument_still step
  have same := settle_eq_of_related related
  rw [settle_pair, settle_pair] at same
  simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
  have plain := congrArg unlocate same.2
  rw [unlocate_push _ _ (tokens_atomAt (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ 0),
    unlocate_push _ _ (tokens_atomAt (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ 0)] at plain
  exact absurd (atomAt_injective 0 plain) (by decide)

/-! ## The matching evaluator lets a rule of another space fire -/

/-- The rule `x ⟶ u`: every term steps to the constant `u`. -/
def takeAll : Dedukti.RewriteRule := ⟨.var 0, .con "u"⟩

theorem takeAll_admitted :
    (∀ rule ∈ [takeAll],
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true) ∧
      ∀ rule ∈ [takeAll], usesOnly (patternVars rule.lhs) 0 rule.rhs = true := by
  decide

/-- **Under the matching evaluator a rule of another space fires**: the atom
of `choose heads tails` in the empty space has a transition to the constant
`u` in the space of the rule `x ⟶ u`.  The outer space is written around the
atom by the equation of a run of a run, and the matching evaluator reads
it. -/
theorem matching_foreign_step :
    TermStep matchingEvaluator located (runAtom [] 0 coin) (runAtom [takeAll] 0 (.con "u")) := by
  refine ⟨runTerm (spaceAt (ruleSpaceTerm [takeAll]) []) (runAtom [] 0 coin),
    runAtom [takeAll] 0 (.con "u"),
    .symm _ _ (runTerm_run _ _ _),
    ⟨1, step_runRoot (by simp [located_rewrites, atomsReduce_rewrites]) ?_⟩, .refl _⟩
  show atomAt 0 (.con "u") ∈ matchResults (contract (ruleSpace [takeAll]))
    (contract (runPattern (ruleSpace []) (atomAt 0 coin)))
  rw [contract_ruleSpace]
  refine (mem_matchResults_ruleSpace takeAll_admitted.1).mpr
    ⟨takeAll, List.mem_singleton.mpr rfl,
      [(metaName 0, contract (runPattern (ruleSpace []) (atomAt 0 coin)))], ?_, ?_⟩
  · show _ ∈ matchPattern (asRule (atomAt 0 (.var 0))) _
    rw [atomAt_freeVariable, asRule_variableAtom]
    simp [matchPattern]
  · show atomAt 0 (.con "u") = applyBindings _ (ruleSide (.con "u"))
    rw [ruleSide_con, applyBindings_symbolAtom]
    rfl

/-- **Under the evaluator of located atoms the atom of `choose heads tails`
in the empty space has no transition.** -/
theorem emptySpace_coin_normal (target : Contexts.Term located AtomsReduce.closedAtom) :
    ¬ TermStep locatedEvaluator located (runAtom [] 0 coin) target := by
  intro step
  obtain ⟨next, sourceStep, -⟩ := runAtom_termStep_inv (theory := Theory.empty)
    noRules_admitted.1 noRules_admitted.2 (fun _ member => absurd member List.not_mem_nil) step
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

#print axioms located?_app_apart
#print axioms spelled_under_stepAt
#print axioms pair_stepAt
#print axioms pair_related
#print axioms pair_termStep_function
#print axioms pair_termStep_inv
#print axioms mixedCoins_function_steps
#print axioms mixedCoins_argument_still
#print axioms mixedCoins_argument_not_by_function_rules
#print axioms matching_foreign_step
#print axioms emptySpace_coin_normal

end Mettapedia.Logic.HostingStyles.LocatedAtoms
