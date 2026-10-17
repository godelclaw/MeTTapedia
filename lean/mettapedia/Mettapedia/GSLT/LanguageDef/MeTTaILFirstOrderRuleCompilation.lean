import Mettapedia.GSLT.LanguageDef.MeTTaILPatternPlan
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.Syntax.CanonicalRelationQueryEvents

/-!
# First-order rule plans for MeTTaIL

This module compiles the first-order fragment of MeTTaIL rewrite rows to an
independent, inspectable plan.  Variables, rigid bound occurrences, and
ordered applications are retained; binders, explicit substitutions, and
collections are rejected rather than silently delegated to a different
matcher.

The plan interpreter is proved equal to the ordinary syntactic matcher,
source-bound relation-premise evaluator, and right-hand-side instantiator.
Unsupported premise forms reject compilation.  This makes the plan suitable
as the next input to a StructuredC lowering without turning a family tag, an
arbitrary premise callback, or a handwritten case number into semantic
authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep

/-! ## Independent pattern plans -/

mutual
  /-- Compile one pattern, rejecting syntax outside the first-order fragment. -/
  def compilePattern? : Pattern -> Option PatternPlan
    | .fvar name => some (.metavariable name)
    | .bvar index => some (.bound index)
    | .apply constructor arguments => do
        let compiled <- compilePatterns? arguments
        pure (.application constructor compiled)
    | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ | .collection _ _ _ =>
        none

  /-- Compile an ordered pattern row without dropping or reordering entries. -/
  def compilePatterns? : List Pattern -> Option (List PatternPlan)
    | [] => some []
    | pattern :: patterns => do
        let compiled <- compilePattern? pattern
        let tail <- compilePatterns? patterns
        pure (compiled :: tail)
end

/- The first-order compiler and the generic matcher-reconstruction theorem
admit exactly the same pattern fragment. This concerns syntax admission, not
typing or the semantic support of a compiled value. -/
mutual
  theorem compilePattern?_isSome_eq_isMatchCorrectAux (pattern : Pattern) :
      (compilePattern? pattern).isSome = isMatchCorrectAux pattern := by
    cases pattern with
    | fvar _ => rfl
    | bvar _ => rfl
    | apply constructor arguments =>
        have ih := compilePatterns?_isSome_eq_isMatchCorrectListAux arguments
        cases h : compilePatterns? arguments with
        | none => simpa [compilePattern?, isMatchCorrectAux, h] using ih
        | some compiled => simpa [compilePattern?, isMatchCorrectAux, h] using ih
    | lambda _ _ => rfl
    | multiLambda _ _ _ => rfl
    | subst _ _ => rfl
    | collection _ _ _ => rfl
  termination_by sizeOf pattern
  decreasing_by all_goals (simp_all only [Pattern.apply.sizeOf_spec]; omega)

  theorem compilePatterns?_isSome_eq_isMatchCorrectListAux
      (patterns : List Pattern) :
      (compilePatterns? patterns).isSome = isMatchCorrectListAux patterns := by
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        have head := compilePattern?_isSome_eq_isMatchCorrectAux pattern
        have tail := compilePatterns?_isSome_eq_isMatchCorrectListAux patterns
        cases hhead : compilePattern? pattern with
        | none =>
            have headFalse : isMatchCorrectAux pattern = false := by
              simpa [hhead] using head.symm
            simp [compilePatterns?, isMatchCorrectListAux, hhead, headFalse]
        | some compiled =>
            have headTrue : isMatchCorrectAux pattern = true := by
              simpa [hhead] using head.symm
            cases htail : compilePatterns? patterns with
            | none =>
                have tailFalse : isMatchCorrectListAux patterns = false := by
                  simpa [htail] using tail.symm
                simp [compilePatterns?, isMatchCorrectListAux, hhead, htail,
                  headTrue, tailFalse]
            | some compiledTail =>
                have tailTrue : isMatchCorrectListAux patterns = true := by
                  simpa [htail] using tail.symm
                simp [compilePatterns?, isMatchCorrectListAux, hhead, htail,
                  headTrue, tailTrue]
  termination_by sizeOf patterns
  decreasing_by all_goals (simp_all only [List.cons.sizeOf_spec]; omega)
end

mutual
  /-- Successful compilation retains the exact source pattern. -/
  theorem erase_of_compilePattern?
      (source : Pattern) (compiled : PatternPlan)
      (accepted : compilePattern? source = some compiled) :
      compiled.erase = source := by
    cases source with
    | fvar name =>
        simp [compilePattern?] at accepted
        subst compiled
        rfl
    | bvar index =>
        simp [compilePattern?] at accepted
        subst compiled
        rfl
    | apply constructor arguments =>
        simp only [compilePattern?, Option.bind_eq_bind] at accepted
        cases argumentsCompiled : compilePatterns? arguments with
        | none => simp [argumentsCompiled] at accepted
        | some plans =>
            simp [argumentsCompiled] at accepted
            subst compiled
            simp [PatternPlan.erase,
              erasePatterns_of_compilePatterns? arguments plans
                argumentsCompiled]
    | lambda name body => simp [compilePattern?] at accepted
    | multiLambda arity names body => simp [compilePattern?] at accepted
    | subst body replacement => simp [compilePattern?] at accepted
    | collection kind elements rest => simp [compilePattern?] at accepted

  /-- Successful row compilation retains every source occurrence in order. -/
  theorem erasePatterns_of_compilePatterns?
      (sources : List Pattern) (compiled : List PatternPlan)
      (accepted : compilePatterns? sources = some compiled) :
      erasePatterns compiled = sources := by
    cases sources with
    | nil =>
        simp [compilePatterns?] at accepted
        subst compiled
        rfl
    | cons source sources =>
        simp only [compilePatterns?, Option.bind_eq_bind] at accepted
        cases headCompiled : compilePattern? source with
        | none => simp [headCompiled] at accepted
        | some head =>
            cases tailCompiled : compilePatterns? sources with
            | none => simp [headCompiled, tailCompiled] at accepted
            | some tail =>
                simp [headCompiled, tailCompiled] at accepted
                subst compiled
                simp [erasePatterns,
                  erase_of_compilePattern? source head headCompiled,
                  erasePatterns_of_compilePatterns? sources tail tailCompiled]
end

/-! ## Exact plan interpretation -/

mutual
  /-- Execute a compiled plan with the same observable binding carrier as the
  canonical MeTTaIL matcher. -/
  def PatternPlan.run : PatternPlan -> Pattern -> List Bindings
    | .metavariable name, subject => [[(name, subject)]]
    | .bound expected, .bvar actual =>
        if expected == actual then [[]] else []
    | .application expected plans, .apply actual subjects =>
        if expected == actual && plans.length == subjects.length then
          runPlans plans subjects
        else
          []
    | _, _ => []

  /-- Execute an ordered plan row, merging repeated variables exactly as the
  canonical matcher does. -/
  def runPlans : List PatternPlan -> List Pattern -> List Bindings
    | [], [] => [[]]
    | plan :: plans, subject :: subjects =>
        (plan.run subject).flatMap fun headBindings =>
          (runPlans plans subjects).filterMap fun tailBindings =>
            mergeBindings headBindings tailBindings
    | _, _ => []
end

mutual
  /-- Plan execution is extensionally the canonical matcher on the erased
  pattern. -/
  theorem run_eq_matchPattern (plan : PatternPlan) (subject : Pattern) :
      plan.run subject = matchPattern plan.erase subject := by
    cases plan with
    | metavariable name =>
        simp [PatternPlan.run, PatternPlan.erase, matchPattern]
    | bound index =>
        cases subject <;> simp [PatternPlan.run, PatternPlan.erase,
          matchPattern]
    | application constructor plans =>
        cases subject with
        | apply actual subjects =>
            simp only [PatternPlan.run, PatternPlan.erase, matchPattern,
              erasePatterns_length]
            by_cases eligible : constructor == actual &&
                plans.length == subjects.length
            · simpa [eligible] using runPlans_eq_matchArgs plans subjects
            · simp [eligible]
        | _ => simp [PatternPlan.run, PatternPlan.erase, matchPattern]
  termination_by 2 * plan.work
  decreasing_by
    simp [PatternPlan.work]
    omega

  /-- List companion to `run_eq_matchPattern`. -/
  theorem runPlans_eq_matchArgs
      (plans : List PatternPlan) (subjects : List Pattern) :
      runPlans plans subjects = matchArgs (erasePatterns plans) subjects := by
    cases plans with
    | nil => cases subjects <;> simp [runPlans, erasePatterns, matchArgs]
    | cons plan plans =>
        cases subjects with
        | nil => simp [runPlans, erasePatterns, matchArgs]
        | cons subject subjects =>
            simp only [runPlans, erasePatterns, matchArgs]
            rw [run_eq_matchPattern, runPlans_eq_matchArgs]
  termination_by 2 * patternPlansWork plans + 1
  decreasing_by
    all_goals
      have positive := PatternPlan.work_pos plan
      rw [patternPlansWork]
      omega
end

/-- A successfully compiled matcher has exactly the source match result. -/
theorem run_compilePattern?
    (source subject : Pattern) (compiled : PatternPlan)
    (accepted : compilePattern? source = some compiled) :
    compiled.run subject = matchPattern source subject := by
  rw [run_eq_matchPattern,
    erase_of_compilePattern? source compiled accepted]

/-! ## Right-hand-side construction -/

/-- Instantiate a first-order plan from canonical bindings.  Missing bindings
remain visible variables, matching the existing gradual `applyBindings`
operation. -/
def PatternPlan.instantiate (bindings : Bindings) : PatternPlan -> Pattern
  | .metavariable name =>
      match bindings.find? (fun entry => entry.1 == name) with
      | some (_, value) => value
      | none => .fvar name
  | .bound index => .bvar index
  | .application constructor arguments =>
      .apply constructor (arguments.map (instantiate bindings))

mutual
  /-- Plan instantiation is exactly canonical binding application on erasure. -/
  theorem instantiate_eq_applyBindings
      (bindings : Bindings) (plan : PatternPlan) :
      plan.instantiate bindings = applyBindings bindings plan.erase := by
    cases plan with
    | metavariable name =>
        unfold PatternPlan.instantiate PatternPlan.erase applyBindings
        rfl
    | bound index =>
        unfold PatternPlan.instantiate PatternPlan.erase applyBindings
        rfl
    | application constructor arguments =>
        simpa [PatternPlan.instantiate, PatternPlan.erase, applyBindings] using
          congrArg (Pattern.apply constructor)
            (instantiateList_eq_applyBindings bindings arguments)
  termination_by 2 * plan.work
  decreasing_by
    simp [PatternPlan.work]
    omega

  /-- Ordered-list companion to `instantiate_eq_applyBindings`. -/
  theorem instantiateList_eq_applyBindings
      (bindings : Bindings) (plans : List PatternPlan) :
      plans.map (PatternPlan.instantiate bindings) =
        (erasePatterns plans).map (applyBindings bindings) := by
    cases plans with
    | nil => rfl
    | cons plan plans =>
        change plan.instantiate bindings ::
            plans.map (PatternPlan.instantiate bindings) =
          applyBindings bindings plan.erase ::
            (erasePatterns plans).map (applyBindings bindings)
        rw [instantiate_eq_applyBindings, instantiateList_eq_applyBindings]
  termination_by 2 * patternPlansWork plans + 1
  decreasing_by
    all_goals
      have positive := PatternPlan.work_pos plan
      rw [patternPlansWork]
      omega
end

/-! ## Source-bound relation-premise plans -/

mutual
  /-- An erased plan recompiles to itself, without changing its syntax. -/
  theorem compilePattern?_erase (plan : PatternPlan) :
      compilePattern? plan.erase = some plan := by
    cases plan with
    | metavariable name => rfl
    | bound index => rfl
    | application constructor arguments =>
        simp [PatternPlan.erase, compilePattern?, compilePatterns?_erase arguments]
  termination_by 2 * plan.work
  decreasing_by simp [PatternPlan.work]; omega

  /-- Recompilation retains every ordered erased child occurrence. -/
  theorem compilePatterns?_erase (plans : List PatternPlan) :
      compilePatterns? (erasePatterns plans) = some plans := by
    cases plans with
    | nil => rfl
    | cons plan plans =>
        simp [erasePatterns, compilePatterns?, compilePattern?_erase plan, compilePatterns?_erase plans]
  termination_by 2 * patternPlansWork plans + 1
  decreasing_by
    all_goals
      have positive := PatternPlan.work_pos plan
      rw [patternPlansWork]
      omega
end

/-- A positive relation query with ordered first-order argument schemas.
Binder and collection syntax cannot cross the residual primitive boundary. -/
structure PremisePlan where
  relation : String
  arguments : List PatternPlan
deriving Repr

/-- The arguments as schema variable names, when every argument is one. -/
def PremisePlan.argumentNames? (plan : PremisePlan) : Option (List String) :=
  plan.arguments.mapM fun
    | .metavariable name => some name
    | _ => none

/-- Compile an ordered row of ordinary schema variables. -/
def compileArgumentNames? : List Pattern -> Option (List String)
  | [] => some []
  | .fvar name :: arguments => do
      let tail <- compileArgumentNames? arguments
      pure (name :: tail)
  | _ => none

/-- Compile exactly the source-bound relation-query fragment. -/
def compilePremise? : Premise -> Option PremisePlan
  | .relationQuery relation arguments => do
      let plans <- compilePatterns? arguments
      pure { relation, arguments := plans }
  | .freshness _ | .congruence _ _ | .scopedStep _ | .forAll _ _ _ => none

/-- Compile a complete authored premise row without dropping or reordering an
occurrence. -/
def compilePremises? : List Premise -> Option (List PremisePlan)
  | [] => some []
  | premise :: premises => do
      let plan <- compilePremise? premise
      let plans <- compilePremises? premises
      pure (plan :: plans)

/-- Reconstruct the complete authored premise represented by a plan. -/
def PremisePlan.erase (plan : PremisePlan) : Premise :=
  .relationQuery plan.relation (erasePatterns plan.arguments)

/-- Reconstruct an ordered authored premise row. -/
def erasePremisePlans (plans : List PremisePlan) : List Premise :=
  plans.map PremisePlan.erase

/-- Ordered variable schemas compile back to their exact authored names. -/
theorem compileArgumentNames?_map_fvar (names : List String) :
    compileArgumentNames? (names.map Pattern.fvar) = some names := by
  induction names with
  | nil => rfl
  | cons name names ih => simp only [List.map_cons, compileArgumentNames?, ih]; rfl

/-- Premise readback is exact; no source query metadata is discarded. -/
theorem compilePremise?_erase (plan : PremisePlan) :
    compilePremise? plan.erase = some plan := by
  cases plan with
  | mk relation arguments =>
      simp only [PremisePlan.erase, compilePremise?, compilePatterns?_erase]
      rfl

/-- Readback retains every ordered premise occurrence, including duplicates. -/
theorem compilePremises?_erase (plans : List PremisePlan) :
    compilePremises? (erasePremisePlans plans) = some plans := by
  induction plans with
  | nil => rfl
  | cons plan plans ih =>
      simp only [erasePremisePlans, List.map_cons, compilePremises?, compilePremise?_erase] at *
      rw [ih]
      rfl

theorem compileArgumentNames?_erase
    (sources : List Pattern) (names : List String)
    (accepted : compileArgumentNames? sources = some names) :
    names.map Pattern.fvar = sources := by
  induction sources generalizing names with
  | nil =>
      simp [compileArgumentNames?] at accepted
      subst names
      rfl
  | cons source sources inductionHypothesis =>
      cases source with
      | fvar name =>
          simp only [compileArgumentNames?, Option.bind_eq_bind] at accepted
          cases tailAccepted : compileArgumentNames? sources with
          | none => simp [tailAccepted] at accepted
          | some tail =>
              simp [tailAccepted] at accepted
              subst names
              simp [inductionHypothesis tail tailAccepted]
      | _ => simp [compileArgumentNames?] at accepted

/-- Successful premise compilation retains its complete source syntax. -/
theorem erase_of_compilePremise?
    (source : Premise) (compiled : PremisePlan)
    (accepted : compilePremise? source = some compiled) :
    compiled.erase = source := by
  cases source with
  | freshness condition => simp [compilePremise?] at accepted
  | congruence left right => simp [compilePremise?] at accepted
  | scopedStep step => simp [compilePremise?] at accepted
  | forAll collection parameter body => simp [compilePremise?] at accepted
  | relationQuery relation arguments =>
      simp only [compilePremise?, Option.bind_eq_bind] at accepted
      cases namesAccepted : compilePatterns? arguments with
      | none => simp [namesAccepted] at accepted
      | some names =>
          simp [namesAccepted] at accepted
          subst compiled
          simp [PremisePlan.erase,
            erasePatterns_of_compilePatterns? arguments names namesAccepted]

/-- Successful row compilation retains premise order and multiplicity. -/
theorem erasePremisePlans_of_compilePremises?
    (source : List Premise) (compiled : List PremisePlan)
    (accepted : compilePremises? source = some compiled) :
    erasePremisePlans compiled = source := by
  induction source generalizing compiled with
  | nil =>
      simp [compilePremises?] at accepted
      subst compiled
      rfl
  | cons premise premises inductionHypothesis =>
      simp only [compilePremises?, Option.bind_eq_bind] at accepted
      cases headAccepted : compilePremise? premise with
      | none => simp [headAccepted] at accepted
      | some plan =>
          cases tailAccepted : compilePremises? premises with
          | none => simp [headAccepted, tailAccepted] at accepted
          | some plans =>
              simp [headAccepted, tailAccepted] at accepted
              subst compiled
              change plan.erase :: erasePremisePlans plans =
                premise :: premises
              rw [erase_of_compilePremise? premise plan headAccepted,
                inductionHypothesis plans tailAccepted]

/-- One variable-only relation argument has at most one binding extension.
An already captured value is compared literally; variables inside that value
do not become new schema variables. -/
def relationArgument? (seed : Bindings) (name : String) (value : Pattern) : Option Bindings :=
  match seed.lookup name with
  | some prior => if prior = value then some [] else none
  | none => some [(name, value)]

theorem relationArgument?_exact (seed : Bindings) (name : String) (value : Pattern) :
    (relationArgument? seed name value).toList =
      matchRelationArgument seed (.fvar name) value := by
  unfold relationArgument? matchRelationArgument
  cases found : seed.lookup name with
  | none => simp [found]
  | some prior => by_cases same : prior = value <;> simp [found, same]

/-- Deterministic residual matching for the admitted variable argument row.
The result remains an extension relative to the seed, as in the canonical
relation matcher; merge order is retained at both continuation boundaries. -/
def relationArguments? (seed : Bindings) : List String → List Pattern → Option Bindings
  | [], [] => some []
  | name :: names, value :: values => do
      let head ← relationArgument? seed name value
      let extended ← mergeBindings seed head
      let tail ← relationArguments? extended names values
      mergeBindings head tail
  | _, _ => none

theorem relationArguments?_exact (seed : Bindings) (names : List String) (values : List Pattern) :
    (relationArguments? seed names values).toList =
      matchRelationArgs seed (names.map Pattern.fvar) values := by
  induction names generalizing seed values with
  | nil => cases values <;> simp [relationArguments?, matchRelationArgs]
  | cons name names ih =>
      cases values with
      | nil => simp [relationArguments?, matchRelationArgs]
      | cons value values =>
          simp only [relationArguments?, Option.bind_eq_bind, List.map_cons, matchRelationArgs,
            ← relationArgument?_exact]
          cases head : relationArgument? seed name value with
          | none => simp
          | some headBindings =>
              simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, Option.bind_some]
              cases merged : mergeBindings seed headBindings with
              | none => simp
              | some extended =>
                  simp only [Option.bind_some]
                  rw [← ih extended values]
                  cases tail : relationArguments? extended names values <;> simp
                  rename_i tailBindings
                  cases final : mergeBindings headBindings tailBindings <;> simp [final]

mutual
  /-- Deterministic structural matching of the admitted first-order schema. -/
  def PatternPlan.match? : PatternPlan → Pattern → Option Bindings
    | .metavariable name, value => some [(name, value)]
    | .bound expected, .bvar actual => if expected == actual then some [] else none
    | .application expected plans, .apply actual values =>
        if expected == actual && plans.length == values.length then
          matchPlans? plans values
        else none
    | _, _ => none

  def matchPlans? : List PatternPlan → List Pattern → Option Bindings
    | [], [] => some []
    | plan :: plans, value :: values => do
        let head ← plan.match? value
        let tail ← matchPlans? plans values
        mergeBindings head tail
    | _, _ => none
end

mutual
  theorem PatternPlan.match?_toList (plan : PatternPlan) (value : Pattern) :
      (plan.match? value).toList = plan.run value := by
    cases plan with
    | metavariable name => rfl
    | bound index =>
        cases value <;> simp [PatternPlan.match?, PatternPlan.run]
        split <;> rfl
    | application constructor plans =>
        cases value with
        | apply actual values =>
            simp only [PatternPlan.match?, PatternPlan.run]
            by_cases eligible : constructor == actual && plans.length == values.length
            · simp only [eligible, ↓reduceIte]
              exact matchPlans?_toList plans values
            · simp [eligible]
        | _ => rfl
  termination_by 2 * plan.work
  decreasing_by simp [PatternPlan.work]; omega

  theorem matchPlans?_toList (plans : List PatternPlan) (values : List Pattern) :
      (matchPlans? plans values).toList = runPlans plans values := by
    cases plans with
    | nil => cases values <;> rfl
    | cons plan plans =>
        cases values with
        | nil => rfl
        | cons value values =>
            simp only [matchPlans?, runPlans, ← plan.match?_toList,
              ← matchPlans?_toList plans values]
            cases head : plan.match? value <;> simp
            rename_i headBindings
            cases tail : matchPlans? plans values <;> simp
            rename_i tailBindings
            cases merged : mergeBindings headBindings tailBindings <;> simp [merged]
  termination_by 2 * patternPlansWork plans + 1
  decreasing_by
    all_goals
      have positive := PatternPlan.work_pos plan
      rw [patternPlansWork]
      omega
end

/-- Top-level variables respect previously captured literal values.  A
constructed schema is matched before merging with the seed. -/
def relationPatternArgument? (seed : Bindings) (plan : PatternPlan)
    (value : Pattern) : Option Bindings :=
  match plan with
  | .metavariable name => relationArgument? seed name value
  | .bound index => (PatternPlan.bound index).match? value
  | .application constructor plans => (PatternPlan.application constructor plans).match? value

theorem relationPatternArgument?_exact (seed : Bindings) (plan : PatternPlan)
    (value : Pattern) :
    (relationPatternArgument? seed plan value).toList =
      matchRelationArgument seed plan.erase value := by
  cases plan with
  | metavariable name => exact relationArgument?_exact seed name value
  | bound index =>
      rw [relationPatternArgument?, PatternPlan.match?_toList, run_eq_matchPattern]
      rfl
  | application constructor plans =>
      rw [relationPatternArgument?, PatternPlan.match?_toList, run_eq_matchPattern]
      rfl

def relationPatternArguments? (seed : Bindings) :
    List PatternPlan → List Pattern → Option Bindings
  | [], [] => some []
  | plan :: plans, value :: values => do
      let head ← relationPatternArgument? seed plan value
      let extended ← mergeBindings seed head
      let tail ← relationPatternArguments? extended plans values
      mergeBindings head tail
  | _, _ => none

theorem relationPatternArguments?_exact (seed : Bindings)
    (plans : List PatternPlan) (values : List Pattern) :
    (relationPatternArguments? seed plans values).toList =
      matchRelationArgs seed (erasePatterns plans) values := by
  induction plans generalizing seed values with
  | nil => cases values <;> simp [relationPatternArguments?, erasePatterns, matchRelationArgs]
  | cons plan plans ih =>
      cases values with
      | nil => simp [relationPatternArguments?, erasePatterns, matchRelationArgs]
      | cons value values =>
          simp only [relationPatternArguments?, erasePatterns, Option.bind_eq_bind,
            matchRelationArgs, ← relationPatternArgument?_exact]
          cases head : relationPatternArgument? seed plan value with
          | none => simp
          | some headBindings =>
              simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, Option.bind_some]
              cases merged : mergeBindings seed headBindings with
              | none => simp
              | some extended =>
                  simp only [Option.bind_some]
                  rw [← ih extended values]
                  cases tail : relationPatternArguments? extended plans values <;> simp
                  rename_i tailBindings
                  cases final : mergeBindings headBindings tailBindings <;> simp [final]

/-- Variable-only query matching is a specialization of the structural
matcher, with the same literal and repeated-variable behavior. -/
theorem relationPatternArguments?_metavariables (seed : Bindings)
    (names : List String) (values : List Pattern) :
    relationPatternArguments? seed (names.map PatternPlan.metavariable) values =
      relationArguments? seed names values := by
  induction names generalizing seed values with
  | nil => cases values <;> rfl
  | cons name names ih =>
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [List.map_cons, relationPatternArguments?, relationPatternArgument?,
            relationArguments?]
          congr 1
          funext head
          congr 1
          funext extended
          rw [ih]

/-- Match one tuple and merge its relative extension through the ordinary
binding boundary. A tuple that conflicts with the seed's first binding is
refused; this operation does not revalidate duplicate bindings already in the
seed. -/
def PremisePlan.matchTuple? (bindings : Bindings) (plan : PremisePlan)
    (values : List Pattern) : Option Bindings := do
  let extended ← relationPatternArguments? bindings plan.arguments values
  mergeBindings bindings extended

theorem PremisePlan.matchTuple?_exact (bindings : Bindings) (plan : PremisePlan)
    (values : List Pattern) :
    (plan.matchTuple? bindings values).toList =
      (matchRelationArgs bindings (erasePatterns plan.arguments) values).filterMap
        (mergeBindings bindings) := by
  rw [← relationPatternArguments?_exact]
  unfold PremisePlan.matchTuple?
  cases matched : relationPatternArguments? bindings plan.arguments values with
  | none => simp
  | some extended =>
      simp only [Option.bind_eq_bind, Option.bind_some, Option.toList_some]
      cases merged : mergeBindings bindings extended <;> simp [merged]

theorem PremisePlan.matchTuples_exact (bindings : Bindings) (plan : PremisePlan)
    (tuples : List (List Pattern)) :
    tuples.filterMap (plan.matchTuple? bindings) =
      tuples.flatMap (fun tuple =>
        (matchRelationArgs bindings (erasePatterns plan.arguments) tuple).filterMap
          (mergeBindings bindings)) := by
  induction tuples with
  | nil => rfl
  | cons tuple tuples ih =>
      rw [List.flatMap_cons, ← plan.matchTuple?_exact, ← ih]
      cases matched : plan.matchTuple? bindings tuple <;> simp [matched]

/-- Execute one residual relation query.  The only semantic primitive is the
declared finite relation table; matching, merge behavior, builtins, and output
bindings remain fixed by the shared MeTTaIL relation-query semantics. -/
def PremisePlan.run (relations : RelationEnv) (language : LanguageDef)
    (bindings : Bindings) (plan : PremisePlan) : List Bindings :=
  let arguments := (erasePatterns plan.arguments).map (applyBindings bindings)
  let tuples := builtinRelationTuples language plan.relation arguments ++
    relations.tuples plan.relation arguments
  tuples.filterMap (plan.matchTuple? bindings)

/-- Execute source-bound relation premises in authored order. -/
def runPremisePlans (relations : RelationEnv) (language : LanguageDef) :
    List PremisePlan -> Bindings -> List Bindings
  | [], bindings => [bindings]
  | plan :: plans, bindings =>
      (plan.run relations language bindings).flatMap
        (runPremisePlans relations language plans)

/-! ## Checked variable-only specialization -/

/-- The variable-only query data executed by older authored source clients.
Its narrower syntax remains explicit beside the general first-order plan. -/
structure VariablePremisePlan where
  relation : String
  arguments : List String
deriving DecidableEq, Repr

def VariablePremisePlan.toPlan (plan : VariablePremisePlan) : PremisePlan :=
  ⟨plan.relation, plan.arguments.map PatternPlan.metavariable⟩

def VariablePremisePlan.erase (plan : VariablePremisePlan) : Premise :=
  .relationQuery plan.relation (plan.arguments.map Pattern.fvar)

def VariablePremisePlan.run (relations : RelationEnv) (language : LanguageDef)
    (bindings : Bindings) (plan : VariablePremisePlan) : List Bindings :=
  let arguments := (plan.arguments.map Pattern.fvar).map (applyBindings bindings)
  let tuples := builtinRelationTuples language plan.relation arguments ++
    relations.tuples plan.relation arguments
  tuples.filterMap fun tuple => do
    let extension ← relationArguments? bindings plan.arguments tuple
    mergeBindings bindings extension

theorem VariablePremisePlan.toPlan_erase (plan : VariablePremisePlan) :
    plan.toPlan.erase = plan.erase := by
  simp [VariablePremisePlan.toPlan, VariablePremisePlan.erase, PremisePlan.erase,
    erasePatterns_eq_map, List.map_map, PatternPlan.erase, Function.comp_def]

theorem VariablePremisePlan.toPlan_run (relations : RelationEnv) (language : LanguageDef)
    (bindings : Bindings) (plan : VariablePremisePlan) :
    plan.toPlan.run relations language bindings = plan.run relations language bindings := by
  have matcher : PremisePlan.matchTuple? bindings plan.toPlan =
      (fun tuple => do
        let extension ← relationArguments? bindings plan.arguments tuple
        mergeBindings bindings extension) := by
    funext tuple
    simp [VariablePremisePlan.toPlan, PremisePlan.matchTuple?,
      relationPatternArguments?_metavariables]
  simp only [VariablePremisePlan.run, PremisePlan.run]
  rw [matcher]
  simp [VariablePremisePlan.toPlan, erasePatterns_eq_map, List.map_map,
    PatternPlan.erase, Function.comp_def]

def compileVariablePremise? : Premise → Option VariablePremisePlan
  | .relationQuery relation arguments => do
      let names ← compileArgumentNames? arguments
      pure ⟨relation, names⟩
  | _ => none

def compileVariablePremises? : List Premise → Option (List VariablePremisePlan)
  | [] => some []
  | premise :: premises => do
      let head ← compileVariablePremise? premise
      let tail ← compileVariablePremises? premises
      pure (head :: tail)

theorem compileVariablePremise?_erase (plan : VariablePremisePlan) :
    compileVariablePremise? plan.erase = some plan := by
  cases plan
  simp [VariablePremisePlan.erase, compileVariablePremise?, compileArgumentNames?_map_fvar]

theorem erase_of_compileVariablePremise? (source : Premise) (plan : VariablePremisePlan)
    (accepted : compileVariablePremise? source = some plan) : plan.erase = source := by
  cases source with
  | relationQuery relation arguments =>
      simp only [compileVariablePremise?, Option.bind_eq_bind] at accepted
      cases namesAccepted : compileArgumentNames? arguments with
      | none => simp [namesAccepted] at accepted
      | some names =>
          simp [namesAccepted] at accepted
          subst plan
          simp [VariablePremisePlan.erase,
            compileArgumentNames?_erase arguments names namesAccepted]
  | _ => simp [compileVariablePremise?] at accepted

/-- Read back names only when every admitted argument is a top-level variable. -/
def argumentNamesOfPlans? : List PatternPlan → Option (List String)
  | [] => some []
  | .metavariable name :: plans => do
      let names ← argumentNamesOfPlans? plans
      pure (name :: names)
  | _ => none

theorem argumentNamesOfPlans?_metavariables (names : List String) :
    argumentNamesOfPlans? (names.map PatternPlan.metavariable) = some names := by
  induction names with
  | nil => rfl
  | cons name names ih => simp [argumentNamesOfPlans?, ih]

theorem argumentNamesOfPlans?_exact (plans : List PatternPlan) (names : List String)
    (accepted : argumentNamesOfPlans? plans = some names) :
    names.map PatternPlan.metavariable = plans := by
  induction plans generalizing names with
  | nil => simp [argumentNamesOfPlans?] at accepted; subst names; rfl
  | cons plan plans ih =>
      cases plan with
      | metavariable name =>
          cases tailAccepted : argumentNamesOfPlans? plans with
          | none => simp [argumentNamesOfPlans?, tailAccepted] at accepted
          | some tail =>
              simp [argumentNamesOfPlans?, tailAccepted] at accepted
              subst names
              simp [ih tail tailAccepted]
      | _ => simp [argumentNamesOfPlans?] at accepted

/-- Older source executors must earn this checked specialization before
assuming that the query arguments are ordinary names. -/
def PremisePlan.toVariable? (plan : PremisePlan) : Option VariablePremisePlan := do
  let names ← argumentNamesOfPlans? plan.arguments
  pure ⟨plan.relation, names⟩

theorem PremisePlan.toVariable?_exact (plan : PremisePlan) (specialized : VariablePremisePlan)
    (accepted : plan.toVariable? = some specialized) : specialized.toPlan = plan := by
  cases plan with
  | mk relation arguments =>
      cases namesAccepted : argumentNamesOfPlans? arguments with
      | none => simp [PremisePlan.toVariable?, namesAccepted] at accepted
      | some names =>
          simp [PremisePlan.toVariable?, namesAccepted] at accepted
          subst specialized
          simp [VariablePremisePlan.toPlan,
            argumentNamesOfPlans?_exact arguments names namesAccepted]

theorem PremisePlan.toVariable?_toPlan (specialized : VariablePremisePlan) :
    specialized.toPlan.toVariable? = some specialized := by
  cases specialized
  simp [VariablePremisePlan.toPlan, PremisePlan.toVariable?,
    argumentNamesOfPlans?_metavariables]

theorem compileVariablePremise?_general (source : Premise) (plan : VariablePremisePlan)
    (accepted : compileVariablePremise? source = some plan) :
    compilePremise? source = some plan.toPlan := by
  have erased := erase_of_compileVariablePremise? source plan accepted
  rw [← erased, ← plan.toPlan_erase]
  exact compilePremise?_erase plan.toPlan

theorem compileVariablePremises?_general (source : List Premise)
    (plans : List VariablePremisePlan) (accepted : compileVariablePremises? source = some plans) :
    compilePremises? source = some (plans.map VariablePremisePlan.toPlan) := by
  induction source generalizing plans with
  | nil => simp [compileVariablePremises?] at accepted; subst plans; rfl
  | cons premise premises ih =>
      cases headAccepted : compileVariablePremise? premise with
      | none => simp [compileVariablePremises?, headAccepted] at accepted
      | some head =>
          cases tailAccepted : compileVariablePremises? premises with
          | none => simp [compileVariablePremises?, headAccepted, tailAccepted] at accepted
          | some tail =>
              simp [compileVariablePremises?, headAccepted, tailAccepted] at accepted
              subst plans
              simp [compilePremises?, compileVariablePremise?_general premise head headAccepted,
                ih tail tailAccepted]

/-- All-or-none checked specialization of the ordered query list. -/
def premisePlansToVariables? : List PremisePlan → Option (List VariablePremisePlan)
  | [] => some []
  | query :: queries => do
      let head ← query.toVariable?
      let tail ← premisePlansToVariables? queries
      pure (head :: tail)

theorem premisePlansToVariables?_exact (plans : List PremisePlan)
    (specialized : List VariablePremisePlan)
    (accepted : premisePlansToVariables? plans = some specialized) :
    specialized.map VariablePremisePlan.toPlan = plans := by
  induction plans generalizing specialized with
  | nil => simp [premisePlansToVariables?] at accepted; subst specialized; rfl
  | cons plan plans ih =>
      cases headAccepted : plan.toVariable? with
      | none => simp [premisePlansToVariables?, headAccepted] at accepted
      | some head =>
          cases tailAccepted : premisePlansToVariables? plans with
          | none => simp [premisePlansToVariables?, headAccepted, tailAccepted] at accepted
          | some tail =>
              simp [premisePlansToVariables?, headAccepted, tailAccepted] at accepted
              subst specialized
              simp [PremisePlan.toVariable?_exact plan head headAccepted, ih tail tailAccepted]

theorem premisePlansToVariables?_toPlan (plans : List VariablePremisePlan) :
    premisePlansToVariables? (plans.map VariablePremisePlan.toPlan) = some plans := by
  induction plans with
  | nil => rfl
  | cons plan plans ih =>
      simp [premisePlansToVariables?, PremisePlan.toVariable?_toPlan, ih]

#print axioms PatternPlan.match?_toList
#print axioms matchPlans?_toList
#print axioms relationPatternArgument?_exact
#print axioms relationPatternArguments?_exact
#print axioms relationPatternArguments?_metavariables
#print axioms VariablePremisePlan.toPlan_erase
#print axioms VariablePremisePlan.toPlan_run
#print axioms compileVariablePremise?_erase
#print axioms erase_of_compileVariablePremise?
#print axioms argumentNamesOfPlans?_metavariables
#print axioms argumentNamesOfPlans?_exact
#print axioms PremisePlan.toVariable?_exact
#print axioms PremisePlan.toVariable?_toPlan
#print axioms compileVariablePremise?_general
#print axioms compileVariablePremises?_general
#print axioms premisePlansToVariables?_exact
#print axioms premisePlansToVariables?_toPlan

/-- One residual query has exactly the ordinary non-contextual premise
meaning of its erased source. -/
theorem PremisePlan.run_eq_premiseStepUsing
    (relations : RelationEnv) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern)
    (bindings : Bindings) (plan : PremisePlan) :
    plan.run relations language bindings =
      premiseStepUsing (engineBasePremises relations) language recursiveStep
        bindings plan.erase := by
  change plan.run relations language bindings =
    relationQueryStep relations language bindings plan.relation
      (erasePatterns plan.arguments)
  unfold PremisePlan.run relationQueryStep
  exact plan.matchTuples_exact bindings _

/-- The residual ordered query program is exactly the authored premise
interpreter. -/
theorem runPremisePlans_eq_premisesUsing
    (relations : RelationEnv) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern)
    (plans : List PremisePlan) (bindings : Bindings) :
    runPremisePlans relations language plans bindings =
      premisesUsing (engineBasePremises relations) language recursiveStep
        (erasePremisePlans plans) bindings := by
  induction plans generalizing bindings with
  | nil => rfl
  | cons plan plans inductionHypothesis =>
      simp only [runPremisePlans, erasePremisePlans, List.map_cons,
        premisesUsing]
      rw [PremisePlan.run_eq_premiseStepUsing]
      congr 1
      funext nextBindings
      exact inductionHypothesis nextBindings

/-- Admitted relation plans have no recursive or scoped-step premise. This
property is derived from their complete erasure, rather than supplied by a
caller of the executor. -/
theorem noncontextual_erasePremisePlans (plans : List PremisePlan) :
    NoncontextualPremises (erasePremisePlans plans) := by
  induction plans with
  | nil => exact .nil
  | cons plan plans ih => exact .relationQuery ih

/-- The ordered residual fold computes the canonical root-premise frontier,
including every duplicate witness contributed by a relation table. -/
theorem runPremisePlans_eq_applyPremisesWithEnv
    (relations : RelationEnv) (language : LanguageDef)
    (plans : List PremisePlan) (bindings : Bindings) :
    runPremisePlans relations language plans bindings =
      applyPremisesWithEnv relations language (erasePremisePlans plans) bindings := by
  rw [runPremisePlans_eq_premisesUsing relations language (fun _ => [])]
  exact premisesUsing_engineBase_zero_eq_applyPremisesWithEnv relations language _ bindings

/-! ## Complete first-order rewrite-row plans -/

/-- An admitted row preserves the authored administrative fields while
replacing both executable patterns by independent first-order plans. -/
structure RulePlan where
  name : String
  typeContext : List (String × TypeExpr)
  premises : List PremisePlan
  left : PatternPlan
  right : PatternPlan
deriving Repr

/-- Compile one rewrite row of the unannotated first-order fragment. -/
def compileRule? (source : RewriteRule) : Option RulePlan := do
  guard source.bindings.isNone
  let left <- compilePattern? source.left
  let premises <- compilePremises? source.premises
  let right <- compilePattern? source.right
  pure
    { name := source.name
      typeContext := source.typeContext
      premises
      left
      right }

/-- The first-order compiler declines scoped binding declarations, which
require the contextual rule interpreter rather than this plan format. -/
theorem compileRule?_annotated_none (source : RewriteRule)
    (spec : RuleBindingSpec) (h : source.bindings = some spec) :
    compileRule? source = none := by
  simp [compileRule?, h]

/-- Reconstruct the complete authored rewrite row represented by a plan. -/
def RulePlan.erase (plan : RulePlan) : RewriteRule :=
  { name := plan.name
    typeContext := plan.typeContext
    premises := erasePremisePlans plan.premises
    left := plan.left.erase
    right := plan.right.erase }

/-- Successful row compilation retains every source field exactly. -/
theorem erase_of_compileRule?
    (source : RewriteRule) (compiled : RulePlan)
    (accepted : compileRule? source = some compiled) :
    compiled.erase = source := by
  have hbindings : source.bindings = none := by
    cases h : source.bindings with
    | none => rfl
    | some spec => simp [compileRule?, h] at accepted
  unfold compileRule? at accepted
  simp only [hbindings] at accepted
  cases leftCompiled : compilePattern? source.left with
  | none => simp [leftCompiled] at accepted
  | some left =>
      cases premisesCompiled : compilePremises? source.premises with
      | none => simp [leftCompiled, premisesCompiled] at accepted
      | some premises =>
          cases rightCompiled : compilePattern? source.right with
          | none =>
              simp [leftCompiled, premisesCompiled, rightCompiled] at accepted
          | some right =>
              simp [leftCompiled, premisesCompiled, rightCompiled] at accepted
              subst compiled
              cases source
              simp [RulePlan.erase,
                erase_of_compilePattern? _ left leftCompiled,
                erasePremisePlans_of_compilePremises? _ premises
                  premisesCompiled,
                erase_of_compilePattern? _ right rightCompiled]
              exact hbindings.symm

mutual
  /-- The admitted fragment has no binder former, so an erased plan is
  binder-free.  This is what makes the compiled instantiator agree with the
  depth-aligned one: with no binder to cross, the alignment shift is zero. -/
  theorem binderFree_erase : ∀ plan : PatternPlan, binderFree plan.erase = true
    | .metavariable _ => rfl
    | .bound _ => rfl
    | .application _ arguments => by
        simp only [PatternPlan.erase, binderFree]
        exact binderFreeList_erasePatterns arguments

  /-- Ordered-list companion to `binderFree_erase`. -/
  theorem binderFreeList_erasePatterns :
      ∀ plans : List PatternPlan, binderFreeList (erasePatterns plans) = true
    | [] => rfl
    | plan :: plans => by
        simp only [erasePatterns, binderFreeList, Bool.and_eq_true]
        exact ⟨binderFree_erase plan, binderFreeList_erasePatterns plans⟩
end

/-- Interpret a plan using one declared relation environment.  Matching,
ordered premise control, and contractum construction all come from the plan;
the relation table is the sole semantic primitive. -/
def RulePlan.run
    (relations : RelationEnv) (language : LanguageDef)
    (plan : RulePlan) (subject : Pattern) : List Pattern :=
  (plan.left.run subject).flatMap fun initialBindings =>
    (runPremisePlans relations language plan.premises initialBindings).map
      fun finalBindings => plan.right.instantiate finalBindings

/-- Plan interpretation agrees exactly with syntactic matching, authored
premise evaluation, and canonical RHS binding application. -/
theorem run_eq_syntactic
    (relations : RelationEnv) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern)
    (plan : RulePlan) (subject : Pattern) :
    plan.run relations language subject =
      (matchPattern plan.left.erase subject).flatMap fun initialBindings =>
        (premisesUsing (engineBasePremises relations) language recursiveStep
          (erasePremisePlans plan.premises) initialBindings).map
          fun finalBindings =>
            applyBindings finalBindings plan.right.erase := by
  simp only [RulePlan.run, run_eq_matchPattern,
    instantiate_eq_applyBindings]
  congr 1
  funext initialBindings
  rw [runPremisePlans_eq_premisesUsing]

/-- A successfully compiled row has exactly the independent syntactic rule
meaning of its source row. -/
theorem run_compileRule?
    (relations : RelationEnv) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern)
    (source : RewriteRule) (compiled : RulePlan) (subject : Pattern)
    (accepted : compileRule? source = some compiled) :
    compiled.run relations language subject =
      (matchPattern source.left subject).flatMap fun initialBindings =>
        (premisesUsing (engineBasePremises relations) language recursiveStep
          source.premises
          initialBindings).map fun finalBindings =>
            applyBindings finalBindings source.right := by
  have erased := erase_of_compileRule? source compiled accepted
  subst source
  simpa [RulePlan.erase] using
    run_eq_syntactic relations language recursiveStep compiled subject

/-- Successful compilation preserves the complete source rule interpreter,
including authored premise order and recursive congruence behavior. -/
theorem run_compileRule?_eq_applyRuleUsing
    (relations : RelationEnv) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern)
    (source : RewriteRule) (compiled : RulePlan) (subject : Pattern)
    (accepted : compileRule? source = some compiled) :
    compiled.run relations language subject =
      Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing
        RuleInterpretation.syntactic (engineBasePremises relations) language
          recursiveStep source subject := by
  have erased := erase_of_compileRule? source compiled accepted
  subst erased
  rw [run_compileRule? relations language recursiveStep _ compiled subject accepted]
  simp only [Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing,
    RuleInterpretation.syntactic, RulePlan.erase, applyRuleBindings,
    applyBindingsScoped_zero_of_binderFree _ _ _
      (binderFree_erase compiled.right)]

/-- With no premises, an admitted plan realizes the canonical root-row
interpreter. Binder-free RHS construction supplies the scoped-substitution
agreement; the row's binding metadata is absent by construction. -/
theorem RulePlan.run_eq_rootRule_of_premiseFree
    (relations : RelationEnv) (language : LanguageDef)
    (plan : RulePlan) (subject : Pattern) (premiseFree : plan.premises = []) :
    plan.run relations language subject =
      applyRuleWithPremisesUsing relations language plan.erase subject := by
  simp only [RulePlan.run, premiseFree, runPremisePlans, List.map_cons,
    List.map_nil, ← List.map_eq_flatMap, run_eq_matchPattern,
    applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    RulePlan.erase, erasePremisePlans, List.map_nil, applyPremisesWithEnv,
    List.foldl_nil,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindingsScoped_zero_of_binderFree _ _ _
      (binderFree_erase plan.right), instantiate_eq_applyBindings]

/-- Every admitted first-order row, including its ordered relation premises,
has the canonical root-row interpretation. -/
theorem RulePlan.run_eq_rootRule
    (relations : RelationEnv) (language : LanguageDef)
    (plan : RulePlan) (subject : Pattern) :
    plan.run relations language subject =
      applyRuleWithPremisesUsing relations language plan.erase subject := by
  simp only [RulePlan.run, run_eq_matchPattern, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    RulePlan.erase,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindingsScoped_zero_of_binderFree _ _ _
      (binderFree_erase plan.right), instantiate_eq_applyBindings]
  apply List.flatMap_congr
  intro bindings _
  rw [runPremisePlans_eq_applyPremisesWithEnv]

/-! ## Ordered rule-program compilation -/

/-- Compile a complete authored rewrite list without dropping or reordering
rows. -/
def compileRules? : List RewriteRule -> Option (List RulePlan)
  | [] => some []
  | rule :: rules => do
      let plan <- compileRule? rule
      let plans <- compileRules? rules
      pure (plan :: plans)

/-- Erase a compiled rule program back to its authored rows. -/
def eraseRulePlans (plans : List RulePlan) : List RewriteRule :=
  plans.map RulePlan.erase

/-- Successful program compilation retains every authored row, occurrence,
field, and order exactly. -/
theorem eraseRulePlans_of_compileRules?
    (source : List RewriteRule) (compiled : List RulePlan)
    (accepted : compileRules? source = some compiled) :
    eraseRulePlans compiled = source := by
  induction source generalizing compiled with
  | nil =>
      simp [compileRules?] at accepted
      subst compiled
      rfl
  | cons rule rules inductionHypothesis =>
      simp only [compileRules?, Option.bind_eq_bind] at accepted
      cases headCompiled : compileRule? rule with
      | none => simp [headCompiled] at accepted
      | some plan =>
          cases tailCompiled : compileRules? rules with
          | none => simp [headCompiled, tailCompiled] at accepted
          | some plans =>
              simp [headCompiled, tailCompiled] at accepted
              subst compiled
              change plan.erase :: eraseRulePlans plans = rule :: rules
              rw [erase_of_compileRule? rule plan headCompiled,
                inductionHypothesis plans tailCompiled]

/-- A proof-carrying compiled program for one exact authored rewrite list. -/
structure RuleProgram (source : List RewriteRule) where
  plans : List RulePlan
  erase_eq_source : eraseRulePlans plans = source

/-- Compile and package an authored rewrite list when every row belongs to the
explicit first-order fragment. -/
def compileProgram? (source : List RewriteRule) : Option (RuleProgram source) :=
  match accepted : compileRules? source with
  | none => none
  | some plans =>
      some
        { plans
          erase_eq_source :=
            eraseRulePlans_of_compileRules? source plans accepted }

@[simp] theorem RuleProgram.plans_length
    {source : List RewriteRule} (program : RuleProgram source) :
    program.plans.length = source.length := by
  have lengths := congrArg List.length program.erase_eq_source
  simpa [eraseRulePlans] using lengths

/-- Retrieve the compiled plan for an exact authored occurrence. -/
def RuleProgram.planAt
    {source : List RewriteRule} (program : RuleProgram source)
    (occurrence : Fin source.length) : RulePlan :=
  program.plans[occurrence.val]'(by
    rw [program.plans_length]
    exact occurrence.isLt)

/-- Occurrence lookup commutes with erasure; duplicate rows therefore remain
distinct source occurrences even when their contents happen to coincide. -/
theorem RuleProgram.erase_planAt
    {source : List RewriteRule} (program : RuleProgram source)
    (occurrence : Fin source.length) :
    (program.planAt occurrence).erase = source[occurrence] := by
  have planBound : occurrence.val < program.plans.length := by
    rw [program.plans_length]
    exact occurrence.isLt
  have point := congrArg (fun rules => rules[occurrence.val]?)
    program.erase_eq_source
  rw [eraseRulePlans, List.getElem?_map,
    List.getElem?_eq_getElem planBound,
    List.getElem?_eq_getElem occurrence.isLt] at point
  exact Option.some.inj point

/-- Exact erasure transports the authored premise-free boundary to every
compiled row, retaining duplicates and their original order. -/
theorem RuleProgram.premiseFree_plans
    {source : List RewriteRule} (program : RuleProgram source)
    (premiseFree : ∀ rule ∈ source, rule.premises = []) :
    ∀ plan ∈ program.plans, plan.premises = [] := by
  intro plan member
  have erasedMember : plan.erase ∈ source := by
    rw [← program.erase_eq_source, eraseRulePlans]
    exact List.mem_map_of_mem member
  have empty := congrArg List.length (premiseFree plan.erase erasedMember)
  apply List.eq_nil_of_length_eq_zero
  simpa [RulePlan.erase, erasePremisePlans] using empty

/-- An admitted program contains no discarded scoped-binding annotations. -/
theorem RuleProgram.bindingMetadata_none
    {source : List RewriteRule} (program : RuleProgram source) :
    ∀ rule ∈ source, rule.bindings = none := by
  intro rule member
  rw [← program.erase_eq_source, eraseRulePlans] at member
  obtain ⟨plan, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- All premise-free plans together enumerate exactly the canonical root
frontier of their admitted language, with authored order and multiplicity. -/
theorem RuleProgram.run_eq_rootFrontier_of_premiseFree
    (relations : RelationEnv) (language : LanguageDef)
    (program : RuleProgram language.rewrites) (subject : Pattern)
    (premiseFree : ∀ rule ∈ language.rewrites, rule.premises = []) :
    program.plans.flatMap (fun plan => plan.run relations language subject) =
      rewriteStepWithPremisesUsing relations language subject := by
  rw [rewriteStepWithPremisesUsing]
  conv_rhs => rw [← program.erase_eq_source, eraseRulePlans, List.flatMap_map]
  apply List.flatMap_congr
  intro plan member
  exact plan.run_eq_rootRule_of_premiseFree relations language subject
    (program.premiseFree_plans premiseFree plan member)

/-- Compiling all admitted rows retains the complete canonical root frontier,
with relation-premise branching, authored row order and multiplicity. -/
theorem RuleProgram.run_eq_rootFrontier
    (relations : RelationEnv) (language : LanguageDef)
    (program : RuleProgram language.rewrites) (subject : Pattern) :
    program.plans.flatMap (fun plan => plan.run relations language subject) =
      rewriteStepWithPremisesUsing relations language subject := by
  rw [rewriteStepWithPremisesUsing]
  conv_rhs => rw [← program.erase_eq_source, eraseRulePlans, List.flatMap_map]
  apply List.flatMap_congr
  intro plan _
  exact plan.run_eq_rootRule relations language subject

/-- Exact source erasure earns the nonrecursive-premise boundary used by the
equation-free GSLT root-step theorem. -/
theorem RuleProgram.noncontextual_premises
    {source : List RewriteRule} (program : RuleProgram source) :
    ∀ rule ∈ source, NoncontextualPremises rule.premises := by
  intro rule member
  rw [← program.erase_eq_source, eraseRulePlans] at member
  obtain ⟨plan, _, rfl⟩ := List.mem_map.mp member
  exact noncontextual_erasePremisePlans plan.premises

/-- The actual query checker required by a variable-only source realization. -/
def RulePlan.variablePremises? (plan : RulePlan) : Option (List VariablePremisePlan) :=
  premisePlansToVariables? plan.premises

theorem RulePlan.variablePremises?_exact (plan : RulePlan)
    (specialized : List VariablePremisePlan)
    (accepted : plan.variablePremises? = some specialized) :
    specialized.map VariablePremisePlan.toPlan = plan.premises :=
  premisePlansToVariables?_exact plan.premises specialized accepted

/-- A separately checked variable source row earns the compiled query view. -/
theorem RulePlan.variablePremises?_of_compileVariablePremises? (plan : RulePlan)
    (specialized : List VariablePremisePlan)
    (accepted : compileVariablePremises? (erasePremisePlans plan.premises) = some specialized) :
    plan.variablePremises? = some specialized := by
  have compiled := compileVariablePremises?_general _ specialized accepted
  rw [compilePremises?_erase] at compiled
  have same := (Option.some.inj compiled).symm
  rw [RulePlan.variablePremises?, ← same, premisePlansToVariables?_toPlan]

/-- A variable-only authored source profile transports to every exact compiled
row occurrence.  The general rule program is unchanged. -/
theorem RuleProgram.variablePremises?_coverage {source : List RewriteRule}
    (program : RuleProgram source)
    (admitted : ∀ rule ∈ source, ∃ specialized,
      compileVariablePremises? rule.premises = some specialized) :
    ∀ plan ∈ program.plans, ∃ specialized, plan.variablePremises? = some specialized := by
  intro plan member
  have erasedMember : plan.erase ∈ source := by
    rw [← program.erase_eq_source, eraseRulePlans]
    exact List.mem_map_of_mem member
  obtain ⟨specialized, accepted⟩ := admitted plan.erase erasedMember
  exact ⟨specialized, plan.variablePremises?_of_compileVariablePremises? specialized accepted⟩

#print axioms RulePlan.variablePremises?_exact
#print axioms RulePlan.variablePremises?_of_compileVariablePremises?
#print axioms RuleProgram.variablePremises?_coverage

/-! ## Ordered query witnesses and firing emissions -/

/-- Builtin and supplied rows have separate ordered occurrence spaces. -/
inductive QueryRowSource where
  | builtin
  | provider
deriving Repr, DecidableEq

/-- A successful query records the row before filtering.  The index is local
to this query's row list, rather than an index in a provider's global table. -/
structure QueryRowChoice where
  relation : String
  arguments : List Pattern
  source : QueryRowSource
  rowIndex : Nat
  tuple : List Pattern
deriving Repr

/-- The bindings and ordered row choices actually returned by premises. -/
structure PremiseReceipt where
  bindings : Bindings
  choices : List QueryRowChoice
deriving Repr

/-- Annotate each successful match with its original row position.  Failed
rows still advance the position, and equal rows remain separate entries. -/
def PremisePlan.matchRowsWithChoices (bindings : Bindings) (plan : PremisePlan)
    (arguments : List Pattern) (source : QueryRowSource) :
    Nat → List (List Pattern) → List PremiseReceipt
  | _, [] => []
  | index, tuple :: tuples =>
      let tail := plan.matchRowsWithChoices bindings arguments source (index + 1) tuples
      match plan.matchTuple? bindings tuple with
      | none => tail
      | some next =>
          { bindings := next
            choices := [⟨plan.relation, arguments, source, index, tuple⟩] } :: tail

theorem PremisePlan.matchRowsWithChoices_bindings
    (bindings : Bindings) (plan : PremisePlan) (arguments : List Pattern)
    (source : QueryRowSource) (index : Nat) (tuples : List (List Pattern)) :
    (plan.matchRowsWithChoices bindings arguments source index tuples).map
        PremiseReceipt.bindings = tuples.filterMap (plan.matchTuple? bindings) := by
  induction tuples generalizing index with
  | nil => rfl
  | cons tuple tuples ih =>
      cases matched : plan.matchTuple? bindings tuple <;>
        simp [PremisePlan.matchRowsWithChoices, matched, ih]

/-- Read and match the actual query rows, retaining builtin/provider identity
and the position of every successful row, including duplicate rows. -/
def PremisePlan.runReceipts (relations : RelationEnv) (language : LanguageDef)
    (bindings : Bindings) (plan : PremisePlan) : List PremiseReceipt :=
  let arguments := (erasePatterns plan.arguments).map (applyBindings bindings)
  plan.matchRowsWithChoices bindings arguments .builtin 0
      (builtinRelationTuples language plan.relation arguments) ++
    plan.matchRowsWithChoices bindings arguments .provider 0
      (relations.tuples plan.relation arguments)

theorem PremisePlan.runReceipts_bindings (relations : RelationEnv)
    (language : LanguageDef) (bindings : Bindings) (plan : PremisePlan) :
    (plan.runReceipts relations language bindings).map PremiseReceipt.bindings =
      plan.run relations language bindings := by
  simp [PremisePlan.runReceipts, PremisePlan.run,
    PremisePlan.matchRowsWithChoices_bindings]

/-- Read a canonical recorded event at the same query observation as the
residual receipt.  The position is an actual tuple position, not output rank. -/
def PremisePlan.receiptOfRecordedEvent (bindings : Bindings) (plan : PremisePlan)
    (source : QueryRowSource)
    (event : Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents.RecordedEvent) : PremiseReceipt :=
  ⟨event.final,
    [⟨plan.relation, (erasePatterns plan.arguments).map (applyBindings bindings),
      source, event.tuplePosition, event.tuple⟩]⟩

private theorem recordedTuple_receipts (bindings : Bindings) (plan : PremisePlan)
    (source : QueryRowSource) (position : Nat) (tuple : List Pattern) :
    ((matchRelationArgs bindings (erasePatterns plan.arguments) tuple).zipIdx.filterMap
      (fun (extension, matchPosition) => (mergeBindings bindings extension).map fun final =>
        (⟨position, tuple, matchPosition, extension, final⟩ :
          Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents.RecordedEvent))).map
        (plan.receiptOfRecordedEvent bindings source) =
      (plan.matchTuple? bindings tuple).toList.map fun final =>
        (⟨final,
          [⟨plan.relation, (erasePatterns plan.arguments).map (applyBindings bindings),
            source, position, tuple⟩]⟩ : PremiseReceipt) := by
  rw [← relationPatternArguments?_exact]
  unfold PremisePlan.matchTuple?
  cases matched : relationPatternArguments? bindings plan.arguments tuple with
  | none => simp
  | some extension =>
      cases merged : mergeBindings bindings extension <;>
        simp [List.zipIdx_cons, merged, PremisePlan.receiptOfRecordedEvent]

/-- Residual indexed row matching equals canonical recorded enumeration at
all receipt fields, including the positions of failed and duplicate rows. -/
theorem PremisePlan.matchRowsWithChoices_eq_recordedRows
    (bindings : Bindings) (plan : PremisePlan) (source : QueryRowSource)
    (position : Nat) (tuples : List (List Pattern)) :
    plan.matchRowsWithChoices bindings
        ((erasePatterns plan.arguments).map (applyBindings bindings)) source position tuples =
      ((tuples.zipIdx position).flatMap fun (tuple, tuplePosition) =>
        (matchRelationArgs bindings (erasePatterns plan.arguments) tuple).zipIdx.filterMap
          (fun (extension, matchPosition) => (mergeBindings bindings extension).map fun final =>
            (⟨tuplePosition, tuple, matchPosition, extension, final⟩ :
              Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents.RecordedEvent))).map
        (plan.receiptOfRecordedEvent bindings source) := by
  induction tuples generalizing position with
  | nil => rfl
  | cons tuple tuples ih =>
      simp only [PremisePlan.matchRowsWithChoices, List.zipIdx_cons, List.flatMap_cons,
        List.map_append, recordedTuple_receipts, ← ih]
      cases matched : plan.matchTuple? bindings tuple <;> simp

/-- For an explicit provider query, the complete receipt list is the same
observation of the engine's independently recorded events. -/
theorem PremisePlan.runReceipts_eq_recordedEvents_of_not_eq
    (relations : RelationEnv) (language : LanguageDef) (bindings : Bindings)
    (plan : PremisePlan) (explicitProvider : plan.relation ≠ "eq") :
    plan.runReceipts relations language bindings =
      (Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents.recordedEvents
        relations language bindings plan.relation (erasePatterns plan.arguments)).map
        (plan.receiptOfRecordedEvent bindings .provider) := by
  have noBuiltin : builtinRelationTuples language plan.relation
      ((erasePatterns plan.arguments).map (applyBindings bindings)) = [] := by
    unfold builtinRelationTuples
    split
    · exact False.elim (explicitProvider (by assumption))
    · rfl
  simp only [PremisePlan.runReceipts,
    Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents.recordedEvents,
    Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents.relationTuples,
    noBuiltin, List.nil_append,
    PremisePlan.matchRowsWithChoices]
  exact plan.matchRowsWithChoices_eq_recordedRows bindings .provider 0 _

/-- Continue each successful query in row order, carrying its actual witness
before the witnesses from the remaining authored premises. -/
def runPremiseReceipts (relations : RelationEnv) (language : LanguageDef) :
    List PremisePlan → Bindings → List PremiseReceipt
  | [], bindings => [⟨bindings, []⟩]
  | query :: queries, bindings =>
      (query.runReceipts relations language bindings).flatMap fun first =>
        (runPremiseReceipts relations language queries first.bindings).map fun rest =>
          { rest with choices := first.choices ++ rest.choices }

theorem runPremiseReceipts_bindings (relations : RelationEnv)
    (language : LanguageDef) (queries : List PremisePlan) (bindings : Bindings) :
    (runPremiseReceipts relations language queries bindings).map PremiseReceipt.bindings =
      runPremisePlans relations language queries bindings := by
  induction queries generalizing bindings with
  | nil => rfl
  | cons query queries ih =>
      simp only [runPremiseReceipts, List.map_flatMap, List.map_map,
        Function.comp_def, runPremisePlans]
      simp only [ih]
      rw [← query.runReceipts_bindings relations language bindings, List.flatMap_map]

/-- One successful firing retains its source occurrence, captured bindings,
completed bindings, ordered query choices and constructed target. -/
structure RuleEmission (Origin : Type) where
  origin : Origin
  initialBindings : Bindings
  bindings : Bindings
  choices : List QueryRowChoice
  target : Pattern
deriving Repr

/-- Re-index a source occurrence without deriving it from answer position. -/
def RuleEmission.mapOrigin {Origin Other : Type} (map : Origin → Other)
    (emission : RuleEmission Origin) : RuleEmission Other :=
  ⟨map emission.origin, emission.initialBindings, emission.bindings,
    emission.choices, emission.target⟩

/-- The compiled matcher and query operations produce the emission; no result
list or expected receipt is supplied by the caller. -/
def RulePlan.runEmissions {Origin : Type}
    (relations : RelationEnv) (language : LanguageDef)
    (origin : Origin) (plan : RulePlan) (subject : Pattern) : List (RuleEmission Origin) :=
  (plan.left.run subject).flatMap fun initial =>
    (runPremiseReceipts relations language plan.premises initial).map fun final =>
      ⟨origin, initial, final.bindings, final.choices,
        plan.right.instantiate final.bindings⟩

/-- Erasure preserves the whole result list, including order and duplicates. -/
theorem RulePlan.runEmissions_targets {Origin : Type}
    (relations : RelationEnv) (language : LanguageDef)
    (origin : Origin) (plan : RulePlan) (subject : Pattern) :
    (plan.runEmissions relations language origin subject).map RuleEmission.target =
      plan.run relations language subject := by
  simp only [RulePlan.runEmissions, RulePlan.run, List.map_flatMap, List.map_map,
    Function.comp_def]
  apply List.flatMap_congr
  intro initial _
  rw [← runPremiseReceipts_bindings relations language plan.premises initial,
    List.map_map]
  rfl

theorem RulePlan.runEmissions_mapOrigin {Origin Other : Type}
    (relations : RelationEnv) (language : LanguageDef) (map : Origin → Other)
    (origin : Origin) (plan : RulePlan) (subject : Pattern) :
    (plan.runEmissions relations language origin subject).map (RuleEmission.mapOrigin map) =
      plan.runEmissions relations language (map origin) subject := by
  simp [RulePlan.runEmissions, RuleEmission.mapOrigin, List.map_flatMap,
    List.map_map, Function.comp_def]

#print axioms PremisePlan.runReceipts_bindings
#print axioms PremisePlan.matchRowsWithChoices_bindings
#print axioms PremisePlan.matchRowsWithChoices_eq_recordedRows
#print axioms PremisePlan.runReceipts_eq_recordedEvents_of_not_eq
#print axioms runPremiseReceipts_bindings
#print axioms RulePlan.runEmissions_targets
#print axioms RulePlan.runEmissions_mapOrigin
#print axioms compilePatterns?_erase

/-! ## Closure of admitted first-order runs -/

theorem PatternPlan.erase_injective : Function.Injective PatternPlan.erase := by
  intro left right same
  have compiled := congrArg compilePattern? same
  simpa only [compilePattern?_erase, Option.some.injEq] using compiled

theorem isMatchCorrect_erase (plan : PatternPlan) : isMatchCorrectAux plan.erase = true := by
  rw [← compilePattern?_isSome_eq_isMatchCorrectAux, compilePattern?_erase]
  rfl

/-- Every actual binding value belongs to the independently admitted syntax
fragment. This does not require groundness or reinterpret variables inside
captured values as new schema parameters. -/
def FirstOrderBindings (bindings : Bindings) : Prop :=
  ∀ entry ∈ bindings, isMatchCorrectAux entry.2 = true

/-- A relation table preserves the admitted syntax when queried with admitted
arguments. Concrete finite providers can earn this closure from compilation of
their literal rows; this is not an execution or authority contract. -/
def FirstOrderRelations (relations : RelationEnv) : Prop :=
  ∀ relation arguments, isMatchCorrectListAux arguments = true →
    ∀ tuple ∈ relations.tuples relation arguments, isMatchCorrectListAux tuple = true

theorem FirstOrderBindings.nil : FirstOrderBindings [] := by
  intro entry member
  cases member

theorem FirstOrderBindings.merge {left right merged : Bindings}
    (leftFirstOrder : FirstOrderBindings left) (rightFirstOrder : FirstOrderBindings right)
    (combined : mergeBindings left right = some merged) : FirstOrderBindings merged := by
  induction right generalizing left with
  | nil =>
      have same : merged = left := by simpa [mergeBindings] using combined.symm
      simpa [same] using leftFirstOrder
  | cons entry rest ih =>
      have head : isMatchCorrectAux entry.2 = true := rightFirstOrder entry (by simp)
      have tail : FirstOrderBindings rest := fun other member =>
        rightFirstOrder other (List.mem_cons_of_mem _ member)
      simp only [mergeBindings, List.foldlM_cons] at combined
      cases found : left.find? (fun pair => pair.1 == entry.1) with
      | none =>
          simp only [found] at combined
          apply ih _ tail combined
          intro other member
          rcases List.mem_cons.mp member with rfl | inLeft
          · exact head
          · exact leftFirstOrder other inLeft
      | some prior =>
          simp only [found] at combined
          split at combined
          · exact ih leftFirstOrder tail combined
          · simp at combined

mutual
  /-- Matching an admitted subject only captures admitted subject data. -/
  theorem PatternPlan.run_bindings_firstOrder (plan : PatternPlan) (subject : Pattern)
      (subjectFirstOrder : isMatchCorrectAux subject = true) (bindings : Bindings)
      (matched : bindings ∈ plan.run subject) : FirstOrderBindings bindings := by
    cases plan with
    | metavariable name =>
        simp only [PatternPlan.run, List.mem_singleton] at matched
        subst bindings
        intro entry member
        simpa using (List.mem_singleton.mp member ▸ subjectFirstOrder)
    | bound index =>
        cases subject with
        | bvar actual =>
            by_cases same : index == actual
            · simp [PatternPlan.run, same] at matched
              subst bindings
              exact FirstOrderBindings.nil
            · simp [PatternPlan.run, same] at matched
        | _ => simp [PatternPlan.run] at matched
    | application constructor plans =>
        cases subject with
        | apply actual subjects =>
            by_cases same : constructor == actual && plans.length == subjects.length
            · simp only [PatternPlan.run, same, ↓reduceIte] at matched
              exact runPlans_bindings_firstOrder plans subjects
                (by simpa only [isMatchCorrectAux] using subjectFirstOrder) bindings matched
            · simp [PatternPlan.run, same] at matched
        | _ => simp [PatternPlan.run] at matched
  termination_by 2 * plan.work
  decreasing_by
    simp_all only [PatternPlan.work]
    omega

  /-- Ordered child matching preserves first-order values through each
successful repeated-variable merge. -/
  theorem runPlans_bindings_firstOrder (plans : List PatternPlan) (subjects : List Pattern)
      (subjectsFirstOrder : isMatchCorrectListAux subjects = true) (bindings : Bindings)
      (matched : bindings ∈ runPlans plans subjects) : FirstOrderBindings bindings := by
    cases plans with
    | nil =>
        cases subjects with
        | nil =>
            simp only [runPlans, List.mem_singleton] at matched
            subst bindings
            exact FirstOrderBindings.nil
        | cons subject subjects => simp [runPlans] at matched
    | cons plan plans =>
        cases subjects with
        | nil => simp [runPlans] at matched
        | cons subject subjects =>
            simp only [isMatchCorrectListAux, Bool.and_eq_true] at subjectsFirstOrder
            obtain ⟨head, headMatched, tailMember⟩ := List.mem_flatMap.mp matched
            obtain ⟨tail, tailMatched, combined⟩ := List.mem_filterMap.mp tailMember
            exact FirstOrderBindings.merge
              (plan.run_bindings_firstOrder subject subjectsFirstOrder.1 head headMatched)
              (runPlans_bindings_firstOrder plans subjects subjectsFirstOrder.2 tail tailMatched) combined
  termination_by 2 * patternPlansWork plans + 1
  decreasing_by
    all_goals
      have positive := PatternPlan.work_pos plan
      simp_all only [patternPlansWork]
      omega
end

mutual
  /-- RHS instantiation preserves the admitted syntax, including rigid bound
indices and unresolved variables, when captures themselves are admitted. -/
  theorem PatternPlan.instantiate_firstOrder (bindings : Bindings)
      (bindingsFirstOrder : FirstOrderBindings bindings) (plan : PatternPlan) :
      isMatchCorrectAux (plan.instantiate bindings) = true := by
    cases plan with
    | metavariable name =>
        cases found : bindings.find? (fun entry => entry.1 == name) with
        | none => simp [PatternPlan.instantiate, found, isMatchCorrectAux]
        | some entry =>
            simpa only [PatternPlan.instantiate, found] using
              bindingsFirstOrder entry (List.mem_of_find?_eq_some found)
    | bound index => simp only [PatternPlan.instantiate, isMatchCorrectAux]
    | application constructor arguments =>
        simpa only [PatternPlan.instantiate, isMatchCorrectAux] using
          instantiateList_firstOrder bindings bindingsFirstOrder arguments
  termination_by 2 * plan.work
  decreasing_by simp [PatternPlan.work]; omega

  theorem instantiateList_firstOrder (bindings : Bindings)
      (bindingsFirstOrder : FirstOrderBindings bindings) (plans : List PatternPlan) :
      isMatchCorrectListAux (plans.map (PatternPlan.instantiate bindings)) = true := by
    cases plans with
    | nil => rfl
    | cons plan plans =>
        simp only [List.map_cons, isMatchCorrectListAux, Bool.and_eq_true]
        exact ⟨plan.instantiate_firstOrder bindings bindingsFirstOrder,
          instantiateList_firstOrder bindings bindingsFirstOrder plans⟩
  termination_by 2 * patternPlansWork plans + 1
  decreasing_by
    all_goals
      have positive := PatternPlan.work_pos plan
      rw [patternPlansWork]
      omega
end

/-- Ordinary binding application stays in the admitted first-order syntax.
This is derived from the independent plan compiler and instantiator. -/
theorem applyBindings_firstOrder (bindings : Bindings)
    (bindingsFirstOrder : FirstOrderBindings bindings) (pattern : Pattern)
    (patternFirstOrder : isMatchCorrectAux pattern = true) :
    isMatchCorrectAux (applyBindings bindings pattern) = true := by
  cases accepted : compilePattern? pattern with
  | none =>
      have same := compilePattern?_isSome_eq_isMatchCorrectAux pattern
      simp only [accepted, Option.isSome_none, patternFirstOrder] at same
      cases same
  | some plan =>
      have erased := erase_of_compilePattern? pattern plan accepted
      rw [← erased, ← instantiate_eq_applyBindings]
      exact plan.instantiate_firstOrder bindings bindingsFirstOrder

/-- Canonical matching of two admitted first-order patterns captures only
admitted values. Repeated-variable consistency is supplied by the matcher. -/
theorem matchPattern_bindings_firstOrder (pattern subject : Pattern)
    (patternFirstOrder : isMatchCorrectAux pattern = true)
    (subjectFirstOrder : isMatchCorrectAux subject = true) (bindings : Bindings)
    (matched : bindings ∈ matchPattern pattern subject) : FirstOrderBindings bindings := by
  cases accepted : compilePattern? pattern with
  | none =>
      have same := compilePattern?_isSome_eq_isMatchCorrectAux pattern
      simp only [accepted, Option.isSome_none, patternFirstOrder] at same
      cases same
  | some plan =>
      have erased := erase_of_compilePattern? pattern plan accepted
      rw [← erased, ← run_eq_matchPattern] at matched
      exact plan.run_bindings_firstOrder subject subjectFirstOrder bindings matched

/-- Admitted first-order patterns contain no binder that would require
capture-depth alignment during right-hand-side construction. -/
theorem binderFree_of_firstOrder (pattern : Pattern)
    (patternFirstOrder : isMatchCorrectAux pattern = true) : binderFree pattern = true := by
  cases accepted : compilePattern? pattern with
  | none =>
      have same := compilePattern?_isSome_eq_isMatchCorrectAux pattern
      simp only [accepted, Option.isSome_none, patternFirstOrder] at same
      cases same
  | some plan =>
      rw [← erase_of_compilePattern? pattern plan accepted]
      exact binderFree_erase plan

theorem relationArgument?_firstOrder (seed : Bindings) (name : String) (value : Pattern)
    (valueFirstOrder : isMatchCorrectAux value = true) (bindings : Bindings)
    (matched : relationArgument? seed name value = some bindings) : FirstOrderBindings bindings := by
  unfold relationArgument? at matched
  cases found : seed.lookup name with
  | none =>
      simp only [found, Option.some.injEq] at matched
      subst bindings
      intro entry member
      simpa using (List.mem_singleton.mp member ▸ valueFirstOrder)
  | some prior =>
      simp only [found] at matched
      split at matched
      · simp only [Option.some.injEq] at matched
        subst bindings
        exact FirstOrderBindings.nil
      · simp at matched

theorem relationArguments?_firstOrder (seed : Bindings) (names : List String) (values : List Pattern)
    (seedFirstOrder : FirstOrderBindings seed) (valuesFirstOrder : isMatchCorrectListAux values = true)
    (bindings : Bindings) (matched : relationArguments? seed names values = some bindings) :
    FirstOrderBindings bindings := by
  induction names generalizing seed values bindings with
  | nil =>
      cases values with
      | nil =>
          simp only [relationArguments?, Option.some.injEq] at matched
          subst bindings
          exact FirstOrderBindings.nil
      | cons value values => simp [relationArguments?] at matched
  | cons name names ih =>
      cases values with
      | nil => simp [relationArguments?] at matched
      | cons value values =>
          simp only [isMatchCorrectListAux, Bool.and_eq_true] at valuesFirstOrder
          simp only [relationArguments?, Option.bind_eq_bind] at matched
          cases headMatched : relationArgument? seed name value with
          | none => simp [headMatched] at matched
          | some head =>
              simp only [headMatched, Option.bind_some] at matched
              have headFirstOrder := relationArgument?_firstOrder seed name value valuesFirstOrder.1 head headMatched
              cases extendedMerged : mergeBindings seed head with
              | none => simp [extendedMerged] at matched
              | some extended =>
                  simp only [extendedMerged, Option.bind_some] at matched
                  have extendedFirstOrder := FirstOrderBindings.merge seedFirstOrder headFirstOrder extendedMerged
                  cases tailMatched : relationArguments? extended names values with
                  | none => simp [tailMatched] at matched
                  | some tail =>
                      simp only [tailMatched, Option.bind_some] at matched
                      exact FirstOrderBindings.merge headFirstOrder
                        (ih extended values extendedFirstOrder valuesFirstOrder.2 tail tailMatched) matched

theorem relationPatternArgument?_firstOrder (seed : Bindings) (plan : PatternPlan)
    (value : Pattern) (valueFirstOrder : isMatchCorrectAux value = true)
    (bindings : Bindings) (matched : relationPatternArgument? seed plan value = some bindings) :
    FirstOrderBindings bindings := by
  cases plan with
  | metavariable name => exact relationArgument?_firstOrder seed name value valueFirstOrder bindings matched
  | bound index =>
      apply PatternPlan.run_bindings_firstOrder (.bound index) value valueFirstOrder bindings
      rw [← PatternPlan.match?_toList]
      simpa [relationPatternArgument?, matched] using matched
  | application constructor plans =>
      apply PatternPlan.run_bindings_firstOrder (.application constructor plans) value valueFirstOrder bindings
      rw [← PatternPlan.match?_toList]
      simpa [relationPatternArgument?, matched] using matched

theorem relationPatternArguments?_firstOrder (seed : Bindings) (names : List PatternPlan) (values : List Pattern)
    (seedFirstOrder : FirstOrderBindings seed) (valuesFirstOrder : isMatchCorrectListAux values = true)
    (bindings : Bindings) (matched : relationPatternArguments? seed names values = some bindings) :
    FirstOrderBindings bindings := by
  induction names generalizing seed values bindings with
  | nil =>
      cases values with
      | nil =>
          simp only [relationPatternArguments?, Option.some.injEq] at matched
          subst bindings
          exact FirstOrderBindings.nil
      | cons value values => simp [relationPatternArguments?] at matched
  | cons name names ih =>
      cases values with
      | nil => simp [relationPatternArguments?] at matched
      | cons value values =>
          simp only [isMatchCorrectListAux, Bool.and_eq_true] at valuesFirstOrder
          simp only [relationPatternArguments?, Option.bind_eq_bind] at matched
          cases headMatched : relationPatternArgument? seed name value with
          | none => simp [headMatched] at matched
          | some head =>
              simp only [headMatched, Option.bind_some] at matched
              have headFirstOrder := relationPatternArgument?_firstOrder seed name value valuesFirstOrder.1 head headMatched
              cases extendedMerged : mergeBindings seed head with
              | none => simp [extendedMerged] at matched
              | some extended =>
                  simp only [extendedMerged, Option.bind_some] at matched
                  have extendedFirstOrder := FirstOrderBindings.merge seedFirstOrder headFirstOrder extendedMerged
                  cases tailMatched : relationPatternArguments? extended names values with
                  | none => simp [tailMatched] at matched
                  | some tail =>
                      simp only [tailMatched, Option.bind_some] at matched
                      exact FirstOrderBindings.merge headFirstOrder
                        (ih extended values extendedFirstOrder valuesFirstOrder.2 tail tailMatched) matched

theorem PremisePlan.matchTuple?_firstOrder (seed : Bindings) (plan : PremisePlan) (values : List Pattern)
    (seedFirstOrder : FirstOrderBindings seed) (valuesFirstOrder : isMatchCorrectListAux values = true)
    (bindings : Bindings) (matched : plan.matchTuple? seed values = some bindings) : FirstOrderBindings bindings := by
  simp only [PremisePlan.matchTuple?, Option.bind_eq_bind] at matched
  cases argumentsMatched : relationPatternArguments? seed plan.arguments values with
  | none => simp [argumentsMatched] at matched
  | some extension =>
      simp only [argumentsMatched, Option.bind_some] at matched
      exact FirstOrderBindings.merge seedFirstOrder
        (relationPatternArguments?_firstOrder seed plan.arguments values seedFirstOrder valuesFirstOrder extension argumentsMatched)
        matched

private theorem patterns_instantiated_firstOrder (seed : Bindings)
    (seedFirstOrder : FirstOrderBindings seed) (plans : List PatternPlan) :
    isMatchCorrectListAux ((erasePatterns plans).map (applyBindings seed)) = true := by
  rw [erasePatterns_eq_map, List.map_map]
  simpa only [Function.comp_def, ← instantiate_eq_applyBindings] using
    instantiateList_firstOrder seed seedFirstOrder plans

theorem builtinRelationTuples_firstOrder (language : LanguageDef) (relation : String) (arguments : List Pattern)
    (argumentsFirstOrder : isMatchCorrectListAux arguments = true) (values : List Pattern)
    (member : values ∈ builtinRelationTuples language relation arguments) : isMatchCorrectListAux values = true := by
  cases arguments with
  | nil => simp [builtinRelationTuples] at member
  | cons left arguments =>
      cases arguments with
      | nil => simp [builtinRelationTuples] at member
      | cons right rest =>
          cases rest with
          | cons extra rest => simp [builtinRelationTuples] at member
          | nil =>
              by_cases same : relation = "eq"
              · subst relation
                simp only [isMatchCorrectListAux, Bool.and_eq_true] at argumentsFirstOrder
                simp [builtinRelationTuples] at member
                rcases member with rfl | rfl <;> simp [isMatchCorrectListAux, argumentsFirstOrder.1,
                  argumentsFirstOrder.2.1]
              · simp [builtinRelationTuples, same] at member

theorem PremisePlan.run_bindings_firstOrder (relations : RelationEnv) (language : LanguageDef)
    (relationsFirstOrder : FirstOrderRelations relations) (seed : Bindings) (seedFirstOrder : FirstOrderBindings seed)
    (plan : PremisePlan) (bindings : Bindings) (member : bindings ∈ plan.run relations language seed) :
    FirstOrderBindings bindings := by
  obtain ⟨tuple, member, matched⟩ := List.mem_filterMap.mp member
  have argumentsFirstOrder := patterns_instantiated_firstOrder seed seedFirstOrder plan.arguments
  have tupleFirstOrder : isMatchCorrectListAux tuple = true := by
    rcases List.mem_append.mp member with builtin | provided
    · exact builtinRelationTuples_firstOrder language plan.relation _ argumentsFirstOrder tuple builtin
    · exact relationsFirstOrder plan.relation _ argumentsFirstOrder tuple provided
  exact plan.matchTuple?_firstOrder seed tuple seedFirstOrder tupleFirstOrder bindings matched

theorem runPremisePlans_bindings_firstOrder (relations : RelationEnv) (language : LanguageDef)
    (relationsFirstOrder : FirstOrderRelations relations) (plans : List PremisePlan)
    (seed : Bindings) (seedFirstOrder : FirstOrderBindings seed) (bindings : Bindings)
    (member : bindings ∈ runPremisePlans relations language plans seed) : FirstOrderBindings bindings := by
  induction plans generalizing seed with
  | nil =>
      simp only [runPremisePlans, List.mem_singleton] at member
      simpa [member] using seedFirstOrder
  | cons plan plans ih =>
      obtain ⟨next, nextMember, tailMember⟩ := List.mem_flatMap.mp member
      exact ih next (plan.run_bindings_firstOrder relations language relationsFirstOrder seed seedFirstOrder next nextMember)
        tailMember

theorem RulePlan.run_firstOrder (relations : RelationEnv) (language : LanguageDef)
    (relationsFirstOrder : FirstOrderRelations relations) (plan : RulePlan) (subject : Pattern)
    (subjectFirstOrder : isMatchCorrectAux subject = true) (target : Pattern)
    (member : target ∈ plan.run relations language subject) : isMatchCorrectAux target = true := by
  obtain ⟨initial, initialMatched, targetMember⟩ := List.mem_flatMap.mp member
  obtain ⟨final, finalMember, rfl⟩ := List.mem_map.mp targetMember
  exact plan.right.instantiate_firstOrder final
    (runPremisePlans_bindings_firstOrder relations language relationsFirstOrder plan.premises initial
      (plan.left.run_bindings_firstOrder subject subjectFirstOrder initial initialMatched) final finalMember)

/-- A fully compiled language stays in its subject compiler's image when its
literal relation payloads satisfy independently checked syntax admission. -/
theorem RuleProgram.rootFrontier_firstOrder (relations : RelationEnv) (language : LanguageDef)
    (relationsFirstOrder : FirstOrderRelations relations) (program : RuleProgram language.rewrites)
    (subject : Pattern) (subjectFirstOrder : isMatchCorrectAux subject = true) (target : Pattern)
    (member : target ∈ rewriteStepWithPremisesUsing relations language subject) : isMatchCorrectAux target = true := by
  rw [← program.run_eq_rootFrontier relations language subject] at member
  obtain ⟨plan, _, targetMember⟩ := List.mem_flatMap.mp member
  exact plan.run_firstOrder relations language relationsFirstOrder subject subjectFirstOrder target targetMember

#print axioms relationPatternArgument?_firstOrder
#print axioms relationPatternArguments?_firstOrder

/-! ## Discriminating controls -/

namespace ClosureControls

private def escapingPayload : Pattern := .lambda (some "bound") (.bvar 0)

private def escapingRule : RulePlan :=
  { name := "provider-value"
    typeContext := []
    premises := [⟨"value", [.metavariable "x"]⟩]
    left := .application "Start" []
    right := .metavariable "x" }

private def escapingRelations : RelationEnv where
  tuples _ _ := [[escapingPayload]]

/-- Captured variables are literal admissible data; syntax closure does not
require ground payloads. -/
theorem literal_variable_admitted :
    isMatchCorrectAux
      ((PatternPlan.application "Box" [.metavariable "x"]).instantiate
        [("x", .fvar "inside")]) = true := by
  simp [PatternPlan.instantiate, isMatchCorrectAux, isMatchCorrectListAux]

/-- Arbitrary provider payloads can escape the compiled first-order image.
This is why finite path lifting checks provider syntax independently. -/
theorem unadmitted_provider_payload_escapes :
    escapingRule.run escapingRelations (LanguageDef.empty "closure-negative")
      (.apply "Start" []) = [escapingPayload] := by
  simp only [RulePlan.run, escapingRule, PatternPlan.run, runPlans,
    runPremisePlans, PremisePlan.run, escapingRelations, PatternPlan.instantiate]
  decide +kernel

theorem escaping_payload_refused : compilePattern? escapingPayload = none := rfl

end ClosureControls

namespace RelationControls

private def left : Pattern := .apply "Left" []
private def right : Pattern := .apply "Right" []

theorem argument_order_retained :
    (PremisePlan.matchTuple? [] ⟨"edge", [.metavariable "x", .metavariable "y"]⟩ [left, right]) =
      some [("x", left), ("y", right)] := by decide +kernel

theorem captured_variable_is_literal :
    relationArguments? [("x", .fvar "inside")] ["x"] [left] = none := by
  decide +kernel

theorem repeated_argument_accepts :
    relationArguments? [] ["x", "x"] [left, left] = some [("x", left)] := by
  decide +kernel

theorem repeated_argument_refuses :
    relationArguments? [] ["x", "x"] [left, right] = none := by decide +kernel

theorem wrong_tuple_arity_refuses :
    relationArguments? [] ["x"] [left, right] = none := by decide +kernel

theorem duplicate_tuples_retained :
    ([[left, right], [left, right]].filterMap
      (PremisePlan.matchTuple? [] ⟨"edge", [.metavariable "x", .metavariable "y"]⟩)) =
      [[("x", left), ("y", right)], [("x", left), ("y", right)]] := by
  decide +kernel

end RelationControls

private def repeatedSource : Pattern :=
  .apply "Pair" [.fvar "x", .fvar "x"]

private def repeatedPlan : PatternPlan :=
  .application "Pair" [.metavariable "x", .metavariable "x"]

/-- Repeated-variable consistency remains load-bearing after compilation. -/
example :
    repeatedPlan.run
      (.apply "Pair" [.apply "Left" [], .apply "Right" []]) = [] := by
  decide

/-- The same repeated value is accepted with one canonical binding. -/
example :
    repeatedPlan.run
      (.apply "Pair" [.apply "Left" [], .apply "Left" []]) =
        [[("x", .apply "Left" [])]] := by
  decide

/-- Binder-bearing syntax is outside this first-order backend and is rejected. -/
example : compilePattern? (.lambda (some "x") (.bvar 0)) = none := by
  rfl

/-- The positive fixture is genuinely compiled from its source. -/
example : compilePattern? repeatedSource = some repeatedPlan := by
  rfl

#print axioms compilePattern?_isSome_eq_isMatchCorrectAux
#print axioms compilePatterns?_isSome_eq_isMatchCorrectListAux
#print axioms erase_of_compilePattern?
#print axioms run_compilePattern?
#print axioms instantiate_eq_applyBindings
#print axioms relationArgument?_exact
#print axioms relationArguments?_exact
#print axioms PremisePlan.matchTuple?_exact
#print axioms PremisePlan.matchTuples_exact
#print axioms RelationControls.argument_order_retained
#print axioms RelationControls.captured_variable_is_literal
#print axioms RelationControls.repeated_argument_accepts
#print axioms RelationControls.repeated_argument_refuses
#print axioms RelationControls.wrong_tuple_arity_refuses
#print axioms RelationControls.duplicate_tuples_retained
#print axioms erase_of_compilePremise?
#print axioms erasePremisePlans_of_compilePremises?
#print axioms runPremisePlans_eq_premisesUsing
#print axioms noncontextual_erasePremisePlans
#print axioms runPremisePlans_eq_applyPremisesWithEnv
#print axioms RulePlan.run_eq_rootRule
#print axioms RuleProgram.run_eq_rootFrontier
#print axioms RuleProgram.noncontextual_premises
#print axioms erase_of_compileRule?
#print axioms run_compileRule?
#print axioms run_compileRule?_eq_applyRuleUsing
#print axioms eraseRulePlans_of_compileRules?
#print axioms RuleProgram.erase_planAt
#print axioms compileArgumentNames?_map_fvar
#print axioms compilePremise?_erase
#print axioms compilePremises?_erase
#print axioms compilePattern?_erase
#print axioms PatternPlan.erase_injective
#print axioms FirstOrderBindings.merge
#print axioms PatternPlan.run_bindings_firstOrder
#print axioms PatternPlan.instantiate_firstOrder
#print axioms applyBindings_firstOrder
#print axioms matchPattern_bindings_firstOrder
#print axioms binderFree_of_firstOrder
#print axioms PremisePlan.run_bindings_firstOrder
#print axioms runPremisePlans_bindings_firstOrder
#print axioms RuleProgram.rootFrontier_firstOrder
#print axioms ClosureControls.literal_variable_admitted
#print axioms ClosureControls.unadmitted_provider_payload_escapes
#print axioms ClosureControls.escaping_payload_refused

end Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
