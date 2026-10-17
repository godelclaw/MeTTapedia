import Mettapedia.Logic.HostingStyles.LocatedAtoms.Evaluator

/-!
# The transitions of located atoms: every step of a table is a step of the run of its atom

This module works with terms of the candidate with located atoms, and proves
that a run in the space of a list of rules computes at least what the theory
of the rules computes.

* **Terms**: the application, the abstraction and the product of terms, the
  run of a term in a space (`appTerm`, `lamTerm`, `piTerm`, `runTerm`), a
  closed space at any stage (`spaceAt`), the atom of a λΠ term and the run of
  that atom in the space of a list of rules (`locatedAtom`, `runAtom`).
* **The equations on terms**: the run of an application is the application of
  the runs, the run of an abstraction or of a product in a closed space is
  the abstraction or the product of the runs, and a run of a run is the inner
  run (`runTerm_app`, `runTerm_lam`, `runTerm_pi`, `runTerm_run`).
* **The static equivalence and the transitions pass through the seven
  one-hole contexts of atoms** (`related_fill`, `termStep_fill`, and
  `termStep_appFunction` … `termStep_runSubject`): each of them is the
  context of a congruence rewrite of the presentation.
* **Every step of a theory whose rules are those of a list and which has no
  definition is a transition between the runs of the atoms in the space of
  the list**, at every depth (`runAtom_termStep`).  A beta step is a step of
  the subject of the run; a step by a rule is a root step of the run of the
  redex, which the equations move to the root from where the run stands.

The other direction, that the run of an atom has no other transition, is the
subject of the module `Spellings`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.LocatedAtoms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory inst patternVars usesOnly)
open Mettapedia.GSLT.LanguageDef.LFTyping (subst0)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)
open Mettapedia.Logic.HostingStyles.AmbientSpace (atomAt_wellSorted_of ruleSpace_wellSorted_of)

variable {base : BasePremiseEvaluator}

/-! ## Terms -/

/-- The interface of the atoms at a stage. -/
abbrev atomsAt (stage : List TypeExpr) : Contexts.Interface := ⟨.base "Atom", stage⟩

/-- The interface of the spaces at a stage. -/
abbrev spacesAt (stage : List TypeExpr) : Contexts.Interface := ⟨.base "Space", stage⟩

/-- The application of an atom to an atom. -/
def appTerm {stage : List TypeExpr} (function argument : Contexts.Term located (atomsAt stage)) :
    Contexts.Term located (atomsAt stage) :=
  ⟨.apply "App" [function.1, argument.1],
    wellSorted_apply_two (lang := located) (label := "App") (firstName := "f")
      (secondName := "a") (located_carriesAtoms applicationConstructor (by decide)) function.2
      argument.2⟩

/-- The abstraction of an atom beneath one more binder. -/
def lamTerm {stage : List TypeExpr} (domain : Contexts.Term located (atomsAt stage))
    (body : Contexts.Term located (atomsAt (.base "Atom" :: stage))) :
    Contexts.Term located (atomsAt stage) :=
  ⟨.apply "Lam" [domain.1, .lambda none body.1],
    wellSorted_apply_binder (lang := located) (label := "Lam") (name := "a") (binder := "x")
      (bodyName := "body") (located_carriesAtoms abstractionConstructor (by decide)) domain.2
      body.2⟩

/-- The product of an atom beneath one more binder. -/
def piTerm {stage : List TypeExpr} (domain : Contexts.Term located (atomsAt stage))
    (body : Contexts.Term located (atomsAt (.base "Atom" :: stage))) :
    Contexts.Term located (atomsAt stage) :=
  ⟨.apply "Pi" [domain.1, .lambda none body.1],
    wellSorted_apply_binder (lang := located) (label := "Pi") (name := "a") (binder := "x")
      (bodyName := "body") (located_carriesAtoms productConstructor (by decide)) domain.2
      body.2⟩

/-- **The run of an atom in a space.** -/
def runTerm {stage : List TypeExpr} (space : Contexts.Term located (spacesAt stage))
    (subject : Contexts.Term located (atomsAt stage)) : Contexts.Term located (atomsAt stage) :=
  ⟨runPattern space.1 subject.1,
    wellSorted_apply_two (lang := located) (label := "prime-run") (firstName := "space")
      (secondName := "subject") (by decide) space.2 subject.2⟩

/-- **A closed space, at any stage.**  It mentions no bound variable, so it
is the same pattern beneath any binders. -/
def spaceAt (space : Contexts.Term located closedSpace) (stage : List TypeExpr) :
    Contexts.Term located (spacesAt stage) :=
  ⟨space.1, wellSorted_extendOuter space.2 stage⟩

@[simp] theorem spaceAt_val (space : Contexts.Term located closedSpace) (stage : List TypeExpr) :
    (spaceAt space stage).1 = space.1 :=
  rfl

/-- The space of a list of rules, as a closed space of the candidate. -/
def ruleSpaceTerm (rules : List Dedukti.RewriteRule) : Contexts.Term located closedSpace :=
  ⟨ruleSpace rules, ruleSpace_wellSorted_of located_carriesAtoms rules⟩

/-- The atom of a λΠ term, as a term of the candidate at the stage of
`depth` binders. -/
def locatedAtom (depth : Nat) (term : LF.Term) : Contexts.Term located (atomInterface depth) :=
  ⟨atomAt depth term, atomAt_wellSorted_of located_carriesAtoms term depth⟩

/-- **The run of the atom of a λΠ term in the space of a list of rules.** -/
def runAtom (rules : List Dedukti.RewriteRule) (depth : Nat) (term : LF.Term) :
    Contexts.Term located (atomInterface depth) :=
  runTerm (spaceAt (ruleSpaceTerm rules) (List.replicate depth (.base "Atom")))
    (locatedAtom depth term)

@[simp] theorem runAtom_val (rules : List Dedukti.RewriteRule) (depth : Nat) (term : LF.Term) :
    (runAtom rules depth term).1 = runPattern (ruleSpace rules) (atomAt depth term) :=
  rfl

/-! ## The equations, on terms -/

/-- **The run of an application is the application of the runs.** -/
theorem runTerm_app {stage : List TypeExpr} (space : Contexts.Term located (spacesAt stage))
    (function argument : Contexts.Term located (atomsAt stage)) :
    (termSetoid base located (atomsAt stage)).r (runTerm space (appTerm function argument))
      (appTerm (runTerm space function) (runTerm space argument)) :=
  related_of_instance (runApplication_instance space.1 function.1 argument.1)

/-- **The run of an abstraction in a closed space is the abstraction of the
runs.** -/
theorem runTerm_lam {stage : List TypeExpr} (space : Contexts.Term located closedSpace)
    (domain : Contexts.Term located (atomsAt stage))
    (body : Contexts.Term located (atomsAt (.base "Atom" :: stage))) :
    (termSetoid base located (atomsAt stage)).r
      (runTerm (spaceAt space stage) (lamTerm domain body))
      (lamTerm (runTerm (spaceAt space stage) domain)
        (runTerm (spaceAt space (.base "Atom" :: stage)) body)) :=
  related_of_instance (runAbstraction_instance space.1 domain.1 body.1 none)

/-- **The run of a product in a closed space is the product of the runs.** -/
theorem runTerm_pi {stage : List TypeExpr} (space : Contexts.Term located closedSpace)
    (domain : Contexts.Term located (atomsAt stage))
    (body : Contexts.Term located (atomsAt (.base "Atom" :: stage))) :
    (termSetoid base located (atomsAt stage)).r
      (runTerm (spaceAt space stage) (piTerm domain body))
      (piTerm (runTerm (spaceAt space stage) domain)
        (runTerm (spaceAt space (.base "Atom" :: stage)) body)) :=
  related_of_instance (runProduct_instance space.1 domain.1 body.1 none)

/-- **A run of a run is the inner run.** -/
theorem runTerm_run {stage : List TypeExpr} (outer space : Contexts.Term located (spacesAt stage))
    (subject : Contexts.Term located (atomsAt stage)) :
    (termSetoid base located (atomsAt stage)).r (runTerm outer (runTerm space subject))
      (runTerm space subject) :=
  related_of_instance (runRun_instance outer.1 space.1 subject.1)

/-! ## Through a one-hole context -/

/-- **The static equivalence passes through a one-hole context** that sends
terms to terms. -/
theorem related_fill (context : OneHoleContext) {inner outer : Contexts.Interface}
    (sorted : ∀ term : Contexts.Term located inner,
      OpenPatternWellSorted located FreeTypeContext.empty outer.stage outer.type
        (context.fill term.1))
    {first second : Contexts.Term located inner}
    (related : (termSetoid base located inner).r first second) :
    (termSetoid base located outer).r ⟨context.fill first.1, sorted first⟩
      ⟨context.fill second.1, sorted second⟩ := by
  induction related with
  | rel first second step => exact .rel _ _ (equationContextStep_fill context step)
  | refl term => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ firstStep secondStep => exact .trans _ _ _ firstStep secondStep

/-- **A transition passes through a one-hole context** that sends terms to
terms and that a congruence rewrite of the presentation covers. -/
theorem termStep_fill (context : OneHoleContext) {inner outer : Contexts.Interface}
    (sorted : ∀ term : Contexts.Term located inner,
      OpenPatternWellSorted located FreeTypeContext.empty outer.stage outer.type
        (context.fill term.1))
    (congruence : ∀ {fuel : Nat} {source target : Pattern},
      StepAt base located fuel source target →
        StepAt base located (fuel + 1) (context.fill source) (context.fill target))
    {source target : Contexts.Term located inner} (step : TermStep base located source target) :
    TermStep base located (⟨context.fill source.1, sorted source⟩ : Contexts.Term located outer)
      ⟨context.fill target.1, sorted target⟩ := by
  obtain ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩ := step
  exact ⟨⟨_, sorted redex⟩, ⟨_, sorted contractum⟩, related_fill context sorted before,
    ⟨fuel + 1, congruence fired⟩, related_fill context sorted after⟩

/-- A raw step between two terms is a transition. -/
theorem termStep_of_step {interface : Contexts.Interface}
    {source target : Contexts.Term located interface}
    (step : Step base located source.1 target.1) : TermStep base located source target :=
  ⟨source, target, .refl _, step, .refl _⟩

/-- A transition between terms that the static equivalence identifies with
its two ends. -/
theorem termStep_between {interface : Contexts.Interface}
    {source redex contractum target : Contexts.Term located interface}
    (before : (termSetoid base located interface).r source redex)
    (step : TermStep base located redex contractum)
    (after : (termSetoid base located interface).r contractum target) :
    TermStep base located source target := by
  obtain ⟨inner, reduct, toInner, fired, fromReduct⟩ := step
  exact ⟨inner, reduct, .trans _ _ _ before toInner, fired, .trans _ _ _ fromReduct after⟩

theorem termStep_appFunction {stage : List TypeExpr}
    {function next : Contexts.Term located (atomsAt stage)}
    (argument : Contexts.Term located (atomsAt stage))
    (step : TermStep base located function next) :
    TermStep base located (appTerm function argument) (appTerm next argument) :=
  termStep_fill (outer := atomsAt stage) (.apply "App" [] .hole [argument.1])
    (fun term => (appTerm term argument).2)
    (fun fired => step_appFunction (by simp [located_rewrites, atomsReduce_rewrites]) argument.1
      fired) step

theorem termStep_appArgument {stage : List TypeExpr}
    {argument next : Contexts.Term located (atomsAt stage)}
    (function : Contexts.Term located (atomsAt stage))
    (step : TermStep base located argument next) :
    TermStep base located (appTerm function argument) (appTerm function next) :=
  termStep_fill (outer := atomsAt stage) (.apply "App" [function.1] .hole [])
    (fun term => (appTerm function term).2)
    (fun fired => step_appArgument (by simp [located_rewrites, atomsReduce_rewrites]) function.1
      fired) step

theorem termStep_lamDomain {stage : List TypeExpr}
    {domain next : Contexts.Term located (atomsAt stage)}
    (body : Contexts.Term located (atomsAt (.base "Atom" :: stage)))
    (step : TermStep base located domain next) :
    TermStep base located (lamTerm domain body) (lamTerm next body) :=
  termStep_fill (outer := atomsAt stage) (.apply "Lam" [] .hole [.lambda none body.1])
    (fun term => (lamTerm term body).2)
    (fun fired => step_lamDomain (by simp [located_rewrites, atomsReduce_rewrites]) body.1 none
      fired) step

theorem termStep_lamBody {stage : List TypeExpr}
    {body next : Contexts.Term located (atomsAt (.base "Atom" :: stage))}
    (domain : Contexts.Term located (atomsAt stage)) (step : TermStep base located body next) :
    TermStep base located (lamTerm domain body) (lamTerm domain next) :=
  termStep_fill (outer := atomsAt stage) (.apply "Lam" [domain.1] (.lambda none .hole) [])
    (fun term => (lamTerm domain term).2)
    (fun fired => step_lamBody (by simp [located_rewrites, atomsReduce_rewrites]) domain.1 none
      fired) step

theorem termStep_piDomain {stage : List TypeExpr}
    {domain next : Contexts.Term located (atomsAt stage)}
    (body : Contexts.Term located (atomsAt (.base "Atom" :: stage)))
    (step : TermStep base located domain next) :
    TermStep base located (piTerm domain body) (piTerm next body) :=
  termStep_fill (outer := atomsAt stage) (.apply "Pi" [] .hole [.lambda none body.1])
    (fun term => (piTerm term body).2)
    (fun fired => step_piDomain (by simp [located_rewrites, atomsReduce_rewrites]) body.1 none
      fired) step

theorem termStep_piBody {stage : List TypeExpr}
    {body next : Contexts.Term located (atomsAt (.base "Atom" :: stage))}
    (domain : Contexts.Term located (atomsAt stage)) (step : TermStep base located body next) :
    TermStep base located (piTerm domain body) (piTerm domain next) :=
  termStep_fill (outer := atomsAt stage) (.apply "Pi" [domain.1] (.lambda none .hole) [])
    (fun term => (piTerm domain term).2)
    (fun fired => step_piBody (by simp [located_rewrites, atomsReduce_rewrites]) domain.1 none
      fired) step

theorem termStep_runSubject {stage : List TypeExpr}
    {subject next : Contexts.Term located (atomsAt stage)}
    (space : Contexts.Term located (spacesAt stage)) (step : TermStep base located subject next) :
    TermStep base located (runTerm space subject) (runTerm space next) :=
  termStep_fill (outer := atomsAt stage) (.apply "prime-run" [space.1] .hole [])
    (fun term => (runTerm space term).2)
    (fun fired => step_runSubject (by simp [located_rewrites, atomsReduce_rewrites]) space.1
      fired) step

/-! ## The steps of a table are transitions of the runs -/

/-- A beta contraction at the root is a step between the atoms, at every
depth and under every evaluator. -/
theorem located_beta_stepAt (depth : Nat) (domain body argument : LF.Term) :
    StepAt base located 1 (atomAt depth (.app (.lam domain body) argument))
      (atomAt depth (subst0 argument body)) := by
  have step := step_beta (base := base) (lang := located)
    (by simp [located_rewrites, atomsReduce_rewrites])
    (atomAt depth domain) (atomAt (depth + 1) body) (atomAt depth argument) none
  rw [instantiateBVar_atomAt] at step
  exact step

/-- **The root step of the run of an instance of a rule**: to the run of the
run of the instance of its right side, which is the run of that instance. -/
theorem runAtom_rule_termStep {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {rule : Dedukti.RewriteRule} (member : rule ∈ rules) (depth : Nat)
    (assignment : Nat → LF.Term) :
    TermStep locatedEvaluator located (runAtom rules depth (inst assignment rule.lhs))
      (runAtom rules depth (inst assignment rule.rhs)) := by
  refine ⟨runAtom rules depth (inst assignment rule.lhs),
    runTerm (spaceAt (ruleSpaceTerm rules) _) (runAtom rules depth (inst assignment rule.rhs)),
    .refl _, ⟨1, step_locatedRoot (by simp [located_rewrites, atomsReduce_rewrites]) ?_⟩,
    runTerm_run _ _ _⟩
  show runPattern (ruleSpace rules) (atomAt depth (inst assignment rule.rhs)) ∈
    locatedAnswers (ruleSpace rules) (atomAt depth (inst assignment rule.lhs))
  rw [locatedAnswers_of_plain (settle_ruleSpace rules) (settle_atomAt _ depth)
    (tokens_atomAt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) _ depth)]
  exact List.mem_map.mpr ⟨_, atomAt_mem_matchResults firstOrder bound member depth assignment, rfl⟩

/-- **Every step of a term, in a theory whose rules are those of a list and
which has no definition, is a transition between the runs of the atoms in the
space of the list**, at every depth. -/
theorem runAtom_termStep {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (listed : ∀ rule, theory.rule rule → rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {source next : LF.Term}
    (step : Dedukti.Step theory source next) :
    ∀ depth : Nat, TermStep locatedEvaluator located (runAtom rules depth source)
      (runAtom rules depth next) := by
  cases step with
  | @inContext context redex contractum root =>
      induction context with
      | hole =>
          intro depth
          cases root with
          | beta domain body argument =>
              exact termStep_of_step ⟨2, step_runSubject
                (by simp [located_rewrites, atomsReduce_rewrites]) _
                (located_beta_stepAt depth domain body argument)⟩
          | delta defined =>
              rw [undefined] at defined
              cases defined
          | @rule rule assignment member =>
              exact runAtom_rule_termStep firstOrder bound (listed rule member) depth assignment
      | appFunction rest argument ih =>
          intro depth
          exact termStep_between
            (runTerm_app (spaceAt (ruleSpaceTerm rules) _) (locatedAtom depth _)
              (locatedAtom depth argument))
            (termStep_appFunction (runAtom rules depth argument) (ih depth))
            (.symm _ _ (runTerm_app (spaceAt (ruleSpaceTerm rules) _) (locatedAtom depth _)
              (locatedAtom depth argument)))
      | appArgument function rest ih =>
          intro depth
          exact termStep_between
            (runTerm_app (spaceAt (ruleSpaceTerm rules) _) (locatedAtom depth function)
              (locatedAtom depth _))
            (termStep_appArgument (runAtom rules depth function) (ih depth))
            (.symm _ _ (runTerm_app (spaceAt (ruleSpaceTerm rules) _) (locatedAtom depth function)
              (locatedAtom depth _)))
      | piDomain rest body ih =>
          intro depth
          exact termStep_between
            (runTerm_pi (ruleSpaceTerm rules) (locatedAtom depth _) (locatedAtom (depth + 1) body))
            (termStep_piDomain (runAtom rules (depth + 1) body) (ih depth))
            (.symm _ _ (runTerm_pi (ruleSpaceTerm rules) (locatedAtom depth _)
              (locatedAtom (depth + 1) body)))
      | piBody domain rest ih =>
          intro depth
          exact termStep_between
            (runTerm_pi (ruleSpaceTerm rules) (locatedAtom depth domain) (locatedAtom (depth + 1) _))
            (termStep_piBody (runAtom rules depth domain) (ih (depth + 1)))
            (.symm _ _ (runTerm_pi (ruleSpaceTerm rules) (locatedAtom depth domain)
              (locatedAtom (depth + 1) _)))
      | lamDomain rest body ih =>
          intro depth
          exact termStep_between
            (runTerm_lam (ruleSpaceTerm rules) (locatedAtom depth _) (locatedAtom (depth + 1) body))
            (termStep_lamDomain (runAtom rules (depth + 1) body) (ih depth))
            (.symm _ _ (runTerm_lam (ruleSpaceTerm rules) (locatedAtom depth _)
              (locatedAtom (depth + 1) body)))
      | lamBody domain rest ih =>
          intro depth
          exact termStep_between
            (runTerm_lam (ruleSpaceTerm rules) (locatedAtom depth domain)
              (locatedAtom (depth + 1) _))
            (termStep_lamBody (runAtom rules depth domain) (ih (depth + 1)))
            (.symm _ _ (runTerm_lam (ruleSpaceTerm rules) (locatedAtom depth domain)
              (locatedAtom (depth + 1) _)))

#print axioms related_fill
#print axioms termStep_fill
#print axioms termStep_appFunction
#print axioms termStep_lamBody
#print axioms termStep_runSubject
#print axioms runTerm_app
#print axioms runTerm_lam
#print axioms runTerm_run
#print axioms runAtom_rule_termStep
#print axioms runAtom_termStep

end Mettapedia.Logic.HostingStyles.LocatedAtoms
