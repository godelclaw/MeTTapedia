import Mettapedia.Logic.HostingStyles.AmbientRegions.Containment

/-!
# The run of the atom of a λΠ term in the space of a list of rules

`run(space of rules, atom of term)` is a term of every presentation that
carries atoms and declares the run (`runAtomIn`), at every depth; it has no
quotation and no dropping, so it is the only term of its class
(`eq_runAtomIn_of_related`).

**In the contained presentation its transitions are the runs of the atoms of
the steps of the term by the rules of the run's space, at every ambient space
that answers nothing for a run** (`contained_runAtom_step_iff`,
`contained_runAtom_termStep_iff`): the ambient space is not in the statement.
This is containment for the theories given by a table.

**Negative** (`contained_runCoin_normal`): the run of `choose heads tails` in
the empty space has no transition, at the ambient space of the two rules of
choice.
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
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

/-! ## The terms -/

section Terms

variable {presentation : ValidatedLanguageDef}

/-- **The space of a list of rules**, as a space of a presentation that
carries atoms, at any stage: it is closed. -/
def ruleSpaceIn (carries : CarriesAtoms presentation.language) (rules : List Dedukti.RewriteRule)
    (stage : List TypeExpr) : Contexts.Term presentation.language ⟨.base "Space", stage⟩ :=
  ⟨ruleSpace rules, wellSorted_extendOuter (ruleSpace_wellSorted_of carries rules) stage⟩

@[simp] theorem ruleSpaceIn_val (carries : CarriesAtoms presentation.language)
    (rules : List Dedukti.RewriteRule) (stage : List TypeExpr) :
    (ruleSpaceIn carries rules stage).1 = ruleSpace rules :=
  rfl

/-- **The run of the atom of a λΠ term in the space of a list of rules**, at
the stage of `depth` binders. -/
def runAtomIn (declares : DeclaresRun presentation.language)
    (carries : CarriesAtoms presentation.language) (rules : List Dedukti.RewriteRule) (depth : Nat)
    (term : LF.Term) : Contexts.Term presentation.language (atomInterface depth) :=
  runTermIn declares (ruleSpaceIn carries rules (List.replicate depth (.base "Atom")))
    (atomTermIn carries depth term)

@[simp] theorem runAtomIn_val (declares : DeclaresRun presentation.language)
    (carries : CarriesAtoms presentation.language) (rules : List Dedukti.RewriteRule) (depth : Nat)
    (term : LF.Term) :
    (runAtomIn declares carries rules depth term).1 =
      runPattern (ruleSpace rules) (atomAt depth term) :=
  rfl

/-- The application of an atom to an atom. -/
def appTermIn (carries : CarriesAtoms presentation.language) {stage : List TypeExpr}
    (function argument : Contexts.Term presentation.language ⟨.base "Atom", stage⟩) :
    Contexts.Term presentation.language ⟨.base "Atom", stage⟩ :=
  ⟨.apply "App" [function.1, argument.1],
    wellSorted_apply_two (lang := presentation.language) (label := "App") (firstName := "f")
      (secondName := "a") (carries applicationConstructor (by decide)) function.2 argument.2⟩

@[simp] theorem appTermIn_val (carries : CarriesAtoms presentation.language) {stage : List TypeExpr}
    (function argument : Contexts.Term presentation.language ⟨.base "Atom", stage⟩) :
    (appTermIn carries function argument).1 = .apply "App" [function.1, argument.1] :=
  rfl

/-- The run of the atom of a term has no dropping. -/
theorem tokens_drop_runAtom (rules : List Dedukti.RewriteRule) (depth : Nat) (term : LF.Term) :
    tokens dropLabel (runPattern (ruleSpace rules) (atomAt depth term)) = 0 := by
  simp [runPattern, tokens, tokensList, dropLabel, tokens_drop_atomAt term depth,
    tokens_ruleSpace (counted := dropLabel) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) rules]

/-- The run of the atom of a term has no quotation to contract. -/
theorem contract_runAtom (rules : List Dedukti.RewriteRule) (depth : Nat) (term : LF.Term) :
    contract (runPattern (ruleSpace rules) (atomAt depth term)) =
      runPattern (ruleSpace rules) (atomAt depth term) := by
  rw [contract_runPattern', contract_ruleSpace, contract_atomAt]

theorem runAtomIn_injective (declares : DeclaresRun presentation.language)
    (carries : CarriesAtoms presentation.language) (rules : List Dedukti.RewriteRule)
    (depth : Nat) : Function.Injective (runAtomIn declares carries rules depth) := by
  intro first second same
  have patterns : runPattern (ruleSpace rules) (atomAt depth first) =
      runPattern (ruleSpace rules) (atomAt depth second) := congrArg Subtype.val same
  exact atomAt_injective depth (runPattern_injective patterns).2

/-- **The run of the atom of a term is the only term of its class.** -/
theorem eq_runAtomIn_of_related (declares : DeclaresRun presentation.language)
    (carries : CarriesAtoms presentation.language) (only : QuoteDropOnly presentation.language)
    (sorted : QuoteDropSorted presentation.language)
    (names : NamesOnlyDropped presentation.language unquotedSorts) {base : BasePremiseEvaluator}
    {rules : List Dedukti.RewriteRule} {depth : Nat} {term : LF.Term}
    {other : Contexts.Term presentation.language (atomInterface depth)}
    (related : (termSetoid base presentation.language (atomInterface depth)).r
      (runAtomIn declares carries rules depth term) other) :
    other = runAtomIn declares carries rules depth term :=
  eq_of_related_of_dropFree_in only sorted names
    (show resultIn unquotedSorts (.base "Atom") = true by decide)
    (contract_runAtom rules depth term) (tokens_drop_runAtom rules depth term) related

/-- **The transitions of the run of the atom of a term are the runs of the
atoms of the steps of a theory**, when the steps of the presentation from such
a run are.  The run of an atom is alone in its class, so a step up to the
static equivalence is a step. -/
theorem termStep_runAtomIn_iff (declares : DeclaresRun presentation.language)
    (carries : CarriesAtoms presentation.language) (only : QuoteDropOnly presentation.language)
    (sorted : QuoteDropSorted presentation.language)
    (names : NamesOnlyDropped presentation.language unquotedSorts) {base : BasePremiseEvaluator}
    {rules : List Dedukti.RewriteRule} {theory : Theory}
    (steps : ∀ {depth : Nat} {source : LF.Term} {target : Pattern},
      Step base presentation.language (runPattern (ruleSpace rules) (atomAt depth source)) target ↔
        ∃ next, target = runPattern (ruleSpace rules) (atomAt depth next) ∧
          Dedukti.Step theory source next)
    {depth : Nat} {source : LF.Term}
    {target : Contexts.Term presentation.language (atomInterface depth)} :
    TermStep base presentation.language (runAtomIn declares carries rules depth source) target ↔
      ∃ next, Dedukti.Step theory source next ∧
        target = runAtomIn declares carries rules depth next := by
  constructor
  · rintro ⟨redex, contractum, before, fired, after⟩
    obtain rfl := eq_runAtomIn_of_related declares carries only sorted names before
    obtain ⟨next, shape, step⟩ := steps.mp fired
    have same : contractum = runAtomIn declares carries rules depth next := Subtype.ext shape
    rw [same] at after
    exact ⟨next, step, eq_runAtomIn_of_related declares carries only sorted names after⟩
  · rintro ⟨next, step, rfl⟩
    exact ⟨runAtomIn declares carries rules depth source,
      runAtomIn declares carries rules depth next, Relation.EqvGen.refl _,
      steps.mpr ⟨next, rfl, step⟩, Relation.EqvGen.refl _⟩

end Terms

variable {admits : Pattern → Bool}

/-! ## In the contained presentation -/

/-- **The steps of the run of the atom of a term, in the space of a list of
rules, are the runs of the atoms of the steps of the term by those rules**, at
every ambient space that answers nothing for a run. -/
theorem contained_runAtom_step_iff (admitsAtoms : AdmitsAtoms admits) {ambientSpace : Pattern}
    (silent : RunSilent admits ambientSpace) {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (regionEvaluator admits ambientSpace) containedRun
        (runPattern (ruleSpace rules) (atomAt depth source)) target ↔
      ∃ next, target = runPattern (ruleSpace rules) (atomAt depth next) ∧
        Dedukti.Step theory source next := by
  rw [contained_run_step_iff silent (.inl (tokens_run_atomAt source depth))]
  constructor
  · rintro ⟨reached, rfl, step⟩
    obtain ⟨next, rfl, sourceStep⟩ :=
      (contained_atom_step_iff admitsAtoms firstOrder bound rulesIff undefined).mp step
    exact ⟨next, rfl, sourceStep⟩
  · rintro ⟨next, rfl, sourceStep⟩
    exact ⟨atomAt depth next, rfl,
      (contained_atom_step_iff admitsAtoms firstOrder bound rulesIff undefined).mpr
        ⟨next, rfl, sourceStep⟩⟩

/-- **On terms.**  For every ambient space that answers nothing for a run,
the transitions of the run of the atom of a term in the space of a list of
rules are the runs of the atoms of its steps by those rules. -/
theorem contained_runAtom_termStep_iff (admitsAtoms : AdmitsAtoms admits) {ambientSpace : Pattern}
    (silent : RunSilent admits ambientSpace) {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Contexts.Term containedRun (atomInterface depth)} :
    TermStep (regionEvaluator admits ambientSpace) containedRun
        (runAtomIn (presentation := containedPresentation) contained_declaresRun
          region_carriesAtoms.1 rules depth source) target ↔
      ∃ next, Dedukti.Step theory source next ∧
        target = runAtomIn (presentation := containedPresentation) contained_declaresRun
          region_carriesAtoms.1 rules depth next :=
  termStep_runAtomIn_iff (presentation := containedPresentation) contained_declaresRun
    region_carriesAtoms.1 contained_quoteDropOnly contained_quoteDropSorted
    contained_namesOnlyDropped
    (contained_runAtom_step_iff admitsAtoms silent firstOrder bound rulesIff undefined)

/-- **Positive**: the run of `choose heads tails` in the space of the two
rules of choice steps to the run of `heads`, at the empty ambient space. -/
theorem contained_runCoin_steps (admitsAtoms : AdmitsAtoms admits) :
    Step (regionEvaluator admits emptySpace) containedRun
      (runPattern (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 coin))
      (runPattern (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 (.con "heads"))) :=
  (contained_runAtom_step_iff admitsAtoms (runSilent_emptySpace admits) choiceRules_admitted.1
    choiceRules_admitted.2 withChoice_rules (fun _ => rfl)).mpr
    ⟨_, rfl, Dedukti.step_choose_left Theory.empty _ _⟩

/-- The two rules of choice have no variable as a left side. -/
theorem choiceRules_headed :
    ∀ rule ∈ [chooseLeft, chooseRight], ∀ index : Nat, rule.lhs ≠ .var index := by
  intro rule member index
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [chooseLeft, chooseRight, Dedukti.choose]

/-- The space of the two rules of choice answers nothing for a run, under
every guard. -/
theorem choiceSpace_runSilent (admits : Pattern → Bool) :
    RunSilent admits (ruleSpace [chooseLeft, chooseRight]) :=
  runSilent_ruleSpace admits choiceRules_admitted.1 choiceRules_headed

/-- **Negative: the ambient space does not reach in.**  The run of
`choose heads tails` in the empty space has no step at the ambient space of
the two rules of choice. -/
theorem contained_runCoin_normal (admitsAtoms : AdmitsAtoms admits) (target : Pattern) :
    ¬ Step (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) containedRun
      (runPattern (ruleSpace []) (atomAt 0 coin)) target := by
  intro step
  obtain ⟨next, -, sourceStep⟩ := (contained_runAtom_step_iff admitsAtoms
    (choiceSpace_runSilent admits) (rules := []) noRules_admitted.1 noRules_admitted.2
    (theory := Theory.empty)
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl)).mp step
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

#print axioms eq_runAtomIn_of_related
#print axioms termStep_runAtomIn_iff
#print axioms contained_runAtom_step_iff
#print axioms contained_runAtom_termStep_iff
#print axioms contained_runCoin_steps
#print axioms choiceSpace_runSilent
#print axioms contained_runCoin_normal
#print axioms tokens_drop_runAtom
#print axioms contract_runAtom
#print axioms runAtomIn_injective
#print axioms choiceRules_headed

end Mettapedia.Logic.HostingStyles.AmbientRegions
